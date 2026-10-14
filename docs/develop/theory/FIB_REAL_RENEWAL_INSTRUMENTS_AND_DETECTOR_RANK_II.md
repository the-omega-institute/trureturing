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

## 25. Sparse coherent renewal outputs separate the full integer phase quotient

**Definition 25.1 (Sparse family, actual preparation and count-preserving access).** Let $H\ge2$, let $K\subseteq\{1,\ldots,H\}$ contain $H$, put $r=|K|$, and fix strictly positive numbers $p_k$ with $\sum_{k\in K}p_k=1$. All phases belong to $\mathbb T=\mathbb R/(2\pi\mathbb Z)$. On $\mathbb C^{H+1}$ define

$$
c_k=\sqrt{p_k}e^{i\theta_k},\qquad
x_\theta=\sum_{k\in K}c_ke_{H-k},\qquad
Se_j=e_{j+1}\ (j<H),\quad Se_H=0,\quad
J_\theta=x_\theta e_H^*.
\tag{25.1}
$$

The branches are $A\mapsto SAS^*$ and $A\mapsto J_\theta A J_\theta^*$. This is Definition 23.1 with $H\ge2$; all probabilities are fixed and known. Use the chronological convention and conjugate-linear-first inner product of Definition 24.1. Replace its memory $\mathbb C^4$ by $\mathbb C^{H+1}$ and its three-coordinate support by $K$. An actual observed tick has posterior $x_\theta x_\theta^*$ by (23.3). The additional observation resources are exactly those of Definition 24.1, now for this memory: repeated coherent applications of the same isometry

$$
V_\theta\psi=S\psi\otimes|0\rangle+J_\theta\psi\otimes|1\rangle,
\tag{25.2}
$$

stable branch phases, no inaccessible record distinguishing the coherent histories, retention of the flags, and arbitrary terminal flag POVMs commuting with their total count. There is no intervention during the coherent run and no terminal memory measurement. The arbitrary within-count-sector terminal POVMs of Definition 24.1 remain available. These resources are hypotheses in addition to the classical instrument: (24.18), with the present $S,J_\theta$, still supplies the same CP branches while inaccessible orthogonal records remove history coherences. Thus neither a classical output law nor an occupation-phase quotient alone supplies this access.

For a chronological binary word $w=b_1\cdots b_n$, set $K_w=K_{b_n}\cdots K_{b_1}$, where $K_0=S$, $K_1=J_\theta$. Write

$$
\begin{aligned}
|\Psi_n(\theta)\rangle&=\sum_{w\in\{0,1\}^n}K_wx_\theta\otimes|w\rangle,\\
\Omega_n(\theta)&=\operatorname{Tr}_{\rm mem}|\Psi_n(\theta)\rangle\langle\Psi_n(\theta)|,\\
Q_n|w\rangle&=|w|_1|w\rangle,\\
\mathcal D_n(B)&=\frac1{2\pi}\int_0^{2\pi}e^{itQ_n}Be^{-itQ_n}\,dt,\qquad
T_n(\theta)=\mathcal D_n(\Omega_n(\theta)).
\end{aligned}
\tag{25.3}
$$

Take $T_0=1$. This $Q_n$ is Definition 24.1's total tick-count operator $N_1$, and $\mathcal D_n=\mathcal T_n$ in (24.3). Here (23.11) gives $S^*S+J_\theta^*J_\theta=I$, so the states are normalized. The integral is the usual $U(1)$ projection onto equal-charge blocks: [Bartlett–Rudolph–Spekkens, *Reference frames, superselection rules, and quantum information*, arXiv:quant-ph/0610030v3, §II.B, equations (7)–(10)](https://arxiv.org/html/quant-ph/0610030v3) uses total photon number; the present integer-valued charge is total tick count. Spectral expansion gives the same block projection here. For every allowed effect $E$, $\operatorname{Tr}(E\Omega_n)=\operatorname{Tr}(ET_n)$. Conversely all effects within each count block are allowed, so equality of $T_n$ is precisely equality of all allowed terminal measurement laws at that horizon.

Define the affine phase subgroup and the integer relation lattice by

$$
\Gamma_K=\{(a+bk)_{k\in K}:a,b\in\mathbb T\},\qquad
L_K=\left\{z\in\mathbb Z^K:\sum_kz_k=0,\ \sum_k kz_k=0\right\}.
\tag{25.4}
$$

**Theorem 25.2 (Actual-history separator, uniform horizon and finite measurement).** Under Definition 25.1, the following conclusions hold.

1. For every nonzero $z\in L_K$, define $z_k^\pm=\max\{\pm z_k,0\}$ and put

$$
z=z^+-z^-,\qquad
m_z=\sum_kz_k^+=\sum_kz_k^-,\qquad
s_z=\sum_k k z_k^+=\sum_k k z_k^-,\qquad
\ell_z=s_z+m_z.
\tag{25.5}
$$

Concatenate $z_k^+$ copies of the actual block $0^k1$ in increasing $k$ order to obtain $u_z$, and do the same with $z_k^-$ to obtain $v_z$. Then these are distinct words of length $\ell_z$ and count $m_z$, and

$$
\boxed{\langle u_z|T_{\ell_z}(\theta)|v_z\rangle
=A_z e^{i z\cdot\theta},\qquad
A_z=\prod_{k\in K}p_k^{|z_k|/2}>0.}
\tag{25.6}
$$

Thus every integer relation has an explicit accessible coherence with a nonzero coefficient and no sum of different characters. No trailing zero block is required. Appending $0^H$ to both words instead gives the coefficient $p_H A_z$ at horizon $\ell_z+H$.

2. Let $\mathcal Z$ be any finite generating family of the abelian group $L_K$, with its zero elements omitted, and put $N_{\mathcal Z}=\max_{z\in\mathcal Z}\ell_z$, taking this maximum to be zero if the family is empty. For every $N\ge N_{\mathcal Z}$ and every pair of phases $\theta,\theta'$,

$$
\boxed{
T_N(\theta)=T_N(\theta')
\quad\Longleftrightarrow\quad
\theta'-\theta\in\Gamma_K
\quad\Longleftrightarrow\quad
T_n(\theta)=T_n(\theta')\ \text{for every }n\ge0.}
\tag{25.7}
$$

Within this supplied shift/reset family, these conditions are also equivalent to memory-unitary equivalence of the averaged channels and to outcome-labeled instrument equivalence, with the meanings in Definition 24.1. The general-$H$ argument (24.7)–(24.9) supplies this connection under the hypotheses verified below. The generating family must generate the full integer kernel; a basis of its real span alone is insufficient.

3. An explicit finite generating family and a uniform horizon are available. Write $r=|K|\ge3$ and

$$
K=\{k_0<k_1<\cdots<k_{r-2}<k_{r-1}=H\},\quad
D=H-k_0,\quad
g=\gcd\{k-k_0:k\in K\},\quad d=D/g.
\tag{25.8}
$$

For every vector $y\in\mathbb N^{r-2}$ satisfying

$$
1\le |y|:=\sum_i y_i\le d,\qquad
\sum_{i=1}^{r-2}(k_i-k_0)y_i\equiv0\pmod D,
\tag{25.9}
$$

put $q(y)=D^{-1}\sum_i(k_i-k_0)y_i$ and define

$$
R(y)_{k_i}=y_i,\qquad R(y)_{k_0}=q(y)-|y|,\qquad R(y)_H=-q(y).
\tag{25.10}
$$

The finite set $\mathcal Z_*:=\{R(y):y\text{ satisfies these conditions}\}$ generates $L_K$. Its corresponding histories satisfy

$$
\ell_{R(y)}=\sum_{i=1}^{r-2}(k_i+1)y_i\le Hd,
\qquad
|\mathcal Z_*|\le {d+r-2\choose r-2}-1.
\tag{25.11}
$$

Consequently the single horizon

$$
\boxed{N=H(H-\min K)/g\le H(H-1)}
\tag{25.12}
$$

always suffices. One may use the smaller computable value $N_{\mathcal Z_*}$ instead. For $r\le2$, $L_K=0$, all phases lie in one affine orbit, every $T_n$ is phase independent, and $N=0$ suffices.

4. If $M=|\mathcal Z|>0$, two fixed three-outcome projective measurements for each $z\in\mathcal Z$, all made only at terminal time $N\ge N_{\mathcal Z}$, give one distribution with $6M$ labeled outcomes whose equality is equivalent to (25.7). The labels retain the measurement setting. The construction requires no observation of the final memory. A lattice basis gives $M=r-2$ relation settings, each with two quadrature choices, when $r\ge3$, with the computable horizon $N_{\mathcal Z}$; thus there are $2(r-2)$ projective settings and $6(r-2)$ labeled outcomes. The explicit uniform bound (25.12) instead uses $\mathcal Z_*$ and its stated cardinality bound. Neither construction asserts a generally optimal horizon.

From an arbitrary initial memory density in this family, measuring the classical output until its first tick prepares the required memory in at most $H+1$ instrument uses almost surely. Hence each trial needs at most $H+1+N$ uses, of which $N$ are coherent. This is a bound on logical uses, with the memory, retained flags, settings, and records accounted for below, rather than an optimization over physical hardware.

Proof. *All actual histories, including unfinished gaps.* A chronological word with $m$ ticks has a unique decomposition

$$
w=0^{a_1}1\cdots0^{a_m}1\,0^t.
\tag{25.13}
$$

Set $c_a=0$ for nonnegative $a$ outside $K$, including $a=0$. Since $e_H^*S^a x_\theta=c_a$,

$$
J_\theta S^a x_\theta=c_a x_\theta,\qquad
K_wx_\theta=\left(\prod_{j=1}^m c_{a_j}\right)S^t x_\theta.
\tag{25.14}
$$

This includes the no-tick case with empty product. Words with a completed gap outside $K$ have zero amplitude; a tail exceeding $H$ also has zero amplitude.

For two nonzero words $w,v$ of the same length and count $m$, let $a,b\in\mathbb N^K$ be their completed-gap multiplicity vectors and let their tails be $t,u$. Then

$$
\begin{aligned}
n&=m+\sum_kka_k+t=m+\sum_kkb_k+u,\\
\langle w|T_n(\theta)|v\rangle
&=c^a\overline{c^b}
\sum_{\substack{k,l\in K\\ k\ge t,\ l\ge u\\ k-t=l-u}}
c_k\overline{c_l},
\qquad c^a=\prod_kc_k^{a_k}.
\end{aligned}
\tag{25.15}
$$

The equality $k-t=l-u$ is exactly equality of the final memory basis coordinate $H-(k-t)$. Each summand is a positive coefficient depending only on $p$ times the character whose exponent vector is

$$
z=a+\mathbf e_k-b-\mathbf e_l\in L_K:
\quad\sum_jz_j=0,\quad
\sum_jjz_j=(u-t)+(k-l)=0.
\tag{25.16}
$$

The completed-gap equality gives $\sum_j j(a_j-b_j)=u-t$, while final-coordinate equality gives $k-l=t-u$, so the weighted sum in (25.16) is zero. Entries between different count sectors vanish. Formula (25.15) specifies the entire density, including incomplete terminal gaps; it does not restrict attention to a chosen pair of words.

*A pure character in actual completed-tick histories.* The constraints defining $L_K$ are the homogenized exponent relations for the column configuration $(1,k)_{k\in K}$. The corresponding binomials are the standard ones in [Sottile, *Toric ideals, real toric varieties, and the algebraic moment map*, arXiv:math/0212044v3, Theorem 2.2 and Corollary 2.3](https://arxiv.org/html/math/0212044v3): the two nonnegative exponents have equal images under the homogenized integer matrix. That algebraic relation alone supplies no permitted output coherence. Here the first equality of sums gives equal tick counts, the second gives equal zero counts, and (25.14) supplies their actual memory amplitudes. For the words $u_z,v_z$, both tails are zero and (25.14) leaves the same normalized vector $x_\theta$ in the memory. In particular, $K_{u_z}x_\theta=(\prod_kc_k^{z_k^+})x_\theta$ and $K_{v_z}x_\theta=(\prod_kc_k^{z_k^-})x_\theta$, both nonzero. Tracing the memory gives

$$
\left(\prod_kc_k^{z_k^+}\right)
\overline{\left(\prod_kc_k^{z_k^-}\right)}\|x_\theta\|^2
=A_z e^{iz\cdot\theta},
\tag{25.17}
$$

which proves (25.6). The terminal factor in (25.15) is here $\sum_kp_k=1$, so it introduces no other character. The two histories have different gap multiplicities but equal count and duration. Merely permuting one multiset would give $z=0$ and no phase contrast. If the common tail is $H$, the identity $S^Hx_\theta=c_He_H$ instead contributes $p_H$, proving the appended-word assertion. No projection onto that memory vector is performed.

*One common horizon without an intermediate observation.* The marginal identity needed to use a single horizon is

$$
\operatorname{Tr}_{n+1,\ldots,N}T_N(\theta)=T_n(\theta)
\qquad(0\le n\le N).
\tag{25.18}
$$

Indeed later isometries act only on the memory and new flags. Tracing those systems is trace preserving, even on a memory entangled with the earlier flags, so $\operatorname{Tr}_{n+1,\ldots,N}\Omega_N=\Omega_n$. Also $Q_N=Q_n\otimes I+I\otimes Q_{N-n}$, and for every operator $B$ on the flags,

$$
\operatorname{Tr}_{n+1,\ldots,N}\mathcal D_N(B)
=\mathcal D_n\!\left(\operatorname{Tr}_{n+1,\ldots,N}B\right).
\tag{25.19}
$$

To see this, split each exponential into the two tensor factors in the defining integral; the suffix conjugation disappears under its partial trace. Thus (25.18) uses no independence assumption on the flags. It is a terminal marginal, not an intermediate measurement.

*The full integer kernel and the compact affine torus.* The distinction between lattice generation and real spanning is the Laurent-character distinction in [Eisenbud–Sturmfels, *Binomial Ideals*, arXiv:alg-geom/9401001v1, Theorem 2.1(b)–(d)](https://arxiv.org/html/alg-geom/9401001v1). Part (b) uses an integer lattice basis to generate the Laurent binomial ideal; part (c) identifies saturated lattices with prime such ideals over an algebraically closed field; part (d) gives distinct character extensions across a finite-index enlargement when the index is coprime to the field characteristic, in particular over $\mathbb C$. Positivity of all $p_k$ keeps the amplitude coordinates nonzero. The following direct circle calculation determines the compact annihilator needed by these actual histories; it does not infer compact-circle conclusions merely from real nullspaces or complex algebraic closures.

Let $\delta\in\mathbb T^K$ annihilate $L_K$, meaning $z\cdot\delta=0$ in $\mathbb T$ for every $z\in L_K$. For $r\ge2$ choose $k_0=\min K$, put $d_i=k_i-k_0$ for every other index, and let $g=\gcd_i d_i>0$. Select integers $t_i$ with $\sum_i t_i d_i=g$. Put

$$
\eta_i=\delta_{k_i}-\delta_{k_0},\qquad
\beta=\sum_i t_i\eta_i\in\mathbb T.
\tag{25.20}
$$

Every integer vector $n$ with $\sum_i d_i n_i=0$ corresponds to the relation $z_{k_i}=n_i$, $z_{k_0}=-\sum_i n_i$. Apply the annihilation hypothesis to $n=\mathbf e_i-(d_i/g)t$. It gives $\eta_i=(d_i/g)\beta$. Choose $b\in\mathbb T$ with $gb=\beta$, which is possible because multiplication by $g$ on a circle is onto, and put $a=\delta_{k_0}-bk_0$. Then $\delta_k=a+bk$ for every $k\in K$. The converse follows by the two defining equations of $L_K$. For $r=1$ one has $K=\{H\}$ and the same conclusion follows by taking $a=\delta_H$, $b=0$. The case $r=0$ is excluded by $H\in K$. Therefore

$$
\{\delta:z\cdot\delta=0\ \forall z\in L_K\}=\Gamma_K.
\tag{25.21}
$$

The kernel $L_K$ is saturated: if $tz\in L_K$ for an integer $t\ne0$, its two integer defining sums force $z\in L_K$. When $r\ge2$, the map $(a,b)\mapsto(a+bk)_k$ has a stabilizer of order $g$, namely $gb=0$ and $a=-bk_0$. Indeed all $(k-k_0)b$ vanish exactly when $gb=0$, by the same integer greatest-common-divisor identity. For $r=1$ the stabilizer is instead the circle $a=-Hb$; the affine image is still the whole phase circle. These stabilizers do not add undetected points to (25.21). For $r\ge2$ the quotient $\mathbb T^K/\Gamma_K$ has character group $L_K$, a free group of rank $r-2$; it has no additional discrete ambiguity. In particular, this argument does not replace integer relations by a real nullspace.

Equality of $T_N$ for $N\ge N_{\mathcal Z}$ now gives equality of every coherence (25.6) by (25.18). Division by the known positive $A_z$ yields $e^{iz\cdot(\theta'-\theta)}=1$ for the generators, hence for all of $L_K$. Equation (25.21) gives affine equivalence.

For the converse, (25.15)–(25.16) show directly that every entry of every $T_n$ is invariant under affine phase changes. One can also keep track of the post-herald preparation phase explicitly. If $\theta'_k=\theta_k+a+bk$ and $D_be_j=e^{-ibj}e_j$, then

$$
\begin{aligned}
x_{\theta'}&=e^{i(a+bH)}D_bx_\theta,\\
S&=e^{ib}D_bSD_b^*,\qquad
J_{\theta'}=e^{ia}D_bJ_\theta D_b^*,\\
K'_w x_{\theta'}
&=e^{i[a(m+1)+b(n-m+H)]}D_bK_wx_\theta
\quad (|w|=n,\ |w|_1=m).
\end{aligned}
\tag{25.22}
$$

After tracing the memory, the remaining transformation of $\Omega_n$ is conjugation by $e^{i(a-b)Q_n}$; the global factor has canceled. Its count twirl is unchanged. This establishes (25.7) with the actual phase-dependent preparation included. It also proves the $r\le2$ assertion, since the corresponding integer kernel is zero and (25.21) gives one orbit. For two distinct labels the two integer equations have rank two; for one label the first equation alone forces $z=0$. Thus there are no omitted phase invariants in either edge case.

*Application to the existing channel and labeled-instrument orbits.* Apply the general-$H$ argument in the proof of Theorem 24.2, equations (24.7)–(24.9), to Definition 23.1 with the present $H,K,p$. Its endpoint hypothesis is exactly $c_H=\sqrt{p_H}e^{i\theta_H}\ne0$. Its shift is the same single nilpotent block on $\mathbb C^{H+1}$ and its reset has norm-one range vector $x_\theta$. The two Kraus operators are independent because the first $H$ columns of $S$ are nonzero and those of $J_\theta$ are zero. Formula (24.7) therefore has the same two singular projective lines, with ranks $H$ and one; $H\ge2$ makes them distinct even when the support is sparse. Exact channel equivalence gives the Choi identity $FF^*=GG^*$ for the two full-column-rank Kraus vectorizations in that proof. Its left-inverse step forces the Kraus mixing matrix to be unitary, and the distinct singular ranks force it to be diagonal. The resulting shift-normalizer identity (24.8) fixes $Ue_j=e^{i\gamma}e^{ijt}e_j$, so its reset coefficients give (24.9) on precisely the nonzero indices $k\in K$. None of those steps requires a positive coefficient at a missing interior index. Conversely the diagonal unitary already specified after (24.9) realizes every affine difference for each labeled CP branch. Hence the channel and labeled-instrument orbits supplied there are exactly $\Gamma_K$ here, and (25.7) identifies them from the present finite output laws. This application classifies this specified family only, without a claim about all minimum-dimensional CP realizations of its classical process.

*Integral generation with a uniform horizon.* For the explicit generating family, suppose $r\ge3$. The residues $k_i-k_0$ for the interior indices generate, together with the zero residue of $D$, a subgroup of $\mathbb Z/D\mathbb Z$ of order $d=D/g$. Every $R(y)$ in (25.10) lies in $L_K$. Because $0<k_i-k_0<D$ and $y\ne0$, one has $0<q(y)<|y|$: its positive part consists precisely of the interior entries $y_i$, and its negative part is supported at $k_0,H$. Its length and the stated length bound follow immediately, since $k_i+1\le H$.

It remains essential to prove integral generation. For each interior $i$, let

$$
h_i=\frac{D}{\gcd(D,k_i-k_0)}\le d.
\tag{25.23}
$$

Then $R(h_i\mathbf e_i)\in\mathcal Z_*$. Given any $z\in L_K$, add nonnegative integer multiples of these relations until every interior coordinate is nonnegative. Call the resulting interior vector $y$. The two equations defining $L_K$ force its endpoint coordinates to be exactly those of $R(y)$, and $\sum_i(k_i-k_0)y_i\equiv0\pmod D$.

If $y\ne0$, view its entries as a multiset of residues with sum zero. Partition it into minimal nonempty zero-sum submultisets. Each such submultiset has at most $d$ terms: in any ordering of a minimal submultiset of length $h$, the partial sums at positions $0,\ldots,h-1$ are distinct, since a repeated partial sum would give a proper nonempty zero-sum submultiset. There are only $d$ possible sums in the subgroup. Consequently each piece is a permitted vector in (25.10), and additivity of $R$ writes $R(y)$ as a sum of elements of $\mathcal Z_*$. Subtract the relations previously added to recover $z$. This proves generation of the entire lattice, not just a finite-index subgroup. Counting all nonzero nonnegative vectors with coordinate sum at most $d$ gives the displayed bound on $|\mathcal Z_*|$. This proves (25.12).

For a basis with fewer relation settings, integer column operations give a constructive alternative: for the row $(k_i-k_0)_{i=1}^{r-1}$ the Euclidean algorithm produces a unimodular integer matrix $U$ taking it to $(g,0,\ldots,0)$. The last $r-2$ columns of $U$ give a basis of its integer kernel: for any integer vector in that kernel, its coordinates under $U^{-1}$ are integers and its first coordinate is zero because $g>0$; the other coordinates are unconstrained. Appending the coordinate minus the column sum at $k_0$ gives a basis of $L_K$. The formula $N_{\mathcal Z}=\max_z\sum_k(k+1)z_k^+$ is an explicit computable bound for that basis. No bound on its horizon is inferred merely from being a real basis.

*Finite terminal measurement.* For the measurements, abbreviate $u=u_z$, $v=v_z$ and define the unit vectors

$$
|R_\pm\rangle=\frac{|u\rangle\pm|v\rangle}{\sqrt2},\qquad
|I_\pm\rangle=\frac{|u\rangle\mp i|v\rangle}{\sqrt2}.
\tag{25.24}
$$

For $B\in\{R,I\}$ let $P^B_\pm=|B_\pm\rangle\langle B_\pm|$ and $P^B_0=I-P^B_+-P^B_-$. These form projective measurements on $\ell_z$ flags. Each projector commutes with $Q_{\ell_z}$ because $u,v$ have the same count. At terminal time $N$, use $\widetilde P^{B,z}_o=P^B_o\otimes I_{N-\ell_z}$. These are still projectors and commute with $Q_N$. By (25.6) and (25.18), their conditional probability differences are

$$
\begin{aligned}
\Pr(+\mid z,R)-\Pr(-\mid z,R)&=2A_z\cos(z\cdot\theta),\\
\Pr(+\mid z,I)-\Pr(-\mid z,I)&=2A_z\sin(z\cdot\theta).
\end{aligned}
\tag{25.25}
$$

Choose $(z,B)$ uniformly among the $2M$ settings and retain that setting in the output. Equivalently use the single POVM

$$
F_{z,B,o}=\frac1{2M}\widetilde P^{B,z}_o,
\qquad z\in\mathcal Z,\ B\in\{R,I\},\ o\in\{+,-,0\}.
\tag{25.26}
$$

Its effects sum to $I$ and commute with $Q_N$. Equality of its joint distribution gives both components of every character in (25.25), hence (25.7). Conversely, affine-equivalent phases give the same $T_N$ by (25.7) and therefore the same probabilities for all these effects. For $M=0$, a single deterministic outcome suffices. The equality statement concerns exact probability laws. For $r\ge3$ the affine quotient has positive dimension, whereas a fixed finite number of outcomes from this finite alphabet has only finitely many possible records. Such a record cannot determine every point of the continuous quotient with zero error. The separator is therefore not finite-sample exact phase recovery; repetitions estimate its probabilities. No perfect discrimination statement for arbitrary stronger access is being made.

*Actual herald and separately counted resources.* For any initial density $\sigma$, the probability that the first tick follows $a$ zeros is, by the same calculation as (24.17),

$$
\Pr_\sigma(0^a1)
=\operatorname{Tr}\bigl(J_\theta S^a\sigma(S^*)^aJ_\theta^*\bigr)
=\sigma_{H-a,H-a}\quad(0\le a\le H),
\qquad
\Pr_\sigma(0^{H+1})=0.
\tag{25.27}
$$

The first $H+1$ mutually exclusive probabilities sum to one, since $S^{H+1}=0$ and $\operatorname{Tr}\sigma=1$. At the first tick the nonzero branch output is a positive scalar times $x_\theta x_\theta^*$, by (23.3). Monitoring until that tick therefore prepares the required memory in at most $H+1$ uses almost surely. Stop monitoring future flags then and retain the next $N$ outputs coherently. Reherald before each trial, including after a terminal measurement has changed the memory: the reset identity holds for every conditional input density. The fixed stable device and independent setting choice then give the same post-herald distribution on each trial. These conclusions require neither stationary initialization nor a memory readout.

For $M>0$, a sufficient logical apparatus has source memory $\mathbb C^{H+1}$, $N$ stored two-dimensional output registers of joint dimension $2^N$, a reusable two-level herald detector, a $2M$-valued setting register and a three-level outcome pointer. A controller may use the $N+3$ states $\mathrm{wait},\mathrm{captured}_0,\ldots,\mathrm{captured}_N,\mathrm{done}$. These are separate resources. Retaining the waiting time adds a classical record with $H+1$ possible values; retaining the selected setting and outcome adds a $6M$-valued record per trial, or a processor that accumulates the corresponding frequencies. Neither the source memory nor the controller absorbs these records for free. For $M=0,N=0$, the setting and pointer may be replaced by a deterministic outcome; the herald remains a sufficient preparation if one is required.

For the selected projective measurement at time $N$, its effects $\widetilde P_o$ admit a pointer coupling

$$
W=\sum_{o\in\{+,-,0\}}\widetilde P_o\otimes R_o,
\qquad
R_o|\mathrm{ready}\rangle=|o\rangle,
\qquad
[W,Q_N\otimes I]=0,
\tag{25.28}
$$

where each $R_o$ is a unitary on the three-level pointer. Orthogonality and completeness of the projectors make $W$ unitary, and their count commutators give the displayed conservation. This is a logical realization of the permitted terminal measurement, with no intermediate observation. The bound $H+1+N$ counts uses of the supplied instrument or isometry, including the herald; it is not an optimum for hardware dimension, elapsed time, control complexity or energy.

The phase-enhanced classical-process precedent remains the Liu–Elliott–Binder–Di Franco–Gu construction cited in the proof of Theorem 23.2. Here (25.14)–(25.16) provide the actual finite-history consumer of the integer relations. The conditioned five-mode pure amplitudes and total occupation measurements in [Hidden Relations continuation, C-76.1–C-78.3 and C-83.2](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS_CONTINUATION.md) have a different domain and charge action: their supplied two-copy tensor factors and occupation labels do not identify chronological renewal flags or provide this $V_\theta$. No such identification is used. The real choice $\theta=0$ remains in the same classical-law family by Theorem 23.2; separating phase orbits gives no complex-over-real generation advantage and supplies no native AURIC quantum-field implementation. $\square$

**Theorem 25.3 (Exact first separating horizon for $K=\{1,2,4\}$).** Let $H=4$, $K=\{1,2,4\}$ and fix any positive $p_1,p_2,p_4$ summing to one. The least coherent horizon at which $T_n$ separates all affine phase orbits is exactly six. Every $T_n$ for $0\le n\le5$ is independent of all phases. At horizon six,

$$
\boxed{
\langle010100|T_6(\theta)|001001\rangle
=c_1^2c_4\overline{c_2}^{\,3}
=p_1p_2^{3/2}\sqrt{p_4}\,
e^{i(2\theta_1-3\theta_2+\theta_4)}.}
\tag{25.29}
$$

The two quadratures of this coherence give a six-outcome terminal POVM separating the affine, channel and labeled-instrument orbits in this family. With the heralding construction, each trial uses at most eleven instrument applications, six of them coherent.

Proof. Solving the two integer equations gives

$$
L_K=\mathbb Z(2,-3,1).
\tag{25.30}
$$

In particular this vector is a primitive generator, so its circle-valued character is complete by (25.21). For these parameters,

$$
x=c_4e_0+c_2e_2+c_1e_3,\qquad S^2x=c_4e_2+c_2e_4.
\tag{25.31}
$$

The words $010100=(01)(01)00$ and $001001=(001)(001)$ both have length six and count two. By (25.14) their memory amplitudes are $c_1^2S^2x$ and $c_2^2x$. Their only common nonzero memory coordinate is $e_2$, yielding (25.29). Its coefficient is nonzero for every allowed fixed $p$.

For the lower bound, take any equal-count pair of length-$n$ words with $n\le5$ and nonzero history amplitudes. Their common count is $m$, and every completed block has length at least two, so $m\le2$. In every summand of their entry (25.15), the exponent is

$$
z=a+\mathbf e_k-b-\mathbf e_l\in L_K,
\qquad \sum_jz_j^+\le m+1\le3.
\tag{25.32}
$$

Every nonzero multiple of $(2,-3,1)$ has positive degree at least three. Thus $z\ne0$ would force $m=2$ and $z=\pm(2,-3,1)$. Reverse the words if necessary. Both nonnegative vectors $a+\mathbf e_k$ and $b+\mathbf e_l$ have total degree three. Since $z^+$ and $z^-$ also have degree three, there is no common part to cancel: they must equal $z^+$ and $z^-$ respectively. The negative side is three copies of label $2$, so $l=2$ and $b$ consists of two completed gaps of length two. That word already contains $(001)(001)$ in completed blocks and therefore has length at least six, a contradiction.

Every summand in every equal-count entry for $n\le5$ consequently has exponent zero and is independent of $\theta$. Invalid histories and unequal-count entries are zero independently of $\theta$. This proves phase independence of the whole density at every shorter horizon. Use (25.24)–(25.26) with $u=010100$, $v=001001$, $M=1$, $N=6$ and positive coefficient $p_1p_2^{3/2}\sqrt{p_4}$. The two probability differences recover the real and imaginary parts of (25.29), hence the complete character of (25.30). This proves sufficiency at six. For comparison, the complete-tick construction (25.6) has $m=3,s=6$, hence length nine; its version with a common $0^4$ tail has length thirteen. The improvement to six uses unequal terminal tails and their actual common memory coordinate. $\square$

**Proposition 25.4 (Primitive anchored triples can miss five affine classes).** Take $K=\{1,3,4,6\}$, $H=6$, with any strictly positive fixed probabilities. In coordinate order $(1,3,4,6)$ the two endpoint-anchored primitive triple relations

$$
t_1=(3,-5,0,2),\qquad t_2=(2,0,-5,3)
\tag{25.33}
$$

span the real relation space but generate a sublattice of index five in $L_K$. The missing relation

$$
z=(-1,1,1,-1)
\tag{25.34}
$$

has an actual length-nine coherence

$$
\langle(0001)(00001)|T_9(\theta)|(01)(0000001)\rangle
=\sqrt{p_1p_3p_4p_6}\,
e^{i(-\theta_1+\theta_3+\theta_4-\theta_6)}.
\tag{25.35}
$$

In particular the five phase vectors $\theta^{(j)}=(0,2\pi j/5,0,0)$ for $j=0,\ldots,4$ agree on both triple characters but belong to distinct affine orbits.

Proof. Projection of $L_K$ to its two interior coordinates identifies it with

$$
\{(u,v)\in\mathbb Z^2:2u+3v\equiv0\pmod5\}
=\{(u,v):u\equiv v\pmod5\}.
\tag{25.36}
$$

The image of the lattice generated by $t_1,t_2$ is $5\mathbb Z^2$. The interior lattice has index five in $\mathbb Z^2$, whereas $5\mathbb Z^2$ has index twenty-five, so the former modulo the latter has order five. This is the finite-index ambiguity described by Eisenbud–Sturmfels, Theorem 2.1(d), cited in the proof of Theorem 25.2, here realized by the five explicit circle phases below. Both triples are primitive because the gcd of their nonzero coordinates is one, and they are linearly independent. Moreover $t_1+t_2=-5z$. Their characters on $\theta^{(j)}$ are both one, while $e^{iz\cdot\theta^{(j)}}=e^{2\pi ij/5}$ takes five different values. By (25.21) these are distinct affine orbits, and (25.35) is (25.6) for the equal-duration gap multisets $\{3,4\}$ and $\{1,6\}$. This counterexample concerns the specified natural anchored triple list; it makes no assertion that the list of all primitive triples always has deficient index. $\square$

## 追加锚（本行以下为增补区）

## 26. Sharp post-tick horizons and identification after coefficient aggregation

**Definition 26.1 (Prepared windows, their complete datum and horizon completeness).** Use the supplied family of Definition 25.1, with $H\ge2$, $H\in K\subseteq\{1,\ldots,H\}$, known $p_k>0$ on $K$ and $\sum_{k\in K}p_k=1$. On $\mathbb C^{H+1}$ the coefficients, normalized reset vector and operators are

$$
c_k=\sqrt{p_k}e^{i\theta_k},\qquad
x_\theta=\sum_{k\in K}c_ke_{H-k},\qquad
Se_j=e_{j+1}\ (j<H),\quad Se_H=0,\qquad
J_\theta=x_\theta e_H^*,\qquad \theta\in\mathbb T^K,
\quad \mathbb T=\mathbb R/(2\pi\mathbb Z).
$$

Coefficients outside $K$, including $c_0$, are zero. The two CP branches are $`M\mapsto SMS^*`$ and $`M\mapsto J_\theta M J_\theta^*`$; their trace-preserving sum is $\mathcal E_\theta$. An actual observed tick prepares $`x_\theta x_\theta^*`$ by (23.3). A prepared post-tick window consists of $n$ subsequent applications of the accessible isometry

$$
V_\theta\psi=S\psi\otimes|0\rangle+J_\theta\psi\otimes|1\rangle,
$$

with the same stable branch representatives throughout the window and the trials. The chronological flags are retained coherently, no inaccessible system distinguishes their paths, and there is neither an intermediate intervention nor a terminal memory measurement. Every terminal effect commutes with the flag count $Q_n$ of (25.3), and arbitrary effects within each count sector are available. With $K_0=S$, $K_1=J_\theta$ and $K_w=K_{w_n}\cdots K_{w_1}$, the complete permitted datum is exactly the density $T_n(\theta)$ of (25.3):

$$
\begin{aligned}
|\Psi_n(\theta)\rangle&=\sum_{w\in\{0,1\}^n}K_wx_\theta\otimes|w\rangle,\qquad
\Omega_n(\theta)=\operatorname{Tr}_{\rm mem}|\Psi_n(\theta)\rangle\langle\Psi_n(\theta)|,\\
T_n(\theta)&=\sum_{m=0}^n P_m^{(n)}\Omega_n(\theta)P_m^{(n)},\qquad
Q_n|w\rangle=|w|_1|w\rangle,\qquad T_0=1.
\end{aligned}
$$

Here $P_m^{(n)}$ is the count-$m$ projection, and inner products are conjugate-linear in the first entry. Equality of $T_n$ is equality of every permitted terminal probability law. Write $\Gamma_K$ and $L_K$ for the affine subgroup and full integer kernel of (25.4):

$$
\Gamma_K=\{(\lambda+\nu k)_{k\in K}:\lambda,\nu\in\mathbb T\},\qquad
L_K=\left\{z\in\mathbb Z^K:\sum_k z_k=0,\ \sum_k k z_k=0\right\}.
$$

A horizon is complete if, for every two phases in this fixed $H,K,p$ family, equality of its $T_n$ is equivalent to memory-unitary equivalence of the averaged channels, with the meaning of Definition 24.1. Outcome-labeled instrument equivalence has that definition's fixed labels and one common memory unitary for both CP branches; scalar phases of Kraus representatives are allowed.

Repeated access in this class means separately prepared windows, each ending in a count-commuting measurement and a classical readout. A setting or window length may depend on previous terminal settings and outcomes. Conditional on that choice, the next window has the prescribed post-tick preparation and no quantum system from a preceding window is coupled to it. The record used for the horizon lower bounds consists of these terminal settings and outcomes. Heralding supplies the preparation; its waiting-time record is not an additional identification datum in this class. Joint measurements across trials subject only to a global count constraint, or additional observations of the preparation process, define different data. Completeness concerns exact probability laws, rather than exact inference of a continuous phase from a finite record.

**Theorem 26.2 (Universal exact horizon for three supported gaps).** Let $K=\{a<b<c\}$ with positive integer labels, $H=c$, and any fixed known positive $p_a,p_b,p_c$ of sum one. Put

$$
g=\gcd(b-a,c-a),\qquad
A=\frac{c-b}{g},\qquad B=\frac{b-a}{g},\qquad
d=A+B=\frac{c-a}{g},\qquad
\phi=A\theta_a-d\theta_b+B\theta_c.
\tag{26.1}
$$

The integer $d$ here is an arithmetic parameter; the memory dimension is $c+1$. The least complete single post-tick horizon in Definition 26.1 is exactly

$$
\boxed{N=(d-1)(b+1).}
\tag{26.2}
$$

For every $0\le n<N$ the entire $T_n(\theta)$ is phase independent. At $N$ the distinct actual words

$$
u=(0^a1)^A(0^c1)^{B-1}0^{c-b},\qquad
v=(0^b1)^{d-1}
\tag{26.3}
$$

have equal length and count, and their exact coherence is

$$
\boxed{C_\theta:=\langle u|T_N(\theta)|v\rangle
=R e^{i\phi}+\mathbf1_{\{d=2\}}p_ap_b,\qquad
R=p_a^{A/2}p_b^{d/2}p_c^{B/2}>0.}
\tag{26.4}
$$

For every $n\ge N$ and any two phases, the following are equivalent: equality of $T_n$, equality of $e^{i\phi}$, affine phase difference in $\Gamma_K$, memory-unitary equivalence of the averaged channels, and outcome-labeled instrument equivalence. One fixed six-label terminal law at $N$, retaining its quadrature setting, has exactly the same equivalences. All its signed probabilities are strictly positive at every phase. The shorter-horizon obstruction also holds for the independent repeated and classically adaptive readouts of Definition 26.1. Actual heralding gives a sufficient total bound of $c+1+N$ uses per trial, including the herald; the asserted optimum is the post-tick horizon.

**Proof.** The normalization and CP operators are precisely (23.2)–(23.3). Equation (23.11) gives $`S^*S+J_\theta^*J_\theta=I`$, so the proposed coherent applications are isometric and their flag states have trace one. No stationary initialization is imposed.

Use the all-history supplier (25.13)–(25.16), including its terminal tails, with the following parameter correspondence. Let $w,v'$ be any length-$n$, count-$m$ words of nonzero amplitude, let $f,h\in\mathbb N^K$ be their completed-gap multiplicities, and let $\rho,\sigma$ be their terminal zero-run lengths. Thus $f,h$ are the vectors denoted $a,b$ in (25.15), and $\rho,\sigma$ are its $t,u$. That formula gives

$$
\begin{aligned}
n&=m+\sum_j j f_j+\rho=m+\sum_j j h_j+\sigma,\\
\langle w|T_n|v'\rangle
&=c^f\overline{c^h}
\sum_{\substack{k,l\in K\\k\ge\rho,\ l\ge\sigma\\k-\rho=l-\sigma}}
c_k\overline{c_l},\qquad c^f=\prod_jc_j^{f_j}.
\end{aligned}
\tag{26.5}
$$

For each individual summand put $\alpha=f+\mathbf e_k$ and $\beta=h+\mathbf e_l$, where $\mathbf e_k$ is the multiplicity coordinate vector. Equation (25.16) states that its exponent $z=\alpha-\beta$ belongs to $L_K$, and its value is

$$
\left(\prod_{j\in K}p_j^{(\alpha_j+\beta_j)/2}\right)e^{iz\cdot\theta}.
\tag{26.6}
$$

This use of the published formula includes every ordering of completed gaps, every terminal tail and every count sector. A completed gap outside $K$, a vanishing tail, or an empty tail sum contributes zero; unequal-count entries are zero. The no-tick case uses the empty product in (25.14).

The two equations defining $L_K$ reduce, after eliminating $z_a$, to

$$
Bz_b+dz_c=0.
$$

Since $\gcd(A,B)=\gcd(B,d)=1$, their integral solutions, in coordinate order $(a,b,c)$, are exactly

$$
L_K=\mathbb Z(A,-d,B).
\tag{26.7}
$$

Suppose a summand in (26.5) has $z=t(A,-d,B)$ for an integer $t>0$. Its $b$ coordinate gives $\beta_b-\alpha_b=dt$, hence $\beta_b\ge dt$. Only one of these $b$ factors can come from its tail index $l$. The actual word $v'$ must therefore have at least $dt-1$ completed $b$-gap blocks. Their length alone gives

$$
n\ge (dt-1)(b+1)\ge(d-1)(b+1)=N.
\tag{26.8}
$$

For $t<0$, exchange the two words and obtain $n\ge(d|t|-1)(b+1)$. Common multiplicity factors do not change this inequality: the augmented multiplicities remain nonnegative, and all other completed blocks and the terminal tail consume nonnegative length. Thus the argument covers all nonzero multiples, with arbitrary common parts, orderings and tails. For $n<N$ every surviving summand has $z=0$ and is phase independent before any coefficient aggregation. All entries of the whole density are consequently phase independent.

For the witness, $Aa+Bc=db$. The words (26.3) have count $A+B-1=d-1$, and

$$
|u|=A(a+1)+(B-1)(c+1)+(c-b)=(d-1)(b+1)=|v|.
$$

Their first ticks occur at different positions, so they are distinct. The actual amplitude formula (25.14), with completed multiplicities $(A,0,B-1)$ and $(0,d-1,0)$ and tails $c-b,0$, gives

$$
K_ux=c_a^Ac_c^{B-1}S^{c-b}x,\qquad K_vx=c_b^{d-1}x.
\tag{26.9}
$$

In the tail sum (25.15) the support pairs must have difference $c-b>0$. The pair $(c,b)$ always survives. The only other possible pair is $(b,a)$, and it survives exactly when $b-a=c-b$. The pair $(c,a)$ has a larger difference. Therefore

$$
\langle x,S^{c-b}x\rangle
=\overline c_b c_c+\mathbf1_{\{b-a=c-b\}}\overline c_a c_b.
\tag{26.10}
$$

Multiplying by $c_a^Ac_c^{B-1}\overline c_b^{\,d-1}$ gives the term $c_a^Ac_c^B\overline c_b^{\,d}=Re^{i\phi}$. Equal spacings are equivalent to $A=B=1$, or $d=2$; exactly in that case the second term is $p_ap_b$. This proves (26.4), including its phase-independent offset and the absence of further terms in that entry.

For completeness on the circle, suppose the characters in (26.4) agree and write $\Delta_k=\theta'_k-\theta_k\in\mathbb T$. Put $X=\Delta_b-\Delta_a$ and $Y=\Delta_c-\Delta_a$. Character equality gives $dX=BY$ in $\mathbb T$. Choose integers $r_0,s_0$ with $r_0B+s_0d=1$ and set $\eta=r_0X+s_0Y$. Then

$$
B\eta=X,\qquad d\eta=Y.
$$

Multiplication by $g$ on $\mathbb T$ is surjective. Choose $\nu$ with $g\nu=\eta$ and put $\lambda=\Delta_a-a\nu$. Since $b-a=gB$ and $c-a=gd$, these identities give

$$
\Delta_k=\lambda+\nu k\quad(k=a,b,c).
\tag{26.11}
$$

Conversely every such affine difference annihilates (26.7). This integral Bézout calculation includes $g>1$ and introduces no unobserved finite-index phase classes. The character is nonconstant and ranges over the circle, so the phase independence below $N$ obstructs completeness for a nontrivial quotient. The lattice and Laurent-character background is [Eisenbud–Sturmfels, *Binomial Ideals*, arXiv:alg-geom/9401001v1, Section 2 and Theorem 2.1(b)–(d), PDF pp. 10–11](https://arxiv.org/pdf/alg-geom/9401001v1): over $\mathbb C$ an integer lattice basis generates the Laurent binomial ideal, saturation controls primeness, and finite-index enlargements have distinct character extensions in characteristic zero. Here all amplitude coordinates are nonzero by positivity of $p$; (26.7) is the full integer kernel. The compact-circle conclusion needed for the measured coefficient is the explicit calculation (26.11), rather than an inference from a real nullspace.

Apply the supplied-family classification in the proof of Theorem 24.2, (24.7)–(24.9), as already applied to sparse supports in Theorem 25.2. Its hypotheses here are $H=c\ge3$, the same single nilpotent shift on $\mathbb C^{c+1}$, the same rank-one reset $`x e_c^*`$ with $\|x\|=1$, and $c_H=c_c\ne0$. The Kraus operators are independent: the first $c$ columns of $S$ are nonzero, while those of $J$ are zero. The determinant (24.7) is $(-1)^c u^c v c_c$, with only the singular lines of ranks $c$ and one, which are distinct. The exact Choi identity and left-inverse step in that proof therefore force a diagonal unitary Kraus mixing, and the shift-normalizer identity (24.8) forces the affine difference (24.9) on the supported indices. Conversely its specified diagonal memory unitary implements every difference (26.11) separately on the labeled CP branches. Missing interior coefficients cause no failure of these hypotheses. Thus the actual averaged-channel and labeled-instrument orbits in this supplied family are precisely the affine orbits recovered above.

Equation (26.4) extracts the character by subtracting the known offset and dividing only by $R>0$. Affine differences preserve every summand of (26.5) by (25.16), hence every $T_n$. For $n\ge N$, (25.18) gives the terminal prefix marginal $\operatorname{Tr}_{N+1,\ldots,n}T_n=T_N$. Equality at any such horizon therefore implies equality of (26.4), and the converse follows from affine invariance. This proves all the asserted equivalences and the exact horizon.

The full stationary quantum-output equivalences in [Guță–Kiukas, arXiv:1402.3535v1, Definition 2, PDF pp. 6–7, Theorem 2 and equation (7), p. 8](https://arxiv.org/pdf/1402.3535v1), for primitive finite-dimensional isometries, and [Girotti–Kiukas–Guță, arXiv:2603.20761v1, Definition 4, PDF p. 30, Theorem 6, p. 32](https://arxiv.org/pdf/2603.20761v1), for irreducible chains, compare untwirled stationary outputs and use one common Kraus phase. Guță–Kiukas, Remark 1, PDF p. 9, also supplies finite full-output determination under its primitive hypotheses. Those are different initialization, data and phase constraints from the prepared count-twirled window here; neither those hypotheses nor their horizon conclusions are premises for (26.8). The needed orbit implication comes from the supplied-family calculation (24.7)–(24.9) with the hypotheses just mapped.

For the fixed six-label law, define on the $N$ flags

$$
F=|v\rangle\langle u|,\qquad X=F+F^*,\qquad Y=(F-F^*)/i.
$$

Each observable commutes with $Q_N$ and has eigenvalues $+1,-1,0$. Write

$$
\begin{aligned}
D_u&=\langle u|T_N|u\rangle
=p_a^Ap_c^{B-1}\sum_{\substack{k\in K\\k\ge c-b}}p_k,\\
D_v&=\langle v|T_N|v\rangle=p_b^{d-1},\qquad M=D_u+D_v.
\end{aligned}
\tag{26.12}
$$

These diagonal weights follow from (26.9) and $\|S^r x\|^2=\sum_{k\ge r}p_k$ in (23.12). Choose $X$ or $Y$ independently with probability $1/2$, retain the setting, and perform its spectral measurement. In outcome order $(+1,-1,0)$ the joint laws are

$$
\begin{aligned}
\Pr(X,\cdot)&=\tfrac12\left(M/2+\operatorname{Re}C_\theta,
M/2-\operatorname{Re}C_\theta,1-M\right),\\
\Pr(Y,\cdot)&=\tfrac12\left(M/2+\operatorname{Im}C_\theta,
M/2-\operatorname{Im}C_\theta,1-M\right).
\end{aligned}
\tag{26.13}
$$

Their differences recover both components of $C_\theta$; the offset in (26.4) is retained in these probabilities and removed only in the stated inversion. This is a single POVM with six labels, whose effects are one half of the corresponding spectral projections and sum to the identity. It uses only within-count-sector control.

Both $x$ and $S^{c-b}x$ are nonzero, the latter because $c_c\ne0$. They cannot be proportional: a nonzero proportionality scalar would be a nonzero eigenvalue of the nilpotent operator $S^{c-b}$. Strict Cauchy–Schwarz and (26.9) give

$$
|C_\theta|<\sqrt{D_uD_v}\le M/2.
\tag{26.14}
$$

Thus all four signed probabilities in (26.13) are strictly positive. In fact $M<1$ too. If $N\le c$, the word $0^N$ has positive weight and is distinct from $u,v$. If $N\ge c+1$, write $N-c-1=q(a+1)+s$ with $q\ge0$ and $0\le s\le a$. The word $(0^c1)(0^a1)^q0^s$ is distinct from $u,v$ by its first tick and has nonzero amplitude $c_c c_a^qS^s x$. In either case another positive diagonal weight exists. Hence all six probabilities are positive. A finite record from this law has the same possible labels at every phase and cannot give zero-error discrimination of distinct phases. The exact probability-law map nevertheless separates their orbits.

The lower bound already concerns every allowed effect, since the whole $T_n$ is phase independent for $n<N$. In a repeated classically adaptive readout, at each previous transcript the next chosen shorter length and measurement have the same conditional law for all phases. Multiplication of these conditional laws gives identical transcript laws for any finite number of trials. This establishes the repeated-access lower bound in Definition 26.1's class.

If $B=1$, the witness contains no completed $c$-block: its necessary $c$ coefficient comes from the terminal pair $(c,b)$, and $N=A(b+1)$, $u=(0^a1)^A0^{c-b}$. If $A=1$, the same argument gives $N=B(b+1)$ and the displayed witness with $B-1$ completed $c$-blocks. For every arithmetic progression $\{a,a+g,a+2g\}$, including $g>1$, $A=B=1$, $N=b+1$ and

$$
C_\theta=p_ap_b+p_b\sqrt{p_ap_c}\,e^{i(\theta_a-2\theta_b+\theta_c)}.
$$

For a nonprogression with $g>1$, $K=\{1,3,7\}$ gives $A=2,B=1,N=8$ and the words $(01)^2 0^4,(0001)^2$. Large terminal gaps remain allowed: $K=\{1,2,10\}$ gives $A=8,B=1,N=24$ and $(01)^8 0^8,(001)^8$; even though $c-b=8>b$, the pair $(c,b)$ still survives the memory trace. As specializations, $K=\{1,2,3\}$ gives Theorem 24.2's horizon three and its offset, while $K=\{1,2,4\}$ gives Theorem 25.3's horizon six, words $010100,001001$, and coefficient $p_1p_2^{3/2}\sqrt{p_4}$. These are instances of (26.2), with the uniform lower bound (26.8) supplying the general conclusion.

For preparation, apply the already established herald bound (25.27) with $H=c$ and the reset identity (23.3). From any initial density, an actual first tick prepares $`xx^*`$ in at most $c+1$ uses almost surely, including that tick. The subsequent window uses $N$ coherent applications, giving the sufficient total $c+1+N$. Reheralding supplies the prescribed preparation for each subsequent window even after a terminal measurement changes memory. The waiting time is auxiliary preparation information as specified in Definition 26.1.

A sufficient logical apparatus for (26.13) consists of memory dimension $c+1$, $N$ stored two-dimensional flags of joint dimension $2^N$, a reusable two-level herald detector, an $N+3$-state controller, a two-valued setting register and a three-level outcome pointer, all separately counted. The controller states may be $\mathrm{wait},\mathrm{captured}_0,\ldots,\mathrm{captured}_N,\mathrm{done}$. Retaining settings and outcomes requires a six-valued classical record per trial, or processing of those data; retaining the herald time additionally requires a $c+1$-valued record. For the spectral projections $P_o$ of either new quadrature, apply the pointer construction (25.28) with these $P_o$: $W=\sum_oP_o\otimes R_o$, where the pointer unitaries send its ready state to distinct outcomes. Its count commutator is zero because every $P_o$ commutes with $Q_N$. These dimensions and use counts are sufficient logical resources, without an optimum for energy, elapsed time or hardware.

The phase-enhanced classical-model precedent is [Liu–Elliott–Binder–Di Franco–Gu, *Optimal stochastic modelling with unitary quantum dynamics*, arXiv:1810.09668v1, equation (6), PDF pp. 2–3, and Theorem 1, p. 3](https://arxiv.org/pdf/1810.09668v1): its supplied unitary phase enhancements preserve computational-basis output statistics. In this family Theorem 23.2 already supplies the same classical renewal law at the real choice $\theta=0$. The present measured phase quotient and its sharp restricted horizon concern identification of the specified devices, without a complex-over-real advantage for generating that law or a classification of all minimum-memory realizations. $\square$

**Theorem 26.3 (Full character support with a full-density collision, and exact horizon four).** Let $H=4$, $K=\{1,2,3,4\}$ and fix any known $p_1,p_2,p_3,p_4>0$ of sum one. Define

$$
\begin{aligned}
\phi_1&=\theta_1-2\theta_2+\theta_3,&z_1&=(1,-2,1,0),\\
\phi_2&=\theta_1-\theta_2-\theta_3+\theta_4,&z_2&=(1,-1,-1,1),\\
\mathsf A&=p_2\sqrt{p_1p_3}>0,&\mathsf B&=\sqrt{p_1p_2p_3p_4}>0.
\end{aligned}
\tag{26.15}
$$

The vectors $z_1,z_2$ form an integral basis of $L_K$. Both characters occur with nonzero coefficients in the full $T_3$, whose only phase-dependent entries are the coherence below and its conjugate:

$$
C_3=\langle010|T_3|001\rangle
=p_1p_2+\mathsf A e^{i\phi_1}+\mathsf B e^{i\phi_2}.
\tag{26.16}
$$

Nevertheless, for every such positive $p$, there are two distinct affine, averaged-channel and labeled-instrument orbits with identical full $T_3$. The least complete post-tick horizon is exactly four. At that horizon the additional coherence

$$
C_4=\langle0100|T_4|0001\rangle
=p_1p_3+\mathsf B e^{i\phi_2}
\tag{26.17}
$$

together with $C_3$ separates all these orbits. Four fixed quadrature settings, chosen uniformly and retained, give one twelve-label terminal law realizing the separation with strictly positive probabilities. The full densities and the inversion below apply to every fixed positive $p$. No individual formal monomial of (26.16) is assumed to be separately measurable. Actual heralding gives a sufficient total bound of nine uses per separating trial.

**Proof.** First solve the integer equations of (25.4). For every $z\in L_K$,

$$
z=(z_3+2z_4,-2z_3-3z_4,z_3,z_4)
=(z_3+z_4)z_1+z_4z_2.
\tag{26.18}
$$

The expression is integral and unique, so it is the full integer basis. For $\theta,\theta'$, write $\Delta_k=\theta'_k-\theta_k\in\mathbb T$. Equality of their two characters gives

$$
\Delta_3=2\Delta_2-\Delta_1,\qquad
\Delta_4=\Delta_2+\Delta_3-\Delta_1=3\Delta_2-2\Delta_1.
$$

With $\lambda=2\Delta_1-\Delta_2$ and $\nu=\Delta_2-\Delta_1$, this is exactly $\Delta_k=\lambda+\nu k$ for all four labels. Conversely those affine differences annihilate both relations.

Here $x=c_4e_0+c_3e_1+c_2e_2+c_1e_3$ in the five-dimensional memory. Apply (25.14) to all length-three words. The only nonzero amplitudes are

$$
K_{000}x=c_4e_3+c_3e_4,\qquad
K_{001}x=c_2x,\qquad K_{010}x=c_1Sx.
\tag{26.19}
$$

A word starting with a tick vanishes because $Jx=0$, and two ticks require at least four positions because the smallest supported completed block has length two. In the terminal tail sum (25.15), with completed labels $1,2$ and tails $1,0$, the possible pairs are $(2,1),(3,2),(4,3)$. Thus

$$
\langle x,Sx\rangle
=\overline c_1c_2+\overline c_2c_3+\overline c_3c_4,
\qquad C_3=\overline c_2c_1\langle x,Sx\rangle.
$$

The entire density, including its zero entries, is

$$
\begin{aligned}
T_3={}&(p_3+p_4)|000\rangle\langle000|
+p_2|001\rangle\langle001|+p_1|010\rangle\langle010|\\
&+C_3|010\rangle\langle001|
+\overline C_3|001\rangle\langle010|,\\
C_3={}&p_1p_2+\mathsf A e^{i\phi_1}+\mathsf B e^{i\phi_2}.
\end{aligned}
\tag{26.20}
$$

Its nonconstant Fourier support is exactly $\{z_1,z_2,-z_1,-z_2\}$, which generates the full lattice (26.18). Those Fourier terms are aggregated in one actually observed complex coefficient.

For a collision at every positive $p$, choose any $0<t<\min(\mathsf A,\mathsf B)$ and the principal real arcsine values

$$
\alpha=\arcsin(t/\mathsf A)\in(0,\pi/2),\qquad
\beta=-\arcsin(t/\mathsf B)\in(-\pi/2,0).
$$

Take the two fixed devices with actual phase vectors

$$
\theta^+=(0,0,\alpha,\alpha+\beta),\qquad
\theta^-=(0,0,-\alpha,-\alpha-\beta).
\tag{26.21}
$$

Their character angles are $(\alpha,\beta)$ and $(-\alpha,-\beta)$. The imaginary parts $\mathsf A\sin\alpha+\mathsf B\sin\beta=t-t$ cancel, and both have

$$
C_3=p_1p_2+\sqrt{\mathsf A^2-t^2}+\sqrt{\mathsf B^2-t^2}.
\tag{26.22}
$$

Their first characters differ since $0<\alpha<\pi/2$, so they are different affine orbits; (26.20) proves equality of their full densities. This is a pair of coherent devices at the same fixed $p$, not a mixture of devices or a change in their probabilities.

To map this conclusion to the actual channel classification, apply (24.7)–(24.9) with $H=4$, memory $\mathbb C^5$, the single rank-four shift, rank-one reset $`x e_4^*`$, $\|x\|=1$ and $c_4\ne0$. The first four columns again make the Kraus operators independent. The pencil determinant is $u^4v c_4$; its two singular lines have distinct ranks four and one. The published exact Choi and shift-normalizer argument therefore identifies precisely the affine phase orbits, with its converse implementing the differences on both labeled branches. Every hypothesis is satisfied for the present positive $p$. Thus the devices (26.21) also have different averaged-channel and labeled-instrument orbits.

For the uniform probabilities $p_k=1/4$, $\mathsf A=\mathsf B=1/16$. The phase vectors $(0,0,0,\pi/2)$ and $(0,0,\pi/2,\pi/2)$ have character pairs $(1,i)$ and $(i,1)$, respectively. Both give $C_3=(2+i)/16$ and hence the same full $T_3$. This character-swap instance is distinct from (26.21), which supplies collisions without equality of $\mathsf A,\mathsf B$.

For horizon four, exhaust (25.14) in the same way. A single tick can occur at positions two, three or four; two ticks can only occupy positions two and four. The complete nonzero amplitude list and diagonal weights are

$$
\begin{array}{c|c|c}
w&K_wx&\|K_wx\|^2\\ \hline
0000&c_4e_4&p_4\\
0001&c_3x&p_3\\
0010&c_2Sx&p_2\\
0100&c_1S^2x&p_1(1-p_1)\\
0101&c_1^2x&p_1^2
\end{array}
\tag{26.23}
$$

The weights sum to one. Count zero and count two are singleton blocks. In count one, use the ordered words $(0001,0010,0100)$. Its entire block is

$$
\begin{pmatrix}
p_3&\overline D&\overline C_4\\
D&p_2&\overline C_3\\
C_4&C_3&p_1(1-p_1)
\end{pmatrix},
\qquad
D=p_2p_3+\mathsf A e^{-i\phi_1}
+p_3\sqrt{p_2p_4}\,e^{i(\phi_2-\phi_1)}.
\tag{26.24}
$$

Together with $p_4|0000\rangle\langle0000|$ and $p_1^2|0101\rangle\langle0101|$, and zero on every other word or between different counts, this specifies the whole $T_4$.

For its new separating entry, the completed labels are $1,3$, the tails are $2,0$, and the only pairs in (25.15) are $(3,1),(4,2)$. Hence

$$
\begin{aligned}
\langle x,S^2x\rangle&=\overline c_1c_3+\overline c_2c_4,\\
C_4&=\overline c_3c_1\langle x,S^2x\rangle
=p_1p_3+\mathsf B e^{i\phi_2}.
\end{aligned}
\tag{26.25}
$$

The other two oriented entries in (26.24) are $D=\overline c_3c_2\langle x,Sx\rangle$ and

$$
\langle0100|T_4|0010\rangle
=\overline c_2c_1\langle Sx,S^2x\rangle=C_3.
\tag{26.26}
$$

The last equality uses $`S^*S=I-e_4e_4^*`$ and $x_4=0$, which give $\langle Sx,S^2x\rangle=\langle x,Sx\rangle$. Expanding the three tail terms gives exactly $D$ in (26.24). Thus neither an omitted tail term nor another entry of the whole density is needed to justify the separation.

The published terminal marginal identity (25.18) also gives $\operatorname{Tr}_4T_4=T_3$. It is a terminal prefix observable without an earlier measurement. The actual inversion is

$$
\boxed{
e^{i\phi_2}=\frac{C_4-p_1p_3}{\mathsf B},\qquad
e^{i\phi_1}=\frac{C_3-C_4-p_1p_2+p_1p_3}{\mathsf A}.}
\tag{26.27}
$$

Both denominators are fixed known positive numbers. Equality of $T_4$ gives equality of these two characters, hence the affine difference proved from (26.18) and the actual channel and instrument equivalences mapped above. Conversely an affine difference leaves all summands of (25.15) unchanged by (25.16), so it leaves the full $T_4$ unchanged. Equation (25.18) extends completeness to every longer horizon. In the uniform example the two values of $C_4$ are $(1+i)/16$ and $1/8$, explicitly separating the same-$T_3$ pair.

At shorter horizons the whole states are

$$
T_0=1,\qquad T_1=|0\rangle\langle0|,\qquad
T_2=(1-p_1)|00\rangle\langle00|+p_1|01\rangle\langle01|.
\tag{26.28}
$$

For every positive $p$, (26.21) agrees on the full $T_3$ and on all its shorter marginals by (25.18). It therefore agrees on every allowed terminal law at $n\le3$. For any adaptive classical transcript in Definition 26.1, the chosen length and terminal measurement at its next step have the same conditional probability kernel for these two devices. Induction gives the same complete finite transcript law. Thus all shorter horizons fail in that class, while (26.27) proves completeness at four.

For one explicit twelve-label law on four flags, set

$$
\begin{aligned}
F_3&=|001\rangle\langle010|\otimes I_2,&
F_4&=|0001\rangle\langle0100|,\\
X_j&=F_j+F_j^*,&Y_j&=(F_j-F_j^*)/i\quad(j=3,4),\\
M_3&=p_1+p_2,&M_4&=p_3+p_1(1-p_1).
\end{aligned}
\tag{26.29}
$$

Here $I_2$ acts on the fourth flag. Each observable is measured only at time four, commutes with $Q_4$, and has spectral outcomes $+1,-1,0$. The prefix marginal gives $\operatorname{Tr}(T_4F_3)=C_3$, while $\operatorname{Tr}(T_4F_4)=C_4$. The squared quadratures are the respective two-word projections, with the identity on the suffix for $j=3$; their expectations are $M_j$. Choose $X_3,Y_3,X_4,Y_4$ independently of the device with probability $1/4$, and retain the setting. The joint probabilities are

$$
\begin{aligned}
\Pr(X_j,\cdot)&=\tfrac14\left(M_j/2+\operatorname{Re}C_j,
M_j/2-\operatorname{Re}C_j,1-M_j\right),\\
\Pr(Y_j,\cdot)&=\tfrac14\left(M_j/2+\operatorname{Im}C_j,
M_j/2-\operatorname{Im}C_j,1-M_j\right),\qquad j=3,4.
\end{aligned}
\tag{26.30}
$$

The twelve effects are one quarter of these four sets of spectral projections and sum to $I$. The signed differences recover the two complex coefficients and then (26.27). The terminal effects observe the sums $C_3,C_4$; no fictitious operation resolving separate monomials of (26.16) is used.

Nilpotence and $c_4\ne0$ make $x,Sx$ nonzero and nonproportional, and likewise $x,S^2x$. Since $\|Sx\|=1$ and $\|S^2x\|^2=1-p_1$, strict Cauchy–Schwarz gives

$$
|C_3|<\sqrt{p_1p_2}\le M_3/2,\qquad
|C_4|<\sqrt{p_3p_1(1-p_1)}\le M_4/2.
\tag{26.31}
$$

Moreover $0<M_3<1$ and $0<M_4<1$, the latter also following from $1-M_4=p_4+p_2+p_1^2>0$. All twelve probabilities in (26.30) are therefore strictly positive for every phase. Their injective exact-law map on the orbit quotient does not imply zero-error phase inference or perfect discrimination from finitely many records of this readout.

The obstruction here is actual coefficient aggregation with the entire relation lattice already in the Fourier support at time three. It is distinct from Proposition 25.4, where the chosen endpoint-anchored character list generates a proper index-five sublattice. In the present case the integral basis (26.18) is present, but (26.21) belongs to a nontrivial fiber of its observed coefficient sum. The new coefficient at time four separates that fiber by (26.27).

Finally, apply the actual herald bound (25.27) with $H=4$ and its reset (23.3). At most five monitored uses prepare $`xx^*`$ almost surely from any initial density; four further coherent uses suffice, for a total of nine. Separately counted sufficient resources are memory dimension five, four stored flags of joint dimension sixteen, a reusable two-level herald detector, a seven-state wait/capture/termination controller, a four-valued setting register, a three-level outcome pointer and a twelve-valued retained terminal record per trial or processing of those data. Retaining the auxiliary herald time adds a five-valued record. For the spectral projectors in (26.29), the already proved pointer construction (25.28) preserves every count sector. These use and dimension bounds are sufficient logical resources for the specified window measurements; they impose no uncounted end-memory readout or intermediate intervention and assert no optimized physical costs. $\square$

## 追加锚（本行以下为增补区）
## 27. Actual global-count renewal batches: sharp window tradeoffs and internal phase references

**Definition 27.1 (Common prepared batches and identification).** Fix $H=4$ and either $K=\{1,2,3,4\}$ or $K=\{1,2,4\}$. Use Definitions 23.1, 25.1 and 26.1 with known $p_k>0$ on $K$, $\sum_{k\in K}p_k=1$, and one fixed internal phase vector $\theta\in\mathbb T^K$. Thus, on the orthonormal memory basis $e_0,\ldots,e_4$,

$$
c_k=\sqrt{p_k}e^{i\theta_k},\quad c_k=0\ (k\notin K),\qquad
x=\sum_{k\in K}c_ke_{4-k},\qquad
Se_j=e_{j+1}\ (j<4),\quad Se_4=0,\quad J=xe_4^*.
$$

An actual monitored tick has posterior $`xx^*`$. A subsequent coherent window uses the same supplied isometry $V\psi=S\psi\otimes|0\rangle+J\psi\otimes|1\rangle$, with stable branch representatives, accessible chronological flags and no inaccessible which-history record. There is no intervention during a window and no terminal memory measurement. Inner products are conjugate-linear in the first entry. For $K_0=S,K_1=J$ and $K_w=K_{w_n}\cdots K_{w_1}$, write

$$
|\Psi_n\rangle=\sum_{w\in\{0,1\}^n}K_wx\otimes|w\rangle,\qquad
\Omega_n=\operatorname{Tr}_{\rm mem}|\Psi_n\rangle\langle\Psi_n|,\qquad
\Omega_n[w,v]=\langle K_vx,K_wx\rangle,\qquad
Q_n|w\rangle=|w|_1|w\rangle,\qquad
U_n(t)=e^{itQ_n},\qquad T_n=\mathcal D_n(\Omega_n)
$$

as in (25.3), with $\Omega_0=1$. A batch is a positive-integer list $\mathbf n=(n_1,\ldots,n_r)$ of independently actually prepared windows of this same device and internal $\theta$. All its flags are stored until one terminal POVM, whose effects commute only with

$$
Q_{\rm tot}=\sum_{j=1}^r Q_{n_j},\qquad
\rho_{\mathbf n,\theta}=\bigotimes_{j=1}^r\Omega_{n_j,\theta},\qquad
\mathsf Q_{\mathbf n,\theta}=\mathcal D_{\rm tot}(\rho_{\mathbf n,\theta}),
\quad \mathcal D_{\rm tot}(A)=\sum_M P_M A P_M.
\tag{27.1}
$$

Arbitrary effects within each total-count block are supplied. Preparation records are ignored: the terminal effect is tensored with their identity. Lengths within a batch are fixed before its preparation, without adaptation to its herald records. Theorem 27.2 gives a serial realization of the required product. Equal classical laws, equal $p$, equal local $T_n$, or equal single-window marginals alone do not imply this actual product with common $\theta$.

The charged batch coordinates are largest window $L=\max_jn_j$, coherent applications $C=\sum_jn_j$, number of heralds $r$, and $C$ stored two-dimensional flags of joint dimension $2^C$. Monitored applications and all other apparatus are separate resources. A window of length one has the pure flag $|0\rangle$; call windows of length at least two nontrivial. Length-zero scalar factors, if supplied, contribute no information.

A batch or fixed finite terminal law identifies the family if its equality implies $\theta'-\theta\in\Gamma_K$, the affine subgroup (25.4). The target is this supplied family's averaged-channel and outcome-labeled instrument orbit, with the memory-unitary meanings of Definition 24.1. In full support its complete character coordinates are

$$
\phi_1=\theta_1-2\theta_2+\theta_3,\qquad
\phi_2=\theta_1-\theta_2-\theta_3+\theta_4;
\tag{27.2}
$$

in sparse support the complete primitive coordinate is $\phi=2\theta_1-3\theta_2+\theta_4$. These are the full integer-quotient coordinates of (26.18) and (25.30), not a list of separately accessible formal monomials. An affine gauge may set $\theta_1=\theta_2=0$, leaving $(\theta_3,\theta_4)=(\phi_1,\phi_1+\phi_2)$ in full support and $\theta_4=\phi$ in sparse support.

**Theorem 27.2 (Actual product preparation and the full-entry bridge).** Every fixed batch in Definition 27.1 can be prepared serially with one five-dimensional source memory, at most five monitored applications per herald, and no success postselection. Averaging every waiting-time record preserves all prior retained flag marginals and prepares the next independent window. Its complete global-count datum has entries

$$
\mathsf Q_{\mathbf n}[\mathbf w,\mathbf v]
=\mathbf1_{\sum_j|w_j|_1=\sum_j|v_j|_1}
\prod_j\Omega_{n_j}[w_j,v_j].
\tag{27.3}
$$

Every affine change of internal phases acts on every $\Omega_n$ by the same count rotation, so every $\mathsf Q_{\mathbf n}$ is affine invariant. The products and entries here require actual preparation, not inference of independence from marginals.

Proof. Normalization gives $`S^*S=I-e_4e_4^*`$ and $`J^*J=e_4e_4^*`$ as in (23.11), so $V$ is an isometry and all the window densities have trace one. For any memory operator $M$, the first-herald subchannel after $a$ monitored zeros is, using the actual reset (23.3),

$$
\mathcal H_a(M)=JS^aM(S^*)^aJ^*
=xx^*\langle e_{4-a},Me_{4-a}\rangle\quad(0\le a\le4),\qquad
\sum_{a=0}^4\mathcal H_a(M)=xx^*\operatorname{Tr}M.
\tag{27.4}
$$

Indeed $e_4^*S^a=e_{4-a}^*$; $S^5=0$ eliminates every no-herald path of length five. For a density the five mutually exclusive waiting-time probabilities sum to one. All are included, with no selection of an accepted waiting time, and every herald terminates in at most five applications almost surely, counting the tick.

For retained flags $A$ possibly entangled with the memory $M$, expand $\eta_{AM}=\sum_{i,j}\eta_{ij}\otimes|e_i\rangle\langle e_j|$. The identity extension of (27.4) gives the exact replacement

$$
\left(\operatorname{id}_A\otimes\sum_a\mathcal H_a\right)(\eta_{AM})
=\operatorname{Tr}_M\eta_{AM}\otimes xx^*.
\tag{27.5}
$$

Applying the next $n$ coherent uses to this memory and tracing it gives $\operatorname{Tr}_M\eta_{AM}\otimes\Omega_n$. Iteration, starting with the first herald from any initial density, proves the batch product (27.1). It also applies after previous terminal measurements have changed the memory, conditional on their classical terminal transcript.

If the new waiting time is retained in a classical register $D$, the actual state instead is

$$
\sum_{a=0}^4\eta_{4-a,4-a}\otimes xx^*\otimes|a\rangle\langle a|_D,
\qquad \sum_a\eta_{4-a,4-a}=\operatorname{Tr}_M\eta_{AM}.
\tag{27.6}
$$

These conditional old-flag operators can differ with $a$. Thus waiting-time records can correlate with old flags, even though averaging them gives (27.5). The defining terminal effects are $E_{\rm flags}\otimes I_D$ for all preparation records, with the final memory traced. Neither conditional independence from $D$ nor record-adaptive lengths follow. Keeping or disposing of those records has an apparatus cost.

For the entry bridge, decompose an actual word of count $m$ as $w=0^{a_1}1\cdots0^{a_m}1\,0^t$ and let $A_k$ be the multiplicity of completed label $k$. Equations (25.13)–(25.14) give $K_wx=c^A S^t x$, where $c^A=\prod_kc_k^{A_k}$. Invalid completed labels give zero; tails beyond four give zero. For a second word $v$ of the same length, count $m'$ and tail $u$, with multiplicities $B$, retaining unequal counts in the actual memory trace gives

$$
\Omega_n[w,v]=c^A\overline{c^B}
\sum_{\substack{k,l\in K\\k\ge t,\ l\ge u\\k-t=l-u}}c_k\overline{c_l},\qquad
n=m+\sum_k kA_k+t=m'+\sum_k kB_k+u.
\tag{27.7}
$$

The constraint is equality of the final memory coordinate $4-(k-t)$. Thus this extends the equal-count actual-tail formula (25.15), without an end-memory projection. Each summand has exponent $z=A+\mathbf e_k-B-\mathbf e_l$, satisfying

$$
\sum_jz_j=m-m',\qquad
\sum_j jz_j=m'-m,
$$

because $k-l=t-u$. An affine change $\theta'_k=\theta_k+\lambda+\nu k$ therefore multiplies the entire entry by $e^{i(\lambda-\nu)(m-m')}$:

$$
\Omega_{n,\theta'}=U_n(\lambda-\nu)\Omega_{n,\theta}U_n(\lambda-\nu)^*.
\tag{27.8}
$$

This is the same angle at every length, in agreement with the phase-dependent prepared-vector calculation (25.22). Constant changes of the branch representatives $S,J$ by $e^{i\alpha_0},e^{i\alpha_1}$ likewise give the common count angle $\alpha_1-\alpha_0$, after length-dependent scalar phases cancel. On a batch these changes are conjugations by $e^{itQ_{\rm tot}}$ and disappear under the global twirl.

The entry formula (27.3) follows directly from the actual product and the diagonal total-count projectors. The marginal of $\mathsf Q_{\mathbf n}$ on window $j$ is $T_{n_j}$: in the common-angle integral the other conjugations disappear under partial trace. All permitted effects have the same expectations on $\rho$ and $\mathsf Q$, and arbitrary effects within the blocks determine every block. This is the usual $U(1)$ averaging principle of [Bartlett–Rudolph–Spekkens, quant-ph/0610030v3, §II.B, equations (7)–(10), and §II.C](https://arxiv.org/html/quant-ph/0610030v3), applied to total renewal tick count. It is one common twirl of the tensor product, generally different from a tensor product of separately twirled windows.

The orbit interpretation uses the existing supplied-family classification (24.7)–(24.9), as applied in Theorem 25.2 and Section 26. Here $H=4\ge2$, $S$ is one nilpotent shift block on $\mathbb C^5$, $J=xe_4^*$ has normalized rank-one range, and $c_4\ne0$. Their first four columns make the two Kraus operators independent; the pencil determinant is $u^4vc_4$, with singular lines of distinct ranks four and one. These are exactly the hypotheses of that classification, including when $c_3=0$. It identifies affine differences with averaged-channel and fixed-label instrument equivalence. No classification of arbitrary other realizations is required. The common-source limitation agrees with [Hidden Relations continuation, C-94.3](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS_CONTINUATION.md) and [Mixed State Capacity and Certification, C-98.1 and C-100.1–C-100.2](AURIC_FIB_ATOM_HIDDEN_RELATIONS_MIXED_STATE_CAPACITY_AND_CERTIFICATION.md): their actual product-source assumptions cannot be replaced by equal marginals. Their declared two-factor bottom embedding, swaps, purities and five-mode occupation measurement have a different carrier and charge from these flags. $\square$

**Theorem 27.3 (Full support: least largest window three and constrained coherent cost five).** For $K=\{1,2,3,4\}$ and every fixed known positive $p$, the least identifying largest window in Definition 27.1 is $L=3$. Within $L\le3$, the least identifying coherent cost is $C=5$, attained by $(2,3)$, and at least two nontrivial windows are necessary. Four quadrature settings, with setting retained, give a twelve-label law identifying exactly the affine, averaged-channel and labeled-instrument orbits. Without the cap $L\le3$, the least coherent cost is four, attained by a single window of length four from Theorem 26.3.

Proof. Put $A=p_2\sqrt{p_1p_3}>0$ and $B=\sqrt{p_1p_2p_3p_4}>0$, the constants of (26.15). The only nonzero history vectors at lengths two and three are

$$
\begin{array}{c|c@{\qquad}c|c}
\text{length two}&K_wx&\text{length three}&K_wx\\ \hline
00&S^2x=c_4e_2+c_3e_3+c_2e_4&000&S^3x=c_4e_3+c_3e_4\\
01&c_1x&001&c_2x\\
&&010&c_1Sx
\end{array}
$$

Also $\Omega_1=|0\rangle\langle0|$. Using (27.7), define

$$
d_1=c_4\overline c_1\overline c_2,\qquad
d_2=d_1+c_3\overline c_1^{\,2},\qquad
C_3=p_1p_2+A e^{i\phi_1}+B e^{i\phi_2}.
\tag{27.9}
$$

The complete untwirled densities, in ordered supports $(00,01)$ and $(000,001,010)$, are

$$
\Omega_2=\begin{pmatrix}1-p_1&d_2\\\overline d_2&p_1\end{pmatrix},\qquad
\Omega_3=\begin{pmatrix}
p_3+p_4&d_1&d_2\\
\overline d_1&p_2&\overline C_3\\
\overline d_2&C_3&p_1
\end{pmatrix}.
\tag{27.10}
$$

Every omitted word row and column is zero. For example $\Omega_2[00,01]=\overline c_1\langle x,S^2x\rangle=d_2$, since $\langle x,S^2x\rangle=\overline c_2c_4+\overline c_1c_3$. Likewise $\Omega_3[000,001]=\overline c_2\langle x,S^3x\rangle=d_1$, $\Omega_3[000,010]=d_2$, and $\Omega_3[010,001]=c_1\overline c_2\langle x,Sx\rangle=C_3$. The latter contains all three terminal-tail pairs of (26.19)–(26.20); its formal characters remain aggregated in one measured coefficient.

For the pair batch, the complete product Gram vectors are

$$
\begin{array}{c|c|c}
\text{joint word}&\text{memory-history vector}&\text{total count}\\ \hline
00|000&S^2x\otimes S^3x&0\\
00|001&S^2x\otimes c_2x&1\\
00|010&S^2x\otimes c_1Sx&1\\
01|000&c_1x\otimes S^3x&1\\
01|001&c_1x\otimes c_2x&2\\
01|010&c_1x\otimes c_1Sx&2
\end{array}
\tag{27.11}
$$

They are actual history vectors for two independent five-level memories; the serial preparation (27.5) gives the same flag product. Tracing these memories and retaining only equal-total-count pairs specifies the whole $\mathsf Q_{(2,3)}$. In particular $u=00|001$ and $v=01|000$ give

$$
Z=\mathsf Q_{(2,3)}[00,001;01,000]
=\langle c_1x\otimes S^3x,S^2x\otimes c_2x\rangle
=d_2\overline d_1=p_1p_2p_4+p_1B e^{-i\phi_2}.
\tag{27.12}
$$

The second-window terminal marginal supplies $C_3$. Consequently the actual inversion is

$$
\boxed{
e^{-i\phi_2}=\frac{Z-p_1p_2p_4}{p_1B},\qquad
e^{i\phi_1}=\frac{C_3-p_1p_2-B e^{i\phi_2}}{A}.}
\tag{27.13}
$$

All denominators are fixed known positive numbers. No division by $d_2,Z,C_3$ or argument of a vanishing observed number occurs. This covers $C_3=0$ and $Z=0$. Since $d_1\ne0$, $Z=0$ is equivalent to $d_2=0$, which requires $p_1p_3=p_2p_4$ and $e^{i\phi_2}=-1$; (27.13) still applies. Equality of the two observations is exactly equality of the two complete source characters, and the affine converse follows from (27.8).

For the largest-window lower bound, use the gauge in Definition 27.1. Then

$$
d_2=e^{i\phi_1}\sqrt{p_1}
\left(\sqrt{p_1p_3}+\sqrt{p_2p_4}e^{i\phi_2}\right).
\tag{27.14}
$$

At fixed $\phi_2$, replacing $\phi_1$ by $\phi_1+t$ gives $\Omega_2'=U_2(-t)\Omega_2U_2(-t)^*$; $\Omega_1$ is unchanged. Hence the entire product for every finite list with $L\le2$ changes only by a common global count rotation and has unchanged $\mathsf Q$. Taking $t\ne0$ modulo $2\pi$ gives distinct affine classes. This obstruction holds even for arbitrarily many short windows.

For a common collision across all batch types with $L\le3,C\le4$, use the established pair (26.21) of Theorem 26.3. Explicitly, for any $0<h<\min(A,B)$ it supplies

$$
\alpha=\arcsin(h/A),\quad \beta=-\arcsin(h/B),\qquad
\theta^+=(0,0,\alpha,\alpha+\beta),\quad \theta^-=-\theta^+,
\tag{27.15}
$$

with distinct affine classes and identical full $T_3$, as proved in (26.20)–(26.22). The additional joint compatibility follows from (27.14): $d_2(\theta^-)=\overline{d_2(\theta^+)}$, so their moduli agree. If this common modulus is nonzero, choose $t$ with $e^{-it}d_2(\theta^+)=d_2(\theta^-)$. If it is zero, either angle works. Then every whole state at lengths one and two is carried from $\theta^+$ to $\theta^-$ by $U_n(t)$. Thus their globally twirled data agree for every all-short list, with one common actual phase pair, including zero-coherence cases.

Every other allowed list contains one length-three window and only pure length-one companions, since $C\le4$. Its global twirl is that same $T_3$ tensored with count-zero pure flags. Therefore the single pair (27.15) defeats every permitted batch type, every permitted terminal measurement, and any pooling of these capped batches. The $(2,3)$ separator attains five. At $L\le3$ any list with at most one nontrivial window has only a single $T_n$ with $n\le3$ and pure companions, and the same collision defeats it; two nontrivial windows are necessary.

For the unrestricted coherent comparison, every list of $C\le3$ is covered by this common collision. Theorem 26.3 supplies a single length-four separator using its actual $C_4=p_1p_3+B e^{i\phi_2}$ and the terminal $C_3$ marginal, with inversion (26.27). Thus the unrestricted minimum is four, with a different $L$ and one herald. This is a source result consumed for the comparison, not a new single-window theorem. Theorem 27.5 supplies the claimed finite law. The recovery of information by permitted joint charge exchanges uses the established activation principle in [Bartlett–Rudolph–Spekkens, quant-ph/0610030v3, §III.C.2](https://arxiv.org/html/quant-ph/0610030v3); here the finite renewal consumer is the actual pair (27.11) and the common lower-bound compatibility just proved. $\square$

**Theorem 27.4 (Sparse support: least largest window four and unrestricted coherent cost six).** For $K=\{1,2,4\}$ and every fixed known positive $p_1,p_2,p_4$, the least identifying largest window is $L=4$ and the least unrestricted coherent cost is $C=6$, attained by $(2,4)$. At $L\le4$ at least two nontrivial windows are necessary. Two quadrature settings, with setting retained, give a six-label law identifying exactly the affine, averaged-channel and labeled-instrument orbits. The single length-six separator of Theorem 25.3 has the same $C$ and one herald, with larger $L$.

Proof. Here $x=c_4e_0+c_2e_2+c_1e_3$. The length-two and length-three vectors are those of Theorem 27.3 with $c_3=0$. Set $d=c_4\overline c_1\overline c_2$ and $e=c_2^2\overline c_1^{\,3}$. The complete short densities are

$$
\Omega_1=|0\rangle\langle0|,\qquad
\Omega_2=\begin{pmatrix}1-p_1&d\\\overline d&p_1\end{pmatrix}_{00,01},\qquad
\Omega_3=\begin{pmatrix}
p_4&d&d\\\overline d&p_2&p_1p_2\\\overline d&p_1p_2&p_1
\end{pmatrix}_{000,001,010}.
\tag{27.16}
$$

The complete length-four vector list is

$$
0000:c_4e_4,\qquad0010:c_2Sx,\qquad
0100:c_1S^2x,\qquad0101:c_1^2x.
\tag{27.17}
$$

All other vectors vanish, including $0001$ whose coefficient is $c_3$. In this order its entire untwirled density is

$$
\Omega_4=\begin{pmatrix}
p_4&d&d&0\\
\overline d&p_2&p_1p_2&e\\
\overline d&p_1p_2&p_1(1-p_1)&p_1d\\
0&\overline e&p_1\overline d&p_1^2
\end{pmatrix}.
\tag{27.18}
$$

For completeness, the tail overlaps are $\langle x,Sx\rangle=\overline c_1c_2$, $\langle x,S^2x\rangle=\overline c_2c_4$, and $\langle Sx,S^2x\rangle=\overline c_1c_2$. Thus the $0010/0101$ entry is $c_2\overline c_1^{\,2}\langle x,Sx\rangle=e$, the $0100/0101$ entry is $c_1\overline c_1^{\,2}\langle x,S^2x\rangle=p_1d$, and the $0010/0100$ entry is $p_1p_2$. The $0000$ overlaps with the two count-one vectors are both $d$, and its overlap with $0101$ is zero. The four displayed diagonal weights sum to one. These calculations specify every supported entry; omitted word rows and columns are zero in (27.16)–(27.18).

The pair's complete product Gram vectors are

$$
\begin{array}{c|c|c}
\text{joint word}&\text{memory-history vector}&\text{total count}\\ \hline
00|0000&S^2x\otimes c_4e_4&0\\
00|0010&S^2x\otimes c_2Sx&1\\
00|0100&S^2x\otimes c_1S^2x&1\\
00|0101&S^2x\otimes c_1^2x&2\\
01|0000&c_1x\otimes c_4e_4&1\\
01|0010&c_1x\otimes c_2Sx&2\\
01|0100&c_1x\otimes c_1S^2x&2\\
01|0101&c_1x\otimes c_1^2x&3
\end{array}
\tag{27.19}
$$

As for (27.11), these realize the product in parallel and (27.5) realizes the identical flag density serially. The allowed count-two pair $u_s=00|0101$, $v_s=01|0010$ has entry

$$
\begin{aligned}
Z_s&=\mathsf Q_{(2,4)}[00,0101;01,0010]
=\langle c_1x\otimes c_2Sx,S^2x\otimes c_1^2x\rangle\\
&=d\overline e=p_1c_1^2c_4\overline c_2^{\,3}
=p_1R_6e^{i\phi},\qquad R_6=p_1p_2^{3/2}\sqrt{p_4}>0.
\end{aligned}
\tag{27.20}
$$

It follows that $e^{i\phi}=Z_s/(p_1R_6)$, with a known positive denominator. The complete primitive character and the source classification mapped in Theorem 27.2 give identification for all phases and all allowed probabilities. The converse is (27.8).

For the largest-window obstruction, take the sparse gauge $\theta_1=\theta_2=0$, $\theta_4=\phi$. Then $d=\sqrt{p_1p_2p_4}e^{i\phi}$, and all its locations in (27.16) have row count zero and column count one. All equal-count entries there are constant. Therefore, including every zero row,

$$
\Omega_n(\phi)=U_n(-\phi)\Omega_n(0)U_n(-\phi)^*\qquad(n=1,2,3).
\tag{27.21}
$$

The same angle acts at every short length. Hence every finite product with $L\le3$, at any coherent cost, has globally twirled density independent of $\phi$. Distinct characters are distinct affine classes, proving $L\ge4$.

For the unrestricted coherent lower bound, partition every positive-integer list of $C\le5$. It is one length-five window; one length-four window with only possible length-one companions; or a list all of whose lengths are at most three. The whole-state phase blindness of $T_4,T_5$ is the established Theorem 25.3 result, and pure companions add no count exchange. Equation (27.21) handles the remaining lists. Thus every allowed batch type is phase independent; any one fixed distinct phase pair is a common collision across all these types. This proves $C\ge6$. At $L\le4$ a list with at most one nontrivial window supplies a single phase-blind $T_n$, $n\le4$, and any number of pure companions, so two nontrivial windows are necessary. Equation (27.20) attains both sharp bounds. The single-window-six comparison uses the actual coherence (25.29), not an abstract relation assumed measurable at a shorter horizon. Theorem 27.5 gives the finite pair readout. $\square$

**Theorem 27.5 (Finite legal laws, positivity and sufficient logical resources).** The two separating batches admit the setting counts in Theorems 27.3–27.4, with every retained-setting label strictly positive. Actual masses, rather than normalized conditional success laws, determine these readouts. Sufficient serial logical resource bounds are as follows; the single-window rows are the source comparisons.

| Family and protocol | $L$ | $C$ | Heralds | Stored flags / joint dimension | Monitored applications, at most | Total device applications, at most | Settings / retained labels |
| --- | ---: | ---: | ---: | --- | ---: | ---: | --- |
| Full, $(2,3)$ | 3 | 5 | 2 | 5 / 32 | 10 | 15 | 4 / 12 |
| Full, single four | 4 | 4 | 1 | 4 / 16 | 5 | 9 | 4 / 12 |
| Sparse, $(2,4)$ | 4 | 6 | 2 | 6 / 64 | 10 | 16 | 2 / 6 |
| Sparse, single six | 6 | 6 | 1 | 6 / 64 | 5 | 11 | 2 / 6 |

Proof. For distinct equal-total-count words $u,v$, with entry $q=\mathsf Q[u,v]$, define the two orthonormal pairs and spectral projectors

$$
|R_\pm\rangle=(|u\rangle\pm|v\rangle)/\sqrt2,\qquad
|I_\pm\rangle=(|u\rangle\mp i|v\rangle)/\sqrt2,\qquad
P^B_\pm=|B_\pm\rangle\langle B_\pm|,\quad
P^B_0=I-P^B_+-P^B_-\quad(B=R,I).
\tag{27.22}
$$

Each three-outcome projective setting commutes with $Q_{\rm tot}$. If $D_u=\mathsf Q[u,u]$, $D_v=\mathsf Q[v,v]$ and $M=D_u+D_v$, direct expectations give, in order $(+,-,0)$,

$$
\Pr(\cdot\mid R)=(M/2+\operatorname{Re}q,M/2-\operatorname{Re}q,1-M),\qquad
\Pr(\cdot\mid I)=(M/2+\operatorname{Im}q,M/2-\operatorname{Im}q,1-M).
\tag{27.23}
$$

The sign of the imaginary part follows from the minus $i$ in $I_+$. Both signed differences recover twice the corresponding component of $q$. The construction is the source quadrature readout (25.24)–(25.26), applied to these actual joint pairs.

For full support use the two settings for $u=00|001,v=01|000,q=Z$, and two settings for $u=010,v=001,q=C_3$ on the second window, lifted by the identity on every first-window flag. The lifted projectors remain count preserving and are measured only at the joint terminal time. Choose uniformly among the four settings, independently of the device, and retain the setting. The twelve effects are $P^s_o/4$ and sum to the identity. Their probabilities are (27.23) times $1/4$, with actual masses

$$
D_u^Z=(1-p_1)p_2,\quad D_v^Z=p_1(p_3+p_4),\quad M_Z=D_u^Z+D_v^Z,\qquad
M_C=p_1+p_2.
\tag{27.24}
$$

For sparse support use the two settings for $u_s,v_s$ of (27.20), uniformly and independently chosen. The six effects are $P^B_o/2$, with (27.23) times $1/2$ and

$$
D_u^s=(1-p_1)p_1^2,\qquad D_v^s=p_1p_2,\qquad M_s=D_u^s+D_v^s.
\tag{27.25}
$$

All four diagonal masses in (27.24)–(27.25) are positive. Since $c_4\ne0$, the first nonzero coordinate of $x$ is $e_0$, whereas that of $S^2x$ is $e_2$; both are nonzero and cannot be proportional. For either product pair in (27.11) or (27.19), the first factors are these vectors times nonzero scalars. Proportional nonzero product vectors would force their first factors to be proportional, so strict Cauchy–Schwarz gives

$$
|Z|<\sqrt{D_u^ZD_v^Z}\le M_Z/2,\qquad
|Z_s|<\sqrt{D_u^sD_v^s}\le M_s/2.
\tag{27.26}
$$

For the lifted $C_3$ pair, $x,Sx$ are likewise nonproportional, giving $|C_3|<\sqrt{p_1p_2}\le M_C/2$. The omitted word $01|010$ has diagonal $p_1^2>0$ in the full batch, so $1-M_Z>0$; $1-M_C=p_3+p_4>0$. The omitted word $01|0101$ has diagonal $p_1^3>0$ in the sparse batch, so $1-M_s>0$. Thus every signed outcome and every zero outcome has strictly positive probability, for all phases, including cancellations in (27.13). There is no conditioning on being in the two-word span.

For each setting its three projectors admit the source pointer realization (25.28), now on the entire batch:

$$
W_s=\sum_{o\in\{+,-,0\}}P^s_o\otimes R_o,\qquad
R_o|\mathrm{ready}\rangle=|o\rangle,\qquad
[W_s,Q_{\rm tot}\otimes I]=0.
\tag{27.27}
$$

The $R_o$ are unitaries on a three-level pointer. Orthogonality and completeness make $W_s$ unitary. This requires no within-window operation; the complex quadrature control occurs within a total-count sector at terminal time.

For the serial pairs one five-level memory, a reusable two-level herald detector, a three-level pointer, and a four-valued or two-valued setting register suffice. One explicit controller has two states $\mathrm{wait}_j$, states $\mathrm{capture}_{j,k}$ for $0\le k\le n_j$, and $\mathrm{done}$: $C+5$ states, respectively ten and eleven. The flag dimensions and use bounds follow from (27.4)–(27.5). Each retained herald time needs a five-valued classical record; two have 25 joint labels. A terminal record needs twelve or six labels per trial, or processing of the corresponding frequencies. Storage, record processing or disposal, detector/controller control, the joint measurement, and maintenance of stable phases through waiting and storage are separate resources. Ignoring a record in the effect does not eliminate its production or disposal cost.

A parallel realization instead uses two five-level memories: joint Hilbert dimension 25 and sum of local level counts ten. It supplies no single ten-dimensional-memory realization. It still requires the same internal $\theta$ and phase relation, independent preparation and all flag/readout resources. These are sufficient logical realizations, without optimized hardware, elapsed time or energy costs. Neither pair route dominates its single-window comparison across all coordinates: the pairs reduce largest window, while the single windows need fewer heralds and fewer sufficient total applications; full single four also uses fewer coherent applications and flags. $\square$

**Theorem 27.6 (Uniform dephasing boundary and fixed count-offset reference extensions).** Independent uniform per-window count rotations remove the activation in the two pair protocols. A single common rotation preserves their datum. In contrast, suppose the same internal $\theta$ is used, but window one and window two have arbitrary fixed unknown count offsets $\beta_1,\beta_2\in\mathbb T$, constant across repetitions. The $(2,3)$ protocol still identifies the full-support internal affine orbit using six quadrature settings and eighteen retained labels; $(2,4)$ identifies the sparse orbit using four settings and twelve labels. These claims include the full-support zero-reference case. They concern fixed count rotations, not arbitrary different internal phase vectors or general noise.

Proof. If each window acquires $U_{n_j}(\beta_j)$ and its angle is independently uniform and averaged before observation, then

$$
\int\bigotimes_j U_{n_j}(\beta_j)\Omega_{n_j}U_{n_j}(\beta_j)^*
\prod_j\frac{d\beta_j}{2\pi}
=\bigotimes_jT_{n_j}.
\tag{27.28}
$$

This state is already globally invariant. For full $(2,3)$ the common collision (27.15) therefore has equal whole data $T_2\otimes T_3$; for sparse $(2,4)$ the whole datum $T_2\otimes T_4$ is phase independent by Theorem 25.3. Neither specified pair then identifies. More generally independent local randomization removes every cross-window unequal-count entry, reducing any batch to its product of local data; it does not exclude longer single-window separators. One common uniform angle gives (27.1) instead and leaves (27.12), (27.20) intact. This is the established shared-reference distinction, not a new general twirl result: [Bartlett–Rudolph–Spekkens, quant-ph/0610030v3, §II.B, §III.C.2 and §IV.A.4](https://arxiv.org/html/quant-ph/0610030v3).

For fixed offsets put $\delta=\beta_2-\beta_1$ and define the datum precisely by

$$
\mathsf Q^\beta_{(n_1,n_2)}
=\mathcal D_{\rm tot}\!\left(\bigotimes_{j=1}^2
U_{n_j}(\beta_j)\Omega_{n_j,\theta}U_{n_j}(\beta_j)^*\right).
$$

Every selected joint pair whose row counts are $(0,m+1)$ and column counts $(1,m)$ gains exactly $e^{i\delta}$ by (27.3). The lifted equal-local-count observation $C_3$ is unchanged. In full support measure additionally

$$
\begin{aligned}
Z^\beta&=\mathsf Q^\beta_{(2,3)}[00,001;01,000]
=e^{i\delta}(p_1p_2p_4+p_1B e^{-i\phi_2}),\\
R&=\mathsf Q^\beta_{(2,3)}[00,010;01,000]
=e^{i\delta}d_2\overline d_2=e^{i\delta}|d_2|^2.
\end{aligned}
\tag{27.29}
$$

Both reference words have total count one. Their actual vectors are $S^2x\otimes c_1Sx$ and $c_1x\otimes S^3x$, present in (27.11); their inner product is $d_2\overline d_2$. Thus the reference is itself an accessible coherence, with no separately supplied phase calibration.

If $R\ne0$, its exact law supplies $R/|R|=e^{i\delta}$. Put $\widehat Z=Z^\beta\overline R/|R|$ and use (27.13) with $\widehat Z$. This divides by an observed reference only after its nonvanishing is established. If $R=0$, positivity and $d_1\ne0$ imply $d_2=0$. Its two summands in (27.9) must have equal magnitudes and opposite phases, giving

$$
p_1p_3=p_2p_4,\qquad e^{i\phi_2}=-1,\qquad Z^\beta=0,\qquad
e^{i\phi_1}=\frac{C_3-p_1p_2+B}{A}.
\tag{27.30}
$$

Thus the internal orbit is still identified although the relative offset itself is undetermined there. The denominator is known positive, and $C_3=0$ creates no exception. There is no division by a vanishing reference or by $Z^\beta$. This zero-case diagnosis concerns exact laws; finitely many observations do not certify that a continuous probability difference is exactly zero.

The two reference quadratures use (27.22) for $00|010,01|000$. Together with the four main settings, uniformly chosen and retained, they give eighteen effects $P^s_o/6$. Their reference masses are

$$
D_u^R=p_1(1-p_1),\qquad D_v^R=p_1(p_3+p_4),\qquad M_R=D_u^R+D_v^R.
\tag{27.31}
$$

The first factors $S^2x,x$ again prove strict Cauchy–Schwarz, $|R|<\sqrt{D_u^RD_v^R}\le M_R/2$, even when $R=0$. The excluded word $01|001$ has diagonal $p_1p_2>0$, so $1-M_R>0$. Offsets only multiply entries by unit scalars, preserving every main mass and strict inequality of Theorem 27.5. Hence all eighteen labels are positive, and (27.23) with probability factor $1/6$ proves legality and recovery of the three complex observations.

For sparse support the additional equal-total-count reference is always nonzero:

$$
\begin{aligned}
Z_s^\beta&=e^{i\delta}p_1R_6e^{i\phi},\\
R_s&=\mathsf Q^\beta_{(2,4)}[00,0010;01,0000]
=e^{i\delta}d\overline d=e^{i\delta}p_1p_2p_4,\\
\boxed{e^{i\phi}}&=\frac{Z_s^\beta\overline R_s}{(p_1R_6)(p_1p_2p_4)}.
\end{aligned}
\tag{27.32}
$$

The reference row and column both have total count one, with actual vectors $S^2x\otimes c_2Sx$ and $c_1x\otimes c_4e_4$ from (27.19). Formula (27.18) gives their inner product $d\overline d$. Only known positive constants divide the final inverse. The main two settings and the two reference quadratures, chosen uniformly, give twelve effects $P^s_o/4$. The reference masses are

$$
D_u^{R_s}=(1-p_1)p_2,\qquad D_v^{R_s}=p_1p_4,\qquad M_{R_s}=D_u^{R_s}+D_v^{R_s}.
\tag{27.33}
$$

Their product vectors are nonproportional in the first factors, so $|R_s|<\sqrt{D_u^{R_s}D_v^{R_s}}\le M_{R_s}/2$. The omitted word $01|0101$ has mass $p_1^3>0$, proving $1-M_{R_s}>0$. The twelve labels are all strictly positive by (27.23), with factor $1/4$.

All extension effects are tensored with identity on preparation records and are measured only after the windows. They use the same flag storage, herald and coherent-use counts; their setting registers and terminal records have respectively six/eighteen or four/twelve values. The pointer realization (27.27) applies unchanged. Relational phase measurements and additional reference resources are established principles, including [Bartlett–Rudolph–Spekkens, quant-ph/0610030v3, §VI.A.2](https://arxiv.org/html/quant-ph/0610030v3); here the reference cancellation is performed on the two specific non-fictitious coherences (27.29), (27.32), with its required degeneracy clause.

The offset model preserves one internal device $\theta$, the product preparation, and relative count rotations constant across the measured trials. It does not include independently different internal branch-phase vectors, random resampling of the offsets, drift, correlated preparation noise or arbitrary channels on the flags. Common additional offsets remain gauge, while independent uniform resampling gives (27.28). These exact-law statements do not supply a uniform finite-sample stability bound near $R=0$ or as known positive coefficients tend to zero. For protocols required to identify every internal orbit at every fixed offset, all sharp resource lower bounds of Theorems 27.3–27.4 remain valid by restriction to zero offsets, provided the flag-only batch restrictions are retained. $\square$

**Theorem 27.7 (Common adaptive obstructions and statistical applicability).** The resource obstructions above extend to separately measured batches chosen by a fixed common, parameter-independent classical policy. At each prior terminal transcript the policy may choose the next lengths, count-preserving effects and stopping decision, using independent random seeds, subject to the relevant per-batch caps. No old quantum flags are retained across batch boundaries, preparation records are not phase side information, and there is no quantum feedback, intermediate window intervention or end-memory measurement. Under these assumptions the common collision pairs have identical adaptive and stopped transcript laws. The values of $C$ describe one identifying batch, not total estimation uses or sample complexity.

Proof. For full $L\le2$, fix $\phi_2$ and two distinct $\phi_1$ values as in (27.14). For full $L\le3,C\le4$, or unrestricted $C\le3$, use the one actual pair (27.15). For sparse $L\le3$, or unrestricted $C\le5$, use any one fixed pair of distinct primitive characters. The proofs above show equality of each pair's whole datum for every allowed batch list, rather than unrelated collisions for separate measurement choices. Conditional on a common finite transcript and seed, the policy chooses the same next list and effects in both devices. The actual reset (27.4) and fixed lengths give the prescribed product marginal for that next batch, even from its conditional initial memory. Its outcome kernel is identical for the two devices. Multiplying conditional kernels proves equality of the extended transcript laws by induction; averaging the independent seeds preserves it.

All finite-cylinder laws of a countable classical transcript therefore agree, so the induced probability measures agree. A stopping time and its stopped output, including the possibility of never stopping, are measurable functions of that transcript and have equal laws. This argument excludes retaining flags to join a later alleged batch, or exploiting correlated preparation records: either would change the datum and the resource boundary. It does not turn the per-batch $C$ into an accuracy cost for repetitions.

The laws of Theorems 27.5–27.6 have the same strictly positive finite alphabet at every parameter. Every fixed finite record from these readouts thus has positive probability at distinct orbits. Their injective exact-law maps do not give finite-record zero-error recovery of a continuous phase. Longer sampling and estimates of the probabilities require additional applications and storage, and exact-zero case distinctions such as (27.30) remain distinct from finite-data zero testing.

The family preserves the classical renewal law under phase changes by Theorem 23.2. The phase-enhanced unitary-model precedent is [Liu–Elliott–Binder–Di Franco–Gu, arXiv:1810.09668v1, equation (6), Theorems 1–2 and equation (7)](https://arxiv.org/html/1810.09668v1): computational-basis output laws are unchanged while model memory measures can change. Those supplied-model results do not establish these post-herald global-count batch minima. Likewise [Renewal Phase Channel Jordan Structure and Identification, Sections 8–10](FIB_RENEWAL_PHASE_CHANNEL_JORDAN_STRUCTURE_AND_IDENTIFICATION.md) distinguishes complex-linear similarity from positivity and memory-unitary equivalence and credits the richer Source Section 24 single-window access. The present target is the existing affine orbit with the actual batch preparation and restricted global observation, rather than Jordan-data or classical-law identification.

Full stationary-output identifiability uses a different datum. [Guță–Kiukas, arXiv:1402.3535v1, Definition 2, Theorem 2, equation (7) and Remark 1](https://arxiv.org/html/1402.3535v1) treats primitive finite-dimensional isometries with equality of all untwirled stationary quantum outputs, obtaining memory-unitary conjugation and one common isometry phase, and a finite full-output determination under its primitive hypotheses. [Girotti–Kiukas–Guță, arXiv:2603.20761v1, Section 3, Definition 4 and Theorem 6](https://arxiv.org/html/2603.20761v1) extends that stationary full-output equivalence to irreducible chains, including periodic cases. Their single common Kraus phase differs from independently scalar-phased labeled CP branches; their stationary initialization and full-output measurements are not the prepared flag-only data used here. Their asymptotic statistical results are not finite heralded-window or sample bounds for (27.23).

[Elliott, arXiv:2610.06519v1, §III.C, Theorem 1, equations (12)–(13), and §IV.B](https://arxiv.org/html/2610.06519v1) concerns memoryful stationary full quantum space series with finite-dimensional primitive causal models, isometric memory-minimal generation and memory-basis/global-phase uniqueness. Its quantum Nemo example is a three-state renewal process of infinite classical Markov order. These are different generation objectives and observation assumptions from finite independently heralded global-count batches. General activation, common-reference averaging and relational readout are credited suppliers within the bearing renewal proofs; none substitutes for their actual-tail entries, common compatible lower bounds or charged preparation. Unknown $p$, additional preparation data, other realizations, finite-sample accuracy and general phase noise require additional hypotheses and conclusions. $\square$

## 追加锚（本行以下为增补区）
