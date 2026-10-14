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
