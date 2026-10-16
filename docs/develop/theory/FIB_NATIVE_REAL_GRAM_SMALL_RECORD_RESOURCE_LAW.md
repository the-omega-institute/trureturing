# Real coefficient Grams and a small-record resource law

## 1. The experiment and the scope of the additional law

**Convention 1.1 (ordinary conditional mathematics).** This volume evaluates an individual-input resource law for the particular complete channel of [CG, (CG.135)–(CG.142)][CG]. The evaluated domain consists of positive inputs whose coefficient Gram is real symmetric and positive definite. It includes all twelve original pure histories, as proved in Section 8. The result gives exact spectral values on explicit positive intervals of record strength, actual finite instruments with at most fourteen acquired branches, and selected-coordinate Pareto vectors outside each of the three sharp-average faces. It does not evaluate the original general complex-input, all-strength problem or its entire resource frontier.

The source algebraic point, root isolation, enclosures, normalization, minimax benchmark, common preparation, control regularity and calibrated-instrument antecedents remain inherited conditional premises. An independent assessment is fallible exposure to an argument, never a proof premise. The proofs below carry the additional conclusions. They assert ordinary mathematics, without kernel verification, physical implementation or a worldwide priority claim.

**Definition 1.2 (five modes and the twelve actual histories).** The original modes have basis $e_0,e_1,e_2,e_3,e_4$, where $e_4$ names original mode $13$. Define

$$
E=\left(\frac{e_0+e_4}{\sqrt2},\frac{e_1+e_3}{\sqrt2},e_2\right),
\qquad P_5=EE^\dagger,\qquad Q_5=I_5-P_5,\qquad V=\operatorname{ran}E.
\tag{RG.1}
$$

Supported coordinates $0,1,2$ denote $(+,-,2)$ and are separate from the five failure labels. For $y\in\{5,16,27\}$ and independently $e,n\in\{+1,-1\}$ put

$$
p_y=\left(\frac y{128},\frac{64-y}{128},\frac12\right),\quad
 a_y=\sqrt{p_y},\quad U_{e,n}=\operatorname{diag}(e,n,1),\quad
\rho_{y,e,n}=U_{e,n}a_ya_y^TU_{e,n}^\dagger.
\tag{RG.2}
$$

The square root is entrywise. The actual normalized sole specimen at the already reached old live cut is $E\rho_{y,e,n}E^\dagger$. Original parameters are $x=y/256$, $e=(-1)^{\beta_{\rm hist}/\pi}$ and $n=e(-1)^m$, with $\beta_{\rm hist}\in\{0,\pi\}$, $m\in\{0,1\}$. Thus $en=(-1)^m$ is original winding parity. Neither sign is given to the processor.

For clarity, the credited common preparation is the double-wall population and signed real phase lift

$$
\begin{aligned}
p(k)&=(k,1/4-k,1/2,1/4-k,k),\\
w(k)&=\left(\frac{1/4-k}{1/2},-\frac{k}{1/2},0,-\frac{k}{1/2},\frac{1/4-k}{1/2}\right),\\
\psi_i(t)&=\sqrt{p(k(t))_i}\exp\left(-i\int_0^t w_i(k(v))\chi'(v)\,dv\right).
\end{aligned}
\tag{RG.3}
$$

Starting at height $1/8$, the six unit-duration legs in CG Proposition 2.2 are phase $0\to2\pi m$, descent to $1/16$, phase $2\pi m\to2\pi m+B_{\rm hist}$, ascent to $1/8$, phase return to $2\pi m$, and height change to $x$, where $B_{\rm hist}=8\beta_{\rm hist}-4\pi m$. Their residual phase vector is $(\beta_{\rm hist},\beta_{\rm hist}-\pi m,0,\beta_{\rm hist}-\pi m,\beta_{\rm hist})$. These histories reach absolute time six; the old live masses $32/177,2/9,32/111$ are earlier positive branch masses, not priors or new acceptance weights.

The requested continuation is $k(t)=x+6t/256$, with phase fixed, for elapsed $0\le t\le1$, in the original common legal command domain $(0,58/256)$. Retain finite duration, strict continuous height domain, signed real phase lifts of finite variation, the absolute-continuity or specified finite-piecewise-$C^1$ alternative, and literal chronological composition. Zero duration permits only a matching zero-displacement identity. Known denial, visible unexecuted rejection, permissions, source and epoch identity, calibrations, controller updates and clock alignment retain their original contracts. A partial command supplies no unknown-height sensor.

**Definition 1.3 (complete targets and error).** Define the target live matrix $B_y^{\rm tar}$ and the separate failure measures by

$$
\begin{gathered}
d_y=\left(\frac y{128},\frac{y(58-y)}{128(y+6)},\frac{y}{2(y+6)}\right),
\qquad (B_y^{\rm tar})_{ij}=\sqrt{d_{yi}d_{yj}},\\
f_y(t)=\frac{6y}{(y+6t)^2},\qquad
w=(0,1/4,1/2,1/4,0),\qquad P_f=|f\rangle\langle f|,\\
\Omega_{y,e,n}^L=EU_{e,n}B_y^{\rm tar}U_{e,n}^\dagger E^\dagger,
\qquad \Omega_{y,e,n,j}^f(dt)=w_j f_y(t)dt\,P_f.
\end{gathered}
\tag{RG.4}
$$

The live trace is $y/(y+6)$; total failure trace is its complement. Exact elapsed time $t$ means absolute time $6+t$. Labels $1,3$ remain distinct; $0$ and $13$ remain named zero-density sectors. First executed failure is absorbing; old stopped archives remain in their own branches.

The processor receives the sole specimen and fixed common metadata, blanks, calibration, source/epoch identity, permissions, controller state and aligned clock. It receives no history record, source-dependent installed programme, waveform or helper specimen. Its original error remains

$$
\mathcal E(\Phi)=\max_{y,e,n}\frac12
 \|\Phi(E\rho_{y,e,n}E^\dagger)-\Omega_{y,e,n}\|_{1,\mathrm{cq}},
\qquad \mathcal E_* =\inf_{\Phi\ \mathrm{common\ CPTP}}\mathcal E(\Phi).
\tag{RG.5}
$$

The full cq norm adds the coherent live trace norm and variation trace norms in all separately labelled exact-time sectors, using a common dominating measure that includes atoms and singular parts. Abort, rejection, wrong support, singular additions and every zero-target extra outcome count. There is no conditioning on any new acquisition or survival event.

## 2. Exact coefficients, complete channel and counted implementations

**Definition 2.1 (the inherited algebraic coefficients).** To specify the exact source without decimal fitting, use source variables $\mathbf x=(\lambda_{\rm src},\alpha_1,\alpha_2,\beta_1,\beta_2,z_{\rm src})$, multipliers $\eta=(\eta_0,\eta_1,\eta_2)$ and

$$
\begin{aligned}
v_5^{\rm src}&=(\alpha_1,\alpha_2,-1)^T,&
v_{27}^{\rm src}&=(\beta_1,\beta_2,1)^T,\\
R_y^{\rm src}&=v_y^{\rm src}(v_y^{\rm src})^T/\|v_y^{\rm src}\|^2,&
A_5^{\rm src}&=\lambda_{\rm src}R_5^{\rm src},\\
A_{27}^{\rm src}&=(1-\lambda_{\rm src})R_{27}^{\rm src},&
\zeta&=(z_{\rm src},59\lambda_{\rm src}/128,\lambda_{\rm src}/2),\\
N^{\rm src}&=\sum_{y=5,27} A_y^{\rm src}\odot(a_ya_y^T),&
S_0^{\rm src}&=\operatorname{diag}\zeta-N^{\rm src},\\
S_{ij}^{\rm src}&=\begin{pmatrix}
\zeta_j-\sum_{y=5,27}(A_y^{\rm src})_{ii}p_{yj}&-N^{\rm src}_{ij}\\
-N^{\rm src}_{ij}&\zeta_i-\sum_{y=5,27}(A_y^{\rm src})_{jj}p_{yi}
\end{pmatrix}\quad(i<j),\\
F^{\rm src}&=\sum_{y=5,27}\operatorname{tr}(A_y^{\rm src}B_y^{\rm tar})-\sum_i\zeta_i+6\lambda_{\rm src}/11,\\
\mathbf g^{\rm src}&=(1000\det S_0^{\rm src},\det S_{01}^{\rm src},\det S_{02}^{\rm src}),\\
\Psi(\mathbf x,\eta)&=(\nabla_{\mathbf x}(F^{\rm src}+\eta\cdot\mathbf g^{\rm src}),\mathbf g^{\rm src}).
\end{aligned}
\tag{RG.6}
$$

Here $\odot$ is entrywise multiplication. The conditional premise is the isolated algebraic zero of $\Psi$ in the radius-$10^{-24}$ product box about these exact rational decimal centres:

| Coordinate | Centre |
| --- | --- |
| $\lambda_{\rm src}$ | $0.479508042205945691075728241615$ |
| $\alpha_1$ | $1.412018697539825943102823246594$ |
| $\alpha_2$ | $1.185897402486986028204155873343$ |
| $\beta_1$ | $0.413330945620125544606320492846$ |
| $\beta_2$ | $0.809647491041060318009094562763$ |
| $z_{\rm src}$ | $0.066998926272600209516864472757$ |
| $\eta_0$ | $0.279795267654829218213193898783$ |
| $\eta_1$ | $0.199570407911600478528148253443$ |
| $\eta_2$ | $0.091392615490799158339482855657$ |

At that point take the credited positive rank-one factors

$$
\begin{aligned}
H^{\rm src}&=1000\eta_0\operatorname{adj}S_0^{\rm src},&
Q^{01}&=\eta_1\operatorname{adj}S_{01}^{\rm src},&
Q^{02}&=\eta_2\operatorname{adj}S_{02}^{\rm src},\\
h&=H^{\rm src}e_0/\sqrt{H^{\rm src}_{00}},&
(a,b)^T&=Q^{01}e_0/\sqrt{Q^{01}_{00}},&
(c,d)^T&=Q^{02}e_0/\sqrt{Q^{02}_{00}},\\
m_1&=1-H^{\rm src}_{11}-Q^{01}_{00},&
m_2&=1-H^{\rm src}_{22}-Q^{02}_{00},\\
D&=\operatorname{diag}(h_0,h_1,h_2),&
T&=a|0\rangle\langle1|+b|1\rangle\langle0|,&
S&=c|0\rangle\langle2|+d|2\rangle\langle0|,\\
M&=\operatorname{diag}(0,m_1,m_2),& \kappa&=h_0a+h_1b.
\end{aligned}
\tag{RG.7}
$$

First-coordinate vectors have the matrix size appropriate to their expression. The adjugate is the transposed cofactor matrix. CG §§13–16 and 22 and current JR Proposition 34.2 supply the following conditional identities and margins:

$$
\begin{gathered}
h_i,a,b,c,d,m_1,m_2>0,\quad 0<\kappa<1/4,\quad
D^\dagger D+T^\dagger T+S^\dagger S+M=I_3,\\
\alpha=\frac{ab}{h_0h_1}>0,\quad \beta=\frac{cd}{h_0h_2}>0,
\quad \ell=\alpha+\beta<\frac{18}{695}<\frac1{36},\quad k=1-\ell,\\
\frac{968}{1000}<h_0^2<\frac{970}{1000},\quad
\frac{498}{1000}<h_1^2<\frac{500}{1000},\quad
\frac{655}{1000}<h_2^2<\frac{656}{1000},\\
h_0h_1>\frac{695}{1000},\quad h_0h_2>\frac{796}{1000},\quad
 a^2+b^2+c^2+d^2<\frac{36}{1000},\quad
(S_{01}^{\rm src})_{00},(S_{02}^{\rm src})_{00}>\frac1{10}.
\end{gathered}
\tag{RG.8}
$$

In particular $h_0^2+b^2+d^2=1$, $h_1^2+a^2+m_1=1$, $h_2^2+c^2+m_2=1$. The symbols $\alpha,\beta$ here are neither root-chart coordinates nor history phases. Section 8 spells out the further rational implications used for the original histories. These are implications of the supplied premises, not a new isolation or enclosure certificate.

**Definition 2.2 (complete fixed channel and binary law).** For every complex $A\in M_5$ put $A_V=E^\dagger AE$, $g(t)=2/(1+t)^2$ for $0\le t\le1$, and fix

$$
\begin{aligned}
\Phi_*^L(A)&=E(DA_VD^\dagger+TA_VT^\dagger+SA_VS^\dagger)E^\dagger,\\
\Phi_{*,j}^f(A)(dt)&=g(t)\left[w_j\operatorname{tr}(MA_V)+\mathbf1_{j=2}\operatorname{tr}(Q_5A)\right]dt\,P_f.
\end{aligned}
\tag{RG.9}
$$

Every extra-sector map is zero. This channel annihilates every $V$–$V^\perp$ cross operator and has zero complementary live action. Since $\int_0^1g(t)dt=1$ and $\sum_jw_j=1$, (RG.8) proves TP; each term is CP, also at arbitrary passive-reference amplification. Equality with this channel always includes all complex matrices, conditional reference operators and every separate labelled Borel-time CP measure. The inherited benchmark is $\mathcal E(\Phi_*)=\mathcal E_*=F^{\rm src}$, with the conditional enclosure

$$
0.14817810291080132013<\mathcal E_*<0.14817810291080132014.
\tag{RG.10}
$$

For public $s\in[0,1]$ the required every-input binary effects are

$$
F_r(s)=\frac{I_5+rs\kappa EX_{01}E^\dagger}{2},\quad
X_{01}=|0\rangle\langle1|+|1\rangle\langle0|,\quad r\in\{+1,-1\}.
\tag{RG.11}
$$

On a positive $\sigma$, write the unnormalized compression $\rho=E^\dagger\sigma E$. Its record mass is $\operatorname{tr}\sigma/2+rs\kappa\operatorname{Re}\rho_{01}$. On an original history this is $1/2+rs\kappa en\sqrt{y(64-y)}/128$. Only the forgotten full channel (RG.9) and these effects are fixed. In particular, the interior binary-conditioned live maps and binary failure-time splits are free to vary. Negative record coefficient means exchanging $r$.

**Definition 2.3 (entire finite common class).** An implementation has a finite actually generated label $\xi$, common CP encoders $\mathcal C_\xi:M_5\to M_{d_\xi}$, arbitrary positive finite integer fibre dimensions, and common full-output CP TP decoders $\mathcal R_\xi$. Require

$$
\sum_\xi\mathcal C_\xi^\dagger(I)=I_5,\qquad
\sum_\xi\mathcal R_\xi\mathcal C_\xi=\Phi_*,\qquad
\sum_{\xi:r(\xi)=r}\mathcal C_\xi^\dagger(I)=F_r(s).
\tag{RG.12}
$$

All finite generated refinements and postprocessing coins are permitted. The encoder branches are CP/TNI; only their total is TP. A decoder is TP on its entire declared fibre; its supported live restriction is TNI. The quantum dimension counts jointly every future-accessible input-dependent system: specimen, memory, controller, accessible environment, returned systems and retained entanglement shares. An earlier receiver share is not a later independent blank. All other dilation systems are permanently inaccessible before the cut. Arbitrary passive references remain inaccessible to both operations.

There is no uncounted bypass, hidden share, callback, helper, extra specimen, history-dependent programme, runtime sensor, source prior, copying, resetting, retry, postselection or acceptance division. A coherent sum without a generated classical label is one quantum payload. An analytic Kraus index is not an already acquired hardware flag.

High means $d_\xi\ge3$. Let $G_H^{\rm acq}$ be the sum of the effects of these actual encoders and $G_H^L$ the effect of their supported live output. For positive $\sigma$ define $p_H^{\rm acq}(\sigma)=\operatorname{tr}(G_H^{\rm acq}\sigma)$ and similarly $p_H^L$. Full decoder TP gives

$$
G_H^{\rm acq}\succeq G_H^L\succeq0.
\tag{RG.13}
$$

These are unnormalized acquired masses, probabilities on normalized specimens. For supported $\rho\succeq0$ let $\mathsf E_s(\rho)$ denote the infimum of acquired high mass on $E\rho E^\dagger$ over the entire class (RG.12). It is distinct from the error $\mathcal E_*$. When the evaluated formula below applies, a finite attainer makes this infimum a minimum. The quantifier is: for each public test input and permitted strength there exists one fixed common instrument, valid on every unknown runtime input. This does not mean one design minimizes every test input simultaneously.

## 3. Coefficient Grams and a universal complex-class lower reduction

**Definition 3.1 (coefficient conventions).** Coefficient space has ordered coordinates $D,T,S$. Put

$$
\begin{gathered}
K(z)=uD+vT+wS\quad(z=(u,v,w)^T\in\mathbb C^3),\\
B=\operatorname{diag}(1,-\alpha,-\beta),\qquad \operatorname{tr}B=k,
\qquad X_c=|D\rangle\langle T|+|T\rangle\langle D|,\\
\Lambda_Z(A)=\sum_{i,j}Z_{ij}K_iAK_j^\dagger,\qquad
\Theta(Z)=\sum_{i,j}Z_{ij}K_j^\dagger K_i,\qquad (K_D,K_T,K_S)=(D,T,S),\\
C(\rho)_{ij}=\operatorname{tr}(K_i^\dagger K_j\rho).
\end{gathered}
\tag{RG.14}
$$

For $\rho\succeq0$, $C(\rho)$ is Hermitian positive semidefinite and

$$
z^\dagger C(\rho)z=\operatorname{tr}(K(z)^\dagger K(z)\rho),\qquad
\operatorname{tr}(C(\rho)Z)=\operatorname{tr}(\Theta(Z)\rho).
\tag{RG.15}
$$

These follow by expanding the sums; the reversed indices in $\Theta$ are essential. In unnormalized output-input vectorization, if $\mathcal V=(|D\rangle\!\rangle,|T\rangle\!\rangle,|S\rangle\!\rangle)$, then $J_{\Lambda_Z}=\mathcal VZ\mathcal V^\dagger$ and $\operatorname{Tr}_{\rm out}J_{\Lambda_Z}=\Theta(Z)^T$. The actual input effect is $\Theta(Z)$, not its transpose. Its order is positive and $\Theta(I)=I-M$, $\Theta(X_c)=\kappa X_{01}$.

The new evaluated domain is

$$
\rho\succeq0,\qquad C(\rho)\text{ real symmetric},\qquad C(\rho)\succ0.
\tag{RG.16}
$$

Every real positive definite $\rho$ belongs to it: $K(z)\ne0$ for $z\ne0$ because the three matrices have disjoint supports, and (RG.15) is then strictly positive. A singular $\rho$ can also belong; all the original pure states do. No nonreal Gram is replaced by its real part, and no competing instrument is required to be real.

**Lemma 3.2 (the entire singular locus).** Direct expansion gives

$$
K(z)=\begin{pmatrix}h_0u&av&cw\\bv&h_1u&0\\dw&0&h_2u\end{pmatrix},\qquad
\det K(z)=h_0h_1h_2u(u^2-\alpha v^2-\beta w^2).
\tag{RG.17}
$$

Every nonzero singular $K(z)$ has rank two. The singular directions are the full complex plane $u=0$ together with the full complex quadratic locus $z^TBz=0$. Every such direction satisfies $z^\dagger Bz\le0$.

Proof. Expanding the determinant gives $h_0h_1h_2u^3-abh_2uv^2-cdh_1uw^2$. If $u\ne0$, the minor in rows and columns $1,2$ equals $h_1h_2u^2\ne0$. If $u=0,z\ne0$, column $0$ is nonzero in coordinates $1,2$, while at least one of columns $1,2$ is nonzero in coordinate $0$. These columns are independent, and the determinant vanishes. On the plane, $z^\dagger Bz=-\alpha|v|^2-\beta|w|^2\le0$. On the quadratic, $|u|^2=|\alpha v^2+\beta w^2|\le\alpha|v|^2+\beta|w|^2$. Both components are retained. $\square$

**Theorem 3.3 (necessity for every original finite complex implementation).** Every implementation in Definition 2.3 supplies an aggregate supported live high coefficient $H$ satisfying

$$
0\preceq H\preceq I_3,\qquad \operatorname{tr}(BH)\ge k,\qquad
G_H^{\rm acq}\succeq G_H^L=E\Theta(H)E^\dagger.
\tag{RG.18}
$$

Proof. Take finite Kraus matrices of each encoder and of each supported live-decoder compression. Their products through an actual fibre give positive rank-one Choi summands of the fixed five-mode live Choi matrix, whose support is the span of the independent columns $|EDE^\dagger\rangle\!\rangle$, $|ETE^\dagger\rangle\!\rangle$, $|ESE^\dagger\rangle\!\rangle$. A kernel vector of the sum has zero quadratic form in each positive summand, hence is killed by its positive square root. Every product vector therefore belongs to that support. Each product is uniquely $EK(z)E^\dagger$, with complex $z$ and zero complementary and cross-support action.

The columns are independent but need not be normalized. A Gram left inverse of their column matrix applied to the sum of the Choi identities makes the sum of all coefficient projectors $zz^\dagger$ exactly $I_3$. Group products through actual high fibres into $H\succeq0$, the others into $L\succeq0$. Then $H+L=I_3$. A low product factors through dimension at most two and thus is singular; Lemma 3.2 gives $\operatorname{tr}(BL)\le0$, proving the first two requirements.

For every actual high label, the full decoder is TP and its live compression is TNI. Applying the positive adjoint encoder to the difference of their effects gives a positive five-mode operator. Summing these differences proves the last inequality and identifies the live effect with $E\Theta(H)E^\dagger$. It includes high acquisition later decoded into failure, and possible acquired complement or cross-support terms. It holds before evaluation on any positive input. Kraus refinements in this proof are analytic only; they add no actual accessible flag to a competitor. $\square$

**Convention 3.4 (the true cone and credited reduction).** Let $\mathcal C_2$ be the finite sums of singular coefficient projectors in Lemma 3.2, with zero included. These atoms are rank-one coefficient projectors, without a canonical factorization or ontological claim. The exact IR reduction retains $H_r\succeq0$, $L_r\in\mathcal C_2$, their sum $\sum_r(H_r+L_r)=I$, and

$$
0\preceq N=\frac{I+s\kappa X_{01}}2-\Theta(H_++L_+)\preceq M.
\tag{RG.19}
$$

It is an exact compact original-class problem, with actual finite realizations; its earlier generic branch bound is thirty. The supplied complex-cone volume CA, Sections 4–8, gives the spectral cone lift, six singular atoms, twenty-four general branches and the complete sharp-average equality face. Those are reused results, not new laws here. In its lift one subtracts a positive $2\times2$ plane slack from $L$, factors the positive remainder $AA^\dagger$, and requires the largest Takagi value of $A^TBA$ to be at most the sum of the other two, padded by zeros. No plane slack is eliminated here.

In particular $\operatorname{tr}(BL)\le0$ alone is not general cone membership. For $z=(\sqrt\alpha,i,0)^T/\sqrt{1+\alpha}$, $zz^\dagger\preceq I$ and $z^\dagger Bz=0$, but $u\ne0$, $z^TBz=2\alpha/(1+\alpha)\ne0$, so $K(z)$ is invertible. Every positive summand of a rank-one positive matrix has its range in that line; a singular-projector decomposition would require a singular vector parallel to $z$, which is impossible. Thus this matrix is outside $\mathcal C_2$. The new proof uses (RG.18) only as a necessary relaxation, and proves true cone sufficiency for its own real low matrices in Section 6.

## 4. Exact spectral evaluation of the necessary lower problem

**Lemma 4.1 (the positive generalized root).** Let $C$ be real symmetric positive definite. There is exactly one positive root $\lambda_0$ of $\det(C-\lambda B)=0$. Its slack is positive semidefinite of rank two. Let $v_0$ be its real unit kernel vector with positive $D$ coordinate. Then $b_0=v_0^TBv_0>0$.

Proof. Congruence gives $C^{-1/2}BC^{-1/2}$ inertia $(+, -,-)$: the invertible change of variables preserves maximal positive and negative subspace dimensions of the quadratic form of $B$. It has one positive eigenvalue $\gamma$ and two negative ones. Thus $C-\lambda B=C^{1/2}(I-\lambda C^{-1/2}BC^{-1/2})C^{1/2}$ has its unique positive determinant root at $\lambda_0=1/\gamma$, with two positive eigenvalues and one zero in the middle factor. The kernel is real and one dimensional. The identity $v_0^TCv_0=\lambda_0b_0>0$ proves $b_0>0$; hence its $D$ coordinate is nonzero and fixes its sign. $\square$

**Lemma 4.2 (the unique saturated branch, including degeneracies).** If $b_0<k$, there is exactly one $\lambda>\lambda_0$ with a $\mu>0$ and real unit $v$, $v_D>0$, such that

$$
A=C+\mu I-\lambda B\succeq0,\quad \operatorname{rank}A=2,\quad
Av=0,\quad v^TBv=k.
\tag{RG.20}
$$

Proof. For $\lambda\ge\lambda_0$ let $\mu(\lambda)$ be the largest eigenvalue of $\lambda B-C$. Its quadratic form is strictly negative on $D^\perp$, so at most one eigenvalue is nonnegative. At $\lambda_0$ it has a simple top eigenvalue zero; at a larger $\lambda$, the Rayleigh test $v_0$ makes the top eigenvalue positive and simple, while the other two remain strictly negative. The real unit top eigenvector can be chosen with $v_D>0$, since $\mu=\lambda v^TBv-v^TCv\ge0$ implies $b=v^TBv>0$.

Differentiating its simple eigenpair gives

$$
\mu'(\lambda)=b(\lambda),\qquad
b'(\lambda)=\mu''(\lambda)
 =2\sum_{j\ne\mathrm{top}}
 \frac{|v_j^TBv|^2}{\mu-\mu_j}\ge0.
\tag{RG.21}
$$

For completeness, differentiating $Mv=\mu v$, $v^Tv=1$, with $M=\lambda B-C$, gives $v^Tv'=0$, $\mu'=v^TBv$ and $v_j^Tv'=v_j^TBv/(\mu-\mu_j)$. Differentiating $v^TBv$ yields (RG.21). An orthonormal eigenbasis of the complementary space suffices even when its eigenvalues coincide. The simple top eigenpair is locally differentiable by solving the eigen-equation together with normalization on $v^\perp$; its positive-$D$ convention patches these solutions.

Vanishing of (RG.21) would make $Bv$ parallel to $v$. Since $b>0$, the only possible eigenline of $B$ is $e_D$. Its eigen-equation then makes $Ce_D$ parallel to $e_D$. In that decoupled case the sole positive generalized kernel in Lemma 4.1 is already $e_D$ and $b_0=1$, contrary to $b_0<k<1$. Thus $b$ increases strictly in the case at hand. This argument also covers $\alpha=\beta$.

The $e_D$ Rayleigh test gives $\mu\ge\lambda-c_{00}$. Combining it with $\mu=\lambda b-v^TCv$ gives

$$
0\le1-b\le c_{00}/\lambda.
\tag{RG.22}
$$

Hence $b\to1$. It starts at $b_0<k$ and crosses $k<1$ once by continuity and strict increase. The resulting $\mu>0$ and $v$ give (RG.20). Conversely PSD of $A$ and a zero eigenvalue make $\mu$ the unique positive top eigenvalue of $\lambda B-C$; therefore any pair in (RG.20) is on the curve just considered. This proves uniqueness. $\square$

**Definition 4.3 (evaluated constants).** For $C$ in (RG.16) define

$$
\begin{array}{c|c|c|c|c}
\text{case}&\lambda&\mu& H^*&F(C)\\ \hline
b_0\ge k&\lambda_0&0&\displaystyle\frac{k}{b_0}v_0v_0^T&k\lambda_0\\
b_0<k&\text{Lemma 4.2}&\text{Lemma 4.2}&vv^T&k\lambda-\mu
\end{array}
\tag{RG.23}
$$

In the first row write $v=v_0$, $t=k/b_0\le1$; in the second write $t=1$. At $b_0=k$ use the first spectral row and the saturated lift below. A decoupled $D$ is in the unsaturated row with $b_0=1$, never in the strict-monotonicity case.

The algebraic branch can be stated explicitly. In coefficient order $D,T,S$ put

$$
\begin{aligned}
P(\lambda,\mu)={}&(c_{00}+\mu-\lambda)(c_{11}+\mu+\alpha\lambda)(c_{22}+\mu+\beta\lambda)
 +2c_{01}c_{02}c_{12}\\
&-(c_{00}+\mu-\lambda)c_{12}^2
 -(c_{11}+\mu+\alpha\lambda)c_{02}^2
 -(c_{22}+\mu+\beta\lambda)c_{01}^2.
\end{aligned}
\tag{RG.24}
$$

For $b_0<k$, the unique branch is exactly

$$
P=0,\qquad P_\lambda+kP_\mu=0,\qquad
\lambda>\lambda_0,\quad\mu>0,\quad C+\mu I-\lambda B\succeq0.
\tag{RG.25}
$$

Indeed the PSD matrix $A$ then has rank two, with $\operatorname{adj}A=\gamma vv^T$, $\gamma>0$. Cofactor differentiation gives $P_\mu=\operatorname{tr}\operatorname{adj}A>0$ and $P_\lambda=-\operatorname{tr}((\operatorname{adj}A)B)$, so the derivative equation is precisely $v^TBv=k$. Lemma 4.2 proves both selection and uniqueness, rather than inferring optimality from stationarity. In either row of (RG.23) a normalized kernel formula is

$$
v=\frac{\operatorname{adj}(A)e_D}
 {\sqrt{(\operatorname{adj}A)_{DD}\operatorname{tr}\operatorname{adj}A}},
\qquad A=C+\mu I-\lambda B.
\tag{RG.26}
$$

The denominator is nonzero because $v_D>0$; substituting $\gamma vv^T$ verifies the normalization and sign. These are finite spectral operations and a uniquely specified branch, with no instrument or matrix minimization left in $F$.

**Theorem 4.4 (exact certificate and unique aggregate equality matrix).** Define

$$
S_{\rm cert}=C-\lambda B+\mu vv^T.
\tag{RG.27}
$$

It is PSD of rank two with kernel $\mathbb Cv$. For every complex Hermitian $H$ satisfying the first two constraints of (RG.18),

$$
\begin{aligned}
\operatorname{tr}(CH)-(\lambda k-\mu)
={}&\lambda[\operatorname{tr}(BH)-k]
 +\operatorname{tr}(S_{\rm cert}H)
 +\mu(1-v^\dagger Hv)\ge0.
\end{aligned}
\tag{RG.28}
$$

Equality holds uniquely at $H^*$ in (RG.23). Consequently every original implementation, at every strength, has acquired and supported live high cost at least $F(C)$ on the selected input.

Proof. In the unsaturated row $S_{\rm cert}=C-\lambda_0B$, whose rank and positivity are Lemma 4.1. In the saturated row, $\lambda B-C$ is $\mu$ on $v$ and strictly negative on $v^\perp$. Subtracting it and adding $\mu vv^T$ gives zero on $v$ and a strictly positive form on $v^\perp$. Expansion proves (RG.28). Its first term is nonnegative by $\lambda>0$ and the trace budget; the second by positivity; the third by $\mu\ge0$ and $H\preceq I$. This remains true for complex $H$.

Both displayed $H^*$ are feasible: $\operatorname{tr}(BH^*)=k$, $0\preceq H^*\preceq I$, and $S_{\rm cert}H^*=0$. If $\mu>0$, they also have $v^\dagger H^*v=1$. Thus each makes every term zero. Conversely $\operatorname{tr}(S_{\rm cert}H)=0$ makes $S_{\rm cert}^{1/2}H^{1/2}=0$, so $\operatorname{ran}H\subseteq\mathbb Cv$. Equality in the first term fixes its coefficient to $k/(v^TBv)$, which is exactly (RG.23), including the transition. Theorem 3.3 and (RG.15) transfer this bound to every original acquired and live cost. $\square$

For an acquired minimizer that matches this lower value, the chain acquired $\ge$ live $\ge F$ forces the same $H^*$. A pure selected input forces only the expectation of $G_H^{\rm acq}-G_H^L$ there to vanish. It does not force that entire positive slack operator to vanish. The instruments below have zero slack on every input, providing the stronger property by construction.

## 5. Explicit positive-strength record lifts

**Lemma 5.1 (unsaturated lift and exact norm cap).** Suppose $b_0>k$, let $H^*=tvv^T$ as in (RG.23), and put

$$
L=I-tvv^T\succ0,\quad G=L^{-1},\quad
\nu=\sqrt{G_{DD}G_{TT}}+|G_{DT}|,\qquad
s_{\rm cap}(C)=\min\{1/2,1/\nu\}>0.
\tag{RG.29}
$$

For every $0\le s\le s_{\rm cap}(C)$ the matrices

$$
H_r=H^*/2,\qquad L_r=(L+rsX_c)/2,\qquad N_r=M/2
\tag{RG.30}
$$

are real PSD, satisfy $\operatorname{tr}(BL_r)=0$, and obey

$$
\sum_r(H_r+L_r)=I,\quad N_++N_-=M,\quad
\Theta(H_r+L_r)+N_r=(I+rs\kappa X_{01})/2.
\tag{RG.31}
$$

Proof. Since $t<1$, $L\succ0$. Set $x=L^{-1/2}e_D$, $y=L^{-1/2}e_T$. The congruence of $X_c$ is $xy^T+yx^T$. Its two nonzero eigenvalues are $x^Ty\pm\|x\|\|y\|$: restrict to their two-dimensional span and compute its characteristic polynomial, whose trace is $2x^Ty$ and determinant $(x^Ty)^2-\|x\|^2\|y\|^2$. The two vectors are independent, so the remaining eigenvalue is zero and the norm is precisely $\nu$. Thus $L\pm sX_c\succeq0$ when $s\nu\le1$, also at equality. The number $\nu$ is finite and positive.

Also $\operatorname{tr}(BL)=k-tb_0=0$ and $\operatorname{tr}(BX_c)=0$. This gives the low trace claims. Finally $H_r+L_r=(I+rsX_c)/2$, so (RG.31) follows from $\Theta(I)=I-M$ and $\Theta(X_c)=\kappa X_{01}$. $\square$

**Lemma 5.2 (saturated and transition lift).** Suppose $H^*=vv^T$, with $v=(v_D,v_T,v_S)^T$ real unit, $v_D>0$ and $v^TBv=k$. This includes $b_0=k,\mu=0$ and $b_0<k,\mu>0$. Set

$$
Q_c=I-vv^T,\qquad R_v=\alpha v_S^2+\beta v_T^2>0.
\tag{RG.32}
$$

Define a real symmetric $J=J_v$ by

$$
\begin{aligned}
J_{DD}&=-v_T/v_D,&J_{DT}&=1,&J_{DS}&=0,\\
J_{TT}&=-\frac{v_T(\beta v_D^2+v_S^2)}{v_DR_v},&
J_{SS}&=-\frac{v_T(v_T^2-\alpha v_D^2)}{v_DR_v},&
J_{TS}&=\frac{v_S(v_T^2-\alpha v_D^2)}{v_DR_v}.
\end{aligned}
\tag{RG.33}
$$

Put

$$
\begin{gathered}
\tau=-(h_0^2J_{DD}+b^2J_{TT}+d^2J_{SS}),\qquad
Z_v=J+\tau I,\qquad W_v=\Theta(Z_v)-\kappa X_{01},\\
M_2=\operatorname{diag}(m_1,m_2),\qquad W_2=W_v[\{1,2\}],\\
s_{\rm cap}(C)=\min\left\{\frac12,\frac1{|\tau|},
\frac1{\|J+\tau Q_c\|_{\rm op}},
\frac1{\|M_2^{-1/2}W_2M_2^{-1/2}\|_{\rm op}}\right\}>0.
\end{gathered}
\tag{RG.34}
$$

A reciprocal with zero denominator means $+\infty$ and imposes no restriction. For every $0\le s\le s_{\rm cap}(C)$ set

$$
\begin{aligned}
H_r&=\frac{1+rs\tau}{2}vv^T,\\
L_r&=\frac{Q_c+rs(J+\tau Q_c)}2,\\
N_r&=\frac{M-rsW_v}2.
\end{aligned}
\tag{RG.35}
$$

These are real PSD matrices satisfying $\operatorname{tr}(BL_r)=0$ and all identities (RG.31). Each $N_r$ kills specimen coordinate $0$ and has rank at most two.

Proof. Unit length and $v^TBv=k=1-\ell$ give

$$
(1+\alpha)v_T^2+(1+\beta)v_S^2=\ell>0.
\tag{RG.36}
$$

Thus $v_T,v_S$ are not both zero, proving $R_v>0$. No formula divides by either of those coordinates individually. The $D$ row of $Jv$ is $-v_T+v_T=0$ and its $S$ row cancels directly. Its $T$ row is

$$
v_D+\frac{-v_T^2(\beta v_D^2+v_S^2)+v_S^2(v_T^2-\alpha v_D^2)}{v_DR_v}
 =v_D-\frac{v_D^2(\beta v_T^2+\alpha v_S^2)}{v_DR_v}=0.
\tag{RG.37}
$$

The $B$ trace of $J$, with common denominator $v_DR_v$, has numerator

$$
-v_TR_v+\alpha v_Tv_S^2+\beta v_T^3=0.
\tag{RG.38}
$$

Hence $Jv=0$, $J=Q_cJQ_c$, and $\operatorname{tr}(BJ)=0$. These calculations remain valid if $v_T=0$ or $v_S=0$.

For a real symmetric coefficient $Z$, direct use of (RG.7) gives

$$
\Theta(Z)_{00}=h_0^2Z_{DD}+b^2Z_{TT}+d^2Z_{SS},\quad
\Theta(Z)_{01}=\kappa Z_{DT},\quad
\Theta(Z)_{02}=(h_0c+h_2d)Z_{DS}.
\tag{RG.39}
$$

The exact $00$ normalization is $h_0^2+b^2+d^2=1$. Substituting $Z_v$ and the definition of $\tau$ makes $\Theta(Z_v)_{00}=0$, its $01$ entry $\kappa$, and its $02$ entry zero. Therefore $W_v$ has zero first row and column. Its $12$ entry is permitted to be nonzero; $W_2$ is the full remaining block.

Every denominator in (RG.33) is positive and finite. Since $M_2\succ0$, all matrices in (RG.34) are finite. With the zero-reciprocal convention, their minimum with $1/2$ is strictly positive. The cap makes $1\pm s\tau\ge0$. On $v^\perp$, $Q_c$ is the identity and $\|s(J+\tau Q_c)\|\le1$; on $v$ both terms vanish. This proves $L_r\succeq0$. On specimen coordinates $1,2$, the failure condition follows from

$$
N_r|_{\{1,2\}}=\tfrac12 M_2^{1/2}
 [I-rsM_2^{-1/2}W_2M_2^{-1/2}]M_2^{1/2}\succeq0.
\tag{RG.40}
$$

Its coordinate $0$ is zero. The proof includes all closed cap endpoints, rank drops and zero high weights.

Finally $\operatorname{tr}(BQ_c)=k-k=0$ and (RG.38) prove the low traces. Summing records gives $H^*$, $I-H^*$ and $M$. At a record,

$$
H_r+L_r=\frac{I+rs(J+\tau I)}2,
\tag{RG.41}
$$

so the definition of $W_v$ gives (RG.31). These lifts use the lawful freedom of interior binary live maps; a fixed JR-conditioned split was never assumed in the lower argument. $\square$

## 6. True low-cone membership and actual fourteen-branch instruments

**Lemma 6.1 (real trace-zero null decomposition).** Every real symmetric $L\succeq0$ with $\operatorname{tr}(BL)=0$ admits

$$
L=\sum_{j=1}^m z_jz_j^T,\quad m\le3,\quad z_j\in\mathbb R^3\setminus\{0\},\quad z_j^TBz_j=0.
\tag{RG.42}
$$

Each $K(z_j)$ has rank exactly two and nonzero $D$ coefficient. This is the real-face decomposition of CA Theorem 5.1, with its construction recorded for use in the instruments.

Proof. A real spectral square root supplies $L=RR^T$ with $r=\operatorname{rank}L\le3$ columns. The real symmetric $A=R^TBR$ has trace zero. It has an orthonormal basis with all Rayleigh diagonal values zero. To construct one, if $A=0$ use any orthonormal basis. Otherwise trace zero gives eigenvalues $\lambda_+>0>\lambda_-$ with real orthonormal eigenvectors $f_+,f_-$. The vector

$$
f=\frac{\sqrt{-\lambda_-}f_++\sqrt{\lambda_+}f_-}{\sqrt{\lambda_+-\lambda_-}}
\tag{RG.43}
$$

is unit with $f^TAf=0$. Compression to $f^\perp$ still has trace zero. Induction constructs the remaining basis, including a zero compression. If $O$ is its orthogonal column matrix, the columns of $RO$ have projector sum $L$ and zero $B$ quadratic value. Delete zero columns; when $L=0$ use no atoms. For a nonzero real null vector, $u=0$ would imply $\alpha v^2+\beta w^2=0$, hence $z=0$. Thus $u\ne0$ and (RG.17) gives rank two, with columns $1,2$ independent. This places every constructed $L_r$ in the actual full singular cone, not only its trace relaxation. $\square$

**Theorem 6.2 (complete common instrument at every stated cap).** Either lift in Section 5 is realizable in Definition 2.3 with acquired high effect exactly $E\Theta(H^*)E^\dagger$, genuine rank-three high products, and at most fourteen actually generated labels. Every fibre dimension is at most three. The realization satisfies the full complex channel, arbitrary passive-reference identities, each labelled Borel-time measure, complement action, zero cross-support action and zero extra sectors.

Proof. Write $H_r=h_rvv^T$, with $h_r=t/2$ in (RG.30) or $h_r=(1+rs\tau)/2$ in (RG.35). For $h_r>0$ install the encoder matrix

$$
C_{r,H}=\sqrt{h_r}K(v)E^\dagger:\mathbb C^5\to\mathbb C^3
\tag{RG.44}
$$

and the full live TP decoder $X\mapsto EXE^\dagger$. Its product is $\sqrt{h_r}EK(v)E^\dagger$ and its effect is $h_rEK(v)^\dagger K(v)E^\dagger$. Since $v_D>0$ and $v^TBv>0$ in either spectral branch,

$$
\det(\sqrt{h_r}K(v))=h_r^{3/2}h_0h_1h_2v_D(v^TBv)\ne0.
\tag{RG.45}
$$

Thus each retained high branch is genuinely rank three. A zero high weight contributes no branch.

Apply Lemma 6.1 separately to each $L_r$. For each nonzero atom $z$, let $b_1,b_2$ be columns $1,2$ of $K(z)$ and fix

$$
q_1=b_1/\|b_1\|,\qquad
q_2=\frac{b_2-q_1(q_1^\dagger b_2)}{\|b_2-q_1(q_1^\dagger b_2)\|},\qquad U_z=(q_1,q_2).
\tag{RG.46}
$$

Their independence proves that the denominators are positive. Then $U_z^\dagger U_z=I_2$ and $U_zU_z^\dagger K(z)=K(z)$. Install the dimension-two encoder $C_{r,L,z}=U_z^\dagger K(z)E^\dagger$ and full TP decoder $X\mapsto EU_zXU_z^\dagger E^\dagger$. Their product is exactly $EK(z)E^\dagger$ and the encoder effect is $EK(z)^\dagger K(z)E^\dagger$. All choices are fixed from public constants, never the unknown specimen.

Each $N_r\succeq0$ is supported on specimen coordinates $1,2$. For its at most two positive spectral eigenpairs $(\eta_j,f_j)$ use the scalar encoder row

$$
C_{r,f,j}=\sqrt{\eta_j}\langle f_j|E^\dagger.
\tag{RG.47}
$$

Decode scalar mass $z$ into the entire five-label failure measure $z w_lg(t)dt\,P_f$ at each original label $l$. This decoder is TP since $\sum_lw_l=\int g=1$, and its live action is zero. Spectral zero rows are omitted.

At each record add one scalar CP complement encoder

$$
\mathcal C_{r,\perp}(A)=\operatorname{tr}(Q_5A)/2.
\tag{RG.48}
$$

Its decoder sends scalar mass $z$ to $zg(t)dt\,P_f$ solely at original label $2$ and is TP. The map has Kraus rows $\langle(e_0-e_4)/\sqrt2|/\sqrt2$ and $\langle(e_1-e_3)/\sqrt2|/\sqrt2$. Their multiplicity is permanently discarded: there is one scalar output branch, not a future-accessible two-dimensional memory.

Give these encoders the actual generated labels $(r,H)$, $(r,L,j)$, $(r,f,j)$ and $(r,\perp)$. They are the specification of a new mathematical instrument, with accessible classical labels as stated. No inaccessible Kraus label of an old implementation has been declared observable. All other input-dependent dilation systems are permanently inaccessible before the counted cut.

At record $r$ the supported encoder effect is $\Theta(H_r+L_r)+N_r$. By (RG.31), adding $Q_5/2$ gives exactly $F_r(s)$. The total encoder effect is

$$
E[\Theta(I)+N_++N_-]E^\dagger+Q_5
 =E[(I-M)+M]E^\dagger+Q_5=I_5.
\tag{RG.49}
$$

Each encoder is CP; each positive individual effect is bounded by this total $I_5$, so each is TNI and their joint sum is TP. Every live decoder is TP on its entire carrier because its defining matrix is an isometry. The scalar decoders were normalized above. There are per record at most one high live branch, three low live branches, two supported scalar failure branches and one scalar complement branch. Thus the actual acquired label bound is

$$
2(1+3+2+1)=14.
\tag{RG.50}
$$

All zero atoms, high weights and spectral rows are deleted, including at cap endpoints. The dimensions of the retained branches are respectively $3,2,1,1$. Continuous output time remains a whole measure supplied by a decoder; the branch bound does not turn time into a finite output alphabet.

The product identities in (RG.44) and (RG.46), summed with coefficient matrix $\sum_r(H_r+L_r)=I$, give exactly the live line of (RG.9) on every complex matrix unit. At record $r$, scalar supported rows sum to the failure functional $\operatorname{tr}(N_rA_V)$, giving $w_lg(t)dt\operatorname{tr}(N_rA_V)P_f$. Summing records gives $M$; the complement halves give the $Q_5$ term only at label $2$. This proves each separate failure measure on every complex input matrix.

To make the reference claim explicit, let $X$ be an arbitrary matrix on $\mathbb C^5\otimes\mathcal H_R$ for a passive finite reference. Replace every encoder and decoder matrix by its tensor product with $I_R$. A scalar supported row retains its actual conditional reference operator $(C\otimes I_R)X(C^\dagger\otimes I_R)$. Summing rows gives

$$
R_{r,f}(X)=\operatorname{Tr}_5[(EN_rE^\dagger\otimes I_R)X],\qquad
R_{r,\perp}(X)=\tfrac12\operatorname{Tr}_5[(Q_5\otimes I_R)X].
\tag{RG.51}
$$

For every Borel set $\mathcal B\subseteq[0,1]$, the record-$r$, label-$l$ failure output is precisely

$$
P_f\otimes\left[w_lR_{r,f}(X)+\mathbf1_{l=2}R_{r,\perp}(X)\right]
 \int_{\mathcal B}g(t)dt.
\tag{RG.52}
$$

The fixed output order is stopped system then reference. Tensoring the live Kraus identities proves its conditional reference output as well. These identities extend to arbitrary passive-reference amplifications by the same finite Kraus formulas. They concern conditional reference operators, not just probabilities or the unconditional reference marginal.

Every supported compression and complement trace kills all $V$–$V^\perp$ cross matrix units. There is no complementary live output, no endpoint atom or singular addition, and no extra-sector map. Labels $0,13$ retain their zero maps, and labels $1,3$ remain separate. Common fixed metadata can be carried identically. Hence the entire channel (RG.9), all twelve complete outputs and the inherited error are preserved. Every high decoder is wholly live, so its acquired and live effects coincide; the aggregate is exactly $E\Theta(H^*)E^\dagger$. $\square$

**Theorem 6.3 (evaluated small-record law).** For every $\rho$ in (RG.16) and every $0\le s\le s_{\rm cap}(C(\rho))$,

$$
\mathsf E_s(\rho)=F(C(\rho)).
\tag{RG.53}
$$

The supported live high minimum is the same. For any positive five-mode test $\sigma$ whose unnormalized compression satisfies (RG.16), its acquired and live minima are $F(C(E^\dagger\sigma E))$. Each has an actual common attainer of at most fourteen branches.

Proof. Theorem 4.4 is a lower bound for every original design at every strength. Lemmas 5.1–5.2 and Theorem 6.2 match it throughout the indicated cap, giving (RG.53) and actual attainment. The five-mode domination in (RG.18) supplies the lower bound for $\sigma$, including complement mass and cross-support coherence; the constructed effect is supported on $V$ and gives the matching upper. There is no normalization of the compression. $\square$

Positive rescaling $\rho\mapsto c\rho$, $c>0$, scales $C,\lambda,\mu,F$ by $c$ and leaves $v,H^*$ and the cap unchanged. This follows directly from the eigen-equations and lift formulas. Algebraic $C$ gives algebraic selected constants: the spectral root, the unique polynomial/PSD branch, adjugate kernel and finite spectral norms in the caps are all real algebraic. This is an exact specification, without a decimal evaluation or efficient-computation claim.

## 7. The already known diagonal and sharp-average laws

**Convention 7.1 (precise current JR credit).** Current [JR, Sections 34–40][JR] already owns the diagonal, common-attainer, original sign-average and worst-history laws. The exact dictionary is

$$
\alpha=\theta_{\rm JR},\quad \beta=\omega_{\rm JR},\quad
\ell=\delta_{\rm JR},\quad k=k_{\rm JR},\quad
p_s=1-\beta-\alpha v_s^{\rm JR},\quad q_s=1-v_s^{\rm JR}.
\tag{RG.54}
$$

For supported diagonal $\tau\succeq0$, the known resource effect is $G_0(s)=p_sD^\dagger D+q_sT^\dagger T$. Its coefficients have $p_s=k,q_s=0$ for $0\le s\le\sqrt\ell$. For $\sqrt\ell<s\le1$, $p_s=k+\alpha q_s$ and the unique $0<q_s\le k/(1-\alpha)$ satisfies

$$
s=\sqrt{p_sq_s}+\sqrt{(1-p_s)(1-q_s)}.
\tag{RG.55}
$$

The known sharp four-sign mean at original height $y$ is

$$
g_y(s)=p_sA_y+q_sB_y,
\quad A_y=\operatorname{tr}(D^\dagger D\operatorname{diag}p_y),
\quad B_y=\operatorname{tr}(T^\dagger T\operatorname{diag}p_y).
\tag{RG.56}
$$

The known worst-history optimum is $g_{27}(s)$, and one common finite design attains all these diagonal minima and means. The sign mean uses the exact identity $\sum_{e,n}\rho_{y,e,n}/4=\operatorname{diag}p_y$ as a proof operation, not a prior on the unknown histories.

Current JR proves its averaged and worst-history conclusions over the broader all-error-optimizer class and its specified countable/integral factorizations. Record-preserving sign averaging relabels $r$ to $enr$ and fixes the averaged live Choi matrix and total failure effect. It does not identify each optimizer's entire forgotten channel or labelled failure-time law. The individual certificates in this volume concern the fixed full channel (RG.9), without extending them to every other error optimizer.

The integrated [IR companion][IR] supplies interior binary-live freedom, perturbation/nonleast results and the compact exact full complex reduction. Its reuse of this diagonal package is credited to the full current JR, rather than only JR Sections 29–33. The cone sequel supplies the six-atom/twenty-four-branch improvement and sharp-average equality classification: a weak/threshold singleton and, at finitely many nonempty exceptional strong interior strengths, closed segments instead of singletons. Equality at one positive definite original sign average kills supported acquired-to-live slack; equality on an arbitrary pure test need not. Those equality resource vectors do not classify other frontier points or complete implementations. Section 9 below constructs points outside all three equality faces, while reusing their sharp means.

## 8. Every original pure history on one common positive interval

**Lemma 8.1 (explicit original Grams).** Put $\kappa_{02}=h_0c+h_2d$ and, for the unsigned height $y$, define

$$
\begin{gathered}
A_y=\sum_i h_i^2p_{yi},\quad
B_y=b^2p_{y0}+a^2p_{y1},\quad
C_y=d^2p_{y0}+c^2p_{y2},\quad q_y=\frac{\sqrt{y(64-y)}}{128},\\
C^{(y)}=\begin{pmatrix}
 A_y&\kappa q_y&\kappa_{02}\sqrt y/16\\
 \kappa q_y&B_y&ac\sqrt{64-y}/16\\
 \kappa_{02}\sqrt y/16&ac\sqrt{64-y}/16&C_y
\end{pmatrix}.
\end{gathered}
\tag{RG.57}
$$

Then $C(\rho_{y,e,n})=C_g C^{(y)}C_g$, where $C_g=\operatorname{diag}(1,en,e)$ commutes with $B$.

Proof. The three vectors $Da_y,Ta_y,Sa_y$ have this Gram matrix: the $DT$ inner product is $(h_0a+h_1b)\sqrt{p_{y0}p_{y1}}$, the $DS$ product is $(h_0c+h_2d)\sqrt{p_{y0}p_{y2}}$, and the $TS$ product is $ac\sqrt{p_{y1}p_{y2}}$. Substituting (RG.2) gives the displayed entries. Also $U_{e,n}DU_{e,n}=D$, $U_{e,n}TU_{e,n}=enT$ and $U_{e,n}SU_{e,n}=eS$. Substitution in (RG.14) proves the congruence. $\square$

**Lemma 8.2 (complete rational implications for nonsingularity).** Under the source box and margins of Section 2, set

$$
r_T=\frac{ah_1}{bh_0},\qquad r_S=\frac{ch_2}{dh_0}.
\tag{RG.58}
$$

Then $1/4<r_T<2/5$, $1/10<r_S<1/6$. The only positive height at which the three columns $Da_y,Ta_y,Sa_y$ can be dependent is

$$
y_{\rm crit}=\frac{64(r_T+r_S)}{1+r_T},\qquad 16<y_{\rm crit}<27.
\tag{RG.59}
$$

Consequently all twelve original Grams are real positive definite.

Proof. The following positive rational comparisons give the entire implication chain, with the inherited source enclosures kept as premises. Write $r_5=1+\alpha_1^2+\alpha_2^2$ and $r_{27}=1+\beta_1^2+\beta_2^2$, only in this source-bound argument. The box implies

$$
\begin{gathered}
479/1000<\lambda_{\rm src}<480/1000,\quad
1412/1000<\alpha_1<1413/1000,\quad
1185/1000<\alpha_2<1186/1000,\\
413/1000<\beta_1<414/1000,\quad
809/1000<\beta_2<810/1000,\quad \eta_1>19/100,\\
439/100<r_5<441/100,\qquad 182/100<r_{27}<183/100,\\
223/100<\sqrt5<224/100,\quad519/100<\sqrt{27}<520/100,\quad
17<\sqrt{295}<18,\quad31<\sqrt{999}<32.
\end{gathered}
\tag{RG.60}
$$

The two $r$ bounds follow by squaring the positive chart bounds and adding one; each radical bound follows by positive square comparison. Lower numerator and upper denominator in the source formulas give

$$
\begin{aligned}
(A_5^{\rm src})_{00}&>
 \frac{(479/1000)(1412/1000)^2}{441/100}>21/100,\\
(A_{27}^{\rm src})_{00}&>
 \frac{(520/1000)(413/1000)^2}{183/100}>4/100.
\end{aligned}
\tag{RG.61}
$$

For their $01$ entries the explicit rational endpoints are

$$
\begin{aligned}
180/1000&<\frac{(479/1000)(1412/1000)(1185/1000)}{441/100}
 <(A_5^{\rm src})_{01}\\
&<\frac{(480/1000)(1413/1000)(1186/1000)}{439/100}<185/1000,\\
94/1000&<\frac{(520/1000)(413/1000)(809/1000)}{183/100}
 <(A_{27}^{\rm src})_{01}\\
&<\frac{(521/1000)(414/1000)(810/1000)}{182/100}<97/1000.
\end{aligned}
\tag{RG.62}
$$

All products and denominators are positive, so every comparison has its indicated direction. The exact formula for $N^{\rm src}_{01}$ therefore yields

$$
\begin{aligned}
45/1000&<\frac{180\cdot17+94\cdot31}{128000}
 <N^{\rm src}_{01}\\
&=\frac{(A_5^{\rm src})_{01}\sqrt{295}+(A_{27}^{\rm src})_{01}\sqrt{999}}{128}\\
&<\frac{185\cdot18+97\cdot32}{128000}<51/1000.
\end{aligned}
\tag{RG.63}
$$

The $02$ source entry has one negative term; retain its sign rather than bounding it as a sum of positive terms. Write $N^{\rm src}_{02}=P_{\rm pos}-P_{\rm neg}$ with

$$
P_{\rm neg}=\frac{\lambda_{\rm src}\alpha_1\sqrt5}{16r_5},\qquad
P_{\rm pos}=\frac{(1-\lambda_{\rm src})\beta_1\sqrt{27}}{16r_{27}}.
\tag{RG.64}
$$

Its full rational endpoint comparisons are

$$
\begin{aligned}
21/1000&<\frac{(479/1000)(1412/1000)(223/100)}{16(441/100)}
 <P_{\rm neg}\\
&<\frac{(480/1000)(1413/1000)(224/100)}{16(439/100)}<22/1000,\\
38/1000&<\frac{(520/1000)(413/1000)(519/100)}{16(183/100)}
 <P_{\rm pos}\\
&<\frac{(521/1000)(414/1000)(520/100)}{16(182/100)}<39/1000.
\end{aligned}
\tag{RG.65}
$$

Subtracting these intervals gives $16/1000<N^{\rm src}_{02}<18/1000$. All the coarse endpoint comparisons (RG.61)–(RG.65) are rational inequalities obtained by multiplying positive integer denominators. They require no new numerical reading of the algebraic root.

The two source pivots have inherited lower bound $1/10$. For their upper bounds, (RG.6) and (RG.61) give

$$
\begin{aligned}
(S_{02}^{\rm src})_{00}
 &=\lambda_{\rm src}/2-[(A_5^{\rm src})_{00}+(A_{27}^{\rm src})_{00}]/2\\
 &<24/100-(21/100+4/100)/2<3/25,\\
(S_{01}^{\rm src})_{00}
 &<\frac{(48/100-21/100)59-(4/100)37}{128}<3/25.
\end{aligned}
\tag{RG.66}
$$

The second formula uses $p_{51}=59/128$ and $p_{27,1}=37/128$. The positive rank-one adjugate identities imply

$$
\frac ab=\frac{N^{\rm src}_{01}}{(S_{01}^{\rm src})_{00}},\qquad
\frac cd=\frac{N^{\rm src}_{02}}{(S_{02}^{\rm src})_{00}},\qquad
b^2=\eta_1(S_{01}^{\rm src})_{00}>19/1000.
\tag{RG.67}
$$

For example $ab=\eta_1N^{\rm src}_{01}$ and $b^2=\eta_1(S_{01}^{\rm src})_{00}$ give the first ratio; the second follows in the same way from $cd$ and $d^2$. This also exhibits the positive sign of $d$, conditional on the factorization premises.

The bounds on the $H^{\rm src}$ diagonals give, by positive square comparisons,

$$
\begin{gathered}
(7/10)^2<498/970<(h_1/h_0)^2<500/968<(3/4)^2,\\
(4/5)^2<655/970<(h_2/h_0)^2<656/968<(5/6)^2.
\end{gathered}
\tag{RG.68}
$$

Combining the established numerator, pivot and ratio bounds gives

$$
\begin{aligned}
r_T&>\frac{(7/10)(45/1000)}{3/25}=21/80>1/4,&
r_T&<\frac{(3/4)(51/1000)}{1/10}<2/5,\\
r_S&>\frac{(4/5)(16/1000)}{3/25}>1/10,&
r_S&<\frac{(5/6)(18/1000)}{1/10}<1/6.
\end{aligned}
\tag{RG.69}
$$

For $a_y=(u_y,v_y,w_y)^T$ expand the determinant of its three specimen columns:

$$
\det[Da_y,Ta_y,Sa_y]=h_0bd\,u_y
 [u_y^2-r_Tv_y^2-r_Sw_y^2].
\tag{RG.70}
$$

Here $u_y>0$. Inserting $u_y^2=y/128$, $v_y^2=(64-y)/128$ and $w_y^2=1/2$ gives the sole zero height in (RG.59). The two required comparisons are exactly

$$
48r_T+64r_S>48/4+64/10>16,\qquad
37r_T+64r_S<37(2/5)+64/6<27.
\tag{RG.71}
$$

They are respectively equivalent to $y_{\rm crit}>16$ and $y_{\rm crit}<27$ after multiplication by $1+r_T>0$. Thus none of $5,16,27$ is singular. The three vectors are independent, so their Gram is strictly positive definite. Lemma 8.1 transports this conclusion to all four signs at each height, proving all twelve cases. $\square$

**Lemma 8.3 (all twelve use the saturated spectral branch).** Every original $C(\rho_{y,e,n})$ has $b_0<k$ in Lemma 4.1.

Proof. First record the exact coarse implications needed for the contradiction. From the combined source margin, not the sum of two separate product bounds,

$$
\ell=\frac{ab}{h_0h_1}+\frac{cd}{h_0h_2}
 <\frac{ab+cd}{695/1000}<\frac{18}{695}<\frac1{36}.
\tag{RG.72}
$$

Indeed $2ab\le a^2+b^2$, $2cd\le c^2+d^2$ and (RG.8) give $ab+cd<18/1000$. In particular $\alpha<3/100$. Also $B_y<36/1000$ and

$$
|c_{12}|=ac\sqrt{64-y}/16\le ac/2<9/1000,
\tag{RG.73}
$$

since $2ac\le a^2+c^2<36/1000$.

From (RG.63), (RG.66) and (RG.67), $a/b>3/8$, while $b^2>19/1000>(2/15)^2$. The source diagonal bounds give $h_0>19/20$, $h_1>7/10$. Therefore

$$
\kappa=b(h_0a/b+h_1)
 >\frac2{15}\left[\frac{19}{20}\frac38+\frac7{10}\right]
 =\frac{169}{1200}>\frac7{50}.
\tag{RG.74}
$$

Suppose an original signed Gram had $b_0\ge k$. For its real unit kernel vector $v_0$ with positive $D$ coordinate,

$$
b_0=1-(1+\alpha)v_T^2-(1+\beta)v_S^2\ge1-\ell
\tag{RG.75}
$$

implies $|v_T|,|v_S|<1/6$ and $v_D>5/6$, by (RG.72). PSD of $C-\lambda_0B$ gives $\lambda_0\le c_{00}=A_y<1$ by its $DD$ entry. The latter strict bound follows from the exact normalization: each $h_i^2<1$ and $p_y$ is a strictly positive probability vector.

The $T$ row of $(C-\lambda_0B)v_0=0$ would then imply

$$
|c_{01}|v_D\le(c_{11}+\alpha\lambda_0)|v_T|+|c_{12}||v_S|
 <\frac{36/1000+3/100+9/1000}{6}=\frac1{80}.
\tag{RG.76}
$$

At the three heights the products $y(64-y)$ are $295,768,999$, each exceeding $17^2$. Sign changes preserve the absolute entry $|c_{01}|=\kappa q_y$. Hence (RG.74) gives instead

$$
|c_{01}|v_D>\frac7{50}\frac{17}{128}\frac56
 =\frac{119}{7680}>\frac1{80},
\tag{RG.77}
$$

a contradiction. This proves $b_0<k$ for every sign and every original height, including exclusion of the transition. $\square$

**Theorem 8.4 (exact original catalogue law on one positive interval).** For each unsigned height $y\in\{5,16,27\}$, let $\lambda_y,\mu_y,v_y$ be the unique branch (RG.20), (RG.24)–(RG.26) for $C^{(y)}$. Let $s_y$ be its saturated cap (RG.34), and put

$$
s_{\rm original}=\min\{\sqrt\ell/2,s_5,s_{16},s_{27}\}>0.
\tag{RG.78}
$$

For every original $y,e,n$ and every $0\le s\le s_{\rm original}$, both acquired and supported live high minima are

$$
\mathsf E_s(\rho_{y,e,n})=k\lambda_y-\mu_y.
\tag{RG.79}
$$

Each selected minimum has its own common unknown-input instrument with at most fourteen actual branches and all properties in Theorem 6.2. All the constants in (RG.78)–(RG.79) are algebraic under the supplied algebraic premises.

Proof. Lemmas 8.1–8.3 establish the real PD domain and saturated branch for all twelve actual states. Since $C_g$ is real orthogonal and commutes with $B$, the eigenvalues, $\lambda_y$ and $\mu_y$ are unchanged under signs, and its positive-$D$ kernel is $v_{y,e,n}=C_gv_y$.

To verify a common cap rather than assume it, substitute the signs into (RG.33). With $U=U_{e,n}$ this gives

$$
J_{C_gv}=en\,C_gJ_vC_g,\qquad
\tau_{C_gv}=en\,\tau_v,\qquad
W_{C_gv}=en\,UW_vU^\dagger.
\tag{RG.80}
$$

The first identity follows entry by entry: $v_T$ gains $en$, $v_S$ gains $e$, and $R_v$ is unchanged. The second follows because coefficient diagonals are unchanged by $C_g$ congruence. For the third use $\Theta(C_gZC_g)=U\Theta(Z)U^\dagger$ and $UX_{01}U^\dagger=enX_{01}$. Likewise $Q_{C_gv}=C_gQ_vC_g$. Thus $|\tau|$, $\|J+\tau Q_c\|$ and the normalized failure-block norm are invariant; $M_2$ commutes with the signed specimen block. The same cap works at all four signs of one height.

Each $s_y$ is strictly positive by Lemma 5.2, so their finite minimum with $\sqrt\ell/2$ is positive and strictly below $\sqrt\ell$. Theorem 6.3 proves (RG.79) for every stated strength, including the closed cap endpoints. Algebraicity follows from Section 6 and the exact source definition. The cap is sufficient; its maximality has not been proved. Equality of the four separately optimized values at one height does not combine their designs into a simultaneous four-input or twelve-input minimizer. $\square$

## 9. Selected-coordinate Pareto vectors beyond every sharp-mean face

**Definition 9.1 (the achieved full resource vectors).** Fix one selected original history $h=(y,e,n)$ and write $v_h=C_gv_y$. For every original $h'=(z,\epsilon,\eta)$ define

$$
V^h_{h'}=\operatorname{tr}(\Theta(v_hv_h^T)\rho_{h'})
 =\|K(v_h)U_{\epsilon,\eta}a_z\|^2.
\tag{RG.81}
$$

For each $0\le s\le s_{\rm original}$, the saturated construction selected by $h$ has exactly this entire twelve-vector of acquired high masses. Its aggregate effect does not change with $s$; only its binary split changes. Each coordinate is the cost of the same common design on that history, without a source prior. Different choices of $h$ are not asserted to yield distinct vectors.

**Theorem 9.2 (coordinatewise least vector among selected minimizers and full-class Pareto status).** At any strength in (RG.78), $V^h$ is coordinatewise least among resource vectors of all original implementations attaining the minimum in coordinate $h$. It is the unique Pareto vector on that minimum-coordinate hyperplane and is globally Pareto against the entire finite complex class of Definition 2.3.

Proof. Theorem 8.4 gives the universal selected minimum $F_y=k\lambda_y-\mu_y$, and the constructed vector has $V^h_h=F_y$. Any original acquired minimizer in that coordinate must have equality in acquired $\ge$ live $\ge F_y$. By Theorem 4.4 its aggregate supported live high coefficient is uniquely $v_hv_h^T$. The full five-mode operator inequality (RG.18) then gives

$$
G_H^{\rm acq}\succeq E\Theta(v_hv_h^T)E^\dagger.
\tag{RG.82}
$$

Taking each original positive-state expectation makes every coordinate at least $V^h$. Since the constructed vector attains these lower values simultaneously, it is least in the selected-minimizer set. Any larger vector in that set is dominated by it; hence it is its only Pareto vector.

If an arbitrary original design weakly lowered every coordinate of $V^h$, its selected coordinate could not fall below $F_y$ and so would still be minimal. Inequality (RG.82) would then forbid any strict decrease in another coordinate. This proves global Pareto status. On the selected pure state a positive acquired-to-live slack need only have expectation zero, and it can raise other coordinates. Thus this proof does not identify all selected-minimizer resource vectors with $V^h$ or identify their entire instruments. $\square$

**Theorem 9.3 (strict selected improvement and strict separation from all three known faces).** For every selected $h=(y,e,n)$,

$$
V^h_h=F_y<kA_y.
\tag{RG.83}
$$

For every original height $z\in\{5,16,27\}$, the four-sign mean of $V^h$ strictly exceeds the known sharp value $g_z(s)=kA_z$ throughout $0\le s\le s_{\rm original}$. Thus these achieved Pareto vectors lie outside all three sharp-average equality faces.

Proof. The signed selected Gram has $c_{01}=en\kappa q_y\ne0$. In the necessary matrix relaxation (RG.18), consider real $x$ close to zero and

$$
z(x)=(1,x,0)^T,\qquad
H(x)=\frac{k\,z(x)z(x)^T}{1-\alpha x^2}.
\tag{RG.84}
$$

Its denominator is positive for sufficiently small $x$, its $B$ trace is $k$, and $H(x)\preceq I$ exactly when

$$
\frac{k(1+x^2)}{1-\alpha x^2}\le1
\quad\Longleftrightarrow\quad (k+\alpha)x^2\le\ell.
\tag{RG.85}
$$

Its relaxed objective is

$$
\operatorname{tr}(CH(x))=
 \frac{k(c_{00}+2c_{01}x+c_{11}x^2)}{1-\alpha x^2},
\qquad \left.\frac d{dx}\operatorname{tr}(CH(x))\right|_{x=0}=2kc_{01}\ne0.
\tag{RG.86}
$$

A sufficiently small opposite-signed $x$ strictly improves on $kc_{00}=kA_y$. Theorem 4.4 identifies $F(C)$ with the exact optimum of that relaxation, so $F_y<kA_y$. Theorem 6.3 independently realizes this same value in the original class, including at $s=0$ and throughout the common interval. The comparison did not assume that each relaxed trial $H(x)$ itself has a record-feasible implementation.

For the second assertion, average (RG.81) over the four signs at height $z$. The average input is $\operatorname{diag}p_z$, so cross terms of $D,T,S$ have zero trace against it. Since $v_h$ is unit and $v_h^TBv_h=k$,

$$
\begin{aligned}
\frac14\sum_{\epsilon,\eta}V^h_{z,\epsilon,\eta}
 &=A_zv_D^2+B_zv_T^2+C_zv_S^2\\
 &=kA_z+(\alpha A_z+B_z)v_T^2+(\beta A_z+C_z)v_S^2
 >kA_z.
\end{aligned}
\tag{RG.87}
$$

All $A_z,B_z,C_z$ are positive. Equation (RG.36) says $v_T,v_S$ are not both zero, proving strictness at all three heights. Since $s_{\rm original}<\sqrt\ell$, (RG.56) gives $g_z(s)=kA_z$ on this entire interval. The old common diagonal vector has coordinate $kA_y$ at the selected history, while the new one strictly improves it and raises all three means above their sharp values. Together with Theorem 9.2 this proves the claimed additional Pareto points beyond that known face. It classifies neither a region nor the remaining frontier. $\square$

## 10. Boundaries, degeneracies and the continuing mathematical target

**Convention 10.1 (domain and endpoint distinctions).** The cases $b_0>k$, $b_0=k$ and $b_0<k$ have separate lift rules. The transition has $\mu=0$, $t=1$ and uses (RG.35). The strict top-derivative argument is used only when $b_0<k$; a decoupled $D$ instead has $b_0=1$. Repeated negative eigenvalues and $\alpha=\beta$ do not affect the simple nonnegative eigenbranch. Every kernel has a nonzero $D$ coordinate. Either of $v_T,v_S$ may vanish individually in the saturated formulas, but (RG.36) prevents both vanishing. Real low matrices of every rank, including zero, have the decomposition in Lemma 6.1.

All cap constraints are non-strict and include their stated endpoints. A zero norm denominator imposes no constraint; no expression divides by it. Vanishing high weights, low atoms or failure eigenvalues remove actual branches. At $s=0$ the required binary record is fair, but finer generated labels can depend on the input. Changing the sign of the record coefficient just exchanges reports. This new evaluation makes no $s=1$ assertion; the existing endpoint laws retain their own scope.

Subnormalized inputs use their unnormalized compression and obey positive homogeneity. A singular specimen with real PD Gram, including every original pure specimen, is covered exactly. A positive input with zero compression has zero high minimum using the credited common supported-live constructions and scalar complementary failure action; it is not inserted into the PD formula or normalized. The full constructed maps handle all complex input matrices, complement and cross-support blocks and passive references regardless of whether a particular test matrix has a real PD Gram. General nonreal and singular Grams are outside the new evaluated domain; their known special or endpoint cases are not replaced by a purported general limit theorem.

**Definition 10.2 (the original goal that remains open).** For the same original experiment and fixed channel, the continuing task is to evaluate $\mathsf E_s(\rho)$ for general positive complex supported inputs, including nonreal and singular coefficient Grams, at general strengths $s\in[0,1]$; to determine every original individual-history law beyond (RG.78), subject to the already known endpoint results; and to classify the entire original twelve-coordinate undominated frontier with actual common implementations. The maximal plateau endpoints are not supplied by the sufficient caps. The spectral necessary bound remains valid at other strengths for real PD Grams, but the present lifts do not prove equality there.

This continuing task keeps the full complex plane-plus-quadratic cone, its plane slack, arbitrary finite complex common encoders, arbitrary full TP decoders, all finite generated refinements and the entire jointly counted future quantum payload. A real, covariant, diagonal, JR-conditioned, pure-encoder or isometric-decoder subfamily can give upper constructions; it cannot replace the original lower-bound class. No general real-minimizer normal form or scalar trace sufficiency has been proved. The compact reduction, spectral cone lift and existence of finite minimizers are not evaluated general complex formulas.

The additional Pareto results identify a finite family of achieved selected-coordinate points and the unique Pareto vector within each selected minimum-coordinate hyperplane. Possible coincidences across selections, other vectors on those hyperplanes, other frontier faces and the remaining undominated boundary are not classified. Separate common pointwise attainers retain the quantifier $\forall\rho\,\exists\mathfrak F_\rho$, with public constants chosen before execution and common maps on unknown inputs. No simultaneous all-history minimizer follows.

## 11. Mathematical credits and distinct resource carriers

**Convention 11.1 (roles of the supplied results).** The source-specific additional content is the evaluated real-PD spectral law with its two exact branches and certificate, both positive-strength lifts, its fourteen-branch full realizations, the original-history interval and the selected-coordinate Pareto conclusions. The following attributions fix their boundary relative to the supplied sources.

| Source | Credited content and scope |
| --- | --- |
| CG Sections 1–7 and 13–28 | The common preparation, twelve reached-cut histories, original control and complete-output task; conditional source root, isolation, enclosures, exact channel and minimax benchmark; averaged-live rigidity, the restricted Schur obstruction, jointly counted acquisition/Schmidt bottlenecks and nonsharp stability/resource penalties. Averaged-live rigidity is not whole-channel uniqueness or an exhaustive native operation menu. |
| Full current JR Sections 34–40 | Positivity and parameter bounds including the combined $\ell$ margin; exact diagonal/common-attainer/three-average/worst-history laws under (RG.54). Its broader all-error-optimizer and specified countable/integral scope is retained, with no inference fixing each optimizer's complete channel or failure-time split. |
| RE | Evaluated fixed-channel endpoint envelope, complete endpoint attainers and the distinction between separate pointwise minima and common paired attainability. Earlier interior constructions are upper constructions in the interior. |
| Integrated IR companion | Interior live-map freedom, lawful perturbations, nonleast and no-simultaneous-minimum statements within their stated ranges, and the full complex compact coefficient reduction with thirty actual branches. Its diagonal package uses the current JR credit above. |
| CA, *Native complex atomic cone and optimal resource faces*, Sections 3–8 | Full complex singular-cone spectral lift with plane slack, four quadratic plus two plane atoms, six-atom bound, exact real trace-zero face, complex trace counterexample and dual separator, twenty-four general branches, and complete singleton/exceptional-segment sharp-average equality vectors. Its mathematical content is reused here. |
| The supplied small-record proposal and independent assessments | The candidate spectral/lift/original-history/Pareto arguments developed and proved here. Their conclusions are assessed by the displayed proofs, without using any approval as mathematical authority. |

The current JR correspondence is exact, not a claim of new diagonal knowledge from a relabeling. The integrated IR companion retains its original-class reduction and its explicit credit to the full current JR. Mathematical content, hypotheses and quantified conclusions determine these attributions.

Finite Choi/Kraus support, rank bottlenecks, real spectral decomposition, eigenvalue differentiation, adjugate identities, Takagi congruence, zero-Rayleigh decomposition, triangle inequalities, Cauchy–Schwarz and finite-dimensional compactness are mature tools. Their use in this particular carrier is a source-specific deduction, not an invention of those tools. The ordinary zero-Rayleigh proof in Section 6 adapts the already supplied real-face argument; the new branch count uses its three-atom bound together with the new rank-one aggregate high matrix, rather than claiming a better general complex-cone atom theorem.

**Convention 11.2 (supplied literature, with conditional external scope).** The external antecedents below are credited as supplied in CG, JR, RE, IR and CA. Their external texts, versions and priority are not independently authenticated in this volume. None supplies an omitted source-specific proof.

| Supplied reference | Relevant antecedent and boundary |
| --- | --- |
| Heinosaari–Jivulescu–Reeb–Wolf, *Extending quantum operations*, arXiv:1205.0641v3, Sections 2.1 and 6.1 | CP/TP and Choi/Kraus framework. A stated at-most-qubit compatibility condition is not a qutrit or continuous-time realization theorem. |
| Terhal–Horodecki, *A Schmidt number for density matrices*, quant-ph/9911117v4; Chruściński–Kossakowski, *On partially entanglement breaking channels*, quant-ph/0511244v1 | Rank-constrained Choi decomposition antecedents. The present rank restriction comes from the entire actual joint fibre. |
| Sekatski, *The bottleneck dimension of quantum operations*, arXiv:2608.25010v1, Section II.A | Classical-assisted bottleneck language, with acquired unnormalized mass and TNI supported live maps explicit here. No capacity law follows. |
| Muñoz-Moller–Leppäjärvi–Heinosaari, *Adversarial Information Gain in Non-ideal Quantum Measurements*, arXiv:2602.20941v1, Definition 1 and Proposition 1 | Joint-operation antecedents; the exact live and separately labelled failure identities are proved above. |
| Leppäjärvi–Sedlák, *Incompatibility of quantum instruments*, arXiv:2212.11225v2, Definition 8, Remark 3 and Proposition 7 | Finite postprocessing and dilation antecedents; an inaccessible port is not an acquired flag, and a continuous measure requires its own full identity. |
| Nechita–Park, *Random covariant quantum channels*, arXiv:2403.03667v2, Section 5; de Vicente–Streltsov, *The power of the resource theory of genuine quantum coherence*, arXiv:1604.08031v2, Section II.2 | Covariance and the zero-transfer Schur subclass. Analytic averaging grants no physical sign operation and no exhaustive native Schur restriction. |

These references delineate inherited methods; they support no literature-absence or worldwide novelty claim for the additional law. Nested library, source-proof, preparation, control, calibration and instrument antecedents remain conditional.

**Convention 11.3 (the classical acquisition-resources comparison).** The supplied [*k-bonacci Self-Calibrating Acquisition Resources, Continuation XXII*, Sections 363–367][XXII] concerns a classical Fibonacci-window divisibility source, source-independent common-seed catalogues, preselected or stopped schedules with at most two paid requests, and selected marked targets in total variation. It supplies complete-law separation, canonical non-domination and fibre-averaging obstructions. Its same-cap stopped survivors $p_*$ or $q^*$ remain; the stated law separations are not strict same-profile target-risk separations. Its unrestricted joint-selection and original nonatomic-target obligations remain separate.

The supplied [*Actual support incidence and the exact count relaxation in native threshold preparation*, Sections 1–12][SI] has a different source again: finite ordered alpha/beta trees, a homomorphic expansion, a complete current row and the unbounded original inverse fibre. Its target is a fixed pointwise threshold code, literal original latches and complete predecessor entries. Its Boolean graph has one changing installed state, fixed coordinate labels and fixed successors; it pays all installed states and every actual query/letter, including constants, repeats and post-certificate visits, at simultaneous caps $n,W$. Its native transfer is $\mathsf N(H,p,\ell)\leftrightarrow\mathsf B(H-4-r,p-1,\ell-3)$ with the complete full-fibre lift, not a quantum carrier correspondence.

In that carrier, SI proves actual support/host incidence, singleton and short-gap rigidity, exact count relaxation $2n-2$ and a budget-feasible false-output graph, common-support localization, compensation through span four and right-cut exclusions. Its later all-history weights and both-directed-conflict set-pairs capacity give a qualified exact grid minimum $k(n-k+1)$, while overload examples retain global compensation. Section 12's proper prefix-hit switch between two block-swapped live orders yields an actual-host injection without imposing an order after certification; its complete overload family is above-grid, not a saving. The unrestricted collective compensation inequality, equivalently SI.59 or SI.83, and unrestricted-budget minimum remain open under their stated parameters. Its literal entries, original full fibre, separately priced eight-state whole-row reader, acquisition/binding/permission/export/handoff services and distinct installed-state versus physical-memory costs all remain in their own model.

The comparison is at the level of retaining actual implementations, common objects, faithful quantifiers and the direction of lower/upper implications. Neither XXII nor SI identifies its source with (RG.2), its paid-query or installed-state count with acquired dimension-at-least-three mass, or its terminal laws with the reference-preserving labelled-time CP channel (RG.9). No proved map preserving those objects, operations, target error and resources is supplied. Thus no scalar cap, state count, capacity or native implementation is transferred into the quantum coefficient cone. The current law uses none of their distinct-carrier theorems as a premise.

## 12. Native acquisition, physical timing and completion limits

**Convention 12.1 (native unknown-specimen obligations).** The encoders and decoders in Theorem 6.2 are actual finite mathematical CP/TP instrument specifications with stated generated labels and jointly counted fibres. Their mathematical existence does not install native access to the original unknown specimen. A native realization must lawfully acquire those flags and payload from the sole specimen at the old cut, preserve coherence in the whole future-accessible carrier, and enact the controlled range or live decoder under the original calibrated operations, permissions, controller state and aligned clock. No second specimen, hidden share, history-conditioned helper, accessible discarded system, extra acquisition interval or free entanglement share is granted.

The original noncommuting probability–phase fields describe their own stated control actions. The supplied `OriginalControlComposition.OriginalControl` is a strict-domain regularity and chronological-path predicate; it does not synthesize an unknown-input acquisition, a coherent store, a sign gate or a controlled decoder. An abstract dilation, rank factorization, geometric reachability or equal effect does not create an accessible native port. Conversely failure of those particular suppliers to install a mechanism is not a proof that every lawful native mechanism is impossible. The original task retains its full operation question, rather than an assumed exhaustive Schur menu.

**Convention 12.2 (the operational exact-time obligation).** A mathematical decoder's CP time measure is a full output law, but a native execution must enact the actual first absorbing failure at elapsed time $t$, absolute time $6+t$. On a failed branch it must perform no later positive-carrier action. A live branch must deliver its specified output at elapsed time one. A scalar flag destined for later failure, or a sampled timestamp written only at the end, does not itself provide this event and timing service. Exact CP measures do not establish finite exact-clock storage or the required time hardware.

The original two side labels remain separate and the two named zero sectors remain zero. Every old stopped archive stays in its branch. Source and epoch identity, calibrations, metadata, permissions, controller updates and clock alignment retain their contracts. Complement, cross-support, reference, live and each labelled-time identity must be met together. Old reach masses are never divided out; there is no new acceptance or survival conditioning.

**Convention 12.3 (the precise extent of the result).** The additional law is a conditional ordinary-proof evaluation on (RG.16) and its explicit sufficient caps, with all twelve original histories on the common interval (RG.78), at most fourteen actual mathematical branches, and achieved full-class Pareto vectors (RG.81). The source root, arithmetic enclosures, Jacobian, minimax proof and nested antecedents are not newly authenticated. The result claims no native feasibility, efficiency or impossibility, no quantum capacity, generic neural-network or empirical machine-learning theorem, no Lean/kernel/frozen declaration and no completion of the original programme.

The unresolved targets of Definition 10.2 remain the original general complex/all-strength laws, the later original-history minima, the rest of the full frontier and any maximal plateau description. Native lawful acquisition, actual flags, coherent retention, controlled decoding and operational exact-time stopping remain the obligations of Conventions 12.1–12.2. Neither a bounded mathematical evaluation nor a finite branch count shrinks those continuing tasks.

[CG]: FIB_NATIVE_COMPLETE_CONTINUATION_DISTINGUISHABILITY_GAP.md
[JR]: FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md
[RE]: FIB_NATIVE_FIXED_CHANNEL_RECORD_RESOURCE_ENVELOPE.md
[IR]: FIB_NATIVE_INTERIOR_RECORD_RESOURCE_REDUCTION.md
[SI]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SUPPORT_INCIDENCE_AND_COUNT_RELAXATION.md
[XXII]: KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XXII.md

## 追加锚（本行以下为增补区）
