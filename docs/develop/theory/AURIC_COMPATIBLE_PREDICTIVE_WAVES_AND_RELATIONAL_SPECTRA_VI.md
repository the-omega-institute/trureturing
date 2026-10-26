# AURIC 相容预测波与关系谱 VI：完整原生记录的固定误差与有限经典记忆

## 72. 原对象、完整联合分布与比较域

**定义 72.1（原空间及忠实来源）。** 本卷接续[第一卷](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md) §35、[第二卷](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_II.md) §§39–42 及[第五卷](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_V.md) §§54–57。以下复述供应对象以固定参数对应；原通道约化、严格点及其提升不是本卷新增结果。全部向量为列，$\dagger$ 为共轭转置，正性指全部复 Hermitian 矩阵的正性。

物理空间为 $H=\mathbb C^5$，标准基为 $e_0,\ldots,e_4$。令

$$
\begin{gathered}
u_H=(e_0+e_3)/\sqrt2,\quad v_H=(e_1+e_4)/\sqrt2,\quad z_H=e_2,
\qquad B=(u_H,v_H,z_H),\\
K_0=u_He_0^\dagger+v_He_2^\dagger/\sqrt2+z_He_4^\dagger,
\qquad K_1=u_He_1^\dagger+v_He_2^\dagger/\sqrt2+z_He_3^\dagger,\\
U=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix},\quad
W=\begin{pmatrix}0&1&0\\1&0&0\\0&0&1\end{pmatrix},\quad P_+=(I_3+W)/2,\\
\xi=(1,1,1)^{\mathsf T}/\sqrt3,\quad e=(1,1,-2)^{\mathsf T}/\sqrt6,
\quad f=(1,-1,0)^{\mathsf T}/\sqrt2,\\
q=(\xi+e)/\sqrt2,\quad r=(\xi-e)/\sqrt2,\quad E=qq^\dagger,
\quad P=BEB^\dagger,\\
a=Uq,\quad h_{\rm out}=Ur,\quad g=Uf,\quad
C=(a+h_{\rm out})(a+h_{\rm out})^\dagger=2\xi\xi^\dagger,\\
\ell=(0,1,0)^{\mathsf T},\quad N_\ell=\ell^\perp,\quad
\tau=3-2\sqrt2,\quad c_\ell=(2+\sqrt2)/\sqrt{12},\quad
\ell=c_\ell(h_{\rm out}-\tau a).
\end{gathered}
\tag{72.1}
$$

Fix $0<d<1$, and write $\beta=1-d$, $e_d=(6-5d)/16$. The source is the full complex set

$$
\mathcal K_d=\left\{\rho=A+D:
\begin{array}{l}
 A,D\succeq0,\quad D\ell=0,\quad\operatorname{Tr}\rho=1,\\
 a^\dagger Aa=d,\quad\operatorname{Tr}(C\rho)=d,\quad
 \operatorname{Tr}(E\rho)=e_d
\end{array}\right\}.
\tag{72.2}
$$

The matrices $A,D$ are existential decomposition variables. They are not additional preparation permissions. First-volume Theorem 35.4 supplies the equivalent characterization by the same trace and two moments together with

$$
\rho\succeq0,\qquad s=\rho_{aa}-d\ge0,\qquad
B_d(\rho)=\begin{pmatrix}d&a^\dagger\rho\ell\\
\ell^\dagger\rho a&\ell^\dagger\rho\ell\end{pmatrix}\succeq0.
\tag{72.3}
$$

The original channel domain is $M_3(\mathbb C)\to M_5(\mathbb C)$, with unrestricted output support and Kraus rank. Put $\mathcal G(Y)=\sum_jK_jYK_j^\dagger$, $J_j=(\mathcal G^\dagger)^j(P)$. In the input basis $(q,r,f)$ its original fiber $\mathcal F_{\sqrt d}$ consists of CPTP maps with $T^\dagger(J_j)=Y_j$ at every $j\ge0$, where

$$
\begin{gathered}
Y_0=\operatorname{diag}(1,0,d),\qquad
Y_1=\frac1{16}\begin{pmatrix}1&3&0\\3&9&0\\0&0&6-5d\end{pmatrix},\\
Y_2=\frac1{32}\begin{pmatrix}17&3&0\\3&9&0\\0&0&6+11d\end{pmatrix},\qquad
Y_{j+2}=(Y_j+Y_{j+1})/2\quad(j\ge1).
\end{gathered}
\tag{72.4}
$$

The supplied successor is

$$
S_\rho(X)=B[UP_+XP_+U^\dagger+(f^\dagger Xf)\rho]B^\dagger.
\tag{72.5}
$$

Every $\rho\in\mathcal K_d$ has a lift $T\in\mathcal F_{\sqrt d}$ with $\mathcal GT=S_\rho$. In particular $S_\rho(ff^\dagger)=B\rho B^\dagger$. The parameter $\sqrt d$ indexing this fiber is distinct from the perturbation amplitude $t$ below.

**假设 72.2（实际原生记录与给定的量子模型）。** Fix one known real $\theta$ with $\sin(2\theta)\ne0$. The actual branches on $H$ are

$$
A_0=\cos\theta K_0+\mathrm i\sin\theta K_1,\qquad
A_1=\mathrm i\sin\theta K_0+\cos\theta K_1.
\tag{72.6}
$$

Use exactly the repetition, ready-environment, interaction, measurement and discard contract of second-volume Assumption 39.2. Retain every label and measure $(P,I_5-P)$ at a predetermined finite endpoint. There is no inserted feedback or gate. Distinct endpoints refer to distinct endpoint experiments; they do not require simultaneous terminal measurements on one sample.

For $h=(j_1,\ldots,j_n)$ the leftmost letter acts earliest. All word products have the same convention:

$$
\begin{gathered}
A_h=A_{j_n}\cdots A_{j_1},\quad V_0=Ue^{\mathrm i\theta W},\quad V_1=V_0W,
\quad V_h=V_{j_n}\cdots V_{j_1},\quad M_h=V_h^\dagger EV_h,\\
P_{\rho,n}(h,1)=2^{-n}\operatorname{Tr}(\rho M_h),\qquad
P_{\rho,n}(h,0)=2^{-n}[1-\operatorname{Tr}(\rho M_h)].
\end{gathered}
\tag{72.7}
$$

Empty products are identities, including at $n=0$. These are joint laws on $\Omega_n=\{0,1\}^n\times\{0,1\}$, with both terminal outcomes and every original $2^{-n}$ weight. Complex Hilbert space, Born pairing, CP composition, the specified source and the actual acquisition/control contract are supplied premises. Exact probabilities as mathematical objects do not assert their acquisition from finite samples.

**定义 72.3（任意有限经典比较器及误差）。** A comparator has any finite $k\ge1$, real matrices $T_0,T_1\ge0$, a fixed effect $f_{\rm cl}\in[0,1]^k$, and arbitrary preparation probability columns $p_+,p_-$. Its only transition normalization is

$$
\mathbf1^{\mathsf T}S=\mathbf1^{\mathsf T},\quad S=T_0+T_1,\qquad
Q_{\pm,n}(h,1)=f_{\rm cl}^{\mathsf T}T_hp_\pm,\quad
Q_{\pm,n}(h,0)=(\mathbf1-f_{\rm cl})^{\mathsf T}T_hp_\pm.
\tag{72.8}
$$

Here $T_h=T_{j_n}\cdots T_{j_1}$. Summing over $h,y$ gives $\mathbf1^{\mathsf T}S^np_\pm=1$, so these are probability laws. No individual branch is required to have mass $1/2$, and no preparation is required to be stationary. There is no assumption of fairness, reversibility, covariance, primitivity, irreducibility of $S$, minimality, reachability, observability, or absence of hidden junk. Preparations on the whole $\mathcal K_d$, when requested, may be arbitrary functions $p(\rho)$ without affineness or continuity. The same transition matrices and effect apply to all preparations of a given comparator.

For two laws on $\Omega_n$ set

$$
\operatorname{TV}(P,Q)=\frac12\sum_{h\in\{0,1\}^n}\sum_{y=0}^1|P(h,y)-Q(h,y)|.
\tag{72.9}
$$

Every norm on $\mathbb C^r$ is Euclidean unless specified. On $(\mathbb C^r)^k$ use $\|x\|_{1,2}=\sum_a\|x_a\|_2$ and its induced operator norm; on matrices use the Hilbert–Schmidt norm when treating conjugation as a Hilbert-space operator.

## 73. 原 V55 双世界的严格全参数余量与原五维提升

**定理 73.1（固定原振幅的正余量）。** Take exactly the pair of fifth-volume (55.2)–(55.3), writing its small source parameter as $\eta$:

$$
\begin{gathered}
\eta=d\beta/100,\qquad
\rho_*=
\begin{pmatrix}d+\eta&-\eta&4\eta/\sqrt6\\
-\eta&\eta&0\\4\eta/\sqrt6&0&\beta-2\eta\end{pmatrix}_{(a,h_{\rm out},g)},\\
\Delta=\mathrm i(\xi e^\dagger-e\xi^\dagger),\qquad
t=\frac14\min\{\lambda_{\min}(\rho_*),\lambda_{\min}(B_d(\rho_*))\},
\qquad\rho_\pm=\rho_*\pm t\Delta.
\end{gathered}
\tag{73.1}
$$

Then $\rho_\pm\in\mathcal K_d$ are strictly positive, have the original five-dimensional CPTP lifts, and

$$
\lambda_{\min}(\rho_*)>\eta/2,\qquad
\lambda_{\min}(B_d(\rho_*))>\eta/2,\qquad
\frac t4>\frac{d(1-d)}{3200}>0.
\tag{73.2}
$$

The strengthened margin in (73.2) is the quantitative addition to the supplied strict-pair construction. The amplitude remains the eigenvalue-defined $t$ of (73.1).

证明。In the displayed basis,

$$
C=\begin{pmatrix}1&1&0\\1&1&0\\0&0&0\end{pmatrix},\qquad
E=\frac1{16}\begin{pmatrix}1&3&\sqrt6\\3&9&3\sqrt6\\\sqrt6&3\sqrt6&6\end{pmatrix}.
\tag{73.3}
$$

Thus $\operatorname{Tr}\rho_*=1$, $\operatorname{Tr}(C\rho_*)=d$, $\operatorname{Tr}(E\rho_*)=e_d$, and $(\rho_*)_{aa}-d=\eta$. Since $\eta\le\min(d,\beta)/100$, the last two diagonal entries of $\rho_*-\eta I_3/2$ are $\eta/2>0$ and $\beta-5\eta/2>0$. Eliminating them leaves the Schur complement

$$
d-\frac{3\eta}{2}-\frac{8\eta^2}{3(\beta-5\eta/2)}
>d-\frac{5\eta}{2}>0,
\tag{73.4}
$$

because the subtracted fraction is at most $16\eta^2/(3\beta)\le4\eta/75<\eta$. Hence the first eigenvalue bound holds.

The exact source compression is

$$
B_d(\rho_*)=
\begin{pmatrix}
d&-c_\ell[\tau d+(1+\tau)\eta]\\
-c_\ell[\tau d+(1+\tau)\eta]&c_\ell^2[\tau^2d+(1+\tau)^2\eta]
\end{pmatrix}.
\tag{73.5}
$$

Expansion gives

$$
\begin{aligned}
\operatorname{Tr}B_d(\rho_*)&=(9-2\sqrt2)d/6+4\eta/3,\\
\det B_d(\rho_*)&=2\sqrt2d\eta/3-4\eta^2/3,\\
\det(B_d(\rho_*)-\eta I_2/2)
&=\frac{10\sqrt2-9}{12}d\eta-\frac74\eta^2
>\frac{479}{1200}d\eta>0.
\end{aligned}
\tag{73.6}
$$

The last strict inequality uses $\sqrt2>7/5$ and $\eta/d\le1/100$. The first diagonal entry after subtraction is $d-\eta/2>0$. Sylvester positivity proves the second eigenvalue bound.

The Hermitian $\Delta$ has eigenvalues $-1,0,1$ and is purely imaginary antisymmetric in every real orthonormal basis. Its trace, $C,E$ moments, $aa$ entry and $\ell\ell$ entry vanish. The perturbation of $B_d$ has only off-diagonal entries $\pm t a^\dagger\Delta\ell$, of modulus at most $t$, so its operator norm is at most $t$. Thus $\rho_\pm$ and $B_d(\rho_\pm)$ retain at least three quarters of their respective original positive margins; their trace, moments and $s=\eta$ are unchanged. Equation (72.3) gives full complex membership. The two bounds above imply $t>\eta/8$ and hence (73.2).

Here is the explicit supplier lift, retaining its original-domain interface. For either $\rho=\rho_\pm$, put

$$
L_\rho=\ell^\dagger\rho\ell>0,\quad
A_{\min}=\rho\ell\ell^\dagger\rho/L_\rho,\quad
r_0=a^\dagger A_{\min}a,\quad
\alpha=\frac{d-r_0}{d+\eta-r_0},\quad
A=(1-\alpha)A_{\min}+\alpha\rho,\quad D=\rho-A.
\tag{73.7}
$$

Writing $A_{\min}=\rho^{1/2}\Pi\rho^{1/2}$ for the rank-one orthogonal projection onto $\rho^{1/2}\ell$ shows $0\preceq A_{\min}\preceq\rho$ and $A_{\min}\ell=\rho\ell$. Strict positivity of $B_d(\rho)$ gives $r_0<d$, whereas $\rho_{aa}=d+\eta$. Therefore $0<\alpha<1$, $A,D\succeq0$, $D\ell=0$, $a^\dagger Aa=d$.

Use the actual supplier matrices

$$
D_+=\frac1{\sqrt2}\begin{pmatrix}1&1&0&0&0\\0&0&\sqrt2&0&0\\0&0&0&1&1\end{pmatrix},\qquad
D_-=\frac1{\sqrt2}\begin{pmatrix}1&-1&0&0&0\\0&0&0&0&0\\0&0&0&-1&1\end{pmatrix}.
\tag{73.8}
$$

They satisfy $D_+^\dagger D_++D_-^\dagger D_-=I_5$, $D_+D_+^\dagger=I_3$, $D_-D_-^\dagger=I_3-\ell\ell^\dagger$, and $D_+D_-^\dagger=0$. Consequently $x\mapsto(D_+x,D_-x)$ is a unitary identification $H\to\mathbb C^3\oplus N_\ell$. The original five-dimensional density and channel are

$$
\omega=D_+^\dagger AD_++D_-^\dagger DD_-,\qquad
T_\omega(X)=BP_+XP_+B^\dagger+(f^\dagger Xf)\omega.
\tag{73.9}
$$

If $\omega=\sum_v\lambda_vw_vw_v^\dagger$, a Kraus list is $BP_+$ and $\sqrt{\lambda_v}w_vf^\dagger$; its adjoint squares sum to $P_++ff^\dagger=I_3$. This is CPTP on the full complex input domain.

The identities

$$
\mathcal G(Y)=B(D_+YD_+^\dagger+D_-YD_-^\dagger)B^\dagger,
\qquad D_+B=UP_+,\qquad D_-B=Uff^\dagger
\tag{73.10}
$$

give $\mathcal GT_\omega=S_\rho$ on every complex matrix unit, hence on every input and every finite untouched reference extension.

To fix membership in the original fiber rather than just fit a scalar input, let $H_j=B^\dagger J_jB$ and $F=H_1$. Directly from (72.1),

$$
\begin{gathered}
H_0=E,\quad H_{j+1}=\tfrac12(U^\dagger H_jU+WU^\dagger H_jUW),\quad H_2=(E+F)/2,\\
J_0=D_+^\dagger aa^\dagger D_+,\quad
J_{j+1}=D_+^\dagger H_jD_++D_-^\dagger H_jD_-,\quad
E+2F=3I_3/4+3C/8.
\end{gathered}
\tag{73.11}
$$

These give $\operatorname{Tr}(\omega J_0)=d$, $\operatorname{Tr}(\omega J_1)=e_d$, and $\operatorname{Tr}(\omega J_2)=(6+11d)/32$. Also

$$
T_\omega^\dagger(J_j)=P_+H_jP_++\operatorname{Tr}(\omega J_j)ff^\dagger.
\tag{73.12}
$$

The $(q,r)$ blocks of $H_0,H_1,H_2$ are respectively $\operatorname{diag}(1,0)$, $\bigl(\begin{smallmatrix}1&3\\3&9\end{smallmatrix}\bigr)/16$, and $\bigl(\begin{smallmatrix}17&3\\3&9\end{smallmatrix}\bigr)/32$. There are no cross-$f$ terms in (73.12). Thus the full first three responses are exactly (72.4). Equation (73.11) implies $J_3=(J_1+J_2)/2$; repeated application of $\mathcal G^\dagger$ gives $J_{j+2}=(J_j+J_{j+1})/2$ for all $j\ge1$. All original responses, including complements, follow, so $T_\omega\in\mathcal F_{\sqrt d}$. This is the original lift of V55, reproduced only to make the source substitution explicit. ∎

## 74. 实际二维块、无限群与同一随机词的二阶矩

**定理 74.1（原权重下的有界对比与二阶矩）。** Put

$$
z=e^{-2\mathrm i\theta},\quad
R=\begin{pmatrix}-1/2&\sqrt3/2\\\sqrt3/2&1/2\end{pmatrix},\quad
Z=\operatorname{diag}(1,-1),\quad
B_0=R\operatorname{diag}(1,z),\quad B_1=B_0Z,\quad u=(1,0)^{\mathsf T}.
\tag{74.1}
$$

For chronological $B_h=B_{j_n}\cdots B_{j_1}$ set

$$
b(h)=\Im(u^\dagger B_hu),\qquad a_n=2^{-n}\sum_{|h|=n}b(h)^2.
\tag{74.2}
$$

Then $|b(h)|\le1$, the closed matrix group $G=\overline{\langle B_0,B_1\rangle}\subset U(2)$ is infinite and complex irreducible, and the positive-word semigroup is dense in $G$. For the exact pair (73.1),

$$
\begin{aligned}
P_{+,n}(h,1)-P_{-,n}(h,1)&=2t\,2^{-n}b(h),\\
P_{+,n}(h,0)-P_{-,n}(h,0)&=-2t\,2^{-n}b(h),\\
\lim_{N\to\infty}\frac1N\sum_{n<N}a_n&=\frac14.
\end{aligned}
\tag{74.3}
$$

Here $P_{\pm,n}=P_{\rho_\pm,n}$. The moment uses precisely the target iid word weights, without a Haar-mixing premise.

证明。The supplied time-word bridge can also be read directly from $K_0B=BU/\sqrt2$, $K_1B=BUW/\sqrt2$:

$$
A_jB=BV_j/\sqrt2,\quad A_hB=2^{-n/2}BV_h,\quad
B^\dagger A_h^\dagger PA_hB=2^{-n}M_h,
\quad B^\dagger A_h^\dagger(I_5-P)A_hB=2^{-n}(I_3-M_h).
\tag{74.4}
$$

Thus (72.7) retains both actual outcomes. Their sum at each $h$ is $2^{-n}$, so target labels are iid fair. This establishes no comparator fairness.

In the real orthonormal basis $(\xi,e,f)$, $U=1\oplus R$, $W=\operatorname{diag}(1,1,-1)$, and $E=\frac12\bigl(\begin{smallmatrix}1&1&0\\1&1&0\\0&0&0\end{smallmatrix}\bigr)$. Therefore

$$
e^{-\mathrm i\theta}V_j=1\oplus B_j.
\tag{74.5}
$$

The removed scalar is common to the entire qutrit matrix. A length-$n$ word has scalar $e^{\mathrm in\theta}$, which cancels in conjugation; no relative block phase is removed. The $\xi e$ and $e\xi$ entries of $(1\oplus B_h)^\dagger E(1\oplus B_h)$ are $(B_h)_{11}/2$ and its conjugate. Hence

$$
\operatorname{Tr}(\Delta M_h)=\frac{\mathrm i}{2}\overline{(B_h)_{11}}-\frac{\mathrm i}{2}(B_h)_{11}=b(h).
\tag{74.6}
$$

Unitarity gives the bound on $b$, and $\rho_+-\rho_-=2t\Delta$ proves the two contrast identities with the stated signs and word order.

For the group hypotheses, $B_0^\dagger B_1=Z$. A common invariant complex line would be invariant under $Z$, so would be a coordinate line; both are mixed by the nonzero off-diagonal entries of $B_0$. This proves irreducibility. Infiniteness is the finite-order obstruction already used in V55: $\det B_0=-z$, $\operatorname{Tr}B_0=(z-1)/2$. If $B_0$ had finite order, its eigenvalues would be roots of unity; thus $z$ would be a root of unity and $(z-1)/2$ an algebraic integer. For primitive order $m>2$, all conjugates $(z^a-1)/2$ in $\mathbb Q(z)$ are nonzero and have modulus strictly less than one. Their product would be a nonzero integer of modulus less than one, impossible. Orders one and two are exactly $z=1,-1$, excluded here. Thus $B_0$ has infinite order.

To see positive-word density without acquiring inverse operations, take any generator $A$ and a strictly increasing sequence $m_j$ with $A^{m_j}$ convergent in the compact unitary group. Then $A^{m_{2j}-m_j}\to I$, with $m_{2j}-m_j\to\infty$. Consequently the nonnegative powers $A^{m_{2j}-m_j-1}\to A^{-1}$. The closed positive semigroup contains both inverses and equals $G$.

We use the following elementary finite-dimensional mean-ergodic fact inside the moment calculation and later proofs. If $L$ is power bounded in a finite-dimensional complex normed space, then its Cesàro means converge in operator norm to the projection onto $\ker(I-L)$. In Jordan form, eigenvalues have modulus at most one, and a nontrivial Jordan block at any unit-modulus eigenvalue would make powers grow polynomially, so is excluded. Interior blocks decay; a unit eigenvalue $\lambda\ne1$ has Cesàro multiplier $(1-\lambda^N)/(N(1-\lambda))\to0$; the $1$ blocks survive as identities. This proves the fact without claiming convergence of $L^n$.

For the conjugated moment, consider the Hilbert–Schmidt contraction

$$
\mathscr C(X)=\tfrac12(B_0XB_0^\dagger+B_1XB_1^\dagger).
\tag{74.7}
$$

A fixed $X$ must be fixed by both conjugations: equality of the norm of the average of two equal-norm vectors forces the vectors to coincide, by the squared-norm variance identity. It then commutes with $Z$, hence is diagonal, and commuting with the mixing $B_0$ makes both diagonal entries equal. Thus the fixed space is $\mathbb CI_2$. Trace preservation and the mean-ergodic fact imply that the Cesàro mean of $\mathscr C^n(uu^\dagger)$ tends to $I_2/2$. Consequently

$$
\lim_{N\to\infty}\frac1N\sum_{n<N}2^{-n}\sum_{|h|=n}|u^\dagger B_hu|^2=\frac12.
\tag{74.8}
$$

For the nonconjugated square, restrict

$$
\mathscr A=\tfrac12(B_0\otimes B_0+B_1\otimes B_1)
\tag{74.9}
$$

to $\operatorname{Sym}^2(\mathbb C^2)$. It is again a Hilbert-space contraction. A fixed vector must be fixed by both tensor unitaries, hence by $Z\otimes Z$. Writing $v=(0,1)^{\mathsf T}$, it must be $\alpha u\otimes u+\gamma v\otimes v$. Applying $B_0\otimes B_0$ gives normalized mixed coefficient $\sqrt6(-\alpha+z^2\gamma)/4$. Its vanishing forces $\alpha=z^2\gamma$; the two diagonal coefficients are then both $\alpha$, so fixedness also requires $\gamma=\alpha$. Since $z^2\ne1$, both vanish. Thus $\mathscr A$ has no fixed vector in the symmetric square and its Cesàro powers tend to zero. In particular

$$
\lim_{N\to\infty}\frac1N\sum_{n<N}2^{-n}\sum_{|h|=n}(u^\dagger B_hu)^2=0.
\tag{74.10}
$$

Finally $(\Im w)^2=(|w|^2-\Re w^2)/2$ gives the exact $1/4$ in (74.3). The tensor square describes two moments of the same random word; it introduces no physical two-copy resource. Neither density in $SU(2)$ nor convergence to Haar measure nor phase averaging is assumed. ∎

## 75. 有限常返类上的等号关系与有限陪集覆盖

**引理 75.1（全词语言的有限类不能承载固定向量）。** Let $J$ be any finite nonempty alphabet, $U_j\in U(r)$, and suppose the closed matrix group $G=\overline{\langle U_j:j\in J\rangle}$ is infinite and complex irreducible on $\mathbb C^r$. Let $T_j\ge0$ be $k\times k$ real matrices whose sum $S$ is column stochastic and irreducible. Assume every finite word $w=j_1\cdots j_n$ has a positive labeled path somewhere in this graph: there are vertices $a_0,\ldots,a_n$ with

$$
\prod_{\ell=1}^n(T_{j_\ell})_{a_\ell a_{\ell-1}}>0.
\tag{75.1}
$$

The endpoints may depend on the word. On $(\mathbb C^r)^k$, set $\Lambda=\sum_jT_j\otimes U_j$. Then $\|\Lambda\|_{1,2}\le1$, $\ker(I-\Lambda)=0$, and its Cesàro powers converge to zero in induced operator norm.

证明。Nonnegativity, unitarity and the column sums give

$$
\sum_b\left\|\sum_{a,j}(T_j)_{ba}U_jx_a\right\|_2
\le\sum_{b,a,j}(T_j)_{ba}\|x_a\|_2=\sum_a\|x_a\|_2.
\tag{75.2}
$$

Suppose $\Lambda x=x\ne0$ and put $r_a=\|x_a\|_2$. Then $r\le Sr$ coordinatewise and the sums agree, so $r=Sr$ and every triangle inequality in (75.2) is an equality. A positive $r_a$ exists; the stationary equation propagates positivity along every positive edge, so irreducibility gives $r_a>0$ at every vertex. Normalize $v_a=x_a/r_a$. For each $b$,

$$
v_b=\sum_{a,j}q_{b;a,j}U_jv_a,\quad
q_{b;a,j}=\frac{(T_j)_{ba}r_a}{r_b}\ge0,\quad \sum_{a,j}q_{b;a,j}=1.
\tag{75.3}
$$

The exact Hilbert-space Jensen equality is

$$
\sum_{a,j}q_{b;a,j}\|U_jv_a-v_b\|_2^2
=\sum_{a,j}q_{b;a,j}\|U_jv_a\|_2^2-\|v_b\|_2^2=0.
\tag{75.4}
$$

Thus $U_jv_a=v_b$ on every positive labeled edge, with no residual phase. These stationary norm weights were derived from the putative fixed vector; they are not assumptions on preparation or on label probabilities. The equality concerns the normalized $v_a$, not generally $x_a$.

Along a path for $w$, chronological composition gives $U_wv_{a_0}=v_{a_n}$. Thus the positive-word semigroup lies in the finite union of closed sets

$$
E_{ab}=\{g\in G:gv_a=v_b\}.
\tag{75.5}
$$

The compact-unitary inverse argument in Theorem 74.1 applies to any finite family of unitaries, so the semigroup is dense in $G$. Hence the same finite union covers $G$.

Some nonempty $E_{ab}$ has nonempty relative interior. Indeed, if every closed $E_{ab}$ had empty interior, each complement would be open dense. Successively intersecting these finitely many complements with a nonempty open set remains nonempty, contradicting their cover. Choose $g_0\in E_{ab}$. Then $E_{ab}=g_0H_a$ for the closed stabilizer subgroup $H_a=\{g:gv_a=v_a\}$. Its nonempty interior makes $H_a$ open. The open cosets cover compact $G$, so finitely many suffice; thus its index, and the orbit $O=Gv_a$, are finite.

The complex span of this nonzero orbit is invariant and hence is $\mathbb C^r$ by irreducibility. Every $g\in G$ permutes $O$; if it fixes all of $O$, it fixes a spanning set and is the identity matrix. Therefore $G$ injects into the finite permutation group of $O$, contradicting infiniteness. There is no nonzero fixed vector. The mean-ergodic fact proved within Theorem 74.1 now yields the asserted operator-norm limit. ∎

**定理 75.2（任意有限比较器的固定谱支持）。** For the arbitrary comparator (72.8) and native matrices (74.1), put

$$
\Lambda=T_0\otimes B_0+T_1\otimes B_1.
\tag{75.6}
$$

Decompose the positive graph of $S$ into closed recurrent irreducible classes and transient vertices. Call a recurrent class full-language if its within-class labeled graph permits every finite binary word in the sense of (75.1), and missing-language otherwise. The Cesàro means of $\Lambda$ converge in induced $\|\cdot\|_{1,2}$ operator norm to a projection $\Pi$ with

$$
\operatorname{ran}\Pi=\ker(I-\Lambda)
\subseteq\{x:x\text{ is supported on missing-language recurrent classes}\}.
\tag{75.7}
$$

证明。The contraction (75.2) needs no irreducibility, so applies globally. Every recurrent class is closed under each $T_j$ separately, because escape mass is a sum of nonnegative terms. Its restricted $S$ is column stochastic and irreducible. Theorem 74.1 supplies exactly the infinite complex-irreducible native group needed by Lemma 75.1, which excludes a fixed vector on every full-language class.

For completeness consider the transient restriction $S_D$. From each transient vertex choose a finite positive-probability path into the recurrent union. With finitely many vertices, choose a common length bound $M$ and a positive lower bound $\delta$ on those path probabilities. Once reached, the union is closed, so by time $M$ the absorption probability from every transient vertex is at least $\delta$. Thus

$$
\|S_D^M\|_1\le1-\delta,\quad
\|S_D^n\|_1\le(1-\delta)^{\lfloor n/M\rfloor},\quad
\|\Lambda_D^n\|_{1,2}\le\|S_D^n\|_1\longrightarrow0.
\tag{75.8}
$$

The last inequality follows by expanding internal paths and taking the triangle inequality on their unitary products. If there are no transient vertices this step is empty.

If $\Lambda x=x$, its transient component is fixed by $\Lambda_D$ and hence zero. Different closed recurrent classes have no transitions between them. Each remaining full-language component is then fixed by its own restricted lift and vanishes by Lemma 75.1. This proves the support inclusion. Applying finite-dimensional mean ergodicity to the global contraction proves the projection statement. Its range is supported as claimed even if transient initial data feed a surviving recurrent mode; there is no assertion that its transient input columns vanish.

All peripheral Jordan blocks are semisimple by power boundedness. Other unit-modulus eigenvalues may occur even on full-language classes, but their signed Cesàro means vanish. Neither $\Lambda^n\to\Pi$ nor decay of absolute correlations is asserted. Periodic classes, reducibility, arbitrary initial mixtures and unreachable junk are all included. ∎

## 76. 原生四循环反例与未过滤捷径的失效

**命题 76.1（合法缺词类可以保留未过滤相关）。** The conclusion that every comparator has zero unfiltered signed Cesàro correlation with $b(h)$ is false for the native source. There is a nonexceptional $\theta$ and a legal four-state comparator with $T_1=0$ for which

$$
\lim_{N\to\infty}\frac1N\sum_{n<N}
\left[\mathbb E_{Q_{+,n}}(2y-1)b(h)-\mathbb E_{Q_{-,n}}(2y-1)b(h)\right]=\frac38.
\tag{76.1}
$$

证明。Choose $z=(-3+4\mathrm i)/5=e^{-2\mathrm i\theta}$. Then $\sin(2\theta)\ne0$. The native $B_0$ has eigenvalues $\mathrm i$ and $\mu=(-4-3\mathrm i)/5$. Its unitary spectral expansion at $u$ is

$$
u^\dagger B_0^nu=\frac38\mathrm i^n+\frac58\mu^n.
\tag{76.2}
$$

Indeed the weights sum to one and at $n=1$ give $(B_0)_{11}=-1/2$; distinct eigenvalues determine them. Let $P_4$ send hidden vertex $r$ to $r+1\pmod4$, set $T_0=P_4$, $T_1=0$, and choose

$$
2f_{\rm cl}(r)-1=\sin(\pi r/2),\qquad p_+=e_0,\quad p_-=e_2.
\tag{76.3}
$$

These are legal probabilities and a legal fixed effect. The pair correlation is $2\sin(\pi n/2)b(0^n)$. Since $\mu\ne\pm\mathrm i$, geometric averaging kills the cross frequency, whereas the average of $\sin^2(\pi n/2)$ is $1/2$. Equation (76.2) gives the limit $2(3/8)(1/2)=3/8$.

There is also an exact fixed-vector explanation. With $c=(1,\mathrm i,-1,-\mathrm i)^{\mathsf T}$, $P_4c=-\mathrm ic$. If $B_0v=\mathrm iv$, then $(P_4\otimes B_0)(c\otimes v)=c\otimes v$. This irreducible recurrent class permits only all-zero words and is missing-language. It is therefore allowed, rather than excluded, by Theorem 75.2. A suffix requiring an occurrence of label $1$ kills it exactly, which is the mechanism used below. ∎

## 77. 不条件化的尾窗过滤与精确时间词相关

**定理 77.1（先深度平均、后尾窗极限的过滤）。** Fix any one finite comparator (72.8). For each missing-language recurrent class $C$ choose a nonempty finite word $u_C$ forbidden from every starting vertex of that class. Choose $L\ge1$ at least their lengths, or $L=1$ if there are no such classes. For a fixed $m\ge L$, let $E_{L,m}$ mean that the last $m$ labels contain every length-$L$ binary word as a contiguous subword. For $n\ge m$ define

$$
\begin{gathered}
g_{n;L,m}(h,y)=(2y-1)b(h)\mathbf1_{E_{L,m}}(\text{suffix}_m h),\\
v_{n;L,m}=2^{-n}\sum_{|h|=n}b(h)^2\mathbf1_{E_{L,m}}(\text{suffix}_m h),\\
A_{n;L,m}=\mathbb E_{P_{+,n}}g_{n;L,m}-\mathbb E_{P_{-,n}}g_{n;L,m},\quad
C_{n;L,m}=\mathbb E_{Q_{+,n}}g_{n;L,m}-\mathbb E_{Q_{-,n}}g_{n;L,m}.
\end{gathered}
\tag{77.1}
$$

Set all four quantities to zero at $n<m$. Then $|g_{n;L,m}|\le1$ and, with

$$
\delta_{L,m}=\min\{1,\ 2^L(1-2^{-L})^{\lfloor m/L\rfloor}\},
\tag{77.2}
$$

one has

$$
\begin{gathered}
A_{n;L,m}=4t\,v_{n;L,m},\qquad
\liminf_{N\to\infty}\frac1N\sum_{n<N}v_{n;L,m}\ge\frac14-\delta_{L,m},\\
\lim_{N\to\infty}\frac1N\sum_{n<N}C_{n;L,m}=0,\qquad
\lim_{m\to\infty}\delta_{L,m}=0\quad\text{for fixed }L.
\end{gathered}
\tag{77.3}
$$

The $N$ limits hold for each fixed comparator, $L$ and finite $m$.

证明。Missing-language means failure of (75.1) with endpoints allowed anywhere in the class. Its chosen word is consequently forbidden from every vertex, not merely from one selected start. An occurrence of every length-$L$ word implies an occurrence of every shorter word: extend that shorter word to any length-$L$ word. Thus $E_{L,m}$ requires every $u_C$. The event may be empty for small $m$; the argument still applies.

Under either target, the suffix is iid fair by (74.4), regardless of its correlations with the terminal outcome. For any length-$L$ word $w$, absence everywhere implies absence in $\lfloor m/L\rfloor$ disjoint length-$L$ blocks. Independence on these blocks bounds its probability by $(1-2^{-L})^{\lfloor m/L\rfloor}$. A union bound over the $2^L$ words gives target rejection probability at most $\delta_{L,m}$, uniformly in $n\ge m$ and in the source state. Therefore

$$
v_{n;L,m}\ge a_n-\delta_{L,m}\quad(n\ge m).
\tag{77.4}
$$

The fixed initial depth prefix has no effect on a Cesàro limit, and (74.3) proves the target lower bound in (77.3). For each $h$, the terminal-$1$ contrast times $g$ contributes $2t\,2^{-n}b(h)^2\mathbf1_E$. The terminal-$0$ contrast contributes the same amount because both signs reverse. Thus their sum is exactly $4t\,v_{n;L,m}$.

For the comparator set $a_{\rm cl}=2f_{\rm cl}-\mathbf1$, $p_{\rm diff}=p_+-p_-$, and define the chronological suffix operator

$$
\mathscr R_{L,m}=\sum_{s\in\{0,1\}^m}\mathbf1_{E_{L,m}}(s)(T_s\otimes B_s).
\tag{77.5}
$$

Nonnegative path weights give $\|\mathscr R_{L,m}\|_{1,2}\le1$, since the sum over selected paths has column masses at most those of $S^m$. If a path starts in a missing-language recurrent class, closedness keeps it there. An accepted suffix contains its forbidden word and has zero weight on that class. Hence $\mathscr R_{L,m}$ annihilates every vector supported on these classes, and Theorem 75.2 implies

$$
\mathscr R_{L,m}\Pi=0.
\tag{77.6}
$$

Write $h=(\text{prefix},s)$. Chronology gives $T_h=T_sT_{\rm prefix}$ and $B_h=B_sB_{\rm prefix}$. Summing both comparator outcomes first produces $a_{\rm cl}^{\mathsf T}T_hp_{\rm diff}$. This is real, so the exact transfer identity is

$$
C_{n;L,m}=\Im\left[(a_{\rm cl}^{\mathsf T}\otimes u^\dagger)
\mathscr R_{L,m}\Lambda^{n-m}(p_{\rm diff}\otimes u)\right]
\quad(n\ge m).
\tag{77.7}
$$

Here $\Lambda=T_0\otimes B_0+T_1\otimes B_1$ has no factor $1/2$, and $\mathscr R$ has no extra $2^{-m}$. The comparator weights are its actual $T_h$; the separate target weights remain their actual $2^{-n}$. Expanding the two factors proves (77.7) with the suffix on the left; no reverse or conjugate word is substituted.

For this fixed $m$, mean ergodicity gives

$$
\frac1N\sum_{n=m}^{N-1}\mathscr R_{L,m}\Lambda^{n-m}
\longrightarrow\mathscr R_{L,m}\Pi=0,
\tag{77.8}
$$

where $(N-m)/N\to1$. Equation (77.7) proves the comparator limit. It is the signed scalar mean, not the mean of absolute correlations. The projection may be nonorthogonal and may receive transient input contributions; its range support suffices. This treats every periodic, reducible or transient comparator allowed by (72.8).

The construction uses only bounded classical functions of the acquired full record. All histories remain in the probability law; rejected histories get statistic zero. No event probability is divided out, and no selected physical branch replaces the experiment. One first fixes the comparator and its finite $L$, then fixes any finite $m$, and takes $N\to\infty$. Only after that does one let $m\to\infty$ with $L$ fixed. There is no moving-window substitution in a fixed-operator convergence result. ∎

## 78. 固定正误差的完整记录下界与全终点记忆发散

**定理 78.1（原双世界的固定误差 Cesàro 下界）。** For every fixed $0<d<1$, every fixed real $\theta$ with $\sin(2\theta)\ne0$, the exact original pair (73.1), and every finite comparator (72.8) with arbitrary two preparations,

$$
\liminf_{N\to\infty}\frac1N\sum_{0\le n<N}
\frac{\operatorname{TV}(P_{+,n},Q_{+,n})+
\operatorname{TV}(P_{-,n},Q_{-,n})}{2}
\ \ge\ \frac t4\ >\ \frac{d(1-d)}{3200}.
\tag{78.1}
$$

The same bound holds with the maximum of the two TV errors inside the depth average.

证明。For any real $|g|\le1$ on the complete record, $|\mathbb E_Pg-\mathbb E_Qg|\le2\operatorname{TV}(P,Q)$. Write $d_{\pm,n}=\operatorname{TV}(P_{\pm,n},Q_{\pm,n})$. Apply this to each preparation and the same statistic of Theorem 77.1:

$$
|A_{n;L,m}-C_{n;L,m}|\le2d_{+,n}+2d_{-,n},\qquad
\frac{d_{+,n}+d_{-,n}}2\ge t\,v_{n;L,m}-\frac14C_{n;L,m}.
\tag{78.2}
$$

For fixed comparator, $L,m$, averaging and taking $\liminf_{N\to\infty}$ gives the lower bound $t(1/4-\delta_{L,m})$ by (77.3). The left side is independent of $m$. Taking the supremum of these bounds as $m\to\infty$, with $L$ fixed, gives $t/4$. This does not exchange the two limits. The strict quantitative inequality follows from (73.2), and the maximum dominates the mean of the two errors. Both terminal entries are essential to the factor $4t$ in (77.3); the TV here sums both entries at every actual word. ∎

**定义 78.2（每个预定终点的有限视野精度）。** For $H\in\mathbb N$ and $\epsilon\ge0$, let $k_{\rm pair}(H,\epsilon)$ be the least number of classical states for which one comparator (72.8) satisfies

$$
\max_{0\le n\le H}\max_{\sigma\in\{+,-\}}
\operatorname{TV}(P_{\sigma,n},Q_{\sigma,n})\le\epsilon.
\tag{78.3}
$$

Let $k_{\mathcal K_d}(H,\epsilon)$ be the corresponding least number for one comparator with arbitrary preparations $p(\rho)$ on all $\rho\in\mathcal K_d$, satisfying the same bound uniformly in $\rho$ at every $0\le n\le H$. A nonexistent finite model has minimum $\infty$. Matrices, effect and preparation rule may depend on $H$; within a given horizon they are common across its endpoints and source states. Thus $k_{\mathcal K_d}\ge k_{\rm pair}$.

**定理 78.3（固定小正误差下的经典状态数发散）。** For each fixed $d,\theta$ as above and each fixed

$$
0<\epsilon<d(1-d)/3200,
\tag{78.4}
$$

both $k_{\rm pair}(H,\epsilon)$ and $k_{\mathcal K_d}(H,\epsilon)$ tend to infinity as $H\to\infty$, even when a new comparator is chosen at each horizon.

证明。Fix $k$. Retain only the parameters $(T_0,T_1,f_{\rm cl},p_+,p_-)$. They range over the compact space $X_k$: all entries lie in $[0,1]$, nonnegativity, column stochasticity of $T_0+T_1$, effect inequalities and the two probability-simplex equalities are closed finite-dimensional conditions. For each fixed $n$, every complete-record comparator probability is a polynomial in these parameters. TV is a continuous finite sum of their absolute differences from the fixed target probabilities.

Let $\mathcal C_H\subset X_k$ impose both TV bounds at every $0\le n\le H$. Each is closed and $\mathcal C_{H+1}\subseteq\mathcal C_H$. If comparators with at most $k$ states worked at arbitrarily large horizons, padding smaller models to $k$ states would make every $\mathcal C_H$ nonempty. Padding is legal: append a block with $T_0=I$, $T_1=0$, zero preparation entries and any legal added effect coordinates. It changes neither outcome at any history.

The nested compact sets would have nonempty intersection, giving one finite comparator with both errors at most $\epsilon$ at every depth. Its average pair error is then at most $\epsilon$, contradicting (78.1). Hence for each $k$ there is a finite $H_k$ such that neither minimum is at most $k$ for any $H\ge H_k$. This is exactly divergence. Only the pair of preparations was compactified; there is no need to extract a whole limiting preparation function on $\mathcal K_d$, or to assume it affine or continuous.

The minima are finite at finite $H$ under the permitted arbitrary-preparation convention. For the pair, the two supplier prefix trees in V56 give exact matching. A finite construction for the full set is also available. Let $\mathcal N_H$ be all binary prefixes of length at most $H$, and let a finite hidden assignment $\omega\in\{0,1\}^{\mathcal N_H}$ give one binary output value to each node. States are $(\omega,h)$ with $h\in\mathcal N_H$. At nonleaves, branch $j$ sends $(\omega,h)$ to $(\omega,hj)$ with mass $1/2$; at leaves each branch is a mass-$1/2$ self-loop. The fixed effect is $f_{\rm cl}(\omega,h)=\omega_h$. For each $\rho$, put $x_h(\rho)=\operatorname{Tr}(\rho M_h)$ and prepare only roots, with weights

$$
p_\rho(\omega,\varnothing)
=\prod_{h\in\mathcal N_H}
\begin{cases}x_h(\rho),&\omega_h=1,\\1-x_h(\rho),&\omega_h=0.\end{cases}
\tag{78.5}
$$

These nonnegative weights sum to one and have the required marginal $x_h(\rho)$ at each node. Each chronological prefix still has mass $2^{-|h|}$, giving exactly both entries of (72.7) for every $|h|\le H$. This construction uses $|\mathcal N_H|2^{|\mathcal N_H|}$ states; it is only an existence bound and does not assert an affine encoding or acquisition of any preparation. The construction shows that divergence concerns increasing finite memory, not finite-horizon nonexistence. ∎

## 79. 来源归属与不可外推的数学边界

**定义 79.1（成熟工具的假设与源特定综合）。** The fixed instrument and the original fiber, full complex $\mathcal K_d$, exact V55 pair, its original five-dimensional lift, and the all-endpoints horizon convention are suppliers from the linked volumes. The added content is the quantitative original-pair margin, the actual iid-word second moment, the classwise Jensen/finite-cover obstruction, the suffix filter, and their fixed-error weighted-TV consequence. These form a `repo-derived` source-specific synthesis, without a literature-priority or originality claim. Repeating supplier formulas fixes interfaces and is not counted as reproving them for a new result.

The following primary references supply context for mature realization methods; neither supplies (78.1) as a theorem to be directly applied:

| Primary source | Precise hypotheses and use boundary |
| --- | --- |
| A. Monras and A. Winter, *Quantum learning of classical stochastic processes: The Completely-Positive Realization Problem*, [arXiv:1412.3634v1](https://arxiv.org/html/1412.3634v1), Theorem 6 | `literature-attested`: for a given quasi-realization, positive realization is equivalent to a convex pointed polyhedral cone containing its initial element, invariant under all word maps, with the terminal functional in its dual. All three cone conditions are essential. This is context for exact positive realizations; no approximate full-record TV conclusion is imported. |
| Same primary source, Theorem 9 | `literature-attested`: two quasi-realizations of the same exact stochastic process have isomorphic quotient realizations. This does not identify arbitrary hidden carriers, eliminate hidden junk, or yield stability for approximate record laws. The proof here works on the entire finite comparator instead of imposing a minimal quotient. |
| M. Fanizza, J. Lumbreras and A. Winter, *Quantum theory in finite dimension cannot explain every general process with finite memory*, [arXiv:2209.11225v2](https://arxiv.org/html/2209.11225v2), Theorem 5 and ensuing spectral discussion | `literature-attested`: a qutrit realization is constructed for that paper's specified FRDN process, and nonnegative-matrix peripheral spectra explain its exact classical obstruction. That process, preparation and branch maps are not this native source. An obstruction after rescaling a single rare word does not establish the present weighted-TV floor. |
| Same primary source, Theorem 6 | `literature-attested`: its specified noisy HQMM family has $0\le q<1$, $0<s\le1$, fixed $r\ne0$ and varying $\alpha$; assuming positive realizations exist for every $\alpha$, their maximum dimension has the stated lower bound when $1-q$ is small enough. This is neither a fixed-$\theta$ theorem nor an approximation theorem for unchanged native full-record laws. Its depolarizing-noise parameter is not substituted for $\epsilon$ in (78.4). |

The mean-ergodic fact, Hilbert variance equality, compact-unitary closure, finite coset cover, Schur positivity, algebraic-integer norm obstruction, elementary iid union bound, TV inequality and nested-compact-set passage are used with their complete arguments above. They require no unquoted mixing theorem, fixed-point-algebra theorem, fair comparator, or imported CP embedding.

**定义 79.2（固定误差结论的适用边界）。** Theorem 78.3 fixes $d\in(0,1)$, one nonexceptional angle and $\epsilon$ strictly below the displayed positive threshold before taking $H\to\infty$. It supplies no effective $H_k$, memory growth rate, sharp threshold, equality-threshold classification, or horizon uniform over angles approaching $\sin(2\theta)=0$. At exceptional angles all native $B_h$ are real and $b(h)=0$; the $1/4$ moment fails, consistently with the finite exact constructions in V55 and V57. At $d=0,1$ the prescribed $\eta$ vanishes and this strict pair argument does not apply.

The all-depth accuracy sets in (78.3) are nested. Requiring accuracy only at the single final endpoint $n=H$ gives a different, nonnested problem; no such endpoint-only theorem follows here. The result also gives no finite-sample acquisition theorem or statistical sample bound. It compares exact full probability laws and uses a bounded function of those records, while actual repetition, control, source preparation and access to probabilities retain Assumption 72.2's supplied scope.

The excluded class is finite-state nonnegative hidden-state realizations at a fixed small error uniformly over growing endpoint ranges. It is not classical probability in general: continuous or infinite hidden-state models are outside the exclusion. Memory cost in finite classical states is different from an impossibility of every classical description.

Complex Hilbert space, Born pairing, CP/source/composition structure and the stated environment/acquisition contract remain premises. No conclusion here derives physical quantum principles, verifies an empirical observation, establishes unconditional information conservation, or certifies a Lean/kernel theorem. The original quantum-principle origin, actual acquisition and full original all-$d$ minimax objectives remain unresolved by this conditional source theorem; their statements are not replaced by the fixed-error memory result.

## 追加锚（本行以下为增补区）

## 80. 单制备源、预测记录与可逆经典比较合同

以下研究 [V §§91–99](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_V.md#91-单个原纯制备与固定混合控制的比较合同) 的实际单制备源。§§72–79 的双世界、固定正误差和完整记录 TV 下界保持原适用域；这里不把第二个制备或那条误差阈值带入。所比较的是同一源全部合法时序的两种终端质量，有限数据与全词预测分别定量。

**定义 80.1（原对象与时间顺序）。** 固定 V (91.1) 的参数与对象：

$$
\begin{gathered}
0<d<1,\quad c=d/2,\quad \sin(2\theta)\ne0,\quad
[N,P_\xi]\ne0,\quad N\in U(3),\\
a=Uq,\quad g=Uf,\quad
\psi=\sqrt d\,a+\mathrm i\sqrt{1-d}\,g,\quad
\rho_0=\psi\psi^\dagger,\quad E=qq^\dagger,\\
G_j=\operatorname{Ad}_{V_j},\quad V_j=U\exp(\mathrm i\theta W)W^j\ (j=0,1),\quad
G_N=\operatorname{Ad}_N,\quad A_j=G_j/2,\quad A_N=G_N.
\end{gathered}
\tag{80.1}
$$

$\rho_0$ 是唯一给定的纯制备，$E$ 是唯一给定的秩一是效果。$N$ 始终是同一个已安装的混合酉控制，不是子空间，也不是新生随机标签。对 $w=b_1\cdots b_n$，最左字母最早发生，记

$$
\begin{gathered}
G_w=G_{b_n}\cdots G_{b_1},\quad
k(w)=\#\{t:b_t\in\{0,1\}\},\quad A_w=2^{-k(w)}G_w,\\
q_w=\operatorname{Tr}(EG_w\rho_0),\qquad
p(w,1)=2^{-k(w)}q_w,\quad p(w,0)=2^{-k(w)}(1-q_w).
\end{gathered}
\tag{80.2}
$$

$q_w$ 只作归一化数学坐标；交付的预测仍是原始 $p(w,b)$，没有条件化筛去稀有事件。$0,1$ 是同一次原生仪器的实际结果。固定时序指定哪些位置用仪器、哪些位置用 $N$；同一时序中的其他标签史一并保留，$N$ 的位置不依赖标签值。以所有这种外定时序为域，每个有限字母词均为一个合法历史事件。

此源仍有原五维来源：V 命题 91.3 的 $\mathcal T_0$ 保留完整源矩映射，$\mathcal G\mathcal T_0=S_{\rho_0}$；所给 $N$ 通过 $BNB^\dagger+(I_5-BB^\dagger)$ 延伸。那里关于所有复矩阵和未触动有限参考的恒等式属于原量子实现。本节的经典比较合同只要求 (80.2) 的单系统终端记录，不擅自要求它也实现该参考合同。

**定义 80.2（有限可逆经典比较器）。** 给一个有限集合 $\Omega$、一个固定概率列 $\mu$、一个固定二元效果 $f:\Omega\to[0,1]$，以及三个固定置换 $P_0,P_1,P_N$。全部持续变化的内部记忆与时钟均计入 $\Omega$。同一符号也记相应的概率推前矩阵，置

$$
\begin{gathered}
B_0=\tfrac12P_0,\quad B_1=\tfrac12P_1,\quad B_N=P_N,\qquad
P_w=P_{b_n}\cdots P_{b_1},\\
\widetilde p(w,1)=2^{-k(w)}f^{\mathsf T}P_w\mu,\qquad
\widetilde p(w,0)=2^{-k(w)}(\mathbf1-f)^{\mathsf T}P_w\mu.
\end{gathered}
\tag{80.3}
$$

于是 $B_0+B_1$ 随机、$B_N$ 随机；每个词质量严格为 $2^{-k(w)}$。归一化更新为置换，保持任意概率列的多重集与 Shannon 熵 $-\sum_x\mu_x\log\mu_x$。这里的可逆性是逐个归一化分支的数学性质，不保证标签擦除后的通道、全部测量或连同随机源的闭合动力学可逆。

允许响应 $f$ 非尖锐，且只要求一个 $\mu$；没有从量子制备族到经典概率单纯形的仿射映射。源的 $E^2=E$ 不推出 $f(x)\in\{0,1\}$，源的纯性也不推出所有比较表示都把它编码成极端分布。这两种额外对应都需要独立合同。具体地，把任意下述模型的载体复制为 $\Omega\times\{0,1\}$，三个更新均保留副本位、效果忽略该位，制备取两个原制备副本的等权混合，所有预测便不变而经典制备不再极端。以下有限构造可以取 $\mu$ 为点质量，此时使用非尖锐效果；原空词概率 $q_\varnothing=(6-5d)/16\in(1/16,3/8)$ 已说明“点质量加尖锐效果”不可能匹配该源。

## 81. 每个有限完整记录域的一个共同置换模型

**定理 81.1（有限前缀闭域的可逆完成）。** 设 $D\subseteq\{0,1,N\}^*$ 有限、包含空词且前缀闭。存在一个总状态数 $|D|$ 的定义 80.2 比较器，同时精确匹配所有 $w\in D$ 的两个终端质量；它的一个制备、一个效果和三个全局置换在整个 $D$ 上共同使用。

证明。取 $\Omega=D$、$\mu=\delta_\varnothing$、$f(w)=q_w$。对每个字母 $b$，只在

$$
D_b=\{w\in D:wb\in D\}
\tag{81.1}
$$

上规定 $I_b(w)=wb$。这是同一有限集合中的部分单射。将 $D\setminus D_b$ 与 $D\setminus I_b(D_b)$ 配成任意双射，就把 $I_b$ 补为全局置换 $P_b$。这一有限单射延拓正是 [FIB_SOURCE_COMPLETION_DYNAMICS §15.1、定理 15.2](FIB_SOURCE_COMPLETION_DYNAMICS.md#151-驱动合同与实际可达容量) 中已用的补集配对机制；这里不借用该窗口问题的最小容量结论。

等价的已知上游供应是钉版 mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 的 [Mathlib/Logic/Equiv/Fintype.lean，Equiv.Perm.exists_extending_pair](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Logic/Equiv/Fintype.lean)：其有限索引类型取 $D_b$，两条单射分别为包含和 $w\mapsto wb$，共同余域取 $D$。该声明供应全域置换在这些点上的延拓，不供应此源的概率、状态数最优性或实验资源。

前缀闭性使逐字归纳给 $P_w\delta_\varnothing=\delta_w$ 对所有 $w\in D$ 成立。因此 $f^{\mathsf T}P_w\mu=q_w$；再乘 (80.3) 的原生质量，即得两个终端等式。每个固定仪器时序的所有结果史都在相应完整词域内时，所得就是该时序的完整联合分布，而非逐词各选一个模型。三个补置换在边界之外的行为无需匹配。它们对 $D$ 内任意概率分布仍保持谱与熵；沿实际已知历史，归一化分布为点质量，熵恒为零。∎

**推论 81.2（两个明确的存在上界）。** 对固定有限深度 $L$，取全部三字母词

$$
D_L=\{w:|w|\le L\},\qquad
|D_L|=\sum_{n=0}^L3^n=\frac{3^{L+1}-1}{2}.
\tag{81.2}
$$

一个比较器便匹配所有这些词、所有插入控制时序及其中全部随机标签。$L=12$ 时该存在构造用 $797161$ 个状态。

若只要求覆盖 V 定理 98.1、命题 108.1 的实际四表时序及其完整分支，可取更小的共同完整域

$$
\begin{aligned}
D_{12,2}&=\{w:|w|\le12,\ \#_N(w)\le2\},\\
|D_{12,2}|&=\sum_{n=0}^{12}\sum_{j=0}^{\min(2,n)}
 {n\choose j}2^{n-j}=167935.
\end{aligned}
\tag{81.3}
$$

它仍前缀闭：删去词尾不会增加长度或 $N$ 次数。取出 $j$ 个 $N$ 位置后，其余 $n-j$ 个位置各有两个标签，故该计数覆盖所有相应时序，特别覆盖四表的较短质量行、所有选定是条目以及相同时序的其他结果史。对 $N$ 的部分规定只用 $\#_N(w)<2$ 且后继仍在域内的点；边界也由同一补集法完成。

这两个数都是所写完整域的总状态存在上界，不是最小值，不是四表必需状态数，也不是标量数、样本数或获取成本。$324=36+288$ 仍仅是四张 $9\times9$ 表的位置计数；质量位置是两个终端质量的和。比较器可依赖指定源、$N$ 和 $L$，效果表包含源的精确实数；构造没有说明怎样由有限实验精确获得它们。尤其其量词是

$$
\forall L<\infty\ \exists(\Omega_L,\mu_L,f_L,P_{0,L},P_{1,L},P_{N,L}),
\tag{81.4}
$$

不是存在同一个有限六元组匹配每个 $L$。∎

## 82. 原单制备的全词有限置换障碍

**定理 82.1（没有一个有限可逆比较器匹配全部词）。** 对 (80.1) 的每个允许参数与混合 $N$，不存在定义 80.2 的一个有限比较器精确匹配所有合法词。该结论只用所指定的一个制备和一个效果，允许任意经典 $\mu$ 和非尖锐 $f$。以下反证还适用于只在可达输入上保证同一组置换给归一化后继、并精确匹配原始质量的模型，不需对未访问隐藏输入另假设逐支公平。

证明。V 定理 95.1 给实际三个归一化变换的正词闭包为 $\operatorname{Ad}(PU(3))$，其假设正是 (80.1)，包括 $d=2/3$ 和 $N\xi\perp\xi$。$\rho_0,E$ 均秩一，$PU(3)$ 在纯态射线上传递，故连续函数 $P\mapsto\operatorname{Tr}(EP)$ 在该轨道的值域为 $[0,1]$。于是实际 $\{q_w:w\in\{0,1,N\}^*\}$ 在 $[0,1]$ 稠密。

反之，有限 $\Omega$ 的三个置换生成有限群。对固定 $\mu,f$，$\{f^{\mathsf T}P_w\mu\}$ 只有有限多个值，不能等于该稠密集合。全词原始质量相等因 $2^{-k(w)}>0$ 必给归一化值相等，遂矛盾。闭包这里只检验固定模型的数学后果，不供应闭包中任意门的精确控制权限。∎

**命题 82.2（给定状态上限的有限周期／上下文分离）。** 对每个正整数 $M$，取 $m=M!$。保留 V §93 的九个前缀 $u_i$ 和八个后缀 $h_t$。至少存在一对 $(i,t)$，使

$$
q_{u_i0^m h_t}\ne q_{u_i h_t}.
\tag{82.1}
$$

任意 $|\Omega|\le M$ 的置换比较器却对每一对都满足对应归一化值相等。因此这些有限上下文已排除给定上限的精确模型；最长词不超过 $M!+11$，每词至多一次 $N$。

证明。先核对用到的实际相对相位，而非只看二维块的投影阶。在 $(\xi,e,f)$ 中，V (92.2) 将 $V_0$ 去掉共同标量相位后写成

$$
V'_0=1\oplus B_z,\quad
B_z=\begin{pmatrix}-1/2&\sqrt3z/2\\\sqrt3/2&z/2\end{pmatrix},\quad
z=e^{-2\mathrm i\theta},\quad
\det B_z=-z,\quad\operatorname{Tr}B_z=(z-1)/2.
\tag{82.2}
$$

这里 $z\notin\{1,-1\}$。V (55.7)–(55.8) 的迹／行列式论证适用这些相同不变量：若 $B_z$ 有限阶，则 $z$ 为阶 $r>2$ 的单位根，且 $(z-1)/2$ 为代数整数；它在 $\mathbb Q(z)$ 中所有共轭都非零且模小于一，范数不可能是非零整数。因此 $B_z$ 无限阶。该论证也覆盖非例外有理角。

若 $G_0^m=\mathrm{id}$ 在整个 $Q=\operatorname{Herm}_3$ 上成立，$V_0'^m$ 必为标量矩阵：它与全部 Hermitian 矩阵交换，也就与全部复矩阵交换。第一块恒为一使该标量只能是一，于是 $B_z^m=I_2$，矛盾。所以 $G_0^m-I_Q\ne0$；没有删去单态与双态的相对块相位。

再用原参数域内的两组基。V 定理 92.1–92.2 供应
$r_i=A_{u_i}\rho_0$ 为 $Q$ 的九列基，$|u_i|\le8$，其中仅第九列可含一次 $N$。V (93.9)–(93.10) 供应

$$
\ell_0=\operatorname{Tr},\quad
\ell_t(X)=\operatorname{Tr}(EA_{h_t}X)\ (1\le t\le8),\quad
\det\mathcal E=\frac{6561}{2^{36}}\sin^7(2\theta)\ne0,
\tag{82.3}
$$

且真实迹配对的度量因子为
$J_{\rm tr}=\operatorname{diag}(1,1,1,2,2,2,2,2,2)$，故这九个泛函确为对偶基意义下的独立观察行。把每列乘 $2^{k(u_i)}$、把每个非迹行乘 $2^{|h_t|}$ 不改独立性，于是
$\rho_i=G_{u_i}\rho_0$ 与 $X\mapsto\operatorname{Tr}(EG_{h_t}X)$ 仍给同一满秩检验。

非零线性映射 $G_0^m-I_Q$ 必在某个 $\rho_i$ 上非零，并被某个观察行检出。迹行在该差上恒零，故可选 $t\ge1$。所检出的恰为 (82.1) 的差，时间顺序是先 $u_i$、再 $m$ 个零标签、再 $h_t$。

任意至多 $M$ 点的置换都有各循环长度不超过 $M$，所以 $P_0^{M!}=I$，在同一前后文的归一化值必相等。若用原始质量写，这一必要等式为

$$
\widetilde p(u_i0^m h_t,1)=2^{-m}\widetilde p(u_i h_t,1),
\tag{82.4}
$$

而源至少对一对违反它。补终端差为是终端差的相反数。八个后缀长至多三，故深度界为 $8+m+3$。这最多用九乘八对上下文，未给出其中非零差的统一大小、有效最小见证深度或统计获取程序。∎

(82.1) 是固定 $M$ 下的精确分离；(82.4) 尤其保留了可能极小的原始质量。它没有建立独立于 $M$ 的正噪声阈值、加权 TV 误差地板或状态增长率。§§72–79 对不同双制备合同的定理不能填上这些量化缺口。任意有限观察域仍有定理 81.1 的精确可逆模型，因此无状态上限时不存在由一张有限精确词表排除所有有限置换模型的结论。

## 83. 保留全部离散群恒等式的有限域完成

**定义 83.1（离散变换群的同一性要求）。** 令

$$
\Gamma=\langle G_0,G_1,G_N\rangle\ \le GL(Q)\simeq GL_9(\mathbb R).
\tag{83.1}
$$

这里包括数学逆，是三个实际归一化共轭所生成的离散群；并未安装逆控制。若两个带逆的群词在 $\Gamma$ 中相同，要求其经典置换也相同。这是从 $\Gamma$ 到置换群的同态要求，不要求单射，不要求每个不同变换都保持不同。原生分支的 $1/2$ 质量不属于 $\Gamma$：两个归一化群词相同但原生标签次数不同，其联合质量仍按各自的 $2^{-k(w)}$ 计算。

**定理 83.2（本源的有限商记录模型）。** 对任意有限词集 $D$，存在定义 80.2 的有限比较器，精确匹配 $D$ 的两个终端质量，并在整个经典载体上尊重定义 83.1 的全部群恒等式。

证明。每个 $G_a$ 是九维实空间上的可逆线性映射，三个固定矩阵生成 $\Gamma$。所以它是有限生成实线性群；参数或 $N$ 的矩阵元不必为代数数。应用 Malcev 的“有限生成线性群剩余有限”定理。所用文献是 B. Nica，[Linear groups — Malcev's theorem and Selberg's lemma，arXiv:1306.2385v1](https://arxiv.org/html/1306.2385v1)，引言中的定理及 §3 的证明；该文按任意域陈述 Malcev 定理，实数域满足其假设。此处引用 Nica 的论述，不声称已核读 Malcev 的原始论文。

取有限集合 $S=\{G_w:w\in D\}\cup\{1\}\subseteq\Gamma$。对每个不同的 $s,t\in S$，剩余有限性给一个有限群同态，使 $s^{-1}t$ 的像非单位。取有限多个这样的商的乘积，再取 $\Gamma$ 的像，得到一个有限群 $F$ 及同态

$$
\pi:\Gamma\longrightarrow F,\qquad \pi|_S\ \text{单射}.
\tag{83.2}
$$

若 $S$ 只有一个点，可取平凡群；一般情形不要求 $\pi$ 在整个 $\Gamma$ 上单射。

置 $\Omega=F$、$\mu=\delta_1$，并令 $P_a$ 为左乘 $\pi(G_a)$。按最早标签在左的词约定，$P_w\delta_1=\delta_{\pi(G_w)}$。在 $\pi(S)$ 上定义

$$
f(\pi(s))=\operatorname{Tr}(Es\rho_0),\qquad s\in S,
\tag{83.3}
$$

其余点任取 $[0,1]$ 中的值。$\pi|_S$ 单射保证定义无冲突；$s$ 是某个酉共轭，故这些值合法。由 (80.3) 得所有 $w\in D$ 的原始两终端质量相等。左正则作用是群同态，所以源中任意精确群恒等式在整个 $F$ 上也成立，而不只是沿被测轨道成立。∎

这比任意前缀树补置换多尊重了离散变换关系。$F$ 可依赖整个有限 $D$；剩余有限性在此没有给有效商大小，(81.2)–(81.3) 的树状态数不转移为这个加强合同的上界。有限商可加入额外恒等式；若另要求同态忠实，则无限的 $\Gamma$ 不可能嵌入有限置换群。定理 82.1 也说明每个这样的有限商模型必在某些其他合法词上失配。

群同一性只约束变换的乘法关系。它不要求所有把 $\rho_0$ 送到同一个密度矩阵的不同群元素都给同一个隐藏状态，也不保留群变换之间的实线性或凸线性等式。更没有供应未知制备的混合语义。因而“保持所有群恒等式”不能替换 V 的全族仿射制备前提或后文的未来预测条件。

$\Gamma$ 的离散有限商也没有被证明连续延伸到其紧闭包 $\operatorname{Ad}(PU(3))$。事实上，若要求整个连通 $PU(3)$ 连续作用于有限离散集，所得到有限离散置换群的连续同态只能是平凡的。定理 83.2 不作这种要求；它保留离散精确关系，不把紧闭包的拓扑、极限或连续控制一并保留。

## 84. 用未来不可见关系替代整个隐藏载体的维数上限

**定义 84.1（可达空间与未来零观察子空间）。** 容许竞争者的实线性载体 $V$ 为任意维；$s_0\in V$ 是一个制备，$B_0,B_1,B_N$ 是三个固定线性映射，$u,e$ 是质量和是效果泛函。若另给正锥，要求这些对象在合法状态上给非负两终端质量，$B_0+B_1$ 与 $B_N$ 保持质量；下面的线性结论不从中假设复 Hilbert 结构。记

$$
\begin{aligned}
\mathscr R&=\operatorname{span}_{\mathbb R}\{B_ws_0:w\in\{0,1,N\}^*\},\\
\mathscr N&=\{x\in\mathscr R:
 u(B_vx)=e(B_vx)=0\ \text{对每个合法有限后缀 }v\}.
\end{aligned}
\tag{84.1}
$$

$\mathscr N$ 是子空间，且对每个 $B_a$ 不变：检验 $B_ax$ 的后缀 $v$ 就是检验 $x$ 的后缀 $av$，因为 $B_{av}=B_vB_a$。补效果 $u-e$ 自动为零。$\mathscr R/\mathscr N$ 称可达预测商；这里的零是所有合法未来都看不见，而非隐藏向量相等。

沿用 V §93 的 $u_1=\varnothing,u_2,\ldots,u_9$ 与
$(h_1,\ldots,h_8)=(\varnothing,0,1,00,10,000,010,100)$。定义

$$
\begin{gathered}
x_i=B_{u_i}s_0,\qquad
X\alpha=\sum_{i=1}^9\alpha_i x_i,\qquad
R\alpha=\sum_{i=1}^9\alpha_i r_i,\\
Cx=(u(x),e(B_{h_1}x),\ldots,e(B_{h_8}x))^{\mathsf T},\\
\mathcal L Y=(\operatorname{Tr}Y,
 \operatorname{Tr}(EA_{h_1}Y),\ldots,
 \operatorname{Tr}(EA_{h_8}Y))^{\mathsf T}.
\end{gathered}
\tag{84.2}
$$

$R:\mathbb R^9\to Q$、$\mathcal L:Q\to\mathbb R^9$ 均可逆；$C$ 定义在 $\mathscr R$，不是预先给定的量子坐标。第零行是无后缀质量，第一个非迹行才是无后缀是概率，两者不可混同。

假设竞争者匹配实际四表，准确地说

$$
CX=H=\mathcal LR,\qquad
CB_aX=H^a=\mathcal LA_aR\quad(a=0,1,N).
\tag{84.3}
$$

这只使用 $p(u_i h_t,1)$、$p(u_i a h_t,1)$ 及相应无后缀双终端和，仍保留全部原始权重。$H$ 可逆，所以 $C$ 在 $\operatorname{im}X$ 上满秩、$x_i$ 独立；尚未证明它们张成整个 $\mathscr R$ 或预测商。

**定理 84.2（四表加未来不可见条件的全词结论）。** 在 (84.1)–(84.3) 下，以下任一条件都充分，而且两者等价：

$$
\ker(C|_{\mathscr R})\subseteq\mathscr N;
\tag{84.4}
$$

或对三个生成元和九个列，令

$$
K_a=H^{-1}H^a,\qquad
z_{ai}=B_ax_i-XK_a\mathbf e_i,
\quad\text{并要求 }z_{ai}\in\mathscr N\quad\text{对所有 }a,i.
\tag{84.5}
$$

此时可达预测商恰为九维，与源 $Q$ 线性同构；该同构保留初始列、质量、效果和三个带权变换，故所有合法词的两个原始终端质量相等。整个 $V$ 或 $\mathscr R$ 不需有维数上限。

证明。由 (84.1) 的所有未来条件，恒有 $\mathscr N\subseteq\ker C$。先假设 (84.4)，则两者相等，且 $\mathscr N$ 不变。在 $\mathscr R/\mathscr N$ 上，$C$ 诱导单射；由 $CX=H$ 可逆知它又满射到 $\mathbb R^9$。所以商恰九维，$[x_i]$ 为基。

另一方面，四表直接给

$$
Cz_{ai}=H^a\mathbf e_i-HH^{-1}H^a\mathbf e_i=0.
\tag{84.6}
$$

(84.4) 遂蕴含 (84.5)。若只假设 (84.5)，在商中有
$[B_ax_i]=[XK_a\mathbf e_i]$。因为 $x_1=s_0$，逐词归纳使每个 $[B_ws_0]$ 都属于 $[x_i]$ 的跨度，故它们张成整个商。若 $[X\alpha]=0$，用 $C$ 得 $H\alpha=0$，所以 $\alpha=0$；商仍恰九维，$C$ 在商上可逆，从而也得到 (84.4)。

定义 $T:Q\to\mathscr R/\mathscr N$ 为

$$
T(R\alpha)=[X\alpha].
\tag{84.7}
$$

因两边都是基，该映射可逆。$H^a=\mathcal LA_aR$、$H=\mathcal LR$ 给
$K_a=R^{-1}A_aR$，而 (84.5) 给
$\overline B_aT=TA_a$，其中 $\overline B_a$ 是商上的更新。又 $u_1=\varnothing$，故 $T\rho_0=[s_0]$。质量和是效果可下降到商，且由 $CX=\mathcal LR$ 的第零行及 $h_1=\varnothing$ 的行，有
$\overline uT=\operatorname{Tr}$、$\overline eT=\operatorname{Tr}(E\,\cdot)$。

最早字母在左的归纳于是给

$$
\begin{aligned}
\overline B_wT&=TA_w,\\
e(B_ws_0)&=\operatorname{Tr}(EA_w\rho_0)=p(w,1),\\
(u-e)(B_ws_0)&=\operatorname{Tr}((I_3-E)A_w\rho_0)=p(w,0).
\end{aligned}
\tag{84.8}
$$

这也推出全部词质量 $u(B_ws_0)=2^{-k(w)}$，未把竞争者逐支公平性作为额外前提。证明对无限维 $V$ 只用有限线性组合和一个代数商，不用隐藏载体的紧性或谱理论。∎

**命题 84.3（两种坐标与有限数据的真实边界）。** 在定理 84.2 的条件下，前缀基的系数坐标按 $K_a=H^{-1}H^a$ 更新；实际九个观察值的列坐标 $y=Cx$ 则按

$$
y\longmapsto H^aH^{-1}y,\qquad y_0=H\mathbf e_1.
\tag{84.9}
$$

证明。若商类 $[x]=[X\alpha]$，则 $y=H\alpha$，后继观察列为 $H^a\alpha$。因此有 (84.9)。不能把 $H^{-1}H^a$ 直接当成观察列的更新矩阵；词复合仍须以后发生的矩阵左乘。∎

四表自身只给 (84.6) 的当前九行零值，没有给 $u(B_vz_{ai})=e(B_vz_{ai})=0$ 对全部未来成立。条件 (84.5) 虽只有二十七个生成元／列关系模板，每条仍量化所有合法后缀，并非另有二十七个标量测量就能认证。等价的 (84.4) 说这些九行在可达部分已经未来完备；这是一条操作预测条件，不是由有限表自动获得的事实。

更强的隐藏线性闭合要求 $z_{ai}=0$ 在 $V$ 中成立。它足以推出 (84.5)，但强于未来零观察，不能把后者改写成前者而不披露新前提。类似地，$\mathscr N$ 中的向量可有真实隐藏分量；从商上的可逆性不能推出整个载体上的可逆性。

任取定理 81.1 中覆盖全部四表的有限置换模型。它匹配 (84.3)，却由定理 82.1 不匹配某些更长词，故必违反 (84.4)–(84.5)。这直接表明即使每个归一化隐藏更新保持全部经典概率谱，有限表也不能自行认证未来完备。V §§100–110 的整个实有序载体维数上限与闭锥条件有自己的全域重建结论；这里以未来完备替换的只是全词线性预测接口。九维预测商不把任意整个隐藏正锥认作 $\operatorname{Herm}_3^+$，也不赋予全体隐藏状态 Born、CP 或复合系统结构。

## 85. 无限可逆经典表示与信息守恒的准确层次

**定理 85.1（相同合同下的可数与连续全词表示）。** 去掉隐藏经典载体的有限性后，(80.1) 的源存在全词精确、逐分支可逆的经典表示；其中一个载体可数，另一个载体为连续紧空间。两者都只需一个点质量制备和一个 $[0,1]$ 值效果。

证明。先取定义 83.1 的 $\Gamma$ 为状态集合。有限个生成元及其逆的所有有限词可数，故 $\Gamma$ 可数。取 $\mu=\delta_1$、$P_a:g\mapsto G_ag$，并在全部 $\Gamma$ 上置

$$
f(g)=\operatorname{Tr}(Eg\rho_0).
\tag{85.1}
$$

群中每个元素都是酉共轭，故 $0\le f(g)\le1$。左乘为双射，时间顺序给状态 $G_w$，读数恰为 $q_w$。再令原生分支为 $P_j/2$、控制分支为 $P_N$，便匹配全部原始两终端质量。它同时尊重全部离散群恒等式。对任意可数概率列，双射推前只是重排概率，故 Shannon 熵在允许 $+\infty$ 的意义下不变；实际归一化点质量的熵为零。

连续表示可直接取纯态投影空间

$$
\Omega=\{P\in\operatorname{Herm}_3:P^2=P,\ P\succeq0,\operatorname{Tr}P=1\}
\simeq\mathbb{CP}^2,
\quad\mu=\delta_{\rho_0},\quad f(P)=\operatorname{Tr}(EP).
\tag{85.2}
$$

令 $P_a(P)=U_aPU_a^\dagger$，其中 $U_0=V_0,U_1=V_1,U_N=N$。这些是连续可逆的确定性经典状态变换，$f$ 连续；把经典概率态取为此空间上的 Borel 概率测度，效果按积分延伸，仍给全部 (80.2)。这构成一个有连续 $PU(3)$ 作用的经典概率表示，说明单独补操作连续性也不能排除无限经典载体。这里不为任意连续分布定义不依赖参考测度的微分熵，更不以“可逆”声称该微分熵恒定。∎

(85.2) 使用源的纯态矩阵作为经典点的坐标。它是明确的表示构造，不是不同物理机制已被实现或已被验证的主张。其全概率测度单纯形大于量子态空间，不同测度可以有相同重心及全部后续读数；模型没有把这些隐藏测度认作相同状态。对所有量子混合制备要求一个共同仿射编码，或对一切参考／复合实验要求相同联合统计，都超出这里的单制备合同。

这两个模型也满足定理 84.2 的未来完备条件，而其整个线性载体可无限维。具体取可达测度的有限实线性组合，并以

$$
J\Big(\sum_j\alpha_j\delta_{P_j}\Big)=\sum_j\alpha_jP_j
\tag{85.3}
$$

为连续模型的矩映射；可数模型对应置 $J(\delta_g)=g\rho_0$。两者均有 $JB_a=A_aJ$、$u=\operatorname{Tr}J$、$e=\operatorname{Tr}(EJ)$。源的九行可观察性使 $Cx=0$ 等价于 $Jx=0$，并进而使所有未来读数为零；九个源前缀使 $J$ 的像为 $Q$。所以相同九维预测商、全词一致及可逆信息保留，仍不识别任意整个隐藏载体为量子载体。

**命题 85.2（保留标签、擦除标签与闭合守恒不是同一断言）。** 在定义 80.2 的有限模型中，对一个含 $k$ 次原生仪器的固定时序，令 $W$ 是全部原生标签记录、$X_0\sim\mu$，$X_W=P_WX_0$。则

$$
H(X_W\mid W)=H(\mu),\qquad
H(X_W,W)=H(\mu)+k\log2.
\tag{85.4}
$$

证明。每个标签的质量在每个隐藏输入上都是 $1/2$，故 $W$ 在该时序的 $2^k$ 条记录上均匀且与 $X_0$ 独立。给定 $W=w$，$P_w$ 是置换，条件熵为 $H(\mu)$；熵链式法则即给联合式。将 $X_W,W$ 中的 $W$ 丢弃只留下置换分布的混合，其熵由凹性至少为 $H(\mu)$，但未必相等。∎

因此“给定历史保持谱”有精确内容，也适用于这里的反模型；它没有决定读出 $q_w$，更没有证明含新生随机资源的整个宇宙无条件熵守恒。V 定理 89.1–89.2 对量子条件酉、擦除标签、相干记录等距及去相干记录也已经作了对应区分；等距的数学存在没有授予相干环境访问。不同载体上各自守恒的概率谱或密度谱，更不是它们已经共享同一种物理谱的证明。

“所有量都是预测的量”可在 (84.1) 中精确化：若两个可达状态的差属于 $\mathscr N$，它们对全部合法未来、两个终端均等价；若只在 $\ker C$ 中，则仅已选九行不能区分，未来仍可分离。共同来源固定允许哪些前缀、后缀和组合；确定与不确定既可体现在记录分支，也可体现在同一固定效果的 $[0,1]$ 响应。预测商保存这些可检验关系，隐藏实现仍可不同。把信息保留作为条件建模原则是可行的，但需要明确保留的对象、允许的丢弃以及复合规则，才能继续约束起源问题。

## 86. 本源综合的供应范围与尚缺的取得桥

**定义 86.1（归属与适用域）。** §§80–85 是在实际单制备合同上的 `repo-derived` 条件综合，不主张文献优先权或原创定理资格。源的所有相位、权重、前缀与后缀均取原文；既有供应和应用边界如下。

| 供应 | 这里使用的确切内容与限制 |
| --- | --- |
| V §§55、89、91–99，尤其 (91.1)–(91.10)、(92.2)、(93.1)–(93.10)、定理 95.1 | 原五维提升、实际单纯制备、混合控制、原始双终端权重、九列／九行秩及正词闭包；没有引入全族制备对应或已取得的逆。 |
| V §§100–110 | 同一四表的有序实现重建及其整个载体维数／闭锥前提；本节只复用其时序与资源对应，不把该前提推广成任意维载体的结论。 |
| 本卷 §§72–79 | 不同双制备合同的固定误差记忆结论；不作为本节单制备的噪声下界供应。 |
| FIB_SOURCE_COMPLETION_DYNAMICS §15.1、定理 15.2；上述钉版 mathlib 的 Equiv.Perm.exists_extending_pair | `literature-attested` 的有限部分单射补为置换机制及其仓内应用；不搬用窗口容量最小值，不声称新的 Lean 应用或编译核验。 |
| Nica，arXiv:1306.2385v1，引言及 §3 | `literature-attested` 的有限生成线性群剩余有限性；本源的 GL_9(R) 对应与有限商效果由定理 83.2 承担，没有有效商大小。 |
| Monras–Winter，[arXiv:1412.3634v1](https://arxiv.org/html/1412.3634v1)，§4、定理 9 | `literature-attested` 的同一精确随机过程之商实现同构背景；不直接供应本源外定时序、多输出四表的有限样本认证。这里的全词接口由 (84.1)–(84.8) 在本合同下推导。 |
| [AURIC FIB ATOM 与量子基本原则：相干递归的条件综合](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md)，§§1、9–13 | 复角、效果、共同相干关系与参考一致性的条件接合背景；这些仍是实质结构前提，不从单系统有限表或谱守恒自动取得。 |

**定义 86.2（保持开放的精确问题）。** 有限原生预测、任意隐藏维数和逐分支可逆谱守恒不能单独选出复量子物理起源：定理 81.1 给每个有限记录域的有限模型，定理 83.2 还保留全部离散群恒等式，定理 85.1 则给全词的无限模型。未来完备 (84.4) 是足够恢复全词预测的明确关系条件；它还没有由四表被认证，也没有单独认证整个隐藏锥、参考一致性或复合规则。

由此得到一个具体的下一步目标：从原环境就绪、固定随机仪器、一个已给混合控制和终端记录出发，寻找实际可取得并可认证的操作原则，使所有可达当前零关系都对全部合法未来保持零；若只能在有限精度成立，须另给合法模型类、误差传播界和取得成本。一般无限载体上怎样用有限噪声数据认证这样的全未来条件，本文未解决。已知状态上限下的周期见证不替代这个问题。

即使补成精确未来完备，还需说明哪些已取得的共同参考、复合与效果关系能排除定理 85.1 的不同隐藏实现，或明确只要求识别它们共同的操作预测商。有限未触动参考恒等式、可复制制备、独立副本、局部层析、纠缠效果、相干环境访问、连续可调控制和全域逆分别有不同量词；本文没有把其中任何一项由原合同免费补入。已有重建中的复 Hilbert、Born、CP 或有序锥前提必须在各自条件下评价，既不能冒充已从记录推出，也不因仍有前提而取消其条件定理的内容。

所有等式在此均为纯理论精确断言；没有有限样本成本、统一噪声间隙、有效商大小或经验物理验证，亦没有新增 Lean／kernel 核验。原量子起源目标继续要求把可检验的共同关系、信息保留层次及实际取得桥连起来；本节所确定的是这条桥上哪些有限记录条件不足、哪一个全未来关系足够恢复预测，以及恢复预测以后仍剩哪些物理结构问题。

## 追加锚（本行以下为增补区）

## 87. 原有限隐藏闭合在任意可测经典空间上的障碍

**定义 87.1（同源测度模型与带权列）。** 固定 V §§91–95 的全部对象和量词，即 (80.1) 中的一个 $\rho_0$、一个 $E=qq^\dagger$、原随机仪器和任意一个已安装的 $[N,P_\xi]\ne0$。原五维来源仍取 V 命题 91.3；本节只比较其单系统完整记录律 (80.2)。沿用 V §93 和 (84.2) 的原九列、九行与四表，记

$$
\alpha_w=2^{-k(w)},\qquad
\alpha_i=\alpha_{u_i},\qquad
P_i=G_{u_i}\rho_0,\qquad r_i=\alpha_iP_i.
\tag{87.1}
$$

其中 $u_1=\varnothing$，$u_1,\ldots,u_8$ 是深度不超过七的原生词，第九词为 V 定理 92.2 所选的 $u_kN$。$N$ 不作任何特别选择；包括 $d=2/3$ 和 $N\xi\perp\xi$。

令 $(\Omega,\Sigma)$ 为任意可测空间，$\mathcal M(\Omega)$ 为其有限、可数可加实符号测度空间，以总变差范数赋范，正锥为非负测度。经典模型给一个概率测度 $\mu$、一个可测响应 $f:\Omega\to[0,1]$，以及三个固定正实线性映射 $B_a:\mathcal M(\Omega)\to\mathcal M(\Omega)$，满足

$$
\begin{gathered}
u(\nu)=\nu(\Omega),\qquad e(\nu)=\int_\Omega f\,d\nu,\\
u\circ(B_0+B_1)=u,\qquad u\circ B_N=u.
\end{gathered}
\tag{87.2}
$$

条件对整个测度空间成立；不要求 $uB_j=u/2$。通常的可测次随机核仪器是其中一类：$B_a\nu(S)=\int\kappa_a(\omega,S)\,d\nu(\omega)$，$\kappa_0(\omega,\Omega)+\kappa_1(\omega,\Omega)=\kappa_N(\omega,\Omega)=1$。允许一般正线性映射使结论也覆盖不先指定核表示的模型。所有隐藏时钟和记忆均可包含在 $\Omega$；没有其基数、拓扑或维数上限，也没有预设确定响应。

置 $x_i=B_{u_i}\mu$、$X\beta=\sum_i\beta_i x_i$，$R\beta=\sum_i\beta_i r_i$。$C$ 仍是 (84.2) 的原质量行和八个带权终端行。要求精确匹配原四表：

$$
CX=H=\mathcal LR,\qquad
CB_aX=H^a=\mathcal LA_aR\quad(a=0,1,N).
\tag{87.3}
$$

其中每个非迹条目是 $p(u_i h_t,1)$ 或 $p(u_i a h_t,1)$，每个质量条目是无后缀的两终端质量之和，完全保留 V (93.4)–(93.5) 的权重与时序。若还要求匹配同一时序中未列入四表的其余记录及全部词质量，模型类只会进一步缩小。

**假设 87.2（原二十七模板的隐藏测度等式）。** 对原四表确定的 $K_a=H^{-1}H^a$，要求

$$
z_{ai}:=B_ax_i-\sum_{j=1}^9(K_a)_{ji}x_j=0
\quad\text{于 }\mathcal M(\Omega),\qquad
a=0,1,N,\quad 1\le i\le9.
\tag{87.4}
$$

这正是 §84 末段已命名的更强隐藏闭合，而不是 (84.5) 的未来零观察条件。每条测度等式要求对每个 $S\in\Sigma$ 都相等；至多二十七条模板不等于二十七个标量读数。相同或恒等的模板可省略。

**定理 87.3（任意可测经典载体不能满足原有限隐藏闭合）。** 对定义 87.1 的每个源、每个允许的原混合控制 $N$，不存在同时满足 (87.3) 和假设 87.2 的经典模型。因此，即使一个任意记忆的经典随机仪器精确匹配全部原记录，它也必违反至少一条 (87.4)。

证明。强闭合所给的线性接口沿用定理 84.2，直接在隐藏空间而非零观察商中取

$$
T=XR^{-1}:Q\longrightarrow\mathcal M(\Omega),\qquad Q=\operatorname{Herm}_3.
\tag{87.5}
$$

具体地，$K_a=R^{-1}A_aR$ 和 (87.4) 给 $B_aT=TA_a$；$CT=\mathcal L$ 使 $T$ 单射。质量行、空后缀是行及空前缀列分别给

$$
u T=\operatorname{Tr},\qquad
eT=\operatorname{Tr}(E\,\cdot),\qquad
T\rho_0=\mu,\qquad
T(G_w\rho_0)=\alpha_w^{-1}B_w\mu.
\tag{87.6}
$$

最后一个等式只是固定映射的代数复合；右侧为非负、质量一的测度。它未把标签变成控制，也未对任意隐藏输入赋予归一化后缀响应界。

关键的新步骤是把这个接口的正性延至全部 $Q_+$。由于 $Q$ 有限维且每个 $x_i$ 的总变差有限，

$$
\|TY\|_{\rm TV}
\le\sum_{i=1}^9|(R^{-1}Y)_i|\,\|x_i\|_{\rm TV},
\tag{87.7}
$$

故 $T$ 对总变差范数连续。V 定理 95.1 对任意所给混合 $N$ 给出的正词闭包，使 $G_w\rho_0$ 稠密于所有纯 qutrit 投影。由 (87.6)，这些点的像都是非负测度；非负有限测度锥在总变差范数下闭，故每个纯投影的像也非负。Hermitian 谱分解再给 $T(Y)\ge0$ 对每个 $Y\succeq0$ 成立。极限只在这个已强制为有限维的隐藏像中进行，不对 $\Omega$ 假设紧性，不对物理控制添加极限门。

现用原终端效果的尖锐性，而不假定 $f$ 尖锐。对每个隐藏事件 $S\in\Sigma$，由有限维迹对偶定义三个 Hermitian 矩阵：

$$
\begin{aligned}
\operatorname{Tr}(M(S)Y)&=(TY)(S),\\
\operatorname{Tr}(M_1(S)Y)&=\int_S f\,d(TY),\\
\operatorname{Tr}(M_0(S)Y)&=\int_S(1-f)\,d(TY).
\end{aligned}
\tag{87.8}
$$

刚证得的正性以及 (87.6) 使

$$
\begin{gathered}
M=M_1+M_0,\qquad M(\Omega)=I_3,\\
0\preceq M_1(S)\preceq E,\qquad
0\preceq M_0(S)\preceq I_3-E.
\end{gathered}
\tag{87.9}
$$

这些矩阵按事件可数可加：在任意固定 Hermitian 基上，其坐标都是 (87.8) 的有限符号测度。因而 $M$ 是一个 POVM，$M_1,M_0$ 是它与原尖锐二元效果的共同细化。这里的 POVM 是反证中由隐藏表示导出的数学对象，不是另行取得的测量。

所用成熟中间事实是 Heinosaari–Reitzner–Stano，[arXiv:0811.0783v2](https://arxiv.org/html/0811.0783v2)，附录命题 8 的尖锐相容性：一个共同可测效果若为投影，另一边的效果必须与它交换。本处也可直接验证所需的一步。若 $0\preceq D\preceq P$ 且 $P$ 是投影，则对 $v\in\ker P$ 有 $\langle v,Dv\rangle=0$，正性给 $Dv=0$，所以 $D=PDP$。对 (87.9) 分别应用，得到

$$
M(S)=EM_1(S)E+(I_3-E)M_0(S)(I_3-E),
\qquad [M(S),E]=0.
\tag{87.10}
$$

取任意单位 $v\perp q$，令 $Y=qv^\dagger+vq^\dagger\ne0$。由 (87.10)，$\operatorname{Tr}(M(S)Y)=0$ 对每个 $S$ 成立，因此 $TY$ 是零测度。这与 $T$ 单射矛盾。等价地，事件效果全落在 $E$ 的 $1\oplus2$ 块对角子空间，其实维数只有五，不能分离原九维 $Q$。

证明仅用了原九列／九行的满秩、每个混合 $N$ 的正词闭包、经典测度正性和一个原尖锐效果。它既未要求整个隐藏正锥等于量子锥，也未调用 V §§100–110 的载体维数或紧基前提。∎

## 88. 两个全词经典模型中同一条非零隐藏残差

**命题 88.1（原零标签插入的显式原子残差）。** 对 (87.1) 的任意原前缀基，至少有一个指标 $i$ 满足

$$
G_0P_i\notin\{P_1,\ldots,P_9\}.
\tag{88.1}
$$

令 $i_*$ 为满足此条件的最小指标，$\gamma_j=G_{u_j}\in\Gamma$，$P_*=G_0P_{i_*}$、$\gamma_*=G_0\gamma_{i_*}$。在定理 85.1 的可数群模型和连续纯态模型中，对应的 (87.4) 残差分别正是

$$
\begin{aligned}
z^{\Gamma}_{0i_*}
 &=\frac{\alpha_{i_*}}2\delta_{\gamma_*}
   -\sum_{j=1}^9(K_0)_{ji_*}\alpha_j\delta_{\gamma_j},\\
z^{\rm pure}_{0i_*}
 &=\frac{\alpha_{i_*}}2\delta_{P_*}
   -\sum_{j=1}^9(K_0)_{ji_*}\alpha_j\delta_{P_j}.
\end{aligned}
\tag{88.2}
$$

两者非零，在各自新单点事件上的值均为 $\alpha_{i_*}/2$，且

$$
\|z^{\Gamma}_{0i_*}\|_{\rm TV}
=\|z^{\rm pure}_{0i_*}\|_{\rm TV}
=\frac{\alpha_{i_*}}2+
 \sum_{j=1}^9|(K_0)_{ji_*}|\alpha_j
\ge\alpha_{i_*}>0.
\tag{88.3}
$$

然而它们的质量、原是效果以及所有合法未来的两终端读数均为零。该选择适用于任意原允许 $N$。

证明。九个 $P_j$ 线性独立，因而互异。若全部 $G_0P_i$ 都在这九点中，可逆的 $G_0$ 就置换这九点。某个正整数幂遂在这组基上恒等，故在整个 $Q$ 上恒等。§82 证明中的 (82.2) 已排除此可能：相同实际块 $B_z$ 的迹为 $(z-1)/2$、行列式为 $-z$，$z\notin\{1,-1\}$ 时其代数整数范数论证给 $G_0$ 无限阶。因此 (88.1) 必有指标；这里只在原二十七插入中指定一条，没有改变控制 $N$。

可数模型的 $x_j=\alpha_j\delta_{\gamma_j}$，连续模型的 $x_j=\alpha_j\delta_{P_j}$；各自 $B_0$ 都是原共轭推前的二分之一，直接得到 (88.2)。$P_*$ 不在九点中也蕴含 $\gamma_*$ 不在九个 $\gamma_j$ 中。可数空间取全部子集，连续模型取 Borel 集，新单点事件均可测。所有显示的原子在各自载体上互异，故总变差范数恰为 (88.3) 的绝对系数和。

由 $R K_0=A_0R$，矩映射 (85.3) 把两条残差都送到零。取迹给

$$
\sum_j(K_0)_{ji_*}\alpha_j=\alpha_{i_*}/2.
\tag{88.4}
$$

这给 (88.3) 的下界，也说明残差总质量为零。由 $JB_v=A_vJ$、$u=\operatorname{Tr}J$ 和 $e=\operatorname{Tr}(EJ)$，对每个合法后缀 $v$ 均有 $u(B_vz)=e(B_vz)=0$；补终端也为零。

此外，该列的 $K_0$ 必有负条目。否则 (88.4) 将 $P_*$ 写成九个 $P_j$ 的凸组合，权重为 $2(K_0)_{ji_*}\alpha_j/\alpha_{i_*}$。纯投影的极端性迫使所有正权重项等于 $P_*$，与 (88.1) 矛盾。正条目也由 (88.4) 的严格正右端保证存在。∎

**定义 88.2（四层等价的对象）。** 对本源有限事件的实系数关系，区分：源矩阵的线性等式；竞争者所选九行的有限标量等式；对每个合法后缀的两终端等式；隐藏符号测度本身相等。它们分别发生在 $Q$、$\mathbb R^9$、全部合法未来的读数族和 $\mathcal M(\Omega)$。隐藏相等蕴含全未来相等，后者蕴含已选行相等；反向不能省去条件。定理 81.1 的有限表模型与定理 82.1 的全词障碍已分开前两种观察强度；(88.2) 则在同一原源、同一原权重下把全未来相等与隐藏相等严格分开。

因此定理 87.3 排除的是加入假设 87.2 后的经典模型。可数和连续模型仍精确满足原全词记录律及定理 84.2 的未来完备条件；它们不满足更强的隐藏等式，不构成定理 87.3 的反例。

## 89. 独立时序彩票、完整档案与约化关系的端口

**假设 89.1（仅用于事件解释的附加接口）。** 若要把 (87.4) 解释为混合制备关系，另供一个与初始隐藏状态及原生随机源独立的有限时序彩票。彩票只选择预先固定的原合法时序，不选择原生结果。各时序结束后须有同一个可接续的系统边界；下文的共同后缀在该边界执行，对每个彩票值和每段已发生历史均相同。此共同边界的后续操作只接触所声明的系统，不读彩票或历史档案；档案仍保留，亦允许在完整输出的比较中读出。不同词长的输出怎样接到同一边界，是这项假设的一部分。

原合同只给固定外定时序，并未实现这组彩票与共同端口。旗标由记录计算，永不改变随后操作；没有反馈、重试、强迫标签或按成功分支选择控制。

**定义 89.2（一条原关系的未归一化彩票）。** 对任一 $(a,i)$，用十个事件槽写

$$
\begin{gathered}
w_0=u_i a,\qquad w_j=u_j\quad(1\le j\le9),\\
c_0=1,\qquad c_j=-(K_a)_{ji},\qquad
c_\ell^+=\max(c_\ell,0),\quad
c_\ell^-=\max(-c_\ell,0).
\end{gathered}
\tag{89.1}
$$

这是源矩阵恒等式 $\sum_{\ell=0}^9c_\ell A_{w_\ell}\rho_0=0$。令

$$
\begin{aligned}
\tau_\pm&=\sum_{\ell=0}^9c_\ell^\pm A_{w_\ell}\rho_0,\\
m&=\operatorname{Tr}\tau_+=\operatorname{Tr}\tau_-
  =\sum_\ell c_\ell^+\alpha_{w_\ell}>0,\\
s_\pm&=\sum_\ell c_\ell^\pm,\qquad
0<\lambda\le\frac1{\max(1,s_+,s_-)}.
\end{aligned}
\tag{89.2}
$$

$m>0$ 因 $c_0=1$ 和 $\alpha_{w_0}>0$；两边等迹且 $\tau_+=\tau_-$。在正／负两个方案中，彩票槽 $\ell$ 分别以概率 $\lambda c_\ell^\pm$ 被选，余下概率 $1-\lambda s_\pm$ 选择填充槽 $\bot$。槽 $\ell$ 执行 $w_\ell$ 所指定的外定时序，保留该时序的每个原生历史 $h$；只把 $h=w_\ell$ 标为成功，其余标为失败。填充槽保留原制备并标为填充。三种旗标是不同记录值。

**命题 89.3（约化成功块相等而完整标记输出可分）。** 在假设 89.1 下，定义 89.2 的两个方案有相等的系统约化成功块 $\lambda\tau_+=\lambda\tau_-$，并对每个共同合法后缀给相等的未归一化成功读数；但其保留彩票与历史的成功输出不相等。具体有一个档案事件在正方案的质量为 $\lambda m$，在负方案为零。因此把这条源矩阵等式当作完整输出相等，是不成立的。

证明。令 $\mathcal H_\ell$ 是槽 $\ell$ 的原固定时序允许的全部历史，$\mathcal V$ 是共同后缀时序允许的全部历史。用 $L,H,F,V,B$ 分别记录彩票、前缀原生历史、旗标、后缀原生历史和终端结果，$b\in\{0,1\}$。完整联合律为

$$
\begin{aligned}
\Pr_\pm(L=\ell,H=h,F=\varepsilon(\ell,h),V=v,B=b)
 &=\lambda c_\ell^\pm p(hv,b),
 \qquad h\in\mathcal H_\ell,\ v\in\mathcal V,\\
\varepsilon(\ell,h)&=
 \begin{cases}\mathrm{成功},&h=w_\ell,\\
 \mathrm{失败},&h\ne w_\ell,
 \end{cases}\\
\Pr_\pm(L=\bot,H=\varnothing,F=\mathrm{填充},V=v,B=b)
 &=(1-\lambda s_\pm)p(v,b).
\end{aligned}
\tag{89.3}
$$

其他值的质量为零。这里 $p(hv,b)=2^{-k(h)-k(v)}\operatorname{Tr}(E_bG_vG_h\rho_0)$，$E_1=E,E_0=I_3-E$，是原始无条件权重。对每个固定时序求全部历史和两终端，总质量为一；故 (89.3) 总和恰为 $\lambda s_\pm+(1-\lambda s_\pm)=1$，失败和填充没有被丢弃。固定后缀也在失败与填充运行中执行。

只在数学上求成功块边缘，不按其质量归一化，有

$$
\begin{aligned}
\Pr_\pm(F=\mathrm{成功},V=v,B=b)
 &=\lambda\sum_\ell c_\ell^\pm p(w_\ell v,b)\\
 &=\lambda\operatorname{Tr}(E_bA_v\tau_\pm).
\end{aligned}
\tag{89.4}
$$

故全部共同后缀的约化成功读数相等。完整成功输出却为

$$
\widehat\tau_\pm
=\lambda\sum_\ell c_\ell^\pm
 |\ell,w_\ell,\mathrm{成功}\rangle
 \langle\ell,w_\ell,\mathrm{成功}|
 \otimes A_{w_\ell}\rho_0.
\tag{89.5}
$$

对同一槽 $\ell$，$c_\ell^+c_\ell^-=0$，所以两边占据互不相交的彩票档案块，均有迹 $\lambda m>0$。于是

$$
\operatorname{Tr}_{\rm 档案}\widehat\tau_+
=\operatorname{Tr}_{\rm 档案}\widehat\tau_-
=\lambda\tau_+,\qquad
\|\widehat\tau_+-\widehat\tau_-\|_1=2\lambda m.
\tag{89.6}
$$

更直接地，档案事件
$\{F=\mathrm{成功},\ L\in\{\ell:c_\ell>0\}\}$
在两个完整概率律中的质量分别为 $\lambda m$ 和零；对后缀及终端求和不改变这个读数。故完整输出总变差距离至少为 $\lambda m$。约化时的数学偏迹未物理擦除档案，未将完整输出宣布等价。∎

**定义 89.4（隐藏仿射提升所多要求的关系）。** 独立彩票在经典模型中按 (89.3) 对应的原事件测度求和，两个成功块为

$$
\nu_\pm^{\rm 成功}
=\lambda\sum_\ell c_\ell^\pm B_{w_\ell}\mu,
\qquad
\nu_+^{\rm 成功}-\nu_-^{\rm 成功}=\lambda z_{ai}.
\tag{89.7}
$$

把系统约化成功块的相等提升为这两个隐藏测度相等，恰好额外要求相应的 (87.4)。对全部原模板如此要求，就是假设 87.2 的有限结构呈示；它结合固定映射、正性与源的稠密轨道，强制了定理 87.3 中全量子态域上的正仿射编码。不能把这一步称作由四表低成本获得全局仿射承诺。

这里的操作等价参考只包含共同边界后的系统操作。若参考还允许读档案，命题 89.3 已给出区分事件，两个方案甚至不满足该较大参考下的操作等价。即使选择较小参考，也须另外接受“此参考下相等的这些约化事件，隐藏测度必须相等”的制备非上下文性原则，才有 (89.7) 的零差；这是新增原则，不是概率论的恒等式。首个未由原菜单提供的原生接口，是独立选择这些时序并将其完整带旗事件送到同一未来端口的能力；把该端口的约化等价提升为隐藏相等又是独立义务。成功块只作次归一化事件，不充当免费取得的条件制备。

## 90. 本源有限提升的供应与关系范围

**定义 90.1（源特定推导与成熟中间供应）。** 定理 87.3、命题 88.1 和命题 89.3 的归属为 `repo-derived` 源特定推导，不赋予文献优先权。所用既有结果及其在本源的对应如下；文献结论只承担推导中的中间步骤。

| 供应 | 在本源实际承担的内容 |
| --- | --- |
| V §§91–95、98–99；本卷 §§80–86 | 原五维来源、单纯制备、原尖锐效果、原带权四表、九列／九行及任意原混合 $N$ 的正词闭包；§84 已有强闭合与预测商闭合的区分，§85 已有两个全词经典模型。新增测度障碍不重复这些线性闭合或模型存在结论。 |
| V §82 与 §§100–110 | 前者的整个 $\mathcal K_d$ 上共同仿射制备合同与后者的整个有序载体维数／闭紧基合同是不同前提。本节不援用其分类结论；它把原有限隐藏等式作为新增结构原则，在任意测度载体上导出正仿射接口并反证。 |
| Spekkens，[Contextuality for preparations, transformations and unsharp measurements，quant-ph/0406166v3](https://arxiv.org/html/quant-ph/0406166v3)，§§II–IV、VIII | 操作等价、混合语义及制备非上下文性的成熟区分；允许随机隐藏响应。其成套制备操作不是这里一个原制备的既有权限。定理 87.3 不把结果确定性作为输入。 |
| Heinosaari–Reitzner–Stano，[0811.0783v2](https://arxiv.org/html/0811.0783v2)，附录命题 8 | (87.8)–(87.10) 中共同细化与尖锐效果迫使交换的成熟中间机制；实际尖锐边是原 $E$，另一边是由 $T$ 导出的隐藏事件 POVM，并非自由控制 qutrit 的替代场景。 |
| Schmid–Spekkens–Wolfe，[1710.08434](https://arxiv.org/html/1710.08434)，§§II–III，尤其式 (10)–(11) | 给定有限制备混合等价时，相应隐藏分布须满足相同线性关系的已知框架。本文的槽来自原加权历史，需 (89.3) 保留失败和全部记录；该文不替原生事件取得或共同边界作保证，也不把有限表自动升级为操作等价。 |
| Selby 等，[2112.04521v3](https://arxiv.org/html/2112.04521v3)，§§I、III–IV | 可取得片段容许次归一化状态而未必容许其归一化状态，及标记凸化须保留结果的成熟区分。这里不从该文的片段／锥等价推出整个标记档案相等，具体差异由 (89.5)–(89.6) 计算。 |
| Gitton–Woods，[System loophole of generalized noncontextuality，DOI:10.1103/PhysRevResearch.6.043289](https://doi.org/10.1103/PhysRevResearch.6.043289)，§§II–III | 不可区分性须指定操作参考和系统范围；本处严格区分只接系统端口的后缀与可读取保留档案的较大参考。 |
| [相干重建 §§25、34](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md#25-关系谱作为共同预测对象谱值切面与有向组合)；[原生叶边界取得 II，Boundary 66.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION_II.md#66-supplier-subtraction-and-the-remaining-realization-boundary) | 类型、方向、共同来源、完整结果及参考接口的已有要求；各自条件模型不能仅因矩阵、秩或数值对应就拼成共同原生／路径／量子实现。 |

**定义 90.2（结论的量词及剩余数学接口）。** 本节的排除域为满足原四表与新增隐藏测度等式的固定经典随机仪器；(87.4) 是强仿射一致性原则的有限结构呈示。它给出用隐藏关系代替载体维数上限的一条条件路线，同时严格加强全未来零观察；它既不是后者的另一个名称，也不供应 V §82 整个制备族的实际制备权限。原全词记录律、有限标量数据、结构原则和有限统计认证是四个不同层次；移去该原则后，命题 88.1 的两种无限模型仍合法。

继续接合原目标所需的接口为：独立时序彩票及共同未来端口的原生取得；约化事件等价的参考与非上下文性范围；原生、路径和量子对象在初始化、合法操作、完整输出、权利及同时资源上的共同实现；共同参考与复合规则；有限精度下的稳定性、噪声界和有限样本认证。定理 87.3 只解决其中“接受原有限隐藏等式后，任意可测经典随机仪器是否仍可能”的精确问题，答案是否定的。它不从这些等式推导 Born、CP、组合律或量子起源；上述其余接口仍需各自的数学条件与取得桥。

## 追加锚（本行以下为增补区）

## 91. 原固定时序的完整记录有界效果

**定义 91.1（同一单制备源与时序域）。** 固定 V 定义 54.1、91.1 及本卷定义 80.1 的源：$0<d<1$、$\sin(2\theta)\ne0$，一个原相容纯制备 $\rho_0=\psi\psi^\dagger$，原效果 $E=qq^\dagger$，以及任意一个已安装、可重复且满足 $[N,P_\xi]\ne0$ 的 $N\in U(3)$。以下所有时序均使用这同一个 $N$。特别保留原矩阵的关系

$$
\begin{gathered}
f=(1,-1,0)^{\mathsf T}/\sqrt2,\qquad
q=(\xi+e)/\sqrt2,\qquad f^\dagger q=0,\\
\psi=\sqrt d\,Uq+\mathrm i\sqrt{1-d}\,Uf,\qquad \rho_0=\psi\psi^\dagger,\\
W=I_3-2ff^\dagger,\qquad
V_0=U\exp(\mathrm i\theta W),\qquad V_1=V_0W,\\
A_j(X)=\tfrac12V_jXV_j^\dagger\quad(j=0,1),\qquad
A_N(X)=NXN^\dagger.
\end{gathered}
\tag{91.1}
$$

一个外定有限时序 $s$ 是字母表 $\{\mathsf J,\mathsf N\}$ 上的有限词；$\mathsf J$ 表示使用原随机仪器，$\mathsf N$ 表示使用 $N$。设 $k=k(s)$ 是仪器位置数，$\mathcal W_s$ 是把每个 $\mathsf J$ 替换为实际标签 $0$ 或 $1$、每个 $\mathsf N$ 替换为 $N$ 得到的全部 $2^k$ 条历史。最左字母最早作用，故对于 $w=b_1\cdots b_n\in\mathcal W_s$，

$$
\begin{gathered}
U_w=U_{b_n}\cdots U_{b_1},\qquad
U_0=V_0,\quad U_1=V_1,\quad U_N=N,\\
A_w=2^{-k}\operatorname{Ad}_{U_w},\qquad
R_w=U_w^\dagger EU_w,\qquad E_1=E,\quad E_0=I_3-E,\\
p_s(w,b)=\operatorname{Tr}(E_bA_w\rho_0),\qquad
p_s(w,0)+p_s(w,1)=2^{-k},\qquad
\sum_{w\in\mathcal W_s}\sum_{b=0}^1p_s(w,b)=1.
\end{gathered}
\tag{91.2}
$$

空时序也在域内。时序长度、终点及 $N$ 的各个位置预先固定，不依赖随机标签；没有反馈或停止规则。$(w,b)$ 是完整输出，所有历史与两种终端结果均在 (91.2) 中。

V 命题 91.3 供应其原五维来源：$B^\dagger B=I_3$，原五维分支与给定控制的角块延伸满足

$$
\begin{gathered}
\widehat K_{\theta,j}B=2^{-1/2}BV_j,\qquad
\widetilde N=BNB^\dagger+(I_5-BB^\dagger),\qquad
\widetilde NB=BN,\\
P_5=BEB^\dagger,\qquad
B^\dagger(I_5-P_5)B=I_3-E.
\end{gathered}
\tag{91.3}
$$

因此沿同一时间词的五维复合在 $B\mathbb C^3$ 上等于 $2^{-k/2}BU_w$，原制备 $B\rho_0B^\dagger$ 与终端 $(P_5,I_5-P_5)$ 给出 (91.2)。$\rho_0$ 的原完整矩映射与纯制备来源仍由该命题承担；这里的数学效果域不增加任何制备。

**定义 91.2（完整记录接受效果与数学扩张）。** 对一个时序 $s$，给每个完整输出一个系数 $a(w,b)\in[0,1]$，定义

$$
F_{s,a}=\sum_{w\in\mathcal W_s}2^{-k}
 \big[a(w,1)R_w+a(w,0)(I_3-R_w)\big].
\tag{91.4}
$$

系数为 $0$ 或 $1$ 时，这是原完整记录的二元事件效果。任意 $[0,1]$ 系数只扩大比较域；其概率随机化是否可物理取得不作前提。由 $\sum_{w,b}A_w^*(E_b)=I_3$，有 $0\preceq F_{s,a}\preceq I_3$，且原始接受质量为

$$
\operatorname{Tr}(F_{s,a}\rho_0)
 =\sum_{w,b}a(w,b)p_s(w,b).
\tag{91.5}
$$

再定义数学比较集

$$
\mathcal B_N=
\overline{\operatorname{conv}\{F_{s,a}:s\text{ 为上述有限时序},\ 0\le a(w,b)\le1\}}
 ^{\|\cdot\|_\infty},
\tag{91.6}
$$

其中 $\theta$ 和原 $E$ 已固定，$\|\cdot\|_\infty$ 为算子范数。凸组合和范数闭包是比较集的数学扩张，不供应时序彩票、无限时序或极限操作。每个 $F_{s,a}$ 的两种二元质量仍来自同一完整分布：接受使用 $a$，拒绝使用 $1-a$；任何记录都未被删除或重新归一化。可取得次归一化片段与其归一化对象的区别，见 Selby 等，[Accessible fragments of generalized probabilistic theories, cone equivalence, and applications to witnessing nonclassicality，2112.04521v3](https://arxiv.org/html/2112.04521v3)，§§I、III；这些区别不预先决定本源 $\mathcal B_N$ 的大小。

## 92. 每个已安装混合控制的统一正距离障碍

**定理 92.1（完整原生记录不能逼近一个数学秩一效果）。** 对定义 91.1 的每个源和每一个允许的 $N$，存在一个数学秩一投影 $P_N$ 及 Hermitian 见证 $Z_N=2P_N-I_3$，使

$$
\operatorname{Tr}(Z_NP_N)=1,\qquad
\sup_{F\in\mathcal B_N}\operatorname{Tr}(Z_NF)\le\frac34,
\qquad
\inf_{F\in\mathcal B_N}\|P_N-F\|_\infty\ge\frac1{12}.
\tag{92.1}
$$

同一个 $P_N$ 适用于全部有限长度、全部外定时序及全部接受系数。$P_N$ 可以只依赖 $N$ 与原 $f$，不依赖 $d$ 或 $\theta$；其定义不供应谱标定、物理制备、测量或新端口。

证明。先构造单位向量 $v_N$，使所有整数 $m\ge0$ 都满足

$$
\frac18\le |f^\dagger N^m v_N|^2\le\frac78.
\tag{92.2}
$$

取 $N$ 的任一正交归一特征基 $z_1,z_2,z_3$，并重排使
$t_1=|f^\dagger z_1|^2=\max_j|f^\dagger z_j|^2$。由 $\sum_jt_j=1$，有 $t_1\ge1/3$。若 $t_1\le7/8$，置 $v_N=z_1$ 即得 (92.2)。若 $t_1>7/8$，置 $v_N=(z_1+z_2)/\sqrt2$。因 $t_2\le1-t_1$，三角不等式给每个 $m$ 的振幅上下界，平方后得到

$$
\begin{aligned}
|f^\dagger N^m v_N|^2
&\ge\frac12\big(\sqrt{t_1}-\sqrt{1-t_1}\big)^2
 =\frac12-\sqrt{t_1(1-t_1)}
 \ge\frac{4-\sqrt7}{8}>\frac18,\\
|f^\dagger N^m v_N|^2
&\le\frac12\big(\sqrt{t_1}+\sqrt{1-t_1}\big)^2
 =\frac12+\sqrt{t_1(1-t_1)}
 \le\frac{4+\sqrt7}{8}<\frac78.
\end{aligned}
\tag{92.3}
$$

这里使用 $t_1(1-t_1)\le7/64$；特征值简并和任意特征相位均在此证明内。置 $P_N=v_Nv_N^\dagger$。令

$$
T_m=N^{-m}WN^m.
\tag{92.4}
$$

这是数学 Heisenberg 共轭，$T_m=T_m^\dagger=T_m^{-1}$，没有调用逆控制。由 (91.1)、(92.2) 及 $q\perp f$，有

$$
\begin{aligned}
|v_N^\dagger T_mv_N|
 &=\big|1-2|f^\dagger N^mv_N|^2\big|\le\frac34,\\
|q^\dagger N^mv_N|^2
 &\le1-|f^\dagger N^mv_N|^2\le\frac78.
\end{aligned}
\tag{92.5}
$$

以下直接估计完整记录 (91.4)。为简记写 $P=P_N$、$v=v_N$、$Z=2P-I_3$。对任一秩一投影 $R$，令 $x=\operatorname{Tr}(PR)\in[0,1]$。则对任意 $\alpha,\beta\in[0,1]$，

$$
\begin{aligned}
\operatorname{Tr}\big(Z[\alpha R+\beta(I_3-R)]\big)
 &=\alpha(2x-1)-2\beta x\\
 &\le(2x-1)_+,\qquad t_+=\max\{t,0\}.
\end{aligned}
\tag{92.6}
$$

所以补终端结果及其任意接受系数已包括在估计内。

若 $s$ 无仪器位置，则其历史为 $N^m$，$R=N^{-m}EN^m$。由 (92.5) 有 $x\le7/8$，故 (92.6) 给 $\operatorname{Tr}(ZF_{s,a})\le3/4$。这包括空时序。

若 $s$ 有 $k\ge1$ 个仪器位置，设其第一处仪器之前恰有 $m$ 次 $N$。固定第一处之后的任一完整标签历史 $t$，成对比较

$$
w_0=N^m0t,\qquad w_1=N^m1t.
\tag{92.7}
$$

同一外定时序保证两条历史的后续操作与 $U_t$ 完全相同；$t$ 包括其全部后续 $N$ 和原生标签。按实际时间顺序，

$$
\begin{gathered}
U_{w_j}=U_tV_jN^m,\\
R_{w_0}=N^{-m}V_0^\dagger U_t^\dagger EU_tV_0N^m,
\qquad R_{w_1}=T_mR_{w_0}T_m.
\end{gathered}
\tag{92.8}
$$

置 $x=\operatorname{Tr}(PR_{w_0})$、$y=\operatorname{Tr}(PR_{w_1})$。则

$$
x+y=\operatorname{Tr}\big[R_{w_0}(P+T_mPT_m)\big]
 \le1+|v^\dagger T_mv|\le\frac74.
\tag{92.9}
$$

中间一步可由两个单位向量 $v,T_mv$ 的 Gram 矩阵得到：$P+T_mPT_m$ 的非零本征值为 $1\pm|v^\dagger T_mv|$。又 $x,y\le1$，故

$$
\begin{aligned}
(2x-1)_++(2y-1)_+
 &=\max\{0,2x-1,2y-1,2x+2y-2\}\\
 &\le\frac32.
\end{aligned}
\tag{92.10}
$$

对 (92.7) 的两条历史各用 (92.6)。它们的四个终端接受系数可以彼此独立、任意依赖完整标签记录；(92.10) 仍给这一对未乘权贡献至多 $3/2$。共有 $2^{k-1}$ 对，每条历史的原质量因子都是 $2^{-k}$，所以

$$
\operatorname{Tr}(ZF_{s,a})
 \le2^{-k}\,2^{k-1}\,\frac32=\frac34.
\tag{92.11}
$$

这一步求和包含整个记录树，而不是只比较擦除标签后的系统秩。标签依赖控制会破坏 (92.8) 的共同 $U_t$，不属于本定理的时序域。

线性连续泛函 $F\mapsto\operatorname{Tr}(ZF)$ 的同一界在数学凸组合及范数闭包下保持。$Z$ 的本征值为 $1,-1,-1$，故其迹范数为三。最后，

$$
\frac14\le\operatorname{Tr}\big[Z(P-F)\big]
 \le\|Z\|_1\|P-F\|_\infty
 =3\|P-F\|_\infty
\qquad(F\in\mathcal B_N).
\tag{92.12}
$$

得到全部 (92.1)。证明保持原 $1/2$ 分支和两终端质量，未对任何标签条件化。∎

## 93. 原九个带权前缀坐标中的共同后缀分离

**定义 93.1（九个原事件与共同读出）。** 依 V 定理 92.1–92.2 选任一原前缀基：$u_1=\varnothing$，$u_1,\ldots,u_8$ 是长至多七的原生词，第九个词 $u_9=u_jN$ 为同一个已安装 $N$ 给出的逃逸列。沿用 V (93.11) 及本卷 (84.2)，置

$$
r_i=A_{u_i}\rho_0,\quad
R:\mathbb R^9\longrightarrow Q=\operatorname{Herm}_3,\quad
R\mathbf e_i=r_i,\qquad
\operatorname{Tr}r_i=2^{-k(u_i)}.
\tag{93.1}
$$

$R$ 是实线性双射。对一个共同后缀时序 $s$ 和同一组后缀接受系数 $a(w,b)$，定义九个带权响应

$$
\begin{aligned}
\mathbf b(F)_i&=\operatorname{Tr}(Fr_i),\qquad F=F_{s,a},\\
\mathbf b(F_{s,a})_i
 &=\sum_{w\in\mathcal W_s}\sum_{b=0}^1a(w,b)\,p(u_iw,b),\\
\sum_{w,b}p(u_iw,b)&=2^{-k(u_i)}.
\end{aligned}
\tag{93.2}
$$

每个 $i$ 的实际上下文是执行 $u_i$ 所在的完整外定前缀时序，再对它的全部历史执行同一个 $s$；$u_i$ 只是最终档案中的前缀事件。共同后缀的操作和 $a(w,b)$ 不依赖 $i$、此前标签或前缀是否命中。其他前缀历史仍在完整分布中；若只计算 (93.2) 的事件，它们的接受系数为零。这里没有制备 $r_i/\operatorname{Tr}r_i$，也没有跨上下文制备彩票。

**推论 93.2（不删原权重的严格正坐标界）。** 用定理 92.1 的同一个 $P_N,Z_N$，定义数学目标响应和实系数

$$
(\mathbf t_N)_i=\operatorname{Tr}(P_Nr_i),\qquad
\gamma=R^{-1}Z_N,\qquad
\eta=\frac1{4\|\gamma\|_1}.
\tag{93.3}
$$

则 $\eta>0$，且对所有 $F\in\mathcal B_N$，

$$
\sum_{i=1}^9\gamma_i\big((\mathbf t_N)_i-\mathbf b(F)_i\big)
 \ge\frac14,\qquad
\max_{1\le i\le9}|(\mathbf t_N)_i-\mathbf b(F)_i|
 \ge\eta.
\tag{93.4}
$$

特别地，每个原二元记录事件的共同后缀读出，都与该数学目标的九个原带权响应至少有一个非零偏差。量词为每个共同 $F$ 存在一个偏差坐标；不声称某个固定坐标分离全部 $F$。

证明。$Z_N\ne0$ 且 $R$ 可逆，故 $\gamma\ne0$、$\|\gamma\|_1$ 有限正。其定义给 $Z_N=\sum_i\gamma_ir_i$，因此由 (92.1)，

$$
\begin{aligned}
\sum_i\gamma_i((\mathbf t_N)_i-\mathbf b(F)_i)
 &=\operatorname{Tr}\big[Z_N(P_N-F)\big]\ge\frac14,\\
\frac14
 &\le\sum_i|\gamma_i|\,|(\mathbf t_N)_i-\mathbf b(F)_i|
 \le\|\gamma\|_1\|\mathbf t_N-\mathbf b(F)\|_{\ell^\infty}.
\end{aligned}
\tag{93.5}
$$

这给出 (93.4)。若需全用原矩阵配对表示系数，置
$G_{ij}=\operatorname{Tr}(r_ir_j)$、$z_i=\operatorname{Tr}(r_iZ_N)$，则 $G$ 正定且 $\gamma=G^{-1}z$，所以 (93.3) 是确切的源参数表达式。

(93.2) 直接来自 $A_{u_iw}=A_wA_{u_i}$；每项仍含 $2^{-k(u_i)-k(s)}$。有符号的 $\gamma_i$ 只是分离泛函系数，不是物理混合权重或质量重标定。$\eta$ 随原参数及前缀基变化，此处没有它们共同的正下界或有限样本认证。$\mathbf t_N$ 是数学比较向量，其定义没有使 $P_N$ 成为已取得的终端。∎

## 94. 闭锥供应、有界效果与起源接口的范围

**推论 94.1（完整数学效果锥不供应完整有界读出）。** 沿用 V (105.5) 的源效果锥

$$
D=\overline{\operatorname{cone}\{2^{-k(w)}U_w^\dagger EU_w:
                 w\in\{0,1,N\}^*\}},
\tag{94.1}
$$

对每个原允许 $N$，有

$$
D=\mathrm{PSD}_3,\qquad
P_N\in D\cap[0,I_3],\qquad
\mathcal B_N\subsetneq[0,I_3],\qquad
\operatorname{dist}_{\|\cdot\|_\infty}(P_N,\mathcal B_N)\ge\frac1{12}.
\tag{94.2}
$$

证明。直接使用 [V 定理 95.1 及 §§105–107](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_V.md#105-定理-1021-的完整运输锥及两侧约束) 的正词共轭闭包与效果轨道锥恒等式，特别是 (106.5)，得到 $D=\mathrm{PSD}_3$。$P_N$ 是秩一投影，故属于 $D\cap[0,I_3]$。定义 91.2 给 $\mathcal B_N\subseteq[0,I_3]$，定理 92.1 则给严格包含及所示正距离。锥运算能消去每个历史的正权重；有界完整事件 (91.4) 同时保留所有历史，接受系数受 $[0,1]$ 限制，故这两个结论相容。原五维提升的效果 $\widehat F$ 满足 $B^\dagger\widehat FB=F$；算子范数在该压缩下不增，因而还得到

$$
\|BP_NB^\dagger-\widehat F\|_\infty
 \ge\|P_N-F\|_\infty\ge\frac1{12}
\tag{94.3}
$$

对所有上述五维完整事件效果及其数学凸闭包成立。∎

**定义 94.2（数学归属及未供接口）。** 定理 92.1 与推论 93.2 的归属是 `repo-derived`：承重点是原反射关系 $V_1=V_0W$、任意已安装 $N$ 的统一目标构造、完整成对历史的有界接受估计，以及同一个后缀在原九列上的严格正分离。不作文献优先权主张。相关供应及其量词如下。

| 供应 | 在本源中的内容与边界 |
| --- | --- |
| V 定义 54.1、命题 91.3、§§91–95；本卷 §§80、84–90 | 原五维等距来源、允许的 $d,\theta,N$、唯一纯制备、原两终端、时间顺序和九列基。定理 92.1 不加隐藏测度等式或隐藏维数上限。§84 的商运输仍以其全未来完备条件 (84.4) 为前提；§85 的可数与连续全词经典模型继续满足原记录合同。 |
| V §§105–107、命题 109.2 | 前者供应闭轨道锥及其有序重建合同下的数学对偶；后者供应未闭有限制备锥的原边界。推论 94.1 直接使用闭效果锥，定理 92.1 的对象则是已取凸闭包的有界完整记录效果。 |
| Selby 等，[2112.04521v3](https://arxiv.org/html/2112.04521v3)，§§I、III、IV，尤其 IV.1–IV.2 | `literature-attested`：可取得片段可含没有可取得归一化对应物的次归一化状态；锥等价及保留标记的凸化、探测效率改变是已有区分。这些结论不供应本源的自由制备、时序彩票、选支或归一化读出，也不直接供应 (92.1) 的统一界。 |
| Janotta–Lal，[Generalized Probabilistic Theories Without the No-Restriction Hypothesis，1302.2632v1](https://arxiv.org/html/1302.2632v1)，§§III.1–III.2 | `literature-attested`：概率值泛函给效果的上界，受限效果集须另行指定，并须与所给变换相容。此成熟原则不把 $D=\mathrm{PSD}_3$ 升级为所有 $0\preceq F\preceq I_3$ 均可读出；本源的具体正距离由 (92.2)–(92.12) 承担。 |
| Monras–Winter，[1412.3634v1](https://arxiv.org/html/1412.3634v1)，§4、定理 9；V §93 与本卷 §84 | `literature-attested` 的可达／零观察商与商实现同构背景。本文仍按原外定时序和双终端记录使用已有源对应；一般平稳过程实现合同不授予此处的新操作或有限数据全未来认证。 |
| [相干重建定义 20.2、34.1](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md#34-完整关系重建的充分接口与开放方向) | 共同类型与实现、复相干、相位参考、完整复合及全效果标定分别有其充分接口；(92.1) 只解决固定原菜单的有界取得障碍。 |

这里 $P_N$、$Z_N$ 与 $\gamma$ 是数学对象；它们的存在不提供源参数的谱标定、$P_N$ 的制备或测量，也不提供共同参考、复合系统或相干环境访问。没有新供应任意控制、逆、标签选择、自适应反馈、停止、制备彩票或无约束效果原则。定理 92.1 的正距离是原固定菜单的严格数学边界；扩大菜单以取得目标、证明不同表示的共同物理实现、取得相位／参考与复合接口，以及在有限噪声和样本下认证这些接口，仍是量子起源目标中的未解决问题。原精确预测商、有序闭锥、数学效果及物理可取得效果各保留自己的量词；这些条件数学结果不声称从原记录推出完整量子起源。

## 追加锚（本行以下为增补区）

## 95. 仅以过去标签决定停止的同源接口

**定义 95.1（固定动作串与有界停止表）。** 保留定义 91.1 的全部对象、原五维来源和唯一制备：$0<d<1$、$\sin(2\theta)\ne0$，以及每个已安装、可重复的 $N\in U(3)$，$[N,P_\xi]\ne0$。原仪器仍为 $A_j=\operatorname{Ad}_{V_j}/2$、$V_1=V_0W$；唯一系统读出仍为原终端 $(E,I_3-E)$。一个停止接口先给定有限动作串 $s\in\{\mathsf J,\mathsf N\}^T$ 及可停止的检查点。未停止时只执行 $s$ 的下一个动作；检查点的决定仅为“停止并调用一次原终端”或“继续”。决定可依赖此前实际标签与给定的经典模型／目标数据，不能改变未停止路径中的 $N$ 位置、选取 $\mathsf J$ 标签或增加量子动作。末点强制终止。原制备不重置、不复制；没有新增制备、逆、环境访问、终端效果或外部彩票。

模型矩阵、目标秩一投影及其精确标定作为经典输入供应，不称为取得的观察。一个有限停止表给每个允许的标签前缀一个停止位；这只定义新增的经典停止权限，不把该权限追认为 §91 的原合同已经安装。以下给其充分性，不断言绝对最小性。

**命题 95.2（完整停止叶及原五维逐路径律）。** 固定这样的表 $\pi$。令 $\Lambda_\pi$ 为全部停止叶，叶 $\ell$ 保留动作位置、实际时间词 $w_\ell$、其中每一个原标签和全部已执行 $N$。可以另附由这些标签确定的失配标记 $m_\ell$ 和超时标记 $t_\ell$，两者不合并或删去叶。记

$$
\begin{gathered}
\alpha_\ell=2^{-k(w_\ell)},\qquad U_\ell=U_{w_\ell},\qquad
R_\ell=U_\ell^\dagger EU_\ell,\qquad E_1=E,\quad E_0=I_3-E,\\
p_\mu^\pi(\ell,b)=\alpha_\ell\operatorname{Tr}(E_bU_\ell\mu U_\ell^\dagger),
\qquad b\in\{0,1\}.
\end{gathered}
\tag{95.1}
$$

则对每个数学密度矩阵 $\mu\succeq0$、$\operatorname{Tr}\mu=1$，

$$
\sum_b p_\mu^\pi(\ell,b)=\alpha_\ell>0,\qquad
\sum_{\ell\in\Lambda_\pi}\alpha_\ell=1,\qquad
F_\pi=\sum_\ell\alpha_\ell R_\ell\in[0,I_3].
\tag{95.2}
$$

$\operatorname{Tr}(F_\pi\mu)$ 是不条件化的原终端“是”质量。任意完整记录接受系数 $a(\ell,b)\in[0,1]$ 的数学扩张为

$$
F_{\pi,a}=\sum_\ell\alpha_\ell
 [a(\ell,1)R_\ell+a(\ell,0)(I_3-R_\ell)]\in[0,I_3].
\tag{95.3}
$$

物理二元事件只需 $a\in\{0,1\}$；一般系数不供应抽签设备。

证明。沿每条叶逐字使用 $A_{w_\ell}=\alpha_\ell\operatorname{Ad}_{U_\ell}$。每个 $\mathsf J$ 子节点各得父质量一半，$\mathsf N$ 保质量；有限完整停止截面把根质量一分配给全部叶，给出 (95.2)。这正是[关系丛 §8、定理 8.2](AURIC_FIB_RELATIONAL_BUNDLE_AND_PREDICTIVE_CLOSURE_THEORY.md#8-输出解析仪器预测观察者与受约束量子控制)及[相干重建 (26.3)–(26.5)](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md#26-有界有向词矩在完整递归原子中的闭合应用) 的既有完整树律在本源的应用。标记为叶的确定函数，故标记事件的质量是相应叶的原质量之和。终端某一结果可以为零，仍保留该格；叶质量本身严格正。(95.3) 的每项在 $0$ 与 $\alpha_\ell I_3$ 之间，故其和有界。

再用 (91.3)，同一叶的原五维复合满足

$$
\widehat K_{w_\ell}B=\sqrt{\alpha_\ell}\,BU_\ell,\qquad
\widetilde N=BNB^\dagger+(I_5-BB^\dagger),\qquad
P_5=BEB^\dagger.
\tag{95.4}
$$

于是原输入 $B\rho_0B^\dagger$、同一标签停止表及一次 $(P_5,I_5-P_5)$ 给出 $p_{\rho_0}^\pi$，两个终端、失配及超时均逐路径对应。对数学输入 $B\mu B^\dagger$ 也成立；这不是供应额外制备。五维接受效果满足 $B^\dagger\widehat F_{\pi,a}B=F_{\pi,a}$；此处只比较原 $B\mathbb C^3$ 扇区，不主张整个五维输入域上的近似。∎

## 96. 同一固定扫掠时序上的无条件近似取得

**定理 96.1（目标一致有限终点与完整记录误差）。** 对每个定义 95.1 的允许 $\theta,N$ 和每个 $\varepsilon>0$，存在一个预定有限动作串、检查点和终点 $T=T(\theta,N,\varepsilon)$，均不依赖 $d$ 或秩一目标 $P$，使对每个这样的 $P$ 有一个模型／目标依赖的有限停止表 $\pi_P$，满足

$$
\|F_{\pi_P}-P\|_\infty<\varepsilon.
\tag{96.1}
$$

并且，对同一完整叶档案（包括所有失配、超时及终端位），令 $P_1=P$、$P_0=I_3-P$，理想比较律为

$$
q_{P,\mu}^{\pi_P}(\ell,b)
 =\alpha_\ell\operatorname{Tr}(P_b\mu).
\tag{96.2}
$$

它具有与原实验完全相同的叶边缘 $\alpha_\ell$。用 $\operatorname{TV}(p,q)=\frac12\sum_{\ell,b}|p(\ell,b)-q(\ell,b)|$，有

$$
\sup_{\mu\succeq0,\ \operatorname{Tr}\mu=1}
\operatorname{TV}(p_\mu^{\pi_P},q_{P,\mu}^{\pi_P})<\varepsilon.
\tag{96.3}
$$

这里的理想律是数学比较对象，不是另装目标终端。

证明。只将 [V 定理 95.1、(100.3)](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_V.md#95-任意一个混合控制把实际原生闭包扩到-pu3) 的正词共轭稠密性作为供应。令
$\delta=\min\{\varepsilon/3,1/4\}>0$。秩一投影空间 $\mathcal P_1\simeq\mathbb{CP}^2$ 紧，取有限的严格 $\delta/3$ 网 $P^{(1)},\ldots,P^{(M)}$。构造一条仅作数学参照的正向标签词

$$
\omega=0v_1\cdots v_M,\qquad
S_0=V_0,\qquad S_j=U_{v_j}S_{j-1},
\qquad \|S_j^\dagger ES_j-P^{(j)}\|_\infty<\delta/3.
\tag{96.4}
$$

给定 $S_{j-1}$，只需由正词轨道逼近 $S_{j-1}P^{(j)}S_{j-1}^\dagger$，便能选择 $v_j$。每个 $v_j$ 可取非空：在任一固定首字母之后追加全部正词仍给稠密轨道。故各检查点严格递增；初始字母 $0$ 保证 $k=k(\omega)\ge1$。这里的 $S_j^\dagger$ 是计算中的共轭，不是执行逆。

将 $\omega$ 的每个 $0,1$ 换成 $\mathsf J$、每个 $N$ 换成 $\mathsf N$，得到一个固定块 $s_*$；检查点是 (96.4) 各前缀的结束处。没有执行 $\omega$ 中指定标签的权限，实际仍运行公平仪器。因为 (96.4) 给一个严格 $\delta$ 网，对任意块入口累计酉 $U$ 和任意目标 $P$，存在一个检查点 $j$ 满足

$$
\|U^\dagger S_j^\dagger ES_jU-P\|_\infty<\delta.
\tag{96.5}
$$

这是将整个网作 $U^\dagger(\cdot)U$ 后仍为网的结果；它同时覆盖所有可能入口，不重置累计酉。

预定重复同一个块 $L$ 次。在每个检查点，由实际已记录词计算 $R_w$；若 $\|R_w-P\|_\infty<\delta$，立即停止并用原终端，否则继续固定串。在最后一个检查点，命中优先；未命中也停止、调用原终端，并记超时 $t_\ell=1$。其余停止叶记 $t_\ell=0$。每个块另记一个失配位：已观测的块内标签是否至少一次不同于 $\omega$ 对应标签；最后一个部分块只检查已发生的标签。各块失配位的向量统记为 $m_\ell$，与完整原标签共同保留；失配不触发改门、复位、删支或重归一。对任意标记值 $(m,t)$，其不条件化总质量恰为 $\sum_{\ell:m_\ell=m,\ t_\ell=t}\alpha_\ell$，带终端位 $b$ 的质量为同一叶集合上 (95.1) 的和；失配和超时是不同标记。

条件于任一尚未停止的块入口历史，取 (96.5) 的 $j$。若该块到此检查点的全部实际标签符合参照词，便已命中，或已在更早检查点命中而停止。该前缀符合的原概率为 $2^{-k_j}\ge p_*=2^{-k}>0$，与输入态、入口历史和目标无关。故对每个存活入口，下一块内命中的条件概率至少 $p_*$。只由条件概率链式法则便得

$$
\tau:=\sum_{\ell:t_\ell=1}\alpha_\ell
 \le(1-p_*)^L.
\tag{96.6}
$$

选择有限 $L$ 使 $(1-p_*)^L<\delta$；这个选择和 $T=L|s_*|$ 只依赖 $\theta,N,\varepsilon$。块间的实际酉一般不同，也没有对 $N$ 进行随机抽样。上述估计只用实际仪器的公平标签，不要求某个随机游走的 Haar 混合或独立块增量模型。

每个非超时叶有 $\|R_\ell-P\|_\infty<\delta$；超时叶仍是原秩一投影，故距离至多一。由 (95.2)，

$$
\begin{aligned}
\|F_{\pi_P}-P\|_\infty
&\le\sum_\ell\alpha_\ell\|R_\ell-P\|_\infty
 \le\delta(1-\tau)+\tau<2\delta<\varepsilon,\\
\operatorname{TV}(p_\mu^{\pi_P},q_{P,\mu}^{\pi_P})
&=\sum_\ell\alpha_\ell
  |\operatorname{Tr}[(R_\ell-P)\mu]|
 \le\delta(1-\tau)+\tau<\varepsilon.
\end{aligned}
\tag{96.7}
$$

最后一步对全部数学密度矩阵一致。每个失配叶、两种终端结果和超时总质量均在 (95.1) 中；超时误差按其原质量计入，没有成功归一化或自由倍率。所有允许角度及混合 $N$ 的稠密性均由原供应承担，包括 $d=2/3$、非例外有理角和 $\langle\xi,N\xi\rangle=0$；这里没有删去这些情形。∎

**推论 96.2（原九列上的同一停止后缀及固定时序边界）。** 对定义 93.1 的实际未归一前缀 $r_i=A_{u_i}\rho_0$，$m_i=\operatorname{Tr}r_i=2^{-k(u_i)}$，在每个原前缀上下文的全部历史后执行同一个 $\pi_P$，忽略前缀身份与标签。则

$$
\begin{gathered}
p_i(\ell,b)=\alpha_\ell\operatorname{Tr}(E_bU_\ell r_iU_\ell^\dagger),\qquad
q_i(\ell,b)=\alpha_\ell\operatorname{Tr}(P_b r_i),\\
\sum_{\ell,b}p_i(\ell,b)=\sum_{\ell,b}q_i(\ell,b)=m_i,\\
\frac12\sum_{\ell,b}|p_i(\ell,b)-q_i(\ell,b)|<m_i\varepsilon,
\qquad
|\operatorname{Tr}[(F_{\pi_P}-P)r_i]|<m_i\varepsilon
\quad(1\le i\le9).
\end{gathered}
\tag{96.8}
$$

证明。用 $A_{u_iw}=A_wA_{u_i}$ 代入 (95.1)，再用 $r_i\succeq0$ 和 $|\operatorname{Tr}(Hr_i)|\le\|H\|_\infty m_i$ 重复 (96.7)。其他前缀历史也执行同一后缀，全部留在所在上下文的完整档案中；(96.8) 只是其中 $u_i$ 事件的原质量，并未制备 $r_i/m_i$。由 (95.4)，它们在原五维逐路径同样成立。

停止表可使 §92 第一处仪器的两条标签历史在不同检查点调用终端；因而 (92.7)–(92.8) 所需的共同剩余词 $t$ 不再存在，尽管所有尚未停止路径的 $N$ 位置仍由同一个串决定。取 $P=P_N$、$\varepsilon<1/12$，(96.1) 与 (92.1) 直接说明所获效果不在 $\mathcal B_N$。将早停路径虚填到共同终点会改变其终端效果，不能用填充后的最后一次终端替代已发生的早期终端。因此这是改变停止接口后越过原固定终点限制，与原定理的适用域相容。∎

## 97. 混合调用上限与精确有限取得的两个边界

**定理 97.1（接近恒等的实际混合控制无统一调用上限）。** 作为数学比较域，允许每个节点按过去标签选择 $\mathsf J$、同一个 $\mathsf N$ 或调用一次原终端并停止；每棵树有限、完整，每条路径至多调用 $B\in\mathbb N$ 次 $N$，原生仪器调用数可为任意有限数，终端接受系数为 (95.3) 的 $[0,1]$ 系数。此域比定义 95.1 大，不将标签依赖的动作选择或随机接受安装为本源权限。对每个这种树／系数 $\pi$，

$$
\|F_{N,\pi}-P_\xi\|_\infty
 \ge\frac25-2B\|N-I_3\|_\infty.
\tag{97.1}
$$

同一界也适用于这些效果的数学凸包及算子范数闭包。于是对任一固定 $0\le\varepsilon_0<2/5$，不存在一个有限 $N$ 调用上限，在全部允许安装 $[N,P_\xi]\ne0$ 上以这些完整效果逼近 $P_\xi$ 到误差 $\varepsilon_0$，即使各安装可选择各自的模型依赖有限策略。

证明。固定给定 $N$ 下已选好的整棵树和接受表，以 $I_3$ 替换每个 $N$，只作比较，不重新选择树。公平标签使叶集、$\alpha_\ell$ 及接受系数均不变。原 $U,W$ 固定 $\xi$，故每个原生 $V_j$ 与 $P_\xi$ 对易；$|\xi^\dagger q|^2=1/2$。所以替换后的每个终端投影 $R_\ell^I$ 都满足 $\operatorname{Tr}(P_\xi R_\ell^I)=1/2$。置

$$
Z=4P_\xi-I_3,\qquad
\operatorname{Tr}(ZP_\xi)=3,\quad \|Z\|_1=5,\quad
\operatorname{Tr}(ZR_\ell^I)=1,\quad
\operatorname{Tr}[Z(I_3-R_\ell^I)]=0.
\tag{97.2}
$$

由完整叶质量之和为一，

$$
\operatorname{Tr}(ZF_{I,\pi})
 =\sum_\ell\alpha_\ell a(\ell,1)\le1,
\qquad
\|P_\xi-F_{I,\pi}\|_\infty\ge(3-1)/5=2/5.
\tag{97.3}
$$

逐叶酉乘积的望远镜差给

$$
\|U_\ell^N-U_\ell^I\|_\infty\le B\|N-I_3\|_\infty,
\qquad
\|R_\ell^N-R_\ell^I\|_\infty\le2B\|N-I_3\|_\infty.
\tag{97.4}
$$

同一叶接受项的差为 $(a(\ell,1)-a(\ell,0))(R_\ell^N-R_\ell^I)$，系数绝对值至多一。乘原 $\alpha_\ell$ 求和得到 $\|F_{N,\pi}-F_{I,\pi}\|_\infty\le2B\|N-I_3\|_\infty$，与 (97.3) 合并即为 (97.1)。对数学凸组合也同时组合对应的 $F_{I,\pi}$；(97.3) 的线性见证仍成立，扰动界仍相同。再取范数极限，得到所述闭包结论。不能仅因范数下界而不经此见证步骤就宣称凸化保界。

实际反例族取

$$
H=\xi e^\dagger+e\xi^\dagger,\qquad
N_t=\exp(\mathrm i tH),\quad 0<t<\pi/2,\qquad
\|N_t-I_3\|_\infty=2\sin(t/2).
\tag{97.5}
$$

$N_t\xi=\cos t\,\xi+\mathrm i\sin t\,e$，故每个成员都满足 $[N_t,P_\xi]\ne0$。对任何有限 $B>0$，取 $t$ 使 $4B\sin(t/2)<2/5-\varepsilon_0$，(97.1) 即排除全部相应策略；$B=0$ 已由 (97.3) 排除。$N=I_3$ 从未作为允许安装，只是比较极限。结论只涉及调用计数，不给经过时间、最优资源或编译代价。定理 96.1 允许终点依赖已安装 $N$，故不受反例族的统一上限阻碍。∎

**命题 97.2（精确有限取得的必要词支撑）。** 对固定允许 $\theta,N$，若一棵有限完整树的 (95.3) 恰为秩一投影 $P$，则每个有正质量的叶必有

$$
R_\ell=P,\qquad a(\ell,1)=1,\qquad a(\ell,0)=0.
\tag{97.6}
$$

特别地，精确目标必须属于原有限词的可数集合

$$
\mathcal O_{\theta,N}=
 \{U_w^\dagger EU_w:w\in\{0,1,N\}^*\}.
\tag{97.7}
$$

证明。直接应用 V 命题 109.2、(109.4) 的正和支撑论证于本源的叶项：正项之和为 $P$ 时，每个项的值域均在 $\operatorname{ran}P$ 内。$I_3-R_\ell$ 秩二，所以 $a(\ell,0)=0$；若 $a(\ell,1)>0$，则 $R_\ell=P$。取迹有 $1=\sum_\ell\alpha_\ell a(\ell,1)$，而 $\sum_\ell\alpha_\ell=1$、每个 $\alpha_\ell>0$、$a(\ell,1)\le1$，迫使全部 $a(\ell,1)=1$。这证明必要条件。有限词可数而 $\mathcal P_1$ 不可数，所以对固定模型有不可数多个目标不能精确有限取得；这与 (96.1) 的任意正误差近似不同。(97.7) 只给必要限制，不将单个命中词或其正权重当作整个完整树可精确取得的充分刻画，也不将此有限支撑论证用于范数极限。∎

## 98. 原单终端的二元模拟外形与三结果障碍

**命题 98.1（本源的单终端包含及正交三态见证）。** 对定义 95.1 的停止策略，甚至定理 97.1 的较大有限因果比较域，允许终端后将完整记录数学重标记为 $a\in\{1,2,3\}$。写 $c(a\mid\ell,b)\ge0$、$\sum_a c(a\mid\ell,b)=1$；随机系数只为外扩比较，未安装外部硬币。其效果必为

$$
M_a=\sum_\ell\alpha_\ell
 [c(a\mid\ell,1)R_\ell+c(a\mid\ell,0)(I_3-R_\ell)],
\qquad \sum_aM_a=I_3.
\tag{98.1}
$$

对每个正交秩一基 $(P_1,P_2,P_3)$，有

$$
\frac13\sum_{i=1}^3\operatorname{Tr}(P_iM_i)\le\frac23,
\qquad
\max_i\|M_i-P_i\|_\infty\ge\frac13.
\tag{98.2}
$$

这些界在上述效果三元组的数学凸包及按 $\max_a\|\cdot\|_\infty$ 所取闭包上保持。因而该单终端域不能任意精确逼近任一尖锐正交三结果测量。

证明。(98.1) 由原完整叶律直接求和；$\alpha_\ell$ 与数学输入态无关。因此它具有 [Guerini–Bavaresco–Terra Cunha–Acín，1705.06343v2，§II 式 (2)–(4)、§IV](https://arxiv.org/html/1705.06343v2) 的成熟二结果模拟形式：其模拟器为 $(R_\ell,I_3-R_\ell)$，混合权重为原 $\alpha_\ell$，后处理为 $c$。这只是包含关系，不授予独立选择这些模拟器或任意混合权重的权限。

令 $x_{\ell i}=\operatorname{Tr}(P_iR_\ell)$，则 $0\le x_{\ell i}\le1$、$\sum_i x_{\ell i}=1$。逐叶有

$$
\begin{aligned}
\sum_i\operatorname{Tr}\big(P_i[
 c(i\mid\ell,1)R_\ell+c(i\mid\ell,0)(I_3-R_\ell)]\big)
&\le\max_i x_{\ell i}+\max_i(1-x_{\ell i})\le2.
\end{aligned}
\tag{98.3}
$$

乘 $\alpha_\ell$ 并求和即得分数上界。若 $\max_i\|M_i-P_i\|_\infty=\eta$，每项正确响应至少 $1-\eta$，故 $1-\eta\le2/3$。等价地，在至少一个数学基态输入上，与理想三标签分布的 TV 距离至少 $1/3$。这些输入只是数学分离见证，不是给装置增加三个制备。分数是效果三元组的连续线性泛函，所以其上界在所述凸闭包保持，再推出同一距离界。

这里的闭包始终是单次原终端之后的经典重标记；不含多次系统测量、额外制备、相干读取标签或终端后的量子接续。分别使用不同 $\pi_{P_i}$ 逼近三个二元效果不提供一个共同三结果 POVM；概率效果的逼近也不确定后测量后继仪器。通用可模拟性是所引文献的供应，(98.1) 的原叶权重对应及其在本 qutrit 合同中的 (98.2) 是此处消费的具体边界。∎

## 99. 全词经典表示、标定及预测商的保留边界

**命题 99.1（停止不排除原全词经典模型）。** 本卷定理 85.1 的可数群模型与连续纯投影空间模型，在每个有限因果标签策略、原双终端及其完整失配／超时档案上，仍精确匹配本源唯一原制备的概率。定理 84.2 的未来零观察前提 (84.4)–(84.5) 仍量化全部合法未来，不能由有限停止表替代。

证明。固定表后，每个叶仍是同一个原有限词 $w_\ell$，终端权重为 $p(w_\ell,b)$。两个经典模型对全部这样的词与两终端逐项一致，故对这棵树逐叶一致；确定标记与任何所述后处理只对相同项求和。原标签公平使停止截面的总质量仍为一。另一方面，一个有限停止表只选有限个词，(84.4)–(84.5) 要求被删方向在每个未来词下为零；有限树的等式不蕴含此全称前提。即使给出全部有限因果树的等式，由于固定词测试也在其中，它们与原全词合同相容，而 §85 已有不同的无限隐藏实现。因此 (96.1) 在供应的量子模型内解决取得接口，不从停止本身选择复量子本体。∎

**命题 99.2（公平前终端标签不标定未知模型）。** 对任意两个允许的 $d,\theta,N$，若动作串、检查点、有限停止位表及标记规则固定相同，则调用终端以前的完整叶标签／停止／失配／超时边缘律相同，均为 $\alpha_\ell=2^{-k(w_\ell)}$。这些标签自身不能区分这两个模型；将模型依赖表作为输入不构成模型的观察取得。

证明。每次实际仪器在任意输入上都有 $\operatorname{Tr}(A_jX)=\operatorname{Tr}(X)/2$，$N$ 保迹。相同前缀导致相同下一动作或停止，故归纳得到相同叶质量，所有前终端标记都是相同标签的函数。终端位的条件律可以随模型改变，不在此不可区分结论中。若各模型另供各自的停止表，表已携带经典信息，不能将表间差异计为标签对未知参数的标定能力。∎

**定义 99.3（六种不同的供应问题）。** 本源的结论按下列量词区分。

| 问题 | 此处的数学范围 |
| --- | --- |
| 已知模型存在性 | (96.1)–(96.7) 对每个固定允许 $\theta,N$ 和每个 $\varepsilon>0$ 给目标一致的有限串／终点，再对每个 $P$ 给停止表；不依赖 $d$。 |
| 供应有限建议 | 有限串、检查点及全部停止位可以作为有限经典建议给定；随后只需读取实际标签选择停止位。证明中的精确矩阵比较不是新增系统读口。 |
| 可计算输入的有效合成 | 需要明确输入表示、误差证书与终止的生成程序；此处不证明从可计算 $\theta,N,P$ 到这些有限建议的编译或复杂度结论。 |
| 未知模型的实际取得 | 标签的模型盲性由命题 99.2 给出；所需模型／目标标定尚未从原单制备、一次终端取得。 |
| 跨安装的统一费用 | (97.1) 排除固定误差小于 $2/5$ 时的统一有限 $N$ 调用上限；没有经过时间或最优总资源结论。 |
| 有限噪声／样本认证 | 精确存在及原始质量等式不供应停止表可靠性、未知参数置信界、全未来完备或后继仪器的有限数据认证。 |

复 Hilbert、Born 配对与 CP 分支仍是 V 定义 54.1、假设 54.2 和定义 91.1 的源输入；[相干重建定义 20.2、应用 26.2–27.1、定义 28.1 与 34.1](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md) 分别保留复词正核、共同交叉核、参考和复合合同。一般不确定性、条件酉的信息保留或二元效果取得均不替代这些前提。

## 100. 原始供应对应与共同实现的具体缺项

**定义 100.1（源合同及文献归属）。** 本节比较的仓内来源取同一修订 $\mathtt{e30c151ba97e8290d5969cb9e29b6adc29090582}$。§§95–99 是 `repo-derived` 的源特定综合：承重点是固定动作扫掠、仅停止反馈的完整质量取得、近恒等实际混合族的调用障碍，以及该权限增长后的单终端／经典表示边界。不主张世界范围新颖性；正词稠密、有限树律、正和支撑和一般测量可模拟性均按原供应使用。

| 原始来源 | 所用陈述与本源对应 |
| --- | --- |
| 预测波 V §§54、91–95、(100.3)、105–110；本卷 §§80、84–94 | 原 $B$、唯一 $\rho_0$、公平 $A_j$、同一个 $N$、双终端质量、九个未归一前缀、正词共轭闭包与全轨道锥。V (109.4) 供应正和的秩一支撑事实；§92 的固定终点见证不涵盖标签早停。这些供应不新增控制或制备。 |
| Gregoratti–Werner，[quant-ph/0209025v1，§II.3.1、Proposition 2、式 (7)](https://arxiv.org/html/quant-ph/0209025v1) | 给定 Kraus 分解 $t_\alpha$ 可由通道 $R_\alpha$ 完全恢复，当且仅当 $t_\alpha^*t_\alpha=c_\alpha I$；同维时相应恢复为逆酉共轭。本源 $V_j/\sqrt2$ 满足比例酉条件，但恢复通道的可调用性没有供应；(96.4) 没有执行这些逆。 |
| Gregoratti–Werner，[quant-ph/0403092v1，§III.1 Proposition 1、式 (8)–(9)；§III.2 Proposition 2、式 (10)–(12)](https://arxiv.org/html/quant-ph/0403092v1) | 同维完全恢复、输入无关分支律及多步酉校正的成熟条件；其控制对象是另供的恢复通道。公平标签不携带输入态信息，与本源相容；知道标签不等于取得逆控制。 |
| Halil-Shah–Oi，[1401.8004v1，§II，尤其单比特随机门与停止段](https://arxiv.org/html/1401.8004v1)；[1303.2066v1，§3.1、式 (4)](https://arxiv.org/html/1303.2066v1) | 前者已讨论固定程序、随机门乘积及按目标误差停止；后者讨论随机 ADQC 门逼近及命中统计。它们供应随机／停止控制的成熟思想，使用其实际辅助比特准备、耦合和测量。这里另需证明原 qutrit、每个允许 $N$、一个目标无关的预定 $\mathsf J/\mathsf N$ 串及有限超时质量的 (96.4)–(96.7)；不把其效率或复合资源搬入。 |
| Paetznick–Svore，[1311.1074v2，§3、Figure 2 与四步 RUS 定义](https://arxiv.org/html/1311.1074v2) | 辅助比特准备、联合酉、辅助测量、失败后恢复再重复构成其 RUS 合同。其 $R_i^\dagger$、新辅助准备、门库与成本不在此源中；本源失配路径继续原累计酉，不作该恢复。 |
| Varjú，[1209.1745v3，§1.5、Lemma 5、Theorem 6](https://arxiv.org/html/1209.1745v3) | 紧半单 Lie 群上的尺度直径／谱隙关系有明确有限生成集或概率测度；Lemma 5 使用含单位元的有限集。它不将本源固定串变成均匀选门、含惰性步的随机采样，也不供应本文的调用上限或 Haar 速率。 |
| Borda，[1906.09432v1，§1 Theorems A–C、Theorem 1](https://arxiv.org/html/1906.09432v1) | i.i.d. 群增量下，弱收敛需 adapted 与严格非周期；TV 收敛还需某卷积有非零绝对连续部分，任意给定 Borel 集的强等分布结论也有该绝对连续前提。本文没有 i.i.d. 的 $N$ 采样；每个固定有限长度的分布只有有限多个原子，对连续群的 Haar 测度为奇异，不能冒用该 TV 前提。(96.6) 只是逐入口正概率与条件链式法则。 |
| Guerini–Bavaresco–Terra Cunha–Acín，[1705.06343v2，§II 式 (2)–(4)、§IV](https://arxiv.org/html/1705.06343v2) | 一般经典预／后处理及低结果数模拟是成熟供应。(98.1) 只将实际叶质量嵌入其二结果模拟外集；不将外集每个 POVM、独立混合或硬币赋予本源。 |

**定义 100.2（相邻取得结果的源／动作／记录对应域）。** 下列比较只比较已声明合同，不给不同场律一个未经证明的共同实现映射。

| 钉版相邻来源 | 实际源、动作及记录 | 与本源的缺失对应 |
| --- | --- | --- |
| [Atomic Generation Acquisition III，§§1–16，尤其定义 2.2–2.4、8.1、边界 16.1–16.3](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_III.md) | 持久有序原生材料和有理场 $T_t=(4I+A_t)/8$；A 的原始 Tick／精确读口及分离间隔，C 的生长后时钟和数字 Read$(j,p)=\lfloor2^px_{\ell_j}\rfloor+\zeta$。其已知 alpha 上的 Reset、Add、验证读及实际权利属于已供准备，C 的滋扰选择是无概率的集合值合同。 | $\zeta$ 不是这里的公平量子标签；原生读口、重置、已取得几何及费用不映成 $A_j,N,E$ 的可调用操作。该卷 16.3 仍要求共同装置保实际准备、操作、后继、完整返回及权利。 |
| [Recovery Geometry III，§§112–120，尤其 (112.1)–(112.2)、定义 112.4、定理 113.4、命题 114.2、117.3](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY_III.md) | 地址标定窗和边权 $\ell_p/100$ 的持久对称有理矩阵；任意未知旧场经实际 split sweep 保零延伸，再由已挣得几何的根窗口取得推进后的预测器。根 Add／Tick 脉冲准备是另供的实际历史合同；原始 Tick 可离开该历史像。 | 根 Read、脉冲控制、标定循环性和未知场取得没有与本源唯一纯准备、公平仪器和一次二元终端的同源映射；其可逆坐标或恢复值不提供本源逆门或历史回退。 |
| [Moving Trace Recovery，§§30–36，尤其定义 30.1、定理 30.2、31.2、32.1 与命题 34.1、35.1](FIB_MOVING_TRACE_RECOVERY_AND_SHARP_CALIBRATED_CONTINUATIONS.md) | 同一逐项严格正的实秩一迹一矩阵 $P$、整段共同多项式 $H,D$、固定原时钟和已取得向量 $Z(W)_i=H(i)\operatorname{tr}(A_iP)+D(i)$；严格逃逸距离 $e(y)>\rho$ 给兼容完整世界的界，接触 $e(y)=\rho$ 有相反实例。这里的实矩阵未被假定 Hermitian PSD。 | 有界误差读口、共同增益／偏置和该记录几何不提供 qutrit Born 标定或本源噪声证书；分别的取得与最优量不能拼成一台共同装置的同时实现。 |

**定义 100.3（仍缺的共同接口问题）。** 在上述合同下，量子起源目标仍含以下具体数学问题。

1. 共同原生／量子实现须给出保类型的同一准备、操作和记录映射，逐合法历史保两终端及失配／停止质量，并保其实际后继；若还主张原生服务合同，则拒绝、返回、绑定和权利也须对应。相邻卷各自的场律、准备和 Read 不能仅靠同名或可逆编码取得这种映射。
2. 物理锚定的相干记录／共同参考须取得相干重建 (27.1) 所需的交叉关系及可操作比较，且去相干边缘仍为本源原完整记录；各自内部核、§85 的经典全词模型或一个形式上的分支等距不决定这项相干接口。有限参考与复合的共同实现还须保其声明的联合正锥和组合，不能由单系统秩一二元效果补出。
3. 原终端之后的后继仪器、共同多结果测量和有限噪声／样本认证各有未供条件。(98.2) 已在当前单终端域给出三结果的正障碍；(96.3) 是对精确已知模型的完整概率律界，不是这些新增接口的认证。

这些缺项不撤销条件定理 96.1，也不改变 §§84–85 的经典表示边界；它们界定了从同源预测记录与停止取得继续走向共同量子实现所需的新关系。∎

## 追加锚（本行以下为增补区）
