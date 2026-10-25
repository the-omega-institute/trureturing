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
