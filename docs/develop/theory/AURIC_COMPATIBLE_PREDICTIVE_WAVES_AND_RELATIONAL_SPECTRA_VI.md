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
