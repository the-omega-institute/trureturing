# 精确二次乘法与原连续幂实际纤维的统一有限截断

## 182. 原系数源、预固定正枢轴与全次数结论

**定义 182.1（原域与实际完成纤维）。** 设 $F$ 为任意特征零域，$D/F$ 为可分**域**扩张，$[D:F]=2m$，$m\ge7$。任取本原元 $\theta$，记其首一最小多项式为 $f(T)$，固定非零体积形式 $\nu:\det_FD\to F$，并置

$$
C=\langle1,\theta,\ldots,\theta^{m-1}\rangle_F,
\quad V=F[T]_{\le m-2},\quad N=\dim_FV=m-1,
\quad W=\bigwedge^2V,\quad h=\left\lfloor\frac{m-1}{2}\right\rfloor.
\tag{182.1}
$$

对同一个 $D$ 中的实际 $m$ 维窗口 $C'$，用包含帧 $E_{C'}$ 和乘法 $M_x$ 定义

$$
P_{C'}(x)=\nu\bigl(\det[E_{C'},M_xE_{C'}]\bigr).
\tag{182.2}
$$

在有限 Galois 分裂域中保持原嵌入标签及其顺序，写

$$
P_{C'}(x)=\sum_{|I|=m}c_I(C')x_I,
\qquad c_I=\alpha\epsilon_Ip_Ip_{I^c}.
\tag{182.3}
$$

这里 $p_I$ 是实际帧的行子式，$\epsilon_I$ 是互补行序符号，$\alpha$ 来自 $\nu$。令 $\mathcal U$ 为所有 $p_I\ne0$ 的统一开集，$T_D=(\operatorname{Res}_{D/F}\mathbb G_m)/\mathbb G_m$。采用 [039，定义 111.1、命题 111.2、定理 113.1](https://github.com/the-omega-institute/trureturing/blob/e5f5994ce4e5c1e553f9fcafb37a5e8fd21f1dbb/docs/develop/theory/AURIC_R5_039_UNIFORM_COEFFICIENT_NORMALIZATION_AND_HIGHER_DEGREE_DEFECT.md) 的原系数像环 $S_F$、实际商 $X_D=\mathcal U/T_D$ 及 Gale 对合 $\iota$。$S_F$ 的分裂扩底是原比值 $(c_I/c_{I_0})^{\pm1}$ 的像代数；$B_F=\mathcal O(X_D)^\iota$ 是它的有限正规化。令 $p=[P_C]$，$y$ 为其唯一正规化点，置

$$
S=(S_F)_p,\quad B=(B_F)_y,\quad
\mathscr T=\widehat S,\quad\mathscr B=\widehat B,
\quad J:\mathfrak m_S/\mathfrak m_S^2\longrightarrow
\mathfrak m_B/\mathfrak m_B^2.
\tag{182.4}
$$

完成均取各自极大理想拓扑。在 [042，§§132--134](https://github.com/the-omega-institute/trureturing/blob/fd9d6f7737ac0bf2274eddc48d5bde4ac0da1db6/docs/develop/theory/AURIC_R5_042_UNIFORM_ORIGINAL_QUARTIC_LIFTS_BEYOND_QUADRATIC_PRODUCTS.md) 的原域对合相容横截面中，正变量为 $U$，负变量为 $Y$，且

$$
\mathscr B=F[[U,Y]]^{Y\mapsto-Y},\qquad
\dim U=a=\frac{m(m-1)}2,\quad
\dim Y=b=\frac{(m-1)(m-2)}2.
\tag{182.5}
$$

负线性坐标采用 $e_i=T^i\in V$ 与

$$
e_i\wedge e_j\longleftrightarrow
z_{ij}(Y)=Y(\theta^{i+1},\theta^j)-Y(\theta^i,\theta^{j+1}),
\qquad 0\le i,j\le m-2
\tag{182.6}
$$

的识别。记正余切为 $P_+^\vee$，$H_d=\operatorname{Sym}^dW$，并定义

$$
w:H_2\longrightarrow\bigwedge^4V,\qquad
w(\xi\zeta)=\xi\wedge\zeta,\qquad K=\ker w.
\tag{182.7}
$$

预先固定任意一组合法原 $F$ 正枢轴 $s=(s_1,\ldots,s_a)\in\mathfrak m_S^a$：若 $J[s_i]=(\ell_i,q_i)\in P_+^\vee\oplus H_2$，则 $\ell_i$ 构成 $P_+^\vee$ 的基。“正”只指对合的正特征空间，不要求 $F$ 有序。始终使用

$$
B_{0,s}=\mathscr B/(s)\mathscr B\simeq F[[Y]]^{Y\mapsto-Y},
\quad\pi_s:\mathscr T\longrightarrow B_{0,s},
\quad A_s=\operatorname{im}\pi_s=\mathscr T/\mathfrak L_s,
\quad\mathfrak L_s=\ker\pi_s.
\tag{182.8}
$$

在覆盖 $F[[Y]]$ 中令 $\mathfrak q=(Y)$，在 $B_{0,s}$ 中令 $\mathfrak n_s$ 为零常数极大理想，在 $A_s$ 中令 $\mathfrak m_s$ 为极大理想。只由定义得到 $(s)\mathscr T\subseteq\mathfrak L_s$；以下没有把这个包含换成等号。

**定理 182.2（任意偶数域次数的实际高阶幂与有限余切）。** 对定义 182.1 的每个 $F,D,\theta$，可以在选择枢轴以前，选定 $K$ 的一组 $F$ 基 $k_1,\ldots,k_t$ 及同一个原源中的元素 $\gamma_1,\ldots,\gamma_t\in\mathfrak m_S$，使对每个合法、事先固定的 $s$ 均有

$$
J[\gamma_i]=(0,k_i),\qquad
g_{s,i}:=\pi_s(\gamma_i)=k_i+O(Y^4).
\tag{182.9}
$$

置 $I_s=(g_{s,1},\ldots,g_{s,t})A_s$。对每个整数 $q\ge h$，有真正的代数理想幂等式

$$
\boxed{
\pi_s\bigl((\gamma_1,\ldots,\gamma_t)^q\mathscr T\bigr)
=I_s^q=\pi_s(\mathfrak m_{\mathscr T}^q)
=\mathfrak m_s^q=\mathfrak n_s^q
=B_{0,s}\cap\mathfrak q^{2q}.
}
\tag{182.10}
$$

尤其右侧的每个完整偶级数都有原 $\mathscr T$ 中的提升，且有有限个 $q$ 重乘积之和的表达式。共同的基提升不依赖 $s$；给定目标元素的完整提升及其高阶修正允许依赖这个已经固定的 $s$ 和该目标元素。

对 $r\ge1$ 定义实际首项空间

$$
\begin{aligned}
C_{s,r}&=A_s\cap\mathfrak n_s^r,\\
M_{(s,r)}&=\operatorname{in}_{2r}(C_{s,r})\subseteq H_{2r},\\
D_{(s,r)}&=\operatorname{in}_{2r}
 \bigl(\mathfrak m_s^2\cap\mathfrak n_s^r\bigr)\subseteq H_{2r}.
\end{aligned}
\tag{182.11}
$$

这里 $\operatorname{in}_{2r}$ 仅在所有较低项已经为零的元素上取 $2r$ 次齐次项，允许该齐次项也为零。实际余切 $Q_s=\mathfrak m_s/\mathfrak m_s^2$ 的下降滤过

$$
\mathcal F^{2r}Q_s=(C_{s,r}+\mathfrak m_s^2)/\mathfrak m_s^2
\tag{182.12}
$$

满足

$$
\boxed{
\mathcal F^2Q_s=Q_s,\quad \mathcal F^{2h}Q_s=0,\quad
\mathcal F^{2r}Q_s/\mathcal F^{2r+2}Q_s
\simeq M_{(s,r)}/D_{(s,r)}\quad(1\le r<h).
}
\tag{182.13}
$$

第一层是 $M_{(s,1)}=K$、$D_{(s,1)}=0$；第二层是 $M_{(s,2)}=J_4(A_s)$、$D_{(s,2)}=K^2$。更高层必须保留实际 $D_{(s,r)}$，不能自动用 $K^r$ 代替。因此全部余切信息只在 $Y$ 次数 $2,4,\ldots,2h-2$；这里没有断言各层的实际子空间已经分类。

证明。§183 给出同一个原源、实际消元和拓扑接口。§184 在本定理的证明中复用经典实际乘法定理，取得所有特征零有限维空间的精确齐次输入与其满性阈值。§185 在原完成源内实施逐阶修正，证明 (182.10)。§186 对实际首项取商，证明 (182.13)，并给出只含有限原源数据的完整公式。各部分共同构成本定理的证明。

## 183. 原域完成、实际消元与共同基提升

**引理 183.1（全 $m\ge7$ 的原源接口）。** 在定义 182.1 的全部假设下，$\mathscr T$ 是完备分离的 Noetherian 局部 $F$ 代数，剩余域为 $F$；$\pi_s$ 保持常数，且

$$
\mathfrak m_s=\pi_s(\mathfrak m_{\mathscr T})
=A_s\cap\mathfrak n_s,
\qquad
\mathfrak n_s^r=B_{0,s}\cap\mathfrak q^{2r}\quad(r\ge1).
\tag{183.1}
$$

$\pi_s$ 对源极大理想拓扑及目标 $\mathfrak n_s$ 拓扑连续，目标完备分离。全部实际二次像为 $K$，并有 (182.9) 的共同原源基提升。

证明。连续幂窗口的最大子式是非零 Vandermonde 行列式，所以属于统一开集。039，命题 111.2、定理 112.1、113.1 给原 $F$ 上有限型像环与有限正规化。039，定理 115.1、117.1 给本原固定点及横截面，两边实际剩余域都是 $F$。在 $S$ 处局部化后的有限正规化只有 $y$ 一个极大理想，故是 $B$。有限维局部代数 $B/\mathfrak m_SB$ 的极大理想幂零，所以 $\mathfrak m_SB$ 与 $\mathfrak m_B$ 的幂拓扑共尾。有限模完成的正合性及张量公式给

$$
\mathscr T\hookrightarrow\mathscr B=B\otimes_S\mathscr T.
\tag{183.2}
$$

这里所用的标准完成结论可见 [Stacks Project，Lemma 10.97.1，Tag 00MA](https://stacks.math.columbia.edu/tag/00MA)。因此源的完备性与分离性在原 $F$ 上成立，不需要扩大剩余域。

为明确横截面的原族对应，042，§133 使用 $\ell(x)=\operatorname{Tr}_{D/F}(x/f'(\theta))$ 及残数迹配对 $\langle x,z\rangle=\ell(xz)$。其在幂上满足 $\ell(\theta^j)=0$（$0\le j\le2m-2$）、$\ell(\theta^{2m-1})=1$，所以 $C$ 最大各向同性。原域双曲帧给 $Z=U+Y$，$U$ 交错、$Y$ 对称；原乘法环面切像正是 Hankel 空间。取原 $F$ 线性补空间后，实际商映射的切映射是同构。形式逆函数定理于是给 (182.5)，并由乘法核识别给 (182.6)。这里的 $N=m-1$；评价多项式的参数 $d=m-4$ 不是负识别中 $V$ 的维数。

040，定理 122.1 的 (122.8)、命题 122.2，在原 $F$ 上给完整耦合像 $M=\operatorname{im}J$：

$$
\operatorname{pr}_{P_+^\vee}M=P_+^\vee,
\qquad M\cap(0\oplus H_2)=0\oplus K.
\tag{183.3}
$$

这不是仅计算负投影的结论。对任意合法 $s$，记 $L_s(U)=(\ell_i(U))_i$、$q_s=(q_i)_i$。042，定义 134.1 的实际方程给唯一偶解

$$
U=\phi_s(Y)=O(Y^2),\qquad
(\phi_s)_2=-L_s^{-1}q_s.
\tag{183.4}
$$

其依据是等变形式换元 $(U,Y)\mapsto(s,Y)$ 可逆；在这组坐标中取二阶群不变量再取商，就得到真实的 $B_{0,s}$。任意源余切类 $(\ell,q)\in M$ 的纤维二次符号因而是

$$
R_s(\ell,q)=q-\ell L_s^{-1}q_s.
\tag{183.5}
$$

枢轴类张成的 $H_s$ 满足 $M=H_s\oplus(0\oplus K)$：先用正投影唯一减去枢轴类，余项由 (183.3) 落在 $0\oplus K$。映射 $R_s$ 消去 $H_s$，在 $0\oplus K$ 上为恒等。正规化极大理想平方限制到纤维至少四阶，完成又不改变有限维源余切，所以这给全部实际二次像，正是 042，引理 134.2 的全次数结论。

每个 $(0,k_i)\in M$ 都有原 $\mathfrak m_S$ 中的代表 $\gamma_i$。式 (183.5) 在这些类上的值恒为 $k_i$，故同一批代表满足所有合法 $s$ 的 (182.9)。这正是 [045，引理 170.1](https://github.com/the-omega-institute/trureturing/blob/a5a20d82984bbb32282adccee504bbcd41fc7ac1/docs/develop/theory/AURIC_R5_045_FAITHFUL_QUARTIC_DETECTION_AND_COMPLETE_ORIGINAL_EVALUATOR_RELATIONS.md) 的共同提升，不需要从次数十四的特殊结论外推。

映射 $\pi_s$ 保持 $F$ 与剩余类。非零常数源元素在 $\mathscr T$ 中可逆，其逆的像仍在 $A_s$；零常数像元素在 $B_{0,s}$ 中不可逆。因此 $A_s$ 的极大理想恰为零常数元素，并得到 (183.1) 的第一个等式。目标极大理想由有限多个二次单项式生成。任意次数至少 $2r$ 的偶单项式均可除去一个次数 $2r$ 的单项式因子，后者是 $r$ 个二次单项式之积；对有限多个可选因子固定分配顺序，把级数按该因子分组，余系数仍为偶级数。这给有限代数理想表达式，证明 (183.1) 的第二式。目标拓扑遂与偶级数的 $Y$ 阶数拓扑相同，完备分离；$\pi_s(\mathfrak m_{\mathscr T}^j)\subseteq\mathfrak n_s^j$ 给连续性。证毕。

## 184. 原族证明中的经典实际乘法输入

本节是定理 182.2 的齐次部分。暂令 $F$ 为任意特征零域，$V$ 为任意有限维 $F$ 空间，$N=\dim V$，$W=\bigwedge^2V$，$H_d=\operatorname{Sym}^dW$，$K=\ker(H_2\to\bigwedge^4V)$；不要求这些临时对象来自域窗口。记 $\rho=\lfloor N/2\rfloor$。若 $z$ 为分拆，置 $z^{[2]}=(z_1,z_1,z_2,z_2,\ldots)$，$\ell(z)$ 为非零部分数，$M_z(V)$ 为 $H_{|z|}$ 中相应的 Schur 分量。空分拆对应常数。

这里需要的输入是**恰好** $r$ 个 $K$ 因子的乘法像

$$
K^r=\operatorname{im}\bigl(\operatorname{Sym}^rK\xrightarrow{\mathrm{mult}}H_{2r}\bigr),
\qquad K^0=F.
\tag{184.1}
$$

以下完整说明经典结果如何给出

$$
K^r=\bigoplus_{\substack{z\vdash2r\\\ell(z)\le r\\2\ell(z)\le N}}M_z(V),
\qquad M_z(V)\simeq\mathbb S_{z^{[2]}}V,
\tag{184.2}
$$

以及对 $N\ge2$、$r\ge1$ 的精确阈值

$$
K^r=H_{2r}\quad\Longleftrightarrow\quad r\ge\rho.
\tag{184.3}
$$

这些是经典实际乘法理论的后果，作为原族推导的中间输入使用。

先明确与普通子式理想幂的经典结论的对应及区别。[Winfried Bruns，*Algebras defined by powers of determinantal ideals*，Journal of Algebra 142，150--163，Theorem 1.1，印刷页 151，作者主页所载原始发表版](https://www.home.uni-osnabrueck.de/wbruns/brunsw/pdf-article/AlgDet.published.pdf) 的系数环是任意整环 $R_0$，$X=(x_{ij})$ 是 $a\times b$ 个独立不定元组成的矩阵，$1\le t\le a\le b$，并要求 $(\min(t,a-t))!\in R_0^\times$。以 $I_j(X)$ 表示全部 $j$ 阶子式生成的理想，对每个整数 $r\ge1$，原文结论为

$$
I_t(X)^r=\bigcap_{j=1}^t I_j(X)^{((t-j+1)r)}
\quad\text{于 }R_0[X].
$$

右侧为符号幂：$I_j(X)^{(c)}=I_j(X)^cR_0[X]_{I_j(X)}\cap R_0[X]$，该交式是普通幂的准素分解。只保留 $u\le j\le t$，其中 $u=\max(1,a-r(a-t))$，所得分解不可删减。这里的 $R_0,a,b,r$ 分别是原文的 $B,m,n,s$，不与本卷的原族环 $B$、半域次数 $m$ 或枢轴 $s$ 混同。原文将特征零的分解归于 De Concini--Eisenbud--Procesi，将上述推广归于 Bruns--Vetter。若没有阶乘可逆的条件，原文 Theorem 1.3（印刷页 152）将同一交式识别为普通幂的整闭包，不能无条件替代为普通幂本身。

在本卷任意特征零域上取 $R_0=F$，阶乘条件全部满足，无须代数闭性或 $F\hookrightarrow\mathbb C$。令 $R_t(X)\subset F[X]_t$ 为 $t$ 阶子式的线性张成。Bruns 的结论确实涉及实际乘法；其最低齐次部分给

$$
\operatorname{im}\bigl(\operatorname{Sym}^rR_t(X)
\xrightarrow{\mathrm{mult}}F[X]_{tr}\bigr)
=(I_t(X)^r)_{tr}
=\left(\bigcap_{j=1}^t I_j(X)^{((t-j+1)r)}\right)_{tr}.
$$

第一个等号因 $I_t(X)$ 由纯 $t$ 次元素生成：次数 $tr$ 的 $r$ 重乘积只能有常数余因子。这正是与 (184.1) 重叠的“普通幂的最低次数即恰好指定个数因子的乘法像”机制，而非只在字符中出现某个分量。不过 $t=2$ 时其生成空间仍是一般矩阵子式空间，尚不是 $K\subset\operatorname{Sym}^2(\bigwedge^2V)$。具体地，在 $N\ge4$ 时取 $a=b=N$，选基后记 $z_{ij}=e_i\wedge e_j$，$z_{ji}=-z_{ij}$、$z_{ii}=0$。实际 $F$ 代数满射

$$
\sigma:F[x_{ij}:1\le i,j\le N]\longrightarrow
\operatorname{Sym}(\bigwedge^2V),\qquad x_{ij}\longmapsto z_{ij}
$$

虽保持乘法，却将行 $1,3$、列 $2,4$ 的子式送到

$$
\sigma(x_{12}x_{34}-x_{14}x_{32})
=z_{12}z_{34}+z_{14}z_{23},\qquad
w(z_{12}z_{34}+z_{14}z_{23})
=2e_1\wedge e_2\wedge e_3\wedge e_4\ne0.
$$

所以这个交错矩阵特化并不把子式生成空间送入 $K$；原交式也不能直接特化为 (184.2)。本证明不作 Schur 分拆转置或超代数乘法迁移，不把子式幂与 $K^r$ 宣称为同一映射的像。Bruns 的精确普通幂结论及上述实际映射比较确定了经典重叠的范围；所缺的本代数乘法识别由下面 Enright--Wallach 的等式支付。

先取 $F=\mathbb C$、$N\ge4$。[Enright--Wallach，*A Pieri rule for Hermitian symmetric pairs II*，Theorem 1，式 (2.1)，印刷页 53](https://msp.org/pjm/2004/216-1/pjm-v216-n1-p03-s.pdf) 在 $\mathcal B=\operatorname{Sym}(\mathfrak p^-)$ 内给出实际乘法等式

$$
\mathcal B[z]\mathcal B[(k)]
=\bigoplus_{y\in I_k(z)}\mathcal B[y],
\quad k\ge1,
\tag{184.4}
$$

$$
I_k(z)=\{y_1\ge z_1\ge y_2\ge z_2\ge\cdots\ge y_\rho\ge z_\rho\ge0:
\ |y|=|z|+k\}.
$$

子空间的乘积指实际乘积的线性张成。原文 §3，Case 2，印刷页 59，取群 $SO^*(2N)$、紧群 $U(N)$，其复化为 $GL_N$，秩为 $\rho$；强正交根是

$$
\gamma_i=e_{N+1-2i}+e_{N+2-2i}\quad(1\le i\le\rho).
$$

分量 $\mathcal B[z]$ 的最高权为 $-\sum_i z_i\gamma_i$，其对偶的多项式最高权为 $z^{[2]}$；奇数 $N$ 时末尾补零。其对称代数次数是 $|z|$，不是 Schur 分拆的大小 $2|z|$。

必须在整个代数上处理这个对偶约定。取 $E=\mathbb C^N$，使用矩阵实现

$$
\mathfrak{so}_{2N}(\mathbb C)=
\left\{\begin{pmatrix}A&B\\C&-A^{\mathsf T}\end{pmatrix}:
B^{\mathsf T}=-B,\ C^{\mathsf T}=-C\right\}.
$$

嵌入 $g\mapsto\operatorname{diag}(g,g^{-\mathsf T})$ 使上、下非对角块分别为 $\bigwedge^2E$ 与 $\bigwedge^2E^*$。因此 $\mathcal B=\operatorname{Sym}(\bigwedge^2E^*)$。将其**整个代数**的群作用沿 $g\mapsto g^{-\mathsf T}$ 扭转，再用标准对偶基到标准基的线性对应延拓，得到代数同构

$$
T:\operatorname{Sym}(\bigwedge^2E^*)\longrightarrow
\operatorname{Sym}(\bigwedge^2\mathbb C^N),\qquad
T(ab)=T(a)T(b).
\tag{184.5}
$$

扭转后的次数一作用是 $\bigwedge^2\mathbb C^N$；最高权对应把 $\mathcal B[z]$ 送到 $M_z$。这里没有把乘法的线性对偶误当作另一个乘法。由 (184.5)，原文的每个实际乘积及其线性张成都被保持。因此 (184.4) 在目标代数中成为

$$
M_zM_{(k)}=
\bigoplus_{\substack{y/z\text{ 为横 }k\text{ 条带}\\\ell(y)\le\rho}}M_y.
\tag{184.6}
$$

“横 $k$ 条带”指新增 $k$ 格且每列至多一格；它与 (184.4) 的交错不等式完全相同。这一步支付的是实际乘法包含的两个方向，而非仅由张量积字符推断非零。

环境代数的无重分解为

$$
H_d=\bigoplus_{\substack{z\vdash d\\\ell(z)\le\rho}}M_z.
\tag{184.7}
$$

可同时参见 [Perlman，*Regularity and Cohomology of Pfaffian Thickenings*，arXiv:1711.02777v2，§2，式 (2.1)--(2.2)](https://arxiv.org/html/1711.02777v2)：其 $n$ 维空间在这里是 $V$，其 $m$ 是这里的 $\rho$，其重复行记号 $z^{(2)}$ 是这里的 $z^{[2]}$。式 (2.2) 的主 Pfaffian 乘积最高权向量同时确定分量在实际代数中的位置。次数二时，(184.7) 是 $H_2=M_{(2)}\oplus M_{(1,1)}$，第二项为 $\bigwedge^4V$。外乘映射满射，因为每个基四向量都是两个基二向量的外积；$(e_1\wedge e_2)^2$ 是第一项的非零最高权向量，外乘为零。等变性与不可约性于是给 $K=M_{(2)}$。在 (184.6) 中取 $k=2$，就得到与本题 $K$ 相乘的实际规则。

还需明确反复横二条带的终点。对 $z\vdash2r$，从空图经 $r$ 次横二条带到达 $z$、且中间各图至多 $\rho$ 行，当且仅当 $\ell(z)\le\min(r,\rho)$。必要性来自每步至多新增一行：若新增两行，它们在第一列的新格会冲突。充分性对 $r$ 归纳，$r=0$ 取空图。设 $r\ge1$ 且 $\ell(z)\le r$，删去横二条带以得到大小 $2r-2$、至多 $r-1$ 行的分拆：若 $\ell(z)\le r-1$，则第一行至少长二，从最右两列各删最下方一格。设列高为 $c_1\ge\cdots\ge c_L>0$，删除后为 $c_1,\ldots,c_{L-2},c_{L-1}-1,c_L-1$，仍弱递减且非负。若 $\ell(z)=r$ 且末行长二，则总大小强迫 $z=(2^r)$，删末行。若末行长一，则第一行至少长三，删末行唯一一格及最右列最下方一格；它们列号不同，所得分拆有 $r-1$ 行。末行不可能更长，故已穷尽情形。归纳后补回这两个格子；所有中间图均包含于 $z$，所以满足 $\rho$ 行限制。

由于交换乘法通过 $\operatorname{Sym}^rK$ 分解，有 $K^{r+1}=K^rK$。从常数开始逐次应用 (184.6) 的实际等式，上一段刻画的每个终点分量都完整出现，其他分量均不出现。无重分解给出复数域上的 (184.2)。

为传到任意特征零域，现给出同一乘法映射与各分量的有理模型。取 $E_{\mathbb Q}=\mathbb Q^N$，在 $E_{\mathbb Q}^{\otimes2d}$ 上令 $G_d=S_2\wr S_d$ 为保持 $d$ 个配对的置换群；$\varepsilon$ 在每对内部取符号，在交换整对时取正号。投影

$$
p_d=\frac1{2^dd!}\sum_{g\in G_d}\varepsilon(g)g
\tag{184.8}
$$

的像自然识别为 $H_{\mathbb Q,d}=\operatorname{Sym}^d(\bigwedge^2E_{\mathbb Q})$。对 $\lambda\vdash2d$，Specht 特征标为整数值，故中心幂等元

$$
e_\lambda=\frac{\dim[\lambda]}{(2d)!}
\sum_{\sigma\in S_{2d}}\chi_\lambda(\sigma^{-1})\sigma
\in\mathbb Q[S_{2d}]
\tag{184.9}
$$

与 $p_d$ 交换。令 $M_{z,\mathbb Q}=e_{z^{[2]}}p_d(E_{\mathbb Q}^{\otimes2d})$，$|z|=d$。Schur--Weyl 分解与 (184.7) 说明其扩到 $\mathbb C$ 后正是 $M_z$，没有额外重数。所有这些有限维投影均与扩域相容。

外乘的有理矩阵给 $K_{\mathbb Q}$，核与扩域交换。固定 $r$，实际有理映射 $\mu_{r,\mathbb Q}:\operatorname{Sym}^rK_{\mathbb Q}\to H_{\mathbb Q,2r}$ 的像也与扩域交换。复数结论说，它与 (184.2) 右侧的有理直和扩到 $\mathbb C$ 后相同。$\mathbb Q\to\mathbb C$ 忠实平坦，因此同一有理环境中的两个子空间相同：可对它们的和分别模掉两个子空间，扩域后商为零即原商为零。再沿 $\mathbb Q\hookrightarrow F$ 扩域，并选 $F^N\simeq V$，得到 (184.2) 在任意 $F$ 上成立。此论证不要求 $F$ 嵌入 $\mathbb C$，也没有只下降一个维数等式。

边界维数可直接处理。任意 $N$、$r=0$ 时两边都是 $F$；$N=0,1$、$r>0$ 时 $W=0$，两边都是零。$N=2,3$ 时 $\bigwedge^4V=0$，所以 $K=H_2$；次数 $2r$ 单项式可分成 $r$ 个二次单项式，故 $K^r=H_{2r}$。这时 $\rho=1$，(184.7) 的唯一分量为 $M_{(2r)}\simeq\mathbb S_{(2r,2r)}V$，与 (184.2) 一致。小维数由这些直接事实承担，不需小秩 Lie 理论。

最后，若 $r\ge\rho$，(184.2) 已包含 (184.7) 中的所有分量。若 $1\le r<\rho$，取 $z=(r,1^r)$，则 $|z|=2r$、$\ell(z)=r+1\le\rho$。其 Schur 分拆有 $2r+2\le N$ 行，故 $M_z(V)$ 非零，却被 (184.2) 排除。于是 (184.3) 是精确的；$N=0,1$ 的正次满性另由零空间解释。回到原族，$N=m-1$、$\rho=h$，所以对每个 $j\ge h$ 都有 $K^j=H_{2j}$。这正是下一节逐阶提升所需的全范围齐次满射。

## 185. 在原完成源内求和并取得有限代数成员资格

继续证明定理 182.2 的 (182.10)。固定任意合法 $s$、任意 $q\ge h$ 及任意 $b\in B_{0,s}\cap\mathfrak q^{2q}$。不再改变这个 $s$。在原 $F$ 上，对每个 $j\ge h$ 选择有限维满射

$$
\operatorname{Sym}^jK\longrightarrow H_{2j}
\tag{185.1}
$$

的一个 $F$ 线性截面。它只用于选齐次多项式原像，不改变源或纤维。

令 $b_q=b$。若 $b_j\in B_{0,s}\cap\mathfrak q^{2j}$，取其 $2j$ 次齐次项 $a_j\in H_{2j}$。由 (185.1) 可选次数恰为 $j$ 的齐次多项式 $P_j(T_1,\ldots,T_t)$，使

$$
P_j(k_1,\ldots,k_t)=a_j.
\tag{185.2}
$$

由 (182.9)，替换一个二次首项为尾项使 $Y$ 次数至少增加二，故

$$
P_j(g_s)=a_j+O(Y^{2j+2}),\qquad
b_{j+1}=b_j-P_j(g_s)\in B_{0,s}\cap\mathfrak q^{2j+2}.
\tag{185.3}
$$

归纳得到 $b-\sum_{j=q}^L P_j(g_s)\in\mathfrak n_s^{L+1}$。齐次项 $a_j$、多项式 $P_j$ 因而可依赖 $b$ 与 $s$；这与共同基提升的统一性是不同量词。

无穷和的见证先在原源中构造。直接使用 [046，引理 177.1](https://github.com/the-omega-institute/trureturing/blob/9b1e19f102fb2f399677cae4b720d631afcc1245/docs/develop/theory/AURIC_R5_046_EXACT_CUBIC_PRODUCTS_AND_ACTUAL_HIGH_ORDER_FIBRE_CLOSURE.md) 的一般形式代入与有限分组结论：其局部代数取本卷的 $R=\mathscr T$，元素取本卷有限个 $\gamma_i\in\mathfrak m_{\mathscr T}$，整数取 $q$。引理 183.1 已支付完备、分离、局部 $F$ 代数及零常数元素的全部假设。因此

$$
P=\sum_{j\ge q}P_j\in F[[T_1,\ldots,T_t]],\qquad
G=P(\gamma)\in\mathscr T
\tag{185.4}
$$

存在，且第 $j$ 次修正 $P_j(\gamma)$ 的**源阶数**至少为 $j$。同一引理还给有限和

$$
P=\sum_{|\beta|=q}T^\beta H_\beta(T),\qquad
G=\sum_{|\beta|=q}\gamma^\beta H_\beta(\gamma)
\in(\gamma_1,\ldots,\gamma_t)^q\mathscr T.
\tag{185.5}
$$

这里 $H_\beta\in F[[T]]$，每个 $H_\beta(\gamma)$ 也由原源形式代入定义；多重指标 $|\beta|=q$ 只有有限个。这是代数理想幂成员资格的有限见证，没有诉诸目标中理想的闭性。

由 $\pi_s$ 的连续性，$\pi_s(G)$ 是 (185.3) 有限和的目标极限；目标分离性及误差属于 $\mathfrak n_s^{L+1}$ 给 $\pi_s(G)=b$。式 (185.5) 进一步给

$$
b=\sum_{|\beta|=q}g_s^\beta\,\pi_s(H_\beta(\gamma))\in I_s^q.
\tag{185.6}
$$

所以全部目标尾项都有真正的原源见证。反向 $I_s\subseteq\mathfrak m_s\subseteq\mathfrak n_s$，故 $I_s^q\subseteq\mathfrak m_s^q\subseteq\mathfrak n_s^q$；引理 183.1 给 $\mathfrak n_s^q=B_{0,s}\cap\mathfrak q^{2q}$，于是这些空间相同。由于 $\pi_s:\mathscr T\twoheadrightarrow A_s$ 满射，有限乘积和给 $\pi_s(\mathfrak m_{\mathscr T}^q)=\mathfrak m_s^q$ 及 $\pi_s((\gamma)^q\mathscr T)=I_s^q$。这完成 (182.10) 的证明。

此推导只复用 046 引理 177.1 的一般源代入结论；其次数十四的齐次满性、具体生成元个数及余切维数均未作为全 $m$ 前提。这里的齐次阈值已由原 $N=m-1$ 的 (184.2)--(184.3) 独立给定。

## 186. 实际首项商与完整有限原源公式

**命题 186.1（有限实际层的精确商）。** 在定义 182.1 的全部假设下，(182.11)--(182.13) 成立，并且

$$
K^r\subseteq D_{(s,r)}\subseteq M_{(s,r)}\subseteq H_{2r}
\quad(r\ge2),
\qquad
M_{(s,r)}=D_{(s,r)}=H_{2r}\quad(r\ge h).
\tag{186.1}
$$

从而

$$
\dim_FQ_s=
\sum_{r=1}^{h-1}\bigl(\dim_FM_{(s,r)}-\dim_FD_{(s,r)}\bigr),
\quad
\dim_FK=\frac{b(b+1)}2-\binom{m-1}{4}.
\tag{186.2}
$$

这些商是指定实际像的环境子商；没有断言它们对 $GL(V)$ 稳定，也没有把它们认作环境 Schur 分量的直和。

证明。首项映射 $C_{s,r}\to H_{2r}$ 的核为 $C_{s,r+1}$。映射

$$
C_{s,r}\longrightarrow
\mathcal F^{2r}Q_s/\mathcal F^{2r+2}Q_s
$$

的核恰为 $C_{s,r+1}+(\mathfrak m_s^2\cap C_{s,r})$：若 $c=c'+d$，$c'\in C_{s,r+1}$、$d\in\mathfrak m_s^2$，则 $d=c-c'\in C_{s,r}$；反向显然。对首项取商便是 $M_{(s,r)}/D_{(s,r)}$。引理 183.1 给 $C_{s,1}=\mathfrak m_s$、$M_{(s,1)}=K$；两个零常数偶函数之积至少四阶，所以 $D_{(s,1)}=0$。

任意 $\mathfrak m_s^2$ 元素是有限个实际乘积的和，其四次项是相应二次项乘积的和，故在 $K^2$；每个 $K$ 元素均有实际提升，给反向实现，故 $D_{(s,2)}=K^2$。$M_{(s,2)}$ 正是零二次实际元素的四次首项 $J_4(A_s)$。对 $r\ge2$，恰好 $r$ 个共同基提升的乘积属于 $\mathfrak m_s^r\subseteq\mathfrak m_s^2$，其 $2r$ 次首项张成 $K^r$，给 (186.1) 的第一个包含。其余包含由定义。

因 $m\ge7$，有 $h\ge3$。式 (182.10) 给 $\mathfrak n_s^h=\mathfrak m_s^h\subseteq\mathfrak m_s^2$，所以 $\mathcal F^{2h}Q_s=0$。对 $r\ge h$，整个 $\mathfrak n_s^r$ 都在 $A_s$ 且属于 $\mathfrak m_s^2$，其首项可任取 $H_{2r}$，给最后一个等式。有限滤过逐层取维数得到 (186.2)；$H_2\to\bigwedge^4V$ 满射给 $K$ 的维数公式。至此定理 182.2 全部得证。

**命题 186.2（只需有限个真实原源喷射）。** 保持定义 182.1 的同一个 $F,D,\theta,s$。取完整原极大理想 $\mathfrak m_S$ 的任意有限理想生成元 $v_1,\ldots,v_e$，并记

$$
\overline B_s=B_{0,s}/\mathfrak n_s^h
=F\oplus\bigoplus_{j=1}^{h-1}H_{2j},\qquad
\overline a_i=\pi_s(v_i)\bmod\mathfrak n_s^h.
\tag{186.3}
$$

右侧使用实际消元后的偶齐次展开，乘法截去次数至少 $2h$ 的项。对 $\ell=1,2$，令

$$
\mathcal I_\ell=\{\alpha\in\mathbb Z_{\ge0}^e:\ell\le|\alpha|<h\},
\qquad
E_\ell=\operatorname{span}_F\{\overline a^\alpha:\alpha\in\mathcal I_\ell\}
\subseteq\overline B_s.
\tag{186.4}
$$

则有精确的有限描述

$$
\mathfrak m_s/\mathfrak n_s^h=E_1,\qquad
\mathfrak m_s^2/\mathfrak n_s^h=E_2,\qquad
Q_s\simeq E_1/E_2.
\tag{186.5}
$$

对 $1\le r<h$、$\ell=1,2$ 定义有限维线性映射

$$
\begin{aligned}
L_{\ell,<r}(c)&=\left(\sum_\alpha c_\alpha[\overline a^\alpha]_{2j}\right)_{1\le j<r}
\in\bigoplus_{j=1}^{r-1}H_{2j},\\
L_{\ell,r}(c)&=\sum_\alpha c_\alpha[\overline a^\alpha]_{2r}\in H_{2r},
\qquad c\in F^{\mathcal I_\ell}.
\end{aligned}
\tag{186.6}
$$

当 $r=1$，第一目标取零空间。则

$$
\boxed{
M_{(s,r)}=L_{1,r}(\ker L_{1,<r}),\qquad
D_{(s,r)}=L_{2,r}(\ker L_{2,<r}).
}
\tag{186.7}
$$

因此所有剩余实际余切层都由这一个固定纤维、有限多个原函数的至多 $2h-2$ 次展开决定。

证明。$S$ Noetherian，故存在有限理想生成元，完成后它们仍生成 $\mathfrak m_{\mathscr T}$。任意元素模 $\mathfrak m_{\mathscr T}^h$ 都可用 $v_i$ 的次数小于 $h$ 的多项式表示：先减剩余类常数，再用 $v_i$ 生成极大理想，逐次减去各系数的常数，有限迭代到源次数 $h$ 即止。同理，$\mathfrak m_{\mathscr T}^\ell$ 的元素可用次数介于 $\ell$ 与 $h-1$ 的单项式表示，余项在 $\mathfrak m_{\mathscr T}^h$。引理 183.1 的连续局部映射将这部分送入 $\mathfrak n_s^h$。反向，每个有限单项式组合显然来自原源的相应幂。由 (182.10)，$\mathfrak n_s^h\subseteq\mathfrak m_s^2\subseteq\mathfrak m_s$，所以 (186.5) 中的两个商都定义良好，并恰为 (186.4) 的空间。

在 $E_\ell$ 内落入 $\mathfrak n_s^r/\mathfrak n_s^h$，恰好要求所有低于 $2r$ 的偶齐次项消失，亦即系数向量在 $\ker L_{\ell,<r}$ 中。取下一齐次项得到 (186.7)。每个这样的有限组合已经是实际原源元素，低项消失是其真实展开的消失；没有用任意环境多项式补作源元素。完整尾项已属于公共的 $\mathfrak n_s^h$，故有限喷射没有遗漏余切类。证毕。

**命题 186.3（六次乘积首项中的抵消项）。** 在命题 186.2 的假设下，进一步设 $h\ge4$，写

$$
\pi_s(v_i)=d_i+e_i+O(Y^6),\qquad d_i\in K,\ e_i\in H_4.
$$

对 $c=(c_{ij})_{i\le j}\in F^{e(e+1)/2}$ 定义

$$
U(c)=\sum_{i\le j}c_{ij}d_id_j\in H_4,
\qquad
V_s(c)=\sum_{i\le j}c_{ij}(d_ie_j+e_id_j)\in H_6.
\tag{186.8}
$$

则

$$
D_{(s,3)}=K^3+V_s(\ker U).
\tag{186.9}
$$

证明。模掉 $\mathfrak n_s^4$ 后，原源平方的元素只需保留源次数二与三的单项式；源次数至少四的像从八阶开始。二次组合的四次项是 $U(c)$，六次项是 $V_s(c)$。三次组合的首项张成 $K^3$，因为所有 $d_i$ 张成全部实际二次像 $K$。所以该平方元素从六阶开始，当且仅当二次组合的系数满足 $U(c)=0$；此时六次项正是 (186.9) 的右侧。反向，任意 $c\in\ker U$ 的原有限二次组合以及任意三次组合均给相应实际元素，故全部可达。证毕。

式 (186.9) 指明了不能忽略的抵消机制：乘积的四次项抵消后，其六次项仍然属于平方的首项空间。仅知道各 $K^r$ 的经典分解，不能删去 $V_s(\ker U)$；本卷没有断言这个额外空间在每个原纤维中非零或必在 $K^3$ 之外。一般层由 (186.7) 同时保留全部这种抵消，而非只保留最低二次符号的乘积。

## 187. 第一处未定的实际四次像及后续有限义务

**命题 187.1（首个有限商的忠实读取）。** 在定义 182.1 的全部假设下，定义

$$
\Psi:H_4\longrightarrow\bigwedge^6V\otimes W,\qquad
\Psi(\xi_1\xi_2\xi_3\xi_4)
=\sum_{i=1}^4\left(\bigwedge_{j\ne i}\xi_j\right)\otimes\xi_i.
\tag{187.1}
$$

令 $\mathcal E_s^{\mathrm{act}}=\Psi(M_{(s,2)})$。则

$$
M_{(s,2)}/D_{(s,2)}
=J_4(A_s)/K^2\simeq\mathcal E_s^{\mathrm{act}}.
\tag{187.2}
$$

若在命题 186.2 中写 $\pi_s(v_i)=d_i+e_i+O(Y^6)$，定义 $D_2(c)=\sum_i c_id_i$、$D_4(c)=\sum_i c_ie_i$，则

$$
J_4(A_s)=K^2+D_4(\ker D_2),\qquad
\mathcal E_s^{\mathrm{act}}=\Psi D_4(\ker D_2).
\tag{187.3}
$$

证明。[045，定理 168.2](https://github.com/the-omega-institute/trureturing/blob/a5a20d82984bbb32282adccee504bbcd41fc7ac1/docs/develop/theory/AURIC_R5_045_FAITHFUL_QUARTIC_DETECTION_AND_COMPLETE_ORIGINAL_EVALUATOR_RELATIONS.md) 在任意特征零域、任意有限维 $V$ 上给 $\ker\Psi=K^2$；命题 186.1 已给 $D_{(s,2)}=K^2\subseteq M_{(s,2)}$，所以限制检测器给 (187.2)。为得 (187.3)，在 (186.7) 的四次层只需源次数一和二：一次组合的二次项为 $D_2(c)$，四次项为 $D_4(c)$；二次组合没有二次项，四次项张成 $K^2$；源次数至少三不贡献四次。因此要求零二次恰为 $c\in\ker D_2$，给第一个等式。对它应用 $\Psi$，$K^2$ 被消去，给第二个等式。证毕。

**定义 187.2（已知原首一评价的共同子空间）。** 在同一个原域族中令 $d=m-4$。对首一 $d$ 次多项式 $t(T)\in F[T]$，置

$$
\begin{aligned}
\Omega_t&=1\wedge T\wedge T^2\wedge t\wedge Tt\wedge T^2t\in\bigwedge^6V,\\
\eta_t&=2T\wedge Tt-1\wedge T^2t-T^2\wedge t\in W,\\
\mathcal C_d&=\operatorname{span}_F\{2\Omega_t\otimes\eta_t:t\text{ 首一、}\deg t=d\}.
\end{aligned}
\tag{187.4}
$$

最高次数 $d+2=m-2$，所以这些向量确实属于原 $V$。045，定义 167.3、定理 167.4、§172 的对应是：真实原函数 $\mathcal E_t(C')=P_{C'}(t(\theta))/P_{C'}(\theta^m)$ 的常数、二次项均为零，四次检测为 $2\Omega_t\otimes\eta_t$，故 $\mathcal C_d\subseteq\mathcal E_s^{\mathrm{act}}$ 对每个预固定 $s$ 同时成立。分母在连续幂点是非零幂基体积，因而是原 $S$ 中单位；此子空间来自实际原函数。

**问题 187.3（固定纤维的首个剩余有限问题）。** 对定义 182.1 的任意给定 $F,D,\theta$ 及事先固定的合法 $s$，确定有限空间

$$
\mathcal E_s^{\mathrm{act}}
=\Psi D_4(\ker D_2)\subseteq\bigwedge^6V\otimes W,
\quad\text{特别是}\quad
\mathcal E_s^{\mathrm{act}}/\mathcal C_d.
\tag{187.5}
$$

这是四次层的完整实际像问题，不能以任意环境检测张量的存在来替代。后续尚需确定 $3\le r<h$ 的实际 $M_{(s,r)}$、$D_{(s,r)}$，或至少它们的商；命题 186.2 将这些义务全部限制到有限原源展开与低项消失关系。

当 $m=7$ 时 $h=3$，余切只有二次、四次两层。[044，定理 157.1、159.1](https://github.com/the-omega-institute/trureturing/blob/74b08723d9c5fb45657df8015bfd47a366f7b199/docs/develop/theory/AURIC_R5_044_RATIONAL_EVALUATOR_QUARTICS_AND_ACTUAL_POSITIVE_PIVOT_CONTROL.md) 及 [046，§179](https://github.com/the-omega-institute/trureturing/blob/9b1e19f102fb2f399677cae4b720d631afcc1245/docs/develop/theory/AURIC_R5_046_EXACT_CUBIC_PRODUCTS_AND_ACTUAL_HIGH_ORDER_FIBRE_CLOSURE.md) 已给更大的共同已知空间 $\Omega\otimes L_6$，其中 $\Omega=e_0\wedge\cdots\wedge e_5$，

$$
L_6=\langle
2z_{14}-z_{05}-z_{23},\ 2z_{13}-z_{04},\ 3z_{12}-z_{03},\
2z_{24}-z_{15},\ 3z_{34}-z_{25},\ z_{05}+z_{14}-8z_{23}
\rangle_F.
\tag{187.6}
$$

所以在这个特定域次数，首个超出已知结果的问题是 $\mathcal E_s^{\mathrm{act}}/(\Omega\otimes L_6)$，最小的新增方向需一个 $c\in\ker D_2$ 使 $\Psi D_4(c)\notin\Omega\otimes L_6$。044 的完整互素二元三次有理评价族检测恰为这个六维空间，因此仅在该族内部继续取值不能给这样的方向。改变枢轴后得到的方向不能拼作原固定纤维的答案。这些次数十四的已知空间不被外推为一般 $m$ 的整个实际四次像。

数学上最先需要的数据是完整原理想生成元的二次、四次实际消元项及其 $D_2$ 关系；式 (187.3) 就给第一层未知商。随后才需要其至 $2h-2$ 次的项及 (186.6) 的低项关系。不存在另一个还须追踪的无限高阶余切余项。

## 188. 完整中文普通语言表述与解释

**定理 188.1（所有允许偶数域次数中的原纤维有限性）。** 在任意特征零域上，给定一个次数为 $2m$ 的实际可分域扩张，其中 $m$ 至少为七。任选一个本原元，以它的零次到 $m-1$ 次连续幂作为半维窗口，使用同一个域的乘法行列式，保留全部原符号及原嵌入标签系数。在这些实际系数的局部环中，预先固定任意一组正向一阶独立的合法原域枢轴，用其真实方程消去正规化中的正变量。取原完成局部环映入这个纤维的实际像，令阈值为 $m-1$ 除以二向下取整。

对每个不低于阈值的整数 $q$，实际像极大理想的 $q$ 次幂，恰好是正规化纤维极大理想的 $q$ 次幂，也恰好是所有负变量总次数至少为 $2q$ 的偶形式级数。这些级数全部由原完成源中的元素实现，而且可以写成有限个 $q$ 重实际乘积之和。可以在选枢轴以前固定同一批原二次基提升，使这些等式适用于每组合法枢轴；一个指定级数的高阶修正则在该指定纤维中进行。

实际纤维余切空间中，负变量次数达到阈值的两倍以后再无独立余类。所有余切信息都由此前有限个偶次数层给出。每层的分子必须是真实原源函数在较低项全部消失后的首项，分母必须是真实平方理想中的函数在较低项全部消失后的首项。第一层是全部外乘核二次信息，第二层是实际零二次函数的四次首项模二次信息的两两乘积；更高层还可能有乘积之间低项抵消所产生的额外分母，不能只凭抽象二次乘法表删除它们。

证明与解释。经典实际乘法定理把一次二次信息相乘对应为在一个分拆图上添加两个不同列的格子。每次至多增加一行；反向删格归纳说明，恰有 $2r$ 格且至多 $r$ 行的图都能经恰好 $r$ 次合法添加得到。原负坐标来自一个维数为 $m-1$ 的空间的外平方，环境只允许至多阈值那么多成对行。因此乘法次数达到阈值时，所有环境齐次分量都已实际出现。这里使用的是保持乘法的整个代数对应；有理模型的忠实下降使结论适用于任意特征零原域。

原二次提升附带高阶尾巴，所以还需逐次修正完整级数。先用长度 $q$ 的原提升乘积消去 $2q$ 次项，再用长度 $q+1$ 的乘积消去下一偶次项，依次继续。第 $j$ 次修正不仅在目标中阶数增加，在原完成源中也至少属于第 $j$ 次极大理想幂，所以修正和先在原源里收敛。按有限多个固定长度因子分组，所得原源元素属于真正的代数理想幂；连续性与目标分离性再说明其像就是指定级数。

余切商模掉两个零常数实际函数的乘积。阈值至少为三，故全部高于截断的尾项已经是平方中的元素，在余切中消失。每个较低层取首项后，核恰为下一层；再模平方中同阶首项，正好得到该层的实际商。取完整原理想的一组有限生成元，将它们实际消元后的展开截到最后一个允许次数，就同时决定全部这些商。因此有限截断确实完整，但它本身没有给出各个固定纤维的全部低阶子空间。证毕。

## 189. 数学来源、精确重叠与未定边界

**约定 189.1（经典输入与本原族的对应范围）。** Enright--Wallach 的文献为 Thomas J. Enright、Nolan R. Wallach，*A Pieri rule for Hermitian symmetric pairs II*，Pacific Journal of Mathematics 216(1)，51--61，DOI [10.2140/pjm.2004.216.51](https://doi.org/10.2140/pjm.2004.216.51)。其 Theorem 1 的 (2.1) 给实际乘法等式，§3 Case 2 给 $SO^*(2N)$、秩 $\lfloor N/2\rfloor$、重复行最高权及对偶约定。§184 的全代数扭转、横二条带归纳与有理下降说明它在本题的精确适用方式；抽象公式 (184.2) 及满性阈值是这条经典理论的后果，不作为新的抽象乘法定理提出。

Michael Perlman，*Regularity and Cohomology of Pfaffian Thickenings*，arXiv:1711.02777v2，§2 的 (2.1)--(2.2) 给环境的无重分解与主 Pfaffian 最高权向量；(2.3)--(2.4) 描述由一个分量生成的整个不变理想。后者允许任意齐次余因子，单独不能证明恰好 $r$ 个本卷 $K$ 因子的实际乘法像。本文的该步依赖 Enright--Wallach 的实际等式，不以理想包含或字符出现替代。

Winfried Bruns，*Algebras defined by powers of determinantal ideals*，Journal of Algebra 142，150--163，DOI [10.1016/0021-8693(91)90222-t](https://doi.org/10.1016/0021-8693(91)90222-t)，Theorem 1.1 的精确整环、矩阵与阶乘条件，以及最低次数乘法像，均在 §184 的原族证明内作了直接比较。它是一般矩阵子式理想普通幂的经典准素分解；§184 给出的交错特化并不把其二阶子式空间送入本卷 $K$，故未以它冒充 (184.2) 的直接证明，也没有以整闭包结论、字符相同或分拆转置代替实际乘法对应。

**约定 189.2（有限的仓内数学重叠）。** 本文原族接口与相关低阶结果的对应限于以下固定来源；一般经典输入的适用范围已在 §184 写明。

| 固定来源 | 复用的数学内容与边界 |
| --- | --- |
| [039，e5f5994ce4e5c1e553f9fcafb37a5e8fd21f1dbb，§§111--117](https://github.com/the-omega-institute/trureturing/blob/e5f5994ce4e5c1e553f9fcafb37a5e8fd21f1dbb/docs/develop/theory/AURIC_R5_039_UNIFORM_COEFFICIENT_NORMALIZATION_AND_HIGHER_DEGREE_DEFECT.md) | 原带符号标签系数像、实际乘法商、有限正规化、原剩余域与固定点横截面。 |
| [040，f32f2d3b8219fae2014e5db4ab3c31575edf0672，定理 122.1、命题 122.2](https://github.com/the-omega-institute/trureturing/blob/f32f2d3b8219fae2014e5db4ab3c31575edf0672/docs/develop/theory/AURIC_R5_040_EXACT_COTANGENT_DEFECT_AND_RECTANGLE_INTERPOLATION.md) | 原域完整耦合余切像，尤其纯负交为 $K$、正投影满射；不是源嵌入维数等式。 |
| [042，fd9d6f7737ac0bf2274eddc48d5bde4ac0da1db6，§§132--134](https://github.com/the-omega-institute/trureturing/blob/fd9d6f7737ac0bf2274eddc48d5bde4ac0da1db6/docs/develop/theory/AURIC_R5_042_UNIFORM_ORIGINAL_QUARTIC_LIFTS_BEYOND_QUADRATIC_PRODUCTS.md) | 全 $m\ge7$ 的同一个原域族、实际正枢轴方程、实际像 $A_s$ 及全部二次像 $K$。 |
| [044，74b08723d9c5fb45657df8015bfd47a366f7b199，定理 157.1、159.1](https://github.com/the-omega-institute/trureturing/blob/74b08723d9c5fb45657df8015bfd47a366f7b199/docs/develop/theory/AURIC_R5_044_RATIONAL_EVALUATOR_QUARTICS_AND_ACTUAL_POSITIVE_PIVOT_CONTROL.md) | 仅次数十四的固定纤维共同六方向和完整互素二元三次有理评价检测空间；不外推到其他次数。 |
| [045，a5a20d82984bbb32282adccee504bbcd41fc7ac1，定理 168.2、引理 170.1、§172](https://github.com/the-omega-institute/trureturing/blob/a5a20d82984bbb32282adccee504bbcd41fc7ac1/docs/develop/theory/AURIC_R5_045_FAITHFUL_QUARTIC_DETECTION_AND_COMPLETE_ORIGINAL_EVALUATOR_RELATIONS.md) | 全特征零有限维的 $\ker\Psi=K^2$、全 $m\ge7$ 的共同原源基提升与首一评价四次子空间。 |
| [046，9b1e19f102fb2f399677cae4b720d631afcc1245，引理 177.1、§§178--179](https://github.com/the-omega-institute/trureturing/blob/9b1e19f102fb2f399677cae4b720d631afcc1245/docs/develop/theory/AURIC_R5_046_EXACT_CUBIC_PRODUCTS_AND_ACTUAL_HIGH_ORDER_FIBRE_CLOSURE.md) | 一般完备分离局部源的形式代入与有限分组；其具体三次阈值及二、四次余切短列只属于次数十四。 |

本卷的原族推导把经典全维数乘法输入接到上述实际原源及每个预固定枢轴，得到所有 $m\ge7$ 的 (182.10)，并以 (186.5)--(186.7) 给出全部剩余余切义务的有限实际源形式。这个对应不声称穷尽仓内或外部文献，也不提出全球新颖性结论。

**约定 189.3（阈值及源的未定范围）。** 式 (184.3) 的阈值对抽象齐次乘法是精确的；它只给实际源尾项吸收的统一充分阈值。额外的实际低阶函数及乘积抵消可以使实际吸收提前，本文没有证明实际阈值尖锐。$A_s$ 始终是实际像，不是抽象初始代数 $F[K]$；其余切层也只是实际环境子商。式 (187.5) 及较高有限层尚未分类。

同样，$\pi_s(g)\in\mathfrak m_s^q$ 不推出原 $g\in\mathfrak m_S^q$；纤维取像可以消去非零源余切类。因此这里没有计算完整源余切、完整评价源余切、$\mathfrak L_s$ 与 $(s)\mathscr T$ 的等号，或完整形式芽与全局导子。所有实际结论均保持同一个可分域、本原元、原连续幂窗口和预固定合法原域枢轴。

## 追加锚（本行以下为增补区）
