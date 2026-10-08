# FIB 合法词整体取得：最优误差首项、联合读出严格分离与平方根测量的非最优性

## 1. 固定来源、合法域与取得合同

**数学引文 1.1（固定来源与证明层次）。** 本卷沿用快照 [`aeb45cd336fe958eabf799ee4580bbad1e364077`](https://github.com/the-omega-institute/trureturing/tree/aeb45cd336fe958eabf799ee4580bbad1e364077) 中 [SIC 时间取得卷](https://github.com/the-omega-institute/trureturing/blob/aeb45cd336fe958eabf799ee4580bbad1e364077/docs/develop/theory/FIB_ATOM_WHITEBOX_SIC_TIME_ACQUISITION.md) 定义 1.1、1.3、1.5 的同一张量符号源、一块式调用和完整五窗服务。原卷定理 2.1 已给出独立符号先验的恢复曲线、合法词的 score-only 分数和尖锐零误差阈值；它明确不把独立位公式作为相关合法先验的有限误差最优值。本卷给出该相关域上的普通数学证明，是参考输入，不是 Lean kernel 核验声明。理想源、校准、准备及读出是以下结论的明确假设，不是物理实验结果。

**定义 1.2（同一未知张量符号源）。** 固定整数 $N,L\ge1$，令 $n=3N$、$\theta=\pi/(4L)$。系统为 $\mathcal K=(\mathbb C^2)^{\otimes n}$，因子标签和带符号的计算基、$X,Y,Z$ 标准均已知。合法词集合与源为

$$
\begin{aligned}
B_n&=\{b\in\{0,1\}^n:b_i b_{i+1}=0\quad(1\le i<n)\},\\
s_i(b)&=(-1)^{b_i},\\
U_{s(b)}&=\bigotimes_{i=1}^n\exp(i s_i(b)\theta Z),\\
\Lambda_{s(b)}(\rho)&=U_{s(b)}\rho U_{s(b)}^\dagger.
\end{aligned}
$$

未知 $b$ 按 $B_n$ 上的均匀先验选定一次，随后所有调用使用同一个理想、无噪声、无记忆、已校准的源。一次普通调用对整个 $n$ 量子位系统施加 $\Lambda_{s(b)}$，对工作空间施加恒等。全零词、末尾 $000$ 窗以及每个跨窗接缝都保留；没有额外标签建议，没有 canonical $\mathrm{End}$。

**定义 1.3（一块式整体恢复）。** $q$ 是满足 $0\le q\le L$ 的整数。协议准备任意与 $b$ 无关的输入密度态及任意有限维参考 $R$，对同一系统连续调用源恰好 $q$ 次，调用间不操作系统，最后作一次任意联合 POVM，并以有限末端计算输出 $\widehat b\in B_n$。允许与源无关的随机化。仅作用于参考的中间操作与源调用交换，可推迟到末端。不允许未知 controlled-$U$、逆源、源复位、重新抽取 $b$ 或调用间系统控制。

令 $M_n=|B_n|=F_{n+2}$，其中 $F_0=0,F_1=1,F_{k+2}=F_{k+1}+F_k$。协议 $\Pi$ 的整词成功概率为 $p_\Pi(b)=\Pr_b(\widehat b=b)$。定义

$$
\beta_n(L,q)=\sup_\Pi\frac1{M_n}\sum_{b\in B_n}p_\Pi(b),
\qquad
\varepsilon_n^\star(L,q)=1-\beta_n(L,q),
\qquad
\beta_n^{\mathrm{mm}}(L,q)=\sup_\Pi\min_{b\in B_n}p_\Pi(b).
$$

这些量优化整个输入、有限参考和末端测量，而非只优化一个指定探针的测量。错误或非法输出可归给一个固定合法词，因而不必另设失败标签。

**定义 1.4（重叠参数与合法词图）。** 置

$$
x=\cos\left(\frac{\pi q}{2L}\right)=\cos(2q\theta),
\qquad
p=\frac{1+\sqrt{1-x^2}}2.
$$

于是 $0\le x\le1$、$1/2\le p\le1$。$x$ 是同一输入连续酉迭代后的重叠，不是 $(\cos(2\theta))^q$；此实验不是 $q$ 份重新准备的样本。

令 $h(b,c)$ 为 Hamming 距离。$A_n$ 是顶点集 $B_n$ 上的实对称邻接矩阵，$A_n(b,c)=1$ 当且仅当 $h(b,c)=1$。记无向边数为 $e_n$，顶点 $b$ 的度数为 $d_b$。计数辅助约定为 $B_0=\{\text{空词}\}$、$M_0=1$、$e_0=0$；实际源始终满足 $n=3N\ge3$。Hilbert–Schmidt 范数记为 $\|T\|_{\mathrm{HS}}^2=\operatorname{Tr}(T^\dagger T)$，算子范数记为 $\|T\|_{\mathrm{op}}$。

**定义 1.5（平方根末端测量）。** 对等先验纯态列矩阵 $\Phi$，若 Gram 矩阵 $G=\Phi^\dagger\Phi$ 正定，平方根测量（SRM）的向量是 $\Phi G^{-1/2}$ 的各列。这是成熟测量构造，来源为 [Eldar 与 Forney，*On Quantum Detection and the Square-Root Measurement*](https://arxiv.org/abs/quant-ph/0005132)，定理 3。它的几何均匀态族特殊最优性需要相应群轨道条件；来源酉彼此交换本身不提供这些条件。以下不假定 SRM 精确最优。

## 2. 全相关域的定量结论

**定理 2.1（整体误差、受限译码与非平稳测量）。** 在定义 1.2–1.5 的合同下，以下结论成立。

(A) 对每个整数合同 $(L,q)$，整个一块式协议类满足

$$
\varepsilon_n^\star(L,q)\ge\ell_n(x),
\qquad
\ell_n(x)=\frac{2e_n}{M_n}\frac{x^2}{(1+\sqrt{1+nx})^2}.
\tag{2.1}
$$

因此 $1-\ell_n(x)$ 是不可超过的均匀整词 Bayes 成功率上界，不断言此有限参数界可达。

(B) 一次准备 $|+\rangle^{\otimes n}$，令 $\phi_b=U_{s(b)}^q|+\rangle^{\otimes n}$，$\Phi$ 以 $\phi_b$ 为列。$q>0$ 时

$$
G_{bc}=x^{h(b,c)},\qquad G>0.
$$

测量 $\Phi G^{-1/2}$ 的正交归一列，并把正交补归给任一固定合法词，得到精确可达分数

$$
P_{\mathrm{SRM}}=\frac1{M_n}\sum_{b\in B_n}\bigl((\sqrt G)_{bb}\bigr)^2.
\tag{2.2}
$$

若 $(1+x)^n<2$，则

$$
\begin{aligned}
\varepsilon_n^\star&\le1-P_{\mathrm{SRM}}\le u_n(x),\\
u_n(x)&=\frac{(2e_n/M_n)x^2+(1+x^2)^n-1-nx^2}
{[1+\sqrt{2-(1+x)^n}]^2}.
\end{aligned}
\tag{2.3}
$$

这里的区间限制属于这条显式上界，不是对源增加承诺。

(C) 图的边数为

$$
e_n=\sum_{b\in B_n}|b|
=\frac{nF_{n+1}+2(n+1)F_n}{5},
\qquad |b|=\sum_i b_i.
\tag{2.4}
$$

对每个固定 $n=3N$，沿符合原整数合同且 $x\to0$ 的参数族，整个一块式协议类的最优错误率满足

$$
\varepsilon_n^\star(L,q)=C_nx^2+O_n(x^3),
\qquad
C_n=\frac{e_n}{2M_n}
=\frac{nF_{n+1}+2(n+1)F_n}{10F_{n+2}}.
\tag{2.5}
$$

$C_n$ 是均匀合法词平均占位数的一半；式（2.5）描述整词错误率，不是平均单个位错误率。固定整数 $r\ge1$，取 $q=L-r$ 且 $L\to\infty$，有

$$
\varepsilon_n^\star(L,L-r)
=\frac{\pi^2r^2e_n}{8M_nL^2}+O_{n,r}(L^{-3}).
\tag{2.6}
$$

极限跨越不同但各自符合定义的设备合同。每次实验的 $L,\theta,b$ 固定，不能在固定设备上免费改角度。最优性仅涉及首项；余项不声称对增长的 $n$ 一致。

(D) 固定 $|+\rangle^{\otimes n}$ 探针和逐位 $Y$ 测量，只优化使用全部读出词的经典译码，允许其使用完整无相邻约束。该受限类的精确最优均匀整词分数为

$$
P_Y^{\mathrm{ML}}=\frac{T_n(p)}{M_n},
\qquad
T_0(p)=1,\quad T_1(p)=2p,\quad
T_n(p)=p[T_{n-1}(p)+T_{n-2}(p)]\quad(n\ge2).
\tag{2.7}
$$

令 $D_n=T_n'(1)$、$K_n=D_n-2e_n$，则

$$
K_0=K_1=0,\quad K_2=1,\quad
K_n=K_{n-1}+K_{n-2}+M_{n-3}\quad(n\ge3).
\tag{2.8}
$$

故每个固定 $n=3N$ 在充分小的 $x>0$ 时满足

$$
P_{\mathrm{SRM}}-P_Y^{\mathrm{ML}}
=\frac{K_n}{4M_n}x^2+O_n(x^3)>0.
\tag{2.9}
$$

完整 $B_3$ 上 $M_3=e_3=5$，$P_Y^{\mathrm{ML}}=(2p^3+3p^2)/5$，并有显式有限区间

$$
0<x\le\frac1{20}\quad\Longrightarrow\quad
P_{\mathrm{SRM}}-P_Y^{\mathrm{ML}}\ge\frac{x^2}{32}>0.
\tag{2.10}
$$

原整数合同 $q=L-1,L\ge32$ 位于此区间。该分离是均匀合法先验的整词 Bayes 分离，不是逐来源支配或 minimax 分离；受限类只包括指定的 $Y$ 测量加任意经典译码，不包括所有局部测量或所有 LOCC。

(E) 对每个固定 $n=3N$，充分小的 $x>0$ 时，保持同一 $|+\rangle^{\otimes n}$ 输入，只旋转 SRM 的两个末端测量向量，即可严格提高 $P_{\mathrm{SRM}}$。因此 SRM 不是这些有限参数下的精确最优策略；达到最优首项与达到精确最优值是不同命题。

## 3. 定理 2.1 的完整证明

### 3.1 合法词图的计数与谱界

每个合法词中的任意一个 $1$ 改成 $0$ 后仍合法。每条邻边恰有一个含较多 $1$ 的端点；按删除一个 $1$ 定向，每个 $b$ 贡献 $|b|$ 条边，得到 $e_n=\sum_b|b|$。

首段分解 $B_n=0B_{n-1}\mathbin{\dot\cup}10B_{n-2}$ 给出 $M_n=M_{n-1}+M_{n-2}$，初值 $M_0=1,M_1=2$，故 $M_n=F_{n+2}$。两部分内部的图分别是 $A_{n-1},A_{n-2}$。跨部分邻边只能翻转第一位，恰为 $00v$ 与 $10v$，$v\in B_{n-2}$，因此

$$
e_n=e_{n-1}+e_{n-2}+M_{n-2}\quad(n\ge2),
\qquad e_0=0,\quad e_1=1.
\tag{3.1}
$$

这是经典 Fibonacci cube 的首段分解和跨部分匹配，见 [Klavžar、Mollard、Petkovšek，*The degree sequence of Fibonacci and Lucas cubes*](https://users.fmf.uni-lj.si/klavzar/preprints/DegSeqRevised.pdf)，§§1–2；这里只用作计数供应。

置 $H_n=nF_{n+1}+2(n+1)F_n$。Fibonacci 递推直接给出

$$
H_n-H_{n-1}-H_{n-2}=5F_n=5M_{n-2}\quad(n\ge2),
\qquad H_0=0,\quad H_1=5.
$$

所以 $H_n/5$ 与 $e_n$ 的递推和初值相同，证明式（2.4）。任一顶点至多翻转 $n$ 个位置，故 $d_b\le n$。对任意复向量 $z$，按无向边求和，利用 $2|z_bz_c|\le|z_b|^2+|z_c|^2$，有

$$
|z^\dagger A_nz|
\le\sum_b d_b|z_b|^2\le n\|z\|^2.
$$

$A_n$ 实对称，故 $\|A_n\|_{\mathrm{op}}\le n$；另有 $\sum_b d_b=2e_n$。

### 3.2 任意参考纯化与邻边实部恒等式

任意输入混态都可在有限附加参考上纯化。原测量通过忽略该参考嵌入纯化协议，保留原成功概率。因此只需对任意共同单位纯探针 $\psi$ 证明下界。附加参考与未知 $b$ 无关。把所有失败或非法输出归给固定合法词只会增加或保持成功概率，故可设末端标签恰为 $B_n$。

记 $\psi_b=(U_{s(b)}^q\otimes I)\psi$。若 $b,c$ 仅在第 $i$ 位不同，其他因子完全抵消，并有

$$
(U_{s(b)}^q)^\dagger U_{s(c)}^q=e^{\pm2iq\theta Z_i}.
$$

由于 $Z_i\otimes I$ 自伴，$\langle\psi,(Z_i\otimes I)\psi\rangle$ 为实数，故

$$
\begin{aligned}
\langle\psi_b,\psi_c\rangle
&=\cos(2q\theta)
\ \pm i\sin(2q\theta)\langle\psi,(Z_i\otimes I)\psi\rangle,\\
\operatorname{Re}\langle\psi_b,\psi_c\rangle&=x.
\end{aligned}
\tag{3.2}
$$

这不依赖输入、参考维数或其纠缠方式。此处采用定义 1.2 的酉代表书写向量相位，没有授予跨未知标签的相干控制，也没有使用未知 controlled-$U$。

### 3.3 全部邻边共用同一整体错误预算

设末端 POVM 为 $(Q_b)_{b\in B_n}$。显式定义等距映射

$$
Vv=\sum_b|b\rangle\otimes\sqrt{Q_b}v,
\qquad
\Pi_b=|b\rangle\langle b|\otimes I.
$$

因为 $\sum_bQ_b=I$，$V^\dagger V=I$；此映射保持内积，并把测量写成互相正交的结果空间。以下仍把 $V\psi_b$ 记为 $\psi_b$。令

$$
c_b=\Pi_b\psi_b,
\quad r_b=\psi_b-c_b,
\quad \eta_b=\|r_b\|^2,
\quad E=\sum_b\eta_b.
$$

$\eta_b$ 是真实标签 $b$ 下的错误率。以 $\psi_b,c_b,r_b$ 为列分别组成 $\Psi,C,R$，则 $\Psi=C+R$，且

$$
C^\dagger C=\operatorname{diag}(1-\eta_b),
\qquad \|R\|_{\mathrm{HS}}^2=E.
$$

利用 $A_n$ 的零对角、式（3.2）及其对称性，全部有向邻边的虚部成对抵消，得到一个实数恒等式

$$
2e_nx=\operatorname{Tr}(A_n\Psi^\dagger\Psi)
=2\operatorname{Re}\operatorname{Tr}(A_nC^\dagger R)
+\operatorname{Tr}(A_nR^\dagger R).
\tag{3.3}
$$

Hilbert–Schmidt Cauchy 不等式给出

$$
\begin{aligned}
|\operatorname{Tr}(A_nC^\dagger R)|
&\le\|CA_n\|_{\mathrm{HS}}\|R\|_{\mathrm{HS}},\\
\|CA_n\|_{\mathrm{HS}}^2
&=\operatorname{Tr}(A_nC^\dagger CA_n)
=\sum_b d_b(1-\eta_b)\le2e_n.
\end{aligned}
$$

又因 $A_n\le nI$ 且 $R^\dagger R\ge0$，有 $\operatorname{Tr}(A_nR^\dagger R)\le nE$。所以

$$
2e_nx\le2\sqrt{2e_nE}+nE.
\tag{3.4}
$$

这里的 $E$ 只计每个真实标签的分类错误一次；没有把同一个错误当成多个互相独立的二元失败。图的度数仅出现在同一个迹估计中。正确答案的正交结果空间约束重叠是已有量子查询下界方法，见 [Ambainis，*Quantum lower bounds by quantum arguments*](https://arxiv.org/abs/quant-ph/0002066)，§3、引理 1；式（3.2）与全邻边迹汇总是此固定源下的具体推导。

由于 $e_n>0$，令 $y=\sqrt{E/(2e_n)}$，式（3.4）等价于 $x\le2y+ny^2$。右侧在 $y\ge0$ 单调，解得

$$
y\ge\frac{\sqrt{1+nx}-1}{n}
=\frac{x}{1+\sqrt{1+nx}}.
$$

于是 $E/M_n\ge\ell_n(x)$。常数不依赖探针、测量或源无关随机种子；对每个种子应用再平均，包含全部随机化协议。取协议错误率的下确界，证明 (A)。

### 3.4 可达联合末端测量与其精确分数

对 $|+\rangle^{\otimes n}$，两个候选输出在相同位置的内积为 $1$，在不同位置的内积为 $\cos(2q\theta)=x$，所以 $G_{bc}=x^{h(b,c)}$，其中对角值在 $x=0$ 仍为 $1$。

$q>0$ 时 $0\le x<1$，每个位点的两个候选向量线性无关。它们的完整张量积族是 $2^n$ 维空间的一组基，合法词子族也线性无关，故 $G>0$。

令 $U=\Phi G^{-1/2}$，则 $U^\dagger U=I$，各列 $\mu_b$ 正交归一，且 $U^\dagger\Phi=\sqrt G$。测量这些一维正交投影，将正交补并入固定标签，形成完整末端测量。候选输入全在 $\Phi$ 的列空间，正交补的归属不影响其概率。真实标签 $b$ 的正确概率为

$$
|\langle\mu_b,\phi_b\rangle|^2=((\sqrt G)_{bb})^2,
$$

均匀平均得到式（2.2）。$G^{-1/2}$ 是根据公开候选模型作的有限矩阵运算，不是未知源的逆调用，也不要求向源取得每个候选标签的样本。该正交化是定义 1.5 所引成熟 SRM 方法，不作为新增数学内容。

### 3.5 SRM 的有限误差界

令 $H=G-I$、$r=(1+x)^n-1$。从固定 $b$ 出发，距离 $h$ 的合法词数不超过 $\binom nh$，故 $H$ 的绝对行和至多为 $r$。$H$ 实对称，所以 $\|H\|_{\mathrm{op}}\le r$。若 $r<1$，$G$ 的最小特征值至少为 $1-r>0$。

记 $S=\sqrt G$。由 $S^2=G$、$G_{bb}=1$ 得

$$
1-P_{\mathrm{SRM}}
=\frac1{M_n}\sum_{b\ne c}|S_{bc}|^2
\le\frac1{M_n}\|S-I\|_{\mathrm{HS}}^2.
$$

在 $G$ 的本征基中，逐特征值 $\lambda$ 有

$$
(\sqrt\lambda-1)^2=\frac{(\lambda-1)^2}{(1+\sqrt\lambda)^2},
\qquad
\|S-I\|_{\mathrm{HS}}^2
\le\frac{\|H\|_{\mathrm{HS}}^2}{(1+\sqrt{1-r})^2}.
$$

距离 $1$ 的有序合法对恰有 $2e_n$ 个；距离 $h\ge2$ 的有序对至多有 $M_n\binom nh$ 个，因而

$$
\frac{\|H\|_{\mathrm{HS}}^2}{M_n}
\le\frac{2e_n}{M_n}x^2+\sum_{h=2}^n\binom nh x^{2h}
=\frac{2e_n}{M_n}x^2+(1+x^2)^n-1-nx^2.
$$

代入并使用 $1-r=2-(1+x)^n$，得到式（2.3），证明 (B)。SRM 与平方根的谱估计是成熟步骤；此式额外保留合法邻边的准确数目，而不将全部有序对都按最坏距离估计。

### 3.6 任意探针最优首项的夹逼

固定 $n$。当 $x\to0$ 时，

$$
\ell_n(x)=\frac{e_n}{2M_n}x^2+O_n(x^3).
$$

$u_n$ 的分子为 $(2e_n/M_n)x^2+O_n(x^4)$，分母为 $4+O_n(x)$，所以

$$
u_n(x)=\frac{e_n}{2M_n}x^2+O_n(x^3).
$$

在足够小的 $x$ 下，(A)、(B) 同时适用，并有

$$
\ell_n(x)\le\varepsilon_n^\star(L,q)
\le1-P_{\mathrm{SRM}}\le u_n(x).
$$

两端首项相同，得到式（2.5），也得到 $1-P_{\mathrm{SRM}}$ 的相同展开。此论证不假定最优探针随 $x$ 连续，不把一个固定态族的测量优化等同于源输入优化。

固定 $r\ge1$、$q=L-r$ 时

$$
x=\sin\left(\frac{\pi r}{2L}\right)
=\frac{\pi r}{2L}+O_r(L^{-3}),
$$

代入式（2.5）即得式（2.6），证明 (C)。固定先验纯态族趋于正交时的测量渐近最优性是已有结果，见 [Tyson，*Error rates of Belavkin weighted quantum measurements and a converse to Holevo’s asymptotic optimality theorem*](https://arxiv.org/abs/0907.1884v1)，§§1.3–1.4；等先验下各幂权版本相同。那项结果不供应本卷对全部源输入的统一下界，后者由 §§3.2–3.3 给出。

### 3.7 对每个读出串最大似然译码

设逐位 $Y$ 测量的特征值为 $v_i\in\{-1,+1\}$，按原卷规则 $\widehat s_i=-v_i$ 转成位读出 $y_i=(1+v_i)/2$。给定固定 $b$，各位条件独立，单个位正确概率为 $p$，因此

$$
\Pr(y\mid b)=p^{n-h(y,b)}(1-p)^{h(y,b)}.
\tag{3.5}
$$

这里只用给定 $b$ 后的测量条件独立性，没有拆开合法词先验。均匀先验下，随机译码不优于逐个 $y$ 选择最大似然合法词，所以最优分数是

$$
P_Y^{\mathrm{ML}}=\frac1{M_n}\sum_{y\in\{0,1\}^n}
\max_{b\in B_n}\Pr(y\mid b).
\tag{3.6}
$$

这处理每一个读出串，包括非法读出；没有丢弃非法样本或重新归一化。$1/2<p<1$ 时最大似然等价于最近 Hamming 合法词；$p=1/2$ 时所有标签似然相同。$p=1$ 时合法读出正确、非法读出概率为零，最近词规则仍达到最优。

最近合法词不需在 $y$ 的零位新增 $1$：删去这样的新增 $1$ 仍合法，并缩短距离。因此只需删去 $y$ 中的一些 $1$。长度为 $a$ 的连续 $1$ 段最多保留 $\lceil a/2\rceil$ 个互不相邻位置，至少删除 $\lfloor a/2\rfloor$ 个；交替保留达到此数。以零分隔的各段互不干扰，故

$$
d(y,B_n)=\sum_{\text{连续 }1\text{ 段}}\left\lfloor\frac a2\right\rfloor.
\tag{3.7}
$$

令 $t=(1-p)/p$，并定义 $Z_n(t)=\sum_y t^{d(y,B_n)}$。以 $E_k,O_k$ 分别记录末端连续 $1$ 段长度为偶数、奇数的加权和，空段归偶数。加一个 $0$ 总进入偶数状态；加一个 $1$ 时，偶转奇不增加删除数，奇转偶增加一次删除。因此

$$
E_{k+1}=E_k+(1+t)O_k,
\qquad O_{k+1}=E_k,
\qquad E_0=1,\quad O_0=0.
$$

两状态转移矩阵满足其特征多项式 $\lambda^2-\lambda-(1+t)$，所以 $Z_k=E_k+O_k$ 满足

$$
Z_0=1,\quad Z_1=2,\quad
Z_n=Z_{n-1}+(1+t)Z_{n-2}.
$$

由式（3.5）–（3.7），最优分数为 $p^n Z_n/M_n$。令 $T_n=p^nZ_n$，使用 $p^2(1+t)=p$，得到式（2.7）。$p=1/2$ 时 $T_n=1$，分数为 $1/M_n$；$p=1$ 时 $T_n=M_n$，分数为 $1$。$t=0$ 采用 $0^0=1$，无须排除端点。

### 3.8 每个固定长度的严格 Bayes 分离

由 $T_n(1)=M_n$，对递推求导并取 $p=1$，得

$$
D_0=0,\quad D_1=2,\quad
D_n=M_n+D_{n-1}+D_{n-2}\quad(n\ge2).
$$

于是 $K_0=K_1=0,K_2=1$；对 $n\ge3$，结合式（3.1）有

$$
\begin{aligned}
K_n&=K_{n-1}+K_{n-2}+M_n-2M_{n-2}\\
&=K_{n-1}+K_{n-2}+M_{n-3}.
\end{aligned}
$$

因此 $n\ge2$ 时 $K_n>0$。又因 $p=1-x^2/4+O(x^4)$，

$$
1-P_Y^{\mathrm{ML}}=\frac{D_n}{4M_n}x^2+O_n(x^4).
$$

与 §3.6 的 SRM 展开相减，得到式（2.9）。它已经允许局部读出利用全部合法约束，因而分离不来自忽略经典后处理。

### 3.9 完整五词域上的显式常数

完整 $B_3=\{000,100,010,101,001\}$ 包括 $000$。递推给出 $M_3=e_3=5$、$T_3(p)=2p^3+3p^2$；没有筛选子域或增加来源建议。

若 $0<x\le1/20$，则

$$
2-(1+x)^3\ge\frac{6739}{8000}>\frac{81}{100}.
$$

式（2.3）的分子为 $2x^2+3x^4+x^6$，故

$$
u_3(x)
\le\frac{2+3/400+1/160000}{361/100}x^2
=\frac{321201}{577600}x^2
<\frac9{16}x^2.
\tag{3.8}
$$

令 $a=1-p=(1-\sqrt{1-x^2})/2$。有理化给出

$$
\frac{x^2}{4}\le a\le\frac{x^2}{2}\le\frac1{800}.
$$

直接展开受限精确式得到

$$
\begin{aligned}
1-P_Y^{\mathrm{ML}}
&=\frac{12a-9a^2+2a^3}{5}\\
&\ge\frac{12-9/800}{20}x^2
=\frac{9591}{16000}x^2
>\frac{19}{32}x^2.
\end{aligned}
\tag{3.9}
$$

由于 $1-P_{\mathrm{SRM}}\le u_3(x)$，相减得 $P_{\mathrm{SRM}}-P_Y^{\mathrm{ML}}\ge x^2/32>0$。所有常数由符号不等式推出，不依赖数值优化或查表枚举。$q=L-1$ 时 $x=\sin(\pi/(2L))$；$L\ge32$ 给出 $0<x\le\pi/64<1/20$，因此式（2.10）在原整数合同中有实际参数，完成 (D)。

### 3.10 二向量旋转证明 SRM 并非精确最优

令 $A_2$ 为距离恰为 $2$ 的指示矩阵。固定 $n$ 时

$$
G=I+xA_n+x^2A_2+O_n(x^3).
$$

在 $\|G-I\|_{\mathrm{op}}<1$ 时，收敛的矩阵平方根级数给出

$$
S=\sqrt G
=I+\frac x2 A_n
+x^2\left(\frac{A_2}{2}-\frac{A_n^2}{8}\right)+O_n(x^3).
$$

于是 $S_{bb}=1-d_bx^2/8+O_n(x^3)$，邻接 $b,c$ 满足 $S_{bc}=x/2+O_n(x^2)$。取 $b=0^n$、$c=(0,1,0,\ldots,0)$，两者均合法且相邻。$b$ 的度数为 $n$；$c$ 可删唯一的 $1$，或在第 $4$ 至 $n$ 位之一新增 $1$，故度数为 $n-2$。因此

$$
S_{bb}-S_{cc}=-\frac{x^2}{4}+O_n(x^3).
$$

其他测量向量不变，仅作

$$
\mu_b(t)=\cos t\,\mu_b+\sin t\,\mu_c,
\qquad
\mu_c(t)=-\sin t\,\mu_b+\cos t\,\mu_c.
$$

这些向量仍正交归一，张成空间不变，正交补的完成也不变，因此是原合同内合法末端测量。输入和调用次数完全相同。记其成功率为 $P(t)$。只有真实标签 $b,c$ 的正确概率改变；$S$ 实对称，故这两项为

$$
\frac1{M_n}
\left[(\cos t\,S_{bb}+\sin t\,S_{bc})^2
+(\cos t\,S_{cc}-\sin t\,S_{bc})^2\right].
$$

直接微分得

$$
P'(0)=\frac2{M_n}S_{bc}(S_{bb}-S_{cc})
=-\frac{x^3}{4M_n}+O_n(x^4).
$$

固定 $n$ 且 $x>0$ 足够小时导数严格为负，取足够小的负 $t$ 即有 $P(t)>P(0)=P_{\mathrm{SRM}}$，证明 (E)。这是非平稳性证据，不给出精确最优旋转角、最优值或最优余项。定理 2.1 证毕。

## 4. 端点、minimax 与完整五窗服务

**推论 4.1（端点与 minimax 的范围）。** $q=0$ 时输出与 $b$ 无关，不能用退化 Gram 矩阵的 $G^{-1/2}$；均匀猜词给出 Bayes 与 minimax 分数均为 $1/M_n$。$q=L$ 时 $x=0,G=I$，联合测量和原局部读出均无误。完整合法词及整条服务的尖锐零误差阈值 $L$ 直接复用 SIC 时间取得卷定理 2.1(iv)、(vi)。对全部 $0\le q\le L$，有

$$
\max\left\{\frac1{M_n},p^n\right\}
\le\beta_n^{\mathrm{mm}}(L,q)
\le\beta_n(L,q)\le1-\ell_n(x).
\tag{4.1}
$$

证明。$q=0$ 时一个源无关答案分布的均匀成功率至多为 $1/M_n$，最小成功率不超过平均值，均匀猜词逐源达到该值。$q=L$ 的结论由 $G=I$ 和所引阈值取得。式（4.1）的左界分别由均匀猜词、逐位原读出并将非法读出归给固定合法词实现。后者在每个合法 $b$ 下至少保留全位都读对的事件，其概率为 $p^n$；归属非法输出不减少该事件。中间不等式来自最小值不超过均值，右界来自定理 2.1(A)。内部 $q$ 的 minimax 最优值不由这些不等式确定，也没有证明 Bayes 与 minimax 相等。证毕。

**定义 4.2（整条服务成功）。** 将合法词按低位到高位分成 $W_j(b)=(b_{3j-2},b_{3j-1},b_{3j})$，$1\le j\le N$。每窗属于 $\Sigma=\{000,100,010,101,001\}$，分别对应 $\mathrm{null},2,3,2\ 5,5$；接缝仍满足 $b_{3j}b_{3j+1}=0$。这是 [FIB 白盒卷](https://github.com/the-omega-institute/trureturing/blob/aeb45cd336fe958eabf799ee4580bbad1e364077/docs/develop/theory/FIB_ATOM_MACHINE_LEARNING_WHITEBOX.md) 定义 2.1 的字典及 SIC 时间取得卷定义 1.5 的完整合法域。

安装输出为闭合确定性服务：每个合法索引请求 $j$ 返回对应窗口；安装和每个合法回复均有限终止。安装后保留取得数据，不再访问源或源相关建议。安装可随机化，安装后的服务确定。整条成功要求每一条有限合法查询历史上的回复都正确，包括重复索引和依回复自适应选择的索引。

指针版本另保留初值为 $1$ 的 $a\in\{1,\ldots,N+1\}$。索引读不改 $a$；$\mathrm{Next}$ 恰在 $a\le N$ 时合法，返回 $W_a(b)$ 并把 $a$ 加一。此接口没有 $\mathrm{End}$；末尾 null 照常占用三位。

**推论 4.3（整词恢复与整条服务安装同分数）。** 在相同一块式取得合同和有限终止要求下，合法词恢复与定义 4.2 的索引服务、指针服务安装具有相同最优均匀 Bayes 分数；分别对 minimax 也相同。因此定理 2.1 与式（4.1）直接适用于这些整条服务。

证明。给定估计合法词 $\widehat b$，存入闭合确定性查表服务，索引 $j$ 返回 $W_j(\widehat b)$；指针版本保留当前 $a$ 并执行定义 4.2 的更新。若 $\widehat b=b$，每条有限合法历史都正确：索引读保留词和指针，$\mathrm{Next}$ 给正确窗且两边同时递增指针，逐词归纳保持回复、合法域及更新。若 $\widehat b\ne b$，某个窗口不同，该索引的一次查询立即区分。因此此安装的整条服务成功事件恰等于整词恢复事件。

反向，给定任一满足有限终止要求的安装服务，安装后执行固定索引扫描 $1,\ldots,N$，把回复串译成词；非法串归给固定合法词。扫描有限且不调用源。若原服务在全部有限历史上正确，此扫描必恢复 $b$；故所成译码的逐来源成功率至少为原服务的整条成功率。末端服务输出及有限扫描可后处理为有限标签 POVM，仍属定义 1.3。该扫描是上界归约，不是认证任意服务对所有历史正确的有限检验。

正向逐源保分，反向逐源不降低分，取均匀平均或逐源最小值，再取协议上确界，得到两个分数相等。指针服务有同样的索引扫描，且正向安装的 pointer 更新已经逐词保持，故同理成立。证毕。

**数学引文 4.4（任务依赖白盒对应）。** FIB 白盒卷定义 8.1 要求解释同时保留读数、合法域和更新。这里任务状态为 $(s(b),a)$，解释为 $(b,a)$；符号码公开可逆，索引读取和 $\mathrm{Next}$ 的读数、域与后继逐点对应。取得到的完整合法词足以安装这种任务服务。相同 SIC 档案则不足以决定服务：$0^n$ 和 $(1,0,\ldots,0)$ 档案相同而第一窗不同，这一纤维见证直接复用 SIC 时间取得卷定理 2.1(vi)。

另一固定来源 [原生守卫延拓卷](https://github.com/the-omega-institute/trureturing/blob/aeb45cd336fe958eabf799ee4580bbad1e364077/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_DETERMINANT_AND_NATIVE_GUARD_CONTINUATION.md) 命题 10.5 使用当前回复条件化后的继续守卫读取关联；其来源、读出和更新不同，不供应此量子实验的概率律。本卷没有建立与原生 FIB 生成树、破坏性根操作、训练状态或任何具体机器学习网络的源及操作对应，因而不从上述服务结果推出实际网络改善。

## 5. 资源假设与有限成本边界

**假设 5.1（普通调用、准备和校准）。** 可达策略使用一次 $|0\rangle^{\otimes n}$ 准备以及 $n$ 个已知 $H$ 门得到 $|+\rangle^{\otimes n}$，不需输入参考。随后恰好 $q$ 次调用同一完整设备，调用间不操作系统。已知 $n,L$、张量源承诺、因子标签、带符号标准以及理想准备读出是必要条件；校准另计未求出的价格 $C_{\mathrm{cal}}$。没有逆源、未知 controlled-$U$、免费复位、重新抽样或额外标签建议。

**假设 5.2（联合测量能力及其价格）。** 任意理想联合末端 POVM 是原一块式合同已有的数学能力。SRM 向量可在原 $2^n$ 维系统补成正交基，旋转保持这一性质，故理想构造不要求额外量子参考。但其综合、控制和读出另计价格 $C_{\mathrm{joint}}(n,L,q)$，本文未求出该价格，也没有沿用原局部方案的 $3n$ 门成本。

若末端硬件另被限制为原局部 $S^\dagger,H$ 和逐位计算基测量，联合构造的可达结论不直接转移；此时式（2.7）的指定 $Y$ 读出类仍适用。严格成功率优势比较的是相同源、准备和普通调用数，不证明包含全部实现价格后的成本优势。

**假设 5.3（经典描述、计算与保留）。** 合法域、均匀先验和测量描述只依赖公开参数。矩阵构造及译码对每个固定有限 $n,L,q$ 都是有限任务，未证明高效，成本可随 $n$ 指数增长。查表安装显式保留 $n$ 位；指针版本另保留有限指针。查询、存储寿命和计算费用另计，这些保留量不是最小存储定理。式（2.7）的分数递推不自动给任意服务或联合测量的低成本实现。

**假设 5.4（理想性与噪声范围）。** 定理 2.1 只对所述理想源成立。没有证明 SRM 的界或严格分离在角度扰动、一般制备读出噪声、源记忆或失校准下仍成立。SIC 时间取得卷的局部方案角度容差结论不能自动转移为联合测量容差定理。

## 6. 数学供应、增量范围与未解问题

**数学引文 6.1（成熟步骤的归属）。** 各供应者只承担列明的步骤。

| 数学来源 | 使用范围与边界 |
| --- | --- |
| SIC 时间取得卷，固定快照的定义 1.1、1.3、1.5 和定理 2.1 | 固定张量源、一块式合同、完整合法域、SIC 档案常性、score-only 分数及零误差阈值；不供应相关先验内部 $q$ 的有限误差最优值。 |
| FIB 白盒卷，固定快照的定义 2.1、6.1、8.1 | 五窗字典、接缝与 terminal 的区别，以及任务读数／域／更新条件；本卷没有加入其 canonical $\mathrm{End}$。 |
| [Eldar、Forney，*On Quantum Detection and the Square-Root Measurement*](https://arxiv.org/abs/quant-ph/0005132)，定理 3、§8、定理 4 | `literature-attested`：SRM 正交化构造及几何均匀群轨道态族的特殊最优性。合法词集合不闭合于异或，例如 $100,010$ 合法而 $110$ 非法；来源酉交换不提供完整群轨道最优性。 |
| [Tyson，*Error rates of Belavkin weighted quantum measurements and a converse to Holevo’s asymptotic optimality theorem*](https://arxiv.org/abs/0907.1884v1)，§§1.3–1.4 | `literature-attested`：等先验下各幂权 SRM 相同、固定先验近正交态族的测量渐近最优性；不承担任意源输入的统一下界。 |
| [Ambainis，*Quantum lower bounds by quantum arguments*](https://arxiv.org/abs/quant-ph/0002066)，§3、引理 1 | `literature-attested`：不同正确答案的正交结果空间约束输出重叠的方法；式（3.3）–（3.4）的全合法邻边 Bayes 汇总由本文展开。 |
| [Klavžar、Mollard、Petkovšek，*The degree sequence of Fibonacci and Lucas cubes*](https://users.fmf.uni-lj.si/klavzar/preprints/DegSeqRevised.pdf)，§§1–2 | `literature-attested`：Fibonacci cube、首段分解和跨部分匹配；边数递推及闭式仅为计数步骤，不列为新增内容。 |
| [仓内一般记录 Gram 谱界](https://github.com/the-omega-institute/trureturing/blob/aeb45cd336fe958eabf799ee4580bbad1e364077/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md)，§8、§16.5；[Montanaro 文献条目](https://github.com/the-omega-institute/trureturing/blob/aeb45cd336fe958eabf799ee4580bbad1e364077/Library/Quantum/montanaro2007distinguishability.md) | 已有 SRM 完成、平方根谱估计与逐标签平方重叠行和界。本文不把这些方法重记为增量；它们不单独给出所有探针的合法词邻边界和所列最优系数。 |
| [仓内 EquiprobablePgmActiveSetRefutation](https://github.com/the-omega-institute/trureturing/blob/aeb45cd336fe958eabf799ee4580bbad1e364077/D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.lean) | 三个正定混态的 active-set 分数反例，与此合法词纯态族、源输入优化及二向量旋转命题不同；不作为定理 2.1 的供应者。 |

**数学引文 6.2（本卷综合推导的范围）。** 定理 2.1 中覆盖任意输入及参考的邻边实部约束与整体 Bayes 下界、两端闭合的全合法域最优误差首项、指定局部 $Y$ 读出经最优全局经典译码后的严格联合测量优势，以及 SRM 的显式非平稳性证据，属于本卷完整普通证明给出的 `repo-derived` 综合。SRM 本身、一般谱估计、固定态族的近正交测量最优性、Fibonacci 图计数和服务的既有任务对应均不作为新增内容。此归属限定于所列来源与对象，不声称全球优先性或物理实现。

**开放问题 6.3（有限参数最优与后续余项）。** 一般内部整数 $0<q<L$ 的完整 $B_{3N}$ 最优 Bayes 值、minimax 值及最优源输入结构仍未确定。$P_{\mathrm{SRM}}$ 是精确可达分数，$T_n(p)/M_n$ 是指定受限协议类的精确最优分数；$1-\ell_n(x)$ 是不能超过的上界，$1-u_n(x)$ 只在其明确区间给出可达下界。它们不是同一层次的最优值，也没有数值最优候选。

在已经闭合的 $x^2$ 首项之后，最优余项的第一个非零阶及其系数是什么，改善是否只需末端测量调整，还是需要改变输入，仍未解。§3.10 排除了直接以 SRM 分数作为完整答案，却没有结算该余项。增长 $n$ 的一致渐近、内部 $q$ 的 minimax 分离、所有局部或 LOCC 读出类的最优值，以及噪声与校准成本问题均保留为不同问题；固定 $n$ 的 $O_n$ 估计和完整 $B_3$ 常数不能替代这些结论。

## 追加锚（本行以下为增补区）
