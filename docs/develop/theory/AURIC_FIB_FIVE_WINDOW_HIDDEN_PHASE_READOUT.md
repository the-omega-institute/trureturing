# AURIC FIB 五窗口隐藏终端相位读出

> 本卷是《AURIC FIB 五窗口切换记忆》的独立后继数学参考卷，采用普通 `generic-v1` 结构。正文陈述当前定义、条件性结论、完整证明及适用边界；后续增补从文末追加锚开始。本卷只撤去已知 $A$ 先交替模型的终端奇偶标签，不改变更新通道或调度。

## 1. 单次读出的三个控制合同

**定义 1.1（完整输入、共同相位与两结果读出）。** 保留系统恰为 $H=\mathbb C^5$。固定前卷的 $\eta=1/2$、两个完整 CPTP 更新 $A,B$，以及输入无关的实际序列 $A,B,A,B,\ldots$。起始为 $A$ 先是已知条件；仅终端奇偶相位不公开。编码位 $b\in\{0,1\}$ 均匀分布，编码为任意完整五维密度对 $\rho_0,\rho_1$，选择编码时不能知道实际终端相位。编码随机性也与该相位独立。

令 $j=0$ 表示偶数输出相位，$j=1$ 表示奇数输出相位，相应完整输入极限通道为 $\Lambda_j$。终端效应满足 $0\le F\le I$，结果 $F$ 判为零，结果 $I-F$ 判为一。分支平均错误为

$$
e_j(F;\rho_0,\rho_1)
=\frac{\operatorname{Tr}((I-F)\Lambda_j(\rho_0))
+\operatorname{Tr}(F\Lambda_j(\rho_1))}{2}.
\tag{1.1}
$$

式 (1.1) 的两个位假设使用同一个分支 $j$。本文的三个合同分别是：公开 $j$ 并允许选择 $F_j$；不公开 $j$ 并以一个固定 $F$ 最小化 $\max\{e_0,e_1\}$；以及真实随机但不公开 $j$，已知 $\theta=\Pr(j=0)$，用一个固定 $F$ 最小化 $\theta e_0+(1-\theta)e_1$。第三个合同要求相位律与 $b$、编码随机性独立，同一个 $\theta$ 用于两个假设。$0<\theta<1$ 是非退化随机合同，$\theta=0,1$ 是边界。

**约定 1.2（允许的终端操作及不同的错误标准）。** 任意固定终端 CPTP 预处理 $\mathcal D$ 后再测量效应 $G$，等同于直接测量 $F=\mathcal D^\dagger(G)$；保持单位元的正伴随使它仍是效应。独立随机选择固定测量也只给出平均效应。因此以上优化已包括这些操作。依赖实际相位的预处理、读出选择或隐藏的时间控制不在相位盲合同内。

为消除量词混淆，记

$$
\begin{aligned}
e_{j,0}&=\operatorname{Tr}((I-F)\Lambda_j(\rho_0)),\\
e_{j,1}&=\operatorname{Tr}(F\Lambda_j(\rho_1)).
\end{aligned}
$$

本文的对抗目标是 $\max_j(e_{j,0}+e_{j,1})/2$。允许对每个位分别选相位会给出 $(\max_j e_{j,0}+\max_j e_{j,1})/2$；最坏单个位错误则是 $\max_{j,b}e_{j,b}$。这些是不同的目标函数，后两者不作为本文的优化靶。未知起始相位也不是撤去终端相位的同一合同。

**定理 1.3（终端相位控制的精确单次价值）。** 在定义 1.1 的完整输入极限模型中，全局最优平均错误为

$$
\begin{aligned}
e_{\mathrm{pub}}&=0,\\
e_{\mathrm{mm}}&=\frac{3-\sqrt5}{8},\\
e_\theta&=\frac{3-\sqrt{5+4(2\theta-1)^2}}8
\qquad(0\le\theta\le1).
\end{aligned}
\tag{1.2}
$$

在每一个合同下，全部全局最优极限编码对，除交换零、一标签外，恰为

$$
\rho_0=P,\qquad \rho_1\text{ 为任意支持于 }\ker E\text{ 的密度}.
\tag{1.3}
$$

因此前卷的 $P,M$ 和 $P,|w_0\rangle\langle w_0|$ 都达到极限最优值。一个明确的固定投影读出达到最坏相位值，且在 $S$ 共轭下不变；每个已知 $\theta$ 也有明确的固定投影读出。它们的全部最优效应族在第 5、6 节给出。

证明由第 3–6 节完成。公开相位的最优错误为零，故擦除终端相位的精确错误代价分别就是式 (1.2) 的 $e_{\mathrm{mm}}$ 与 $e_\theta$。前者严格正；后者在 $0<\theta<1$ 严格正，在两个确定相位端点为零。这些是均匀二元位一次读出的错误概率差，不是容量、总资源效率或物理实现声明。

## 2. 与前卷完全一致的五维接口

**定义 2.1（完整通道、固定态与瞬态效应）。** 在有序正交基 $e_0,\ldots,e_4$ 中，令

$$
\begin{gathered}
q=1/\sqrt2,\qquad u=q(e_0+e_3),\qquad v=q(e_1+e_4),\qquad z=e_2,\\
R=\operatorname{span}\{u,v,z\},\qquad s=(u+v+z)/\sqrt3,\\
P=|s\rangle\langle s|,\qquad M=(P_R-P)/2,\qquad
w_0=(u-2v+z)/\sqrt6.
\end{gathered}
\tag{2.1}
$$

完整五维 Kraus 算子及相位算子为

$$
\begin{aligned}
K_0&=|u\rangle\langle e_0|+q|v\rangle\langle e_2|+|z\rangle\langle e_4|,\\
K_1&=|u\rangle\langle e_1|+q|v\rangle\langle e_2|+|z\rangle\langle e_3|,\\
C(X)&=K_0XK_0^\dagger+K_1XK_1^\dagger,\\
S&=\operatorname{diag}(1,-1,1,1,1),\qquad \mathcal U(X)=SXS,\\
A&=\mathcal U\circ C,\qquad B=C\circ\mathcal U,\qquad
v_-=Sv=q(-e_1+e_4).
\end{aligned}
\tag{2.2}
$$

所有算子在复 Hilbert 空间上解释，内积对第一变量共轭线性。设

$$
d=(e_0-e_1-e_3+e_4)/2,\qquad
E=P+\frac23|d\rangle\langle d|.
\tag{2.3}
$$

$d$ 是 $R^\perp$ 内单位向量，$E$ 的完整谱为 $1,2/3,0,0,0$。

**约定 2.2（复用的完整映射结果）。** 前卷命题 4.2 与定理 5.1 给出 $C(P)=P$、$C(M)=M$，以及对每个复矩阵 $X\in M_5(\mathbb C)$ 的完整公式

$$
\begin{aligned}
\mathcal T(X)&=P\operatorname{Tr}(EX)+M\operatorname{Tr}((I-E)X),\\
C^\dagger(P)&=E,\qquad C^\dagger(E)=E,\\
C^n-\mathcal T&=(-1/2)^{n-2}(C^2-\mathcal T)\quad(n\ge2),\\
\|C^n-\mathcal T\|_\diamond&\le\epsilon_n,
\qquad\epsilon_n=\frac43\,2^{-(n-2)}\quad(n\ge2).
\end{aligned}
\tag{2.4}
$$

这里迹范数不除以二；$\|L\|_\diamond$ 是对任意复输入及任意有限恒等参考放大的迹范数算子范数。引用这个范数界只是为了完整输入的一致估计，不授予操作方一个保留参考系统。

前卷定理 4.1 的实际 $A$ 先调度恒等式为

$$
T_{2m}=C^{2m},\qquad T_{2m+1}=\mathcal U\circ C^{2m+1}
\qquad(m\ge0).
\tag{2.5}
$$

所以两条完整输入极限为 $\Lambda_0=\mathcal T$、$\Lambda_1=\mathcal U\circ\mathcal T$。记

$$
P_j=S^jPS^j,\quad M_j=S^jMS^j,\quad D_j=P_j-M_j,
$$

则

$$
\Lambda_j(X)=M_j\operatorname{Tr}X+D_j\operatorname{Tr}(EX).
\tag{2.6}
$$

两个分支的输入效应同为 $E$；$A$ 先的合同没有输入端 $S$。以上完整映射结果归于前卷，不从局部人口等式推定，也不在本卷重证前卷的量子记忆、NPT、精确码或任意切换定理。

## 3. 全输入编码约化与完整端点族

**引理 3.1（五个输入维度上的唯一幸存标量）。** 对任意初始密度 $\rho$，定义 $t=\operatorname{Tr}(E\rho)$。则 $0\le t\le1$，且

$$
t=1\Longleftrightarrow\rho=P,\qquad
t=0\Longleftrightarrow\operatorname{supp}\rho\subseteq\ker E.
\tag{3.1}
$$

两密度在两个极限分支的输出分别相同，当且仅当它们的 $t$ 相同。对任意复矩阵，两个极限映射的共同核为

$$
\{X:\operatorname{Tr}X=0,\ \operatorname{Tr}(EX)=0\}.
\tag{3.2}
$$

证明。完整 Kraus 算子实际给出

$$
\begin{aligned}
x_0=K_0^\dagger s&=(e_0+e_4)/\sqrt3+e_2/\sqrt6,\\
x_1=K_1^\dagger s&=(e_1+e_3)/\sqrt3+e_2/\sqrt6,\\
(x_0+x_1)/\sqrt2&=s,\qquad
(x_0-x_1)/\sqrt2=\sqrt{2/3}\,d.
\end{aligned}
$$

因此 $C^\dagger(P)=|x_0\rangle\langle x_0|+|x_1\rangle\langle x_1|=E$，这里明确保留了 $R$ 外的输入。补全 $s,d$ 为五维正交基，得

$$
\begin{aligned}
t&=\langle s,\rho s\rangle+\frac23\langle d,\rho d\rangle,\\
1-t&=\frac13\langle d,\rho d\rangle
+\operatorname{Tr}(P_{\ker E}\rho).
\end{aligned}
\tag{3.3}
$$

各项非负，故 $t\in[0,1]$。若 $t=1$，$d$ 及 $\ker E$ 的全部对角人口为零；正性给出的 $|\rho_{ab}|^2\le\rho_{aa}\rho_{bb}$ 迫使对应整行整列为零，仅余 $P$。若 $t=0$，同理删去 $s,d$ 的行列，密度支持于 $\ker E$。逆向由定义即得。

由式 (2.6)，密度输出恰为 $M_j+tD_j$；$D_j\ne0$，故同一分支中输出相同等价于 $t$ 相同。对一般复 $X$，若 $\Lambda_j(X)=0$，保迹先给出 $\operatorname{Tr}X=0$，再由 $D_j\ne0$ 给出 $\operatorname{Tr}(EX)=0$；逆向也成立。这说明结论针对整个复代数，而非先删掉相干或限制人口所得的商。特别地，输入 $|d\rangle\langle d|$ 有 $t=2/3$，绝不能把 $E$ 替换成 $P$。$\square$

**引理 3.2（任意密度对的完整约化）。** 对任意密度对，记

$$
t_b=\operatorname{Tr}(E\rho_b),\qquad \xi=t_0-t_1\in[-1,1].
$$

则对每个效应，

$$
\Lambda_j(\rho_0-\rho_1)=\xi D_j,\qquad
e_j=\frac{1-\xi\operatorname{Tr}(FD_j)}2.
\tag{3.4}
$$

除交换位标签和互补效应外，可按 $\xi\ge0$ 优化。对每个既定编码对，三个合同的最优错误分别为

$$
\begin{aligned}
e_{\mathrm{pub}}(\rho_0,\rho_1)&=\frac{1-|\xi|}{2},\\
e_{\mathrm{mm}}(\rho_0,\rho_1)&=\frac{1-|\xi|\lambda_*}{2},\\
e_\theta(\rho_0,\rho_1)&=\frac12-\frac{|\xi|(1+\delta_\theta)}8,
\end{aligned}
\tag{3.5}
$$

其中 $\lambda_*=(1+\sqrt5)/4$、$\delta_\theta=\sqrt{5+4(2\theta-1)^2}$。

证明。两个输入迹相等，式 (2.6) 的 $M_j$ 项相消，得到式 (3.4)。$\operatorname{Tr}D_j=0$，所以将 $F$ 换为 $I-F$ 会反转信号符号；交换编码标签也将 $\xi$ 反号。后两式的测量常数将在第 5、6 节直接求出。公开分支中 $D_j$ 的谱为 $1,-1/2,-1/2,0,0$，正谱迹为一；第 4 节的谱变分引理给出第一式，$P_j$ 在 $\xi\ge0$ 时达到它。若 $\xi=0$，三个合同的每个效应错误都是 $1/2$，也符合式 (3.5)。$\square$

**推论 3.3（全局最优编码恰为端点编码）。** 式 (1.3) 是三个极限合同的完整最优编码族。

证明。式 (3.5) 中三个信号常数均严格正，故每个全局最优编码必须且只须有 $|\xi|=1$。两个数 $t_b$ 都在 $[0,1]$，差的绝对值为一迫使它们为两个端点。引理 3.1 给出式 (1.3)。$M$ 支持于 $R\cap s^\perp\subseteq\ker E$；$w_0$ 也属于这个子空间且范数为一，所以两个前卷编码都在该族中。维数三的 $\ker E$ 内还允许 $R$ 外的输入，未把最优性限定在三维常返支持上。任何包含瞬态 $2/3$ 特征方向的非端点密度都不能增加 $|\xi|$。$\square$

## 4. 完整复算子的正交分块与谱变分

**引理 4.1（所有相位概率的完整五维谱）。** 设 $0\le\theta\le1$，并令

$$
\begin{gathered}
a=(u+z)/\sqrt2,\qquad k=(u-z)/\sqrt2,\qquad
\ell=(e_0-e_3)/\sqrt2,\\
h_\theta=\theta v+(1-\theta)v_-,\qquad
\kappa_\theta=\sqrt{\theta^2+(1-\theta)^2},\\
g_\theta=h_\theta/\kappa_\theta,\qquad
r_\theta=((1-\theta)v-\theta v_-)/\kappa_\theta,\\
D_\theta=\theta D_0+(1-\theta)D_1.
\end{gathered}
\tag{4.1}
$$

这是整个复空间 $H$ 上的算子，确切表达式为

$$
D_\theta=\frac12|a\rangle\langle a|-\frac12|k\rangle\langle k|
+\frac{|a\rangle\langle h_\theta|+|h_\theta\rangle\langle a|}{\sqrt2}.
\tag{4.2}
$$

尤其，若 $x=2\theta-1$，在原始基 $e_0,\ldots,e_4$ 中为

$$
D_\theta=\frac14\begin{pmatrix}
0&x&\sqrt2&0&1\\
x&0&\sqrt2x&x&0\\
\sqrt2&\sqrt2x&0&\sqrt2&\sqrt2\\
0&x&\sqrt2&0&1\\
1&0&\sqrt2&1&0
\end{pmatrix}.
\tag{4.3}
$$

令

$$
\delta_\theta=\sqrt{1+8\kappa_\theta^2}
=\sqrt{5+4(2\theta-1)^2},\qquad
\lambda_\pm=\frac{1\pm\delta_\theta}{4}.
\tag{4.4}
$$

全部特征值及重数为 $\lambda_+,\lambda_-,-1/2,0,0$；零特征空间恰为 $Z_\theta=\operatorname{span}\{r_\theta,\ell\}$。迹范数为

$$
\|D_\theta\|_1=\frac{1+\delta_\theta}{2}=2\lambda_+.
\tag{4.5}
$$

证明。$a,k,v,v_-,\ell$ 是五维正交单位基，$S$ 固定 $a,k,\ell$ 并交换 $v,v_-$。$\kappa_\theta$ 始终非零，$g_\theta,r_\theta$ 也是对应二维空间的正交单位基。又

$$
s=(\sqrt2a+v)/\sqrt3,\qquad
D_0=(3P-P_R)/2,
$$

展开得

$$
D_0=\frac12|a\rangle\langle a|-\frac12|k\rangle\langle k|
+\frac{|a\rangle\langle v|+|v\rangle\langle a|}{\sqrt2}.
$$

共轭 $S$ 得到将 $v$ 换成 $v_-$ 的 $D_1$，于是式 (4.2) 成立。再用 $u=(e_0+e_3)/\sqrt2$、$h_\theta=(xe_1+e_4)/\sqrt2$，式 (4.2) 等价于

$$
\frac12\bigl(|u\rangle\langle z|+|z\rangle\langle u|
+|u+z\rangle\langle h_\theta|+|h_\theta\rangle\langle u+z|\bigr),
$$

给出式 (4.3) 的每个矩阵项。

在正交基 $(a,g_\theta,k,r_\theta,\ell)$ 中，完整算子为

$$
D_\theta\cong
\begin{pmatrix}1/2&\kappa_\theta/\sqrt2\\
\kappa_\theta/\sqrt2&0\end{pmatrix}
\oplus(-1/2)\oplus0\oplus0.
\tag{4.6}
$$

二阶块的特征方程是 $y^2-y/2-\kappa_\theta^2/2=0$，所以其两个根就是式 (4.4)。完整特征多项式为

$$
\det(yI-D_\theta)=y^2(y+1/2)
(y^2-y/2-\kappa_\theta^2/2).
\tag{4.7}
$$

因 $\kappa_\theta>0$，一个根严格正，另一个严格负，且都非零。两根的乘积为 $-\kappa_\theta^2/2$。对应的明确单位特征向量为

$$
f_\pm(\theta)=
\frac{\lambda_\pm a+h_\theta/\sqrt2}
{\sqrt{\lambda_\pm^2+\kappa_\theta^2/2}}.
\tag{4.8}
$$

在二阶块中把 $c=\kappa_\theta/\sqrt2$ 代入，方程 $\lambda_\pm^2=\lambda_\pm/2+c^2$ 直接说明 $(\lambda_\pm,c)$ 是该根的特征向量。两向量内积的分子为 $\lambda_+\lambda_-+c^2=0$，所以 $f_+,f_-,k,r_\theta,\ell$ 构成完整正交特征基。由正负谱求和即得式 (4.5)。

若 $0<\theta<1$，$\lambda_-$ 与 $-1/2$ 不同，两者各单重；$\lambda_+$ 单重，零重数二。若 $\theta=0$ 或 $1$，谱为 $1,-1/2,-1/2,0,0$，负特征值 $-1/2$ 的重数变为二，式 (4.8) 与 $k$ 仍提供它的正交基。式 (4.3) 的系数虽为实数，整个证明是在复 Hilbert 空间中作酉基变换；没有把输入或效应限制为实数，也没有遗漏可带任意复系数的相干。$\square$

**引理 4.2（等先验的谱变分及全部等号条件）。** 若 $H_0$ 是无迹厄米矩阵，$\Pi_+,\Pi_-,\Pi_0$ 分别是其正、负、零谱投影，则

$$
\max_{0\le F\le I}\operatorname{Tr}(FH_0)
=\operatorname{Tr}(H_{0,+})=\frac12\|H_0\|_1.
\tag{4.9}
$$

全部最大化效应恰为 $F=\Pi_++K$，其中 $0\le K\le\Pi_0$。若 $H_0$ 是等先验密度差，相应最小平均错误为 $1/2-\|H_0\|_1/4$。

证明。写 $H_0=H_{0,+}-H_{0,-}$，则正性与 $F\le I$ 给出

$$
\operatorname{Tr}(FH_0)
\le\operatorname{Tr}(FH_{0,+})
\le\operatorname{Tr}(H_{0,+}).
$$

无迹性使两个 Jordan 部分迹相同，为迹范数之半。正谱投影达到上界。若等号成立，则 $\operatorname{Tr}((I-F)H_{0,+})=0$ 且 $\operatorname{Tr}(FH_{0,-})=0$。在每个非零特征方向上，这迫使 $F$ 分别有期望一或零；正性使零期望方向属于 $F$ 的核，$I-F$ 的正性使期望一方向属于 $I-F$ 的核，故所有跨这些方向的矩阵块都消失。只余零谱空间上的任意效应。将谱变分代入 $(1-\operatorname{Tr}(FH_0))/2$ 即得错误公式。这是标准 Helstrom 二元判别规则的有限维证明，适用于所有复厄米效应。$\square$

## 5. 真实随机相位的精确误差律与全部最优效应

**定理 5.1（已知相位概率的全局解）。** 定义

$$
f_\theta=f_+(\theta),\qquad
\Pi_\theta=|f_\theta\rangle\langle f_\theta|.
\tag{5.1}
$$

在端点编码 $\rho_0=P$、$\operatorname{supp}\rho_1\subseteq\ker E$ 下，全部最优固定效应为

$$
F=\Pi_\theta+K,\qquad 0\le K\le P_{Z_\theta}.
\tag{5.2}
$$

它们的互补效应为 $I-F$；$K=0$ 给出一个归一化向量所定义的秩一投影 POVM。全局最优错误为式 (1.2) 的 $e_\theta$。交换位标签时，全部最优效应相应互补。

证明。相位律对两假设相同，故平均输出态为

$$
\sigma_b(\theta)=\theta\Lambda_0(\rho_b)
+(1-\theta)\Lambda_1(\rho_b),\qquad
\sigma_0(\theta)-\sigma_1(\theta)=\xi D_\theta.
\tag{5.3}
$$

由引理 4.1、4.2，既定编码对的最优错误为

$$
\frac12-\frac{|\xi|\|D_\theta\|_1}{4}
=\frac12-\frac{|\xi|(1+\delta_\theta)}8.
$$

这证明式 (3.5) 的第三式。完整编码约化允许且只允许端点对取得 $|\xi|=1$，给出 $e_\theta=(3-\delta_\theta)/8$。端点方向 $\xi=1$ 的正谱投影就是 $\Pi_\theta$，零谱空间为 $Z_\theta$，所以引理 4.2 的等号条件正好给出式 (5.2)，包括零空间内任意复相干。$\square$

**推论 5.2（全部概率端点与公平相位）。** 在 $\theta=1$ 时 $f_\theta=s$、$\Pi_\theta=P$、$Z_\theta=R^\perp=\operatorname{span}\{v_-,\ell\}$；在 $\theta=0$ 时 $f_\theta=Ss$、$\Pi_\theta=SPS$、$Z_\theta=(SR)^\perp=\operatorname{span}\{v,\ell\}$。这两个边界的全部最优效应仍由式 (5.2) 给出，错误为零。

在 $\theta=1/2$ 时，令

$$
\begin{gathered}
g=(v+v_-)/\sqrt2,\qquad r_*=(v-v_-)/\sqrt2,\\
\lambda_*=(1+\sqrt5)/4,\qquad
f_* =\frac{\lambda_* a+g/2}{\sqrt{\lambda_*^2+1/4}},\qquad
F_*=|f_*\rangle\langle f_*|.
\end{gathered}
\tag{5.4}
$$

这时 $\delta_\theta=\sqrt5$，$e_\theta=(3-\sqrt5)/8$。在整个 $[0,1]$ 上，$e_\theta$ 的最大值唯一在 $1/2$ 达到，最小值零恰在 $0,1$ 达到。

证明。在两个端点 $\kappa_\theta=1$、$\lambda_+=1$，式 (4.8) 的正向量分别为 $(\sqrt2a+v)/\sqrt3$、$(\sqrt2a+v_-)/\sqrt3$。零向量基由式 (4.1) 直接确定。在中点 $h_\theta=g/\sqrt2$、$\kappa_\theta=1/\sqrt2$，式 (4.8) 化为式 (5.4)。最后 $0\le(2\theta-1)^2\le1$，且各等号条件如述，代入误差式即可。$\square$

## 6. 不公开相位的最坏平均错误与直接鞍点

**定理 6.1（共同最不利相位律与全部最优固定效应）。** 在最坏共同相位合同中，$P,M$ 配合 $\{F_*,I-F_*\}$ 达到全局最优错误 $e_{\mathrm{mm}}=(3-\sqrt5)/8$。$SF_*S=F_*$。固定端点编码方向为 $\xi=1$ 时，全部最优效应恰为

$$
F=F_*+K,\qquad
0\le K\le P_{Z_*},\qquad Z_* =\operatorname{span}\{r_*,\ell\}.
\tag{6.1}
$$

该族允许非 $S$ 不变的零空间效应；$K=0$ 本身已是固定且 $S$ 不变的实际达到者。交换位标签时取上述效应的互补。公平相位律 $\Pr(j=0)=\Pr(j=1)=1/2$ 是共同的最不利律。

证明。先取端点编码，令 $s_j(F)=\operatorname{Tr}(FD_j)$。最小化最坏错误等价于最大化 $\min_j s_j(F)$。对任意效应，

$$
\min\{s_0(F),s_1(F)\}
\le\frac{s_0(F)+s_1(F)}2
=\operatorname{Tr}(FD_{1/2})\le\lambda_*.
\tag{6.2}
$$

最后一步正是引理 4.2 的公平相位谱上界。由于 $S$ 固定 $a,g$，也固定 $f_*$，而 $D_1=SD_0S$，两个信号在 $F_*$ 下相等。其均值是 $D_{1/2}$ 的正谱迹，所以

$$
s_0(F_*)=s_1(F_*)=\lambda_*.
\tag{6.3}
$$

因此式 (6.2) 的界被一个真实合法的固定测量在每个纯相位达到，最优错误为 $(1-\lambda_*)/2$。

更明确地，若相位概率为任意 $\pi\in[0,1]$，则对每个 $F$，

$$
\operatorname{Tr}(FD_{1/2})\le\lambda_*
=\operatorname{Tr}(F_*D_\pi).
\tag{6.4}
$$

公平律同时限制所有效应，$F_*$ 对任意相位律都有相同信号，给出了直接的有限维鞍点。这里没有交换编码、测量与对抗者的优化次序，也不要求对抗者实际随机化；纯相位的最坏值已经相同。第 5 节还说明其他相位律的最优错误严格小于公平律，所以公平律在概率律中唯一最不利。

对一般编码对，先互补效应处理 $\xi<0$。式 (6.2)、(6.3) 的信号同乘 $|\xi|$，故最优最坏错误为 $(1-|\xi|\lambda_*)/2$，证明式 (3.5) 的第二式与全局端点最优性。

最后设端点编码下某个 $F$ 达到最坏值，则其两个信号都至少为 $\lambda_*$，而均值至多为 $\lambda_*$。故两个信号都等于该数，且它必须达到公平算子的谱变分等号。引理 4.2 迫使 $F=F_*+K$、$0\le K\le P_{Z_*}$。反过来，式 (4.2) 表明

$$
P_{Z_*}D_jP_{Z_*}=0\qquad(j=0,1),
$$

故每个这样的 $K$ 都满足 $\operatorname{Tr}(KD_j)=0$，两个信号仍为式 (6.3)。这证明了整个效应族，而不只给出一个达到者。$\square$

## 7. 零误差的支持障碍与仍然可读的标量

**命题 7.1（全支持障碍及旧读出的局限）。** 相位不公开且两个分支都可能时，没有任何完整输入密度对与固定效应能在两分支都零误差。真实随机合同在 $0<\theta<1$ 也不能零误差。

证明。非端点编码有 $|\xi|<1$，即使公开相位也有最小错误 $(1-|\xi|)/2>0$，故只须处理完整端点族。端点族的输出相同，分别为 $P_j,M_j$。它们的全部支持可写成

$$
\begin{aligned}
U_0&=\mathbb Cs,&U_1&=\mathbb CSs,\\
W_0&=\operatorname{span}\{k,b_0\},&
W_1&=\operatorname{span}\{k,b_1\},\\
b_0&=(a-\sqrt2v)/\sqrt3,&
b_1&=(a-\sqrt2v_-)/\sqrt3.
\end{aligned}
\tag{7.1}
$$

其中 $M_j=P_{W_j}/2$，$U_j\perp W_j$。但两个不同相位的相反标签不正交：

$$
\langle s,Ss\rangle=2/3,\qquad
\operatorname{Tr}(PSPS)=4/9,\qquad
\operatorname{Tr}(PP_{SR})=2/3,
$$

因而

$$
\operatorname{Tr}(PSMS)=\operatorname{Tr}(SPSM)=1/9.
\tag{7.2}
$$

也可直接由 $|\langle s,b_1\rangle|^2=2/9$ 与 $M_1=P_{W_1}/2$ 得到同一值。若一个效应零误差，它必须在 $U_0,U_1$ 上恒等，在 $W_0,W_1$ 上为零。正性使这些分别成为其一、零特征空间，二者必须正交，式 (7.2) 予以排除。

对真实随机端点输出，$\sigma_0=\theta P+(1-\theta)SPS$、$\sigma_1=\theta M+(1-\theta)SMS$。当两个权重都正时，正算子和的核是各核的交，因此

$$
\operatorname{supp}\sigma_0=U_0+U_1,\qquad
\operatorname{supp}\sigma_1=W_0+W_1.
\tag{7.3}
$$

这两个支持甚至有共同直线：$s-Ss=(v-v_-)/\sqrt3$，而 $b_0-b_1=-\sqrt{2/3}(v-v_-)$。由 $a,v,v_-$ 系数比较，它们的交恰为 $\mathbb C(v-v_-)$；$k$ 与第一支持正交。并且

$$
\operatorname{Tr}(\sigma_0\sigma_1)
=\frac{2\theta(1-\theta)}9>0.
\tag{7.4}
$$

所以不存在零误差测量。与此相符，精确误差式中 $\sqrt5<3$，且在 $0<\theta<1$ 有 $\delta_\theta<3$，最优错误确实严格正。

只检验前卷的相位适配测量则不足以证明这个最优不可能性。例如固定采用 $F=P$ 时，端点编码在偶相位的信号为一，奇相位的信号为 $4/9-1/9=1/3$，故错误分别为零与 $1/3$，最坏错误为 $1/3$，已知律错误为 $(1-\theta)/3$。这是一个特定测量的失败；量化所有测量和所有编码的结论来自第 3–6 节及上述支持障碍。$\square$

**定理 7.2（不依赖相位的明确仿射读数）。** 对任意完整输入密度，使用固定测量 $\{F_*,I-F_*\}$ 时，两个极限分支都有

$$
\Pr(F_*\mid\rho,j)
=\frac{1-2/\sqrt5}{6}
+\frac{1+\sqrt5}{4}\,\operatorname{Tr}(E\rho).
\tag{7.5}
$$

因此丢失零误差位不等于完全遗忘；幸存标量 $t$ 的不同值仍给出不同的相位盲结果分布。

证明。写 $f_*=\alpha a+\beta g$，选 $\alpha,\beta>0$。由式 (5.4) 的归一化向量与二阶特征方程，得到

$$
\alpha^2=\frac{1+1/\sqrt5}{2},\qquad
\beta^2=\frac{1-1/\sqrt5}{2},\qquad
\alpha\beta=1/\sqrt5.
$$

由于 $s=(\sqrt2a+v)/\sqrt3$ 且 $\langle g,v\rangle=1/\sqrt2$，

$$
\begin{aligned}
p_P:=\operatorname{Tr}(F_*P)
&=(2\alpha+\beta)^2/6=(5+11/\sqrt5)/12,\\
\operatorname{Tr}(F_*P_R)&=\alpha^2+\beta^2/2,\\
p_M:=\operatorname{Tr}(F_*M)
&=(\alpha^2+\beta^2/2-p_P)/2
=(1-2/\sqrt5)/6.
\end{aligned}
\tag{7.6}
$$

两者之差为 $\lambda_*=(1+\sqrt5)/4$。$SF_*S=F_*$ 使 $P_1,M_1$ 的概率也分别等于 $p_P,p_M$。将式 (2.6) 的密度输出 $tP_j+(1-t)M_j$ 代入即可。斜率严格正，故读数随 $t$ 非平凡变化。反之，同一个 $t$ 的所有输入在两个分支完全相同，见引理 3.1，所以这里没有暗中恢复其他输入信息。

一个单次二元结果不能精确估计任意连续实数 $t$；式 (7.5) 陈述的是参数化结果分布及统计可区分性。对最优端点编码，成功概率为 $(5+\sqrt5)/8>1/2$，但两个位的条件错误分别为 $1-p_P$ 和 $p_M$，并非本文把两者各自优化为同一个数。给出实际相位后使用 $P_j$ 则立即恢复零误差，不需要改变编码或更新。$\square$

## 8. 不变调度的实际有限停止时刻

**定义 8.1（有限隐藏停止实验）。** 预先声明候选偶数停止时刻 $n_0$ 与奇数停止时刻 $n_1$。分支 $j$ 使用实际前缀 $T_{n_j}$，两个位假设使用相同前缀；解码器可知道候选时刻，不能知道实际选择、实际时刻或其奇偶。定义 $e_j^{\mathrm{fin}}$ 为式 (1.1) 中用 $T_{n_j}$ 替换 $\Lambda_j$ 的错误。$e_{\mathrm{mm}}^{\mathrm{fin}}(n_0,n_1)$、$e_\theta^{\mathrm{fin}}(n_0,n_1)$ 对全部五维密度对与一个固定效应取下确界。

真实随机合同要求实际选择候选时刻的随机控制独立于位、编码随机性，且有声明的共同概率 $\theta$。这是一种停止随机化，不是随机施加 $S$、改变起始相位或更换序列。若停止触发或时钟向解码器泄漏奇偶，就已经是公开相位合同。

**命题 8.2（完整有限递推与精确可达到值）。** 令 $j=n\bmod2$。对全部复输入与 $n\ge2$，

$$
T_n-\Lambda_j
=(-1/2)^{n-2}\operatorname{Ad}_{S^j}\circ(C^2-\mathcal T),
\qquad\|T_n-\Lambda_j\|_\diamond\le\epsilon_n.
\tag{8.1}
$$

对 $P,M$ 编码则在每个 $n\ge0$ 已有精确恒等式

$$
T_n(P)=P_j,\qquad T_n(M)=M_j.
\tag{8.2}
$$

所以 $F_*$ 在每个候选时刻对都有完全相同的最坏相位错误 $e_{\mathrm{mm}}$；$\Pi_\theta$ 对每个候选时刻对都有精确的已知律平均错误 $e_\theta$。公开相位下的全局有限最优错误在所有时刻都为零。

证明。将式 (2.4) 的完整递推与式 (2.5) 的实际调度相接即得式 (8.1)，输出酉共轭保持 diamond 范数。$P,M$ 为 $C$ 的固定态，所以式 (2.5) 直接给出式 (8.2)，包括时间零。第 5、6 节的两个测量于是给出所述精确可达到值；公开相位用 $P_j$ 读出，非负性给出全局最优值零。

纯态选项 $|w_0\rangle\langle w_0|$ 在 $C$ 下始终支持于 $R\cap s^\perp$，所以公开相位也始终零误差，且由完整极限公式趋于 $M$。它不是本命题的固定混态 $M$，不应把其有限输出写成式 (8.2) 的第二式：在时间零二者的秩已不同。若这个纯态在 $C$ 下固定，其极限将等于自身，矛盾于极限为秩二的 $M$，故它确实不是固定态。它在隐藏相位极限最优，并不承诺隐藏相位有限错误与 $P,M$ 一样恒定。$\square$

**定理 8.3（对所有输入和效应一致的有限最优区间）。** 若 $n_0,n_1\ge2$，则

$$
\max\left\{0,e_{\mathrm{mm}}-
\frac{\max\{\epsilon_{n_0},\epsilon_{n_1}\}}2\right\}
\le e_{\mathrm{mm}}^{\mathrm{fin}}(n_0,n_1)
\le e_{\mathrm{mm}},
\tag{8.3}
$$

并且对每个 $0\le\theta\le1$，

$$
\max\left\{0,e_\theta-
\frac{\theta\epsilon_{n_0}+(1-\theta)\epsilon_{n_1}}2\right\}
\le e_\theta^{\mathrm{fin}}(n_0,n_1)
\le e_\theta.
\tag{8.4}
$$

这些是无限制完整输入有限最优值的区间，不把右端可达到值冒称为一般有限全局等号。确定相位端点 $\theta=0,1$ 的右端为零，所以这两个有限端点确有全局等号零。

证明。固定任意 $\rho_0,\rho_1,F$，令

$$
Z_b^j=T_{n_j}(\rho_b)-\Lambda_j(\rho_b).
$$

式 (8.1) 给出 $\|Z_b^j\|_1\le\epsilon_{n_j}$。两通道保迹且保厄米，故 $Z_b^j$ 厄米无迹。对任何这种 $Z$，Jordan 部分有相同的迹 $\|Z\|_1/2$，所以任何效应都满足

$$
|\operatorname{Tr}(FZ)|\le\|Z\|_1/2.
\tag{8.5}
$$

使用无迹性也可把 $(I-F)Z_0^j$ 换成 $-FZ_0^j$，因此

$$
\begin{aligned}
|e_j^{\mathrm{fin}}-e_j|
&=\frac12\left|-\operatorname{Tr}(FZ_0^j)
+\operatorname{Tr}(FZ_1^j)\right|\\
&\le\frac{\|Z_0^j\|_1+\|Z_1^j\|_1}{4}
\le\epsilon_{n_j}/2.
\end{aligned}
\tag{8.6}
$$

这里显式使用无迹输出误差的半迹范数因子，而不是把一般迹范数对偶界直接当作等式。估计与编码、效应及全部复相干无关。

两个数的最大值之差不超过逐项差的最大值，所以同一策略的最坏错误至多相差 $\max_j\epsilon_{n_j}/2$；共同权重平均则至多相差 $[\theta\epsilon_{n_0}+(1-\theta)\epsilon_{n_1}]/2$。对所有策略取下确界，结合已证极限全局最优值，得到两式左端；错误非负允许剪切于零。右端由命题 8.2 的实际 $P,M$ 策略达到，完全不使用渐近近似。$\square$

**推论 8.4（声明的停止分布与渐近不可能性）。** 可令每个奇偶分支内部还有声明的停止分布 $\mu_j$，支持于相应奇偶且 $n\ge2$，对两位假设相同并独立于编码随机性。令

$$
\overline\epsilon_j=\sum_n\mu_j(n)\epsilon_n.
\tag{8.7}
$$

用 $\overline\epsilon_j$ 替换式 (8.3)、(8.4) 的 $\epsilon_{n_j}$ 后，两式仍成立；若只知道所有可能时刻 $n\ge N\ge2$，可统一用 $\epsilon_N$。在非退化已知律下，总概率 $\mu$ 的相同结论也可直接写成误差差至多 $\sum_n\mu(n)\epsilon_n/2$。

证明。条件于每个实际 $n$ 应用式 (8.6)，再取同一条件分布的平均即可。命题 8.2 的 $P,M$ 输出只依赖奇偶，不依赖具体时间，所以右端精确达到性也保留。每个状态与效应有界，概率和中的平均通道、迹配对和相应不等式均由有限部分和及其范数极限成立。两位使用不同停止律时，不能作式 (5.3) 或这个平均，故不在合同内。

因为 $\epsilon_n\to0$，这些区间对全部输入和固定效应一致收敛到精确极限值。若 $\max_j\epsilon_{n_j}/2<e_{\mathrm{mm}}$，有限最坏平均错误已经严格正；即使为该候选时刻对重新优化编码和效应，也不能零误差。已知 $0<\theta<1$ 时，相应充分条件为 $[\theta\epsilon_{n_0}+(1-\theta)\epsilon_{n_1}]/2<e_\theta$。因此隐藏奇偶下不能用一个策略在所有任意大的候选偶、奇时刻持续零误差。这是实际不变序列的结论，而非仅替换成极限通道的声明。未给出概率律时不允许把不确定相位擅自解释成公平随机相位；最坏合同仍由式 (8.3) 控制。$\square$

## 9. 控制权与数学资源逐项计费

**约定 9.1（本卷操作成本）。** 本卷只使用下列已声明资源和操作；证明坐标与谱分块不增加操作方可用的系统。

| 项目 | 实际支付的资源与边界 |
| --- | --- |
| 保留数据 | 一个 $\mathbb C^5$；不增加第二份输入相关数据、辅助纠缠、保留参考、环境、综合征或结果历史。 |
| 实际更新 | 固定的 $A,B,A,B,\ldots$，时间 $n$ 就是 $n$ 次完整更新。每步使用一个新鲜二维最小环境并立即丢弃，合计 $n$ 次环境交互；Kraus 分支不可访问。 |
| 内含相位操作 | 按定义分解，每个 $A$ 含一次 $C$ 后的 $S$，每个 $B$ 含一次 $C$ 前的 $S$。相邻代数因子抵消是完整映射恒等式，不提供中途恢复权。 |
| 公开相位合同 | 支付一个与位独立的终端二值标签，并按它在 $P$、$SPS$ 两个投影读出间选择；等价实现可在固定 $P$ 读出前支付至多一次条件终端 $S$。 |
| 最坏隐藏相位合同 | 支付一次固定投影 POVM $\{F_*,I-F_*\}$，不获取实际相位；它是替换原终端读出的实际操作。 |
| 已知概率合同 | 支付以公开参数 $\theta$ 编程的一次固定 POVM，例如 $\{\Pi_\theta,I-\Pi_\theta\}$；编程只知道概率，不知道实现的相位。 |
| 真实停止随机化 | 若以独立选择偶、奇时刻产生 $\theta$，需支付该独立随机选择和停止控制；条件停止分布也需声明。它不来自对抗不确定性本身。 |
| 时钟与触发 | 隐藏相位要求不向解码器泄漏实际 $n$ 或可推知奇偶的时钟、触发、计数信息。若接收这些信息，就恢复公开相位权利，必须计费。已知 $A$ 先并不在实际停止数被隐瞒时自动给出终端奇偶。 |
| 终端预处理 | 固定 CPTP 预处理及独立测量随机化已由拉回效应覆盖；不额外赋予信息。依相位选择的终端预处理须支付相位标签。 |
| 不使用的权利 | 没有位相关时间选择、环境或测量结果访问、中间读出、反馈、恢复、任意调度更换或免费相位选择。 |

上述计数是数学接口计数。用固定预测量酉实现投影也算额外终端操作；本卷未证明其硬件门数或物理时间等价。一个保留五维系统不代表控制器、时钟、停止装置、环境制备及测量全部只需五维资源。不从这些计数推出本征完整窗口次数、总工作量、总存储、容量或任何全资源效率结论。

## 10. 来源对应、标准方法与本卷内容

**约定 10.1（逐项归属）。** 本卷数学输入是所给《AURIC FIB 五窗口切换记忆》完整文本。该卷中指向半参数卷、量子记忆卷及其他文献的标识只保留为不透明来源标识；这里不独立认证它们的版本或优先权。

| 来源或标准方法 | 本卷精确对应及内容归属 |
| --- | --- |
| 前卷定义 2.1，式 (2.1)–(2.4) | 本卷 $e_j,u,v,z,C,K_0,K_1,S,A,B$ 完全相同，参数固定 $\eta=1/2$；未替换完整 Kraus 通道。 |
| 前卷定义 2.1、命题 4.2 中式 (4.4) | 本卷 $s,P,M,w_0$ 及公开相位零误差策略由此前卷给出；沿用相同向量、支持和编码标签。 |
| 前卷定理 4.1 | 式 (2.5) 的实际前缀来自其完整复映射恒等式；只取已知 $A$ 先行，不混入 $B$ 先的输入端相位。 |
| 前卷定理 5.1、推论 5.2、命题 5.3 | 本卷的完整效应 $E$、瞬态特征值 $2/3$、$\mathcal T$、精确全输入递推与 diamond 误差界；这些是复用结果，不再宣称为新固定通道成果。 |
| 标准 Helstrom 谱变分规则 | 引理 4.2 展开其等先验二元判别及全部等号条件；不把标准正谱投影规则归为本卷发明。 |
| 有限维极小极大与鞍点方法 | 第 6 节用公平律上界所有效应，再用一个不变测量逐相位达到；直接证明所需鞍点，不借未验证的优化交换。 |
| 普通复线性代数 | 正交变基、二阶特征方程、谱分解、支持与正性、Jordan 迹范数界及凸平均。 |
| 本卷针对该模型的推导 | 全五维编码约化与端点族；所有 $\theta$ 的完整 $D_\theta$ 谱、明确归一化最优向量和整个效应族；终端相位擦除的精确正代价、完整支持障碍与幸存标量读数；不变实际调度的有限全局最优区间。 |

本卷所谓模型特定的精确控制擦除定理，是相对于给定前卷增加的定量推导。它不是全球文献优先权、独立评审批准或原创性认证。

## 11. 适用范围、未解边界与证据上限

**约定 11.1（已定量范围与未解问题）。** 在一个五维保留系统、固定半参数、已知 $A$ 先且调度不变、均匀编码位、一次终端两结果读出和共同相位的完整输入极限合同中，本卷给出了三个全局最优平均错误、完整最优编码族、隐藏相位的完整最优效应族、严格零误差障碍与非平凡标量读数。实际有限时刻的 $P,M$ 达到值是精确恒等式，有限无限制最优值则只由第 8 节的区间控制。

每个给定小偶、奇停止时刻对的精确无限制最优值没有在本卷求出；有限瞬态可能改进右端达到值，其幅度受所给区间限制。不能以极限只剩 $t$ 推断有限时刻已无其他输入信息。未知起始相位、非均匀位先验、最坏单个位标准、按位分别选择相位或停止律、多次使用、辅助纠缠、保留参考或额外副本，均不属于本卷的优化结论。

任意更新序列、任意参数、位相关调度、结果与环境访问、反馈、中间恢复、改变保留系统或揭示时钟，均改变合同。这里不提供它们的精确隐藏相位判别最优值，也不解决前卷更广的切换分类与最佳收敛问题。有限纠缠或经典标签结果不能自动转为量子容量、信道容量或可恢复非交换信息的结论。

本卷证明的证据层级是未经执行数学核验的、可错的条件性符号论证；所引完整通道接口作为给定前提。这里没有 Lean 内核、数值或 CAS、数学测试或构建、渲染验证、外部文献检索、硬件、物理、经验机器学习、全球新颖性、全资源或更大研究目标完成认证。数学模型内的精确错误概率与控制差价不提供从经典人口接口到 CPTP 实现、本征窗口、Hamiltonian 或自然界本体的额外桥梁。

## 追加锚（本行以下为增补区）
