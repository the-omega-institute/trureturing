# FIB 合法边误差分配：完整词域的 minimax 首项与 Bayes 目标不相容性

## 1. 不变的来源、评分与合法边分配

**数学引文 1.1（固定来源与证明范围）。** 本卷以科学输入快照 [`7772839e6bdae1ed339d9a35f2932f300081c7f1`](https://github.com/the-omega-institute/trureturing/tree/7772839e6bdae1ed339d9a35f2932f300081c7f1) 中的 [Correlated Word Recovery 卷][Recovery] 为来源，完整沿用其定义 1.2–1.4。该卷定理 2.1(C) 的最优均匀 Bayes 首项、式（3.2）的任意共同探针邻边实部恒等式、§3.4 的乘积输出 Gram 构造，以及定义 4.2、推论 4.3 的完整服务对应均为复用。本卷处理该卷开放问题 6.3 的固定词长 minimax 端点首项及目标分离，给出普通数学证明；它是理论参考输入，未经 Lean kernel 核验。以下理想来源、已知校准和任意末端联合测量都是明确假设，不是物理实现结论。

**定义 1.2（完整合法词与同一固定源）。** 固定整数 $N,L\ge1$，置 $n=3N$、$\theta=\pi/(4L)$。系统为 $\mathcal K=(\mathbb C^2)^{\otimes n}$，因子标签、带符号的计算基及 $X,Y,Z$ 标准均已知。令

$$
\begin{aligned}
B_n&=\{b\in\{0,1\}^n:b_i b_{i+1}=0\quad(1\le i<n)\},\\
s_i(b)&=(-1)^{b_i},\\
U_{s(b)}&=\bigotimes_{i=1}^n\exp(i s_i(b)\theta Z),\\
\Lambda_{s(b)}(\rho)&=U_{s(b)}\rho U_{s(b)}^\dagger.
\end{aligned}
$$

未知 $b$ 选定一次，此后所有普通调用使用同一个理想、无噪声、无记忆、已校准的源。一次普通调用作用于整个 $n$ 量子位系统，对参考和工作空间作用为恒等。Bayes 评分使用 $B_n$ 上的均匀先验；minimax 评分取所有固定合法来源中的最坏者。全零词、尾部 null 窗和每个跨窗接缝全部保留，没有 canonical $\mathrm{End}$，没有额外标签建议。

**定义 1.3（一块式协议与整词错误）。** $q$ 是满足 $0\le q\le L$ 的整数。协议 $\Pi$ 准备任意与 $b$ 无关的输入密度态和有限维参考，在同一系统上连续调用源恰好 $q$ 次，调用间不操作系统，最后作一次任意联合 POVM，经有限末端计算输出 $\widehat b\in B_n$。允许与源无关的准备、参考、工作空间初值和随机化。仅作用于参考的中间操作与源调用交换，可推迟到末端。不允许未知 controlled-$U$、逆源、源复位、重新抽取 $b$ 或调用间系统控制。所有最优性量词均取遍这个原协议类。

记 $p_\Pi(b)=\Pr_b(\widehat b=b)$、$\eta_b=1-p_\Pi(b)$，令 $M=M_n=F_{n+2}$，其中 $F_0=0,F_1=1,F_{k+2}=F_{k+1}+F_k$。定义

$$
\begin{aligned}
\beta_n(L,q)&=\sup_\Pi\frac1M\sum_{b\in B_n}p_\Pi(b),
&\varepsilon_n^\star(L,q)&=1-\beta_n(L,q),\\
\beta_n^{\mathrm{mm}}(L,q)&=\sup_\Pi\min_{b\in B_n}p_\Pi(b),
&\delta_n(L,q)&=1-\beta_n^{\mathrm{mm}}(L,q)
=\inf_\Pi\max_{b\in B_n}\eta_b.
\end{aligned}
$$

非法答案可归给一个固定合法词，因而末端决策不必另设失败标签。上述错误是整词错误，不能换成平均单个位错误。

**定义 1.4（重叠与完整合法词图）。** 令

$$
x=\cos\left(\frac{\pi q}{2L}\right)=\cos(2q\theta),\qquad 0\le x\le1.
$$

这是同一次准备后连续酉迭代的重叠参数，不是 $q$ 份重新准备样本的重叠。以完整 $B_n$ 为顶点，Hamming 距离为一时连一条无向边，得到图 $\Gamma_n$。记其边集为 $E_n$、邻接矩阵为 $A=A_n$、边数为 $e=e_n$、顶点度数为 $d_b$。复用 [Recovery][Recovery] 式（2.4）–（2.5），其中渐近式对每个固定 $n$ 沿原整数合同且 $x\to0$ 的族成立：

$$
e_n=\frac{nF_{n+1}+2(n+1)F_n}{5},\qquad
C_n=\frac{e_n}{2M_n},\qquad
\varepsilon_n^\star(L,q)=C_nx^2+O_n(x^3).
\tag{1.1}
$$

该计数和 Bayes 首项是既有供应，不作为本卷新增结论。实际源始终为 $n=3N\ge3$。

**定义 1.5（合法边的误差分配系数）。** 对每条无向边 $\{b,c\}$，选取两个有向量

$$
0\le a_{c\leftarrow b}\le1,\qquad
a_{c\leftarrow b}+a_{b\leftarrow c}=1.
$$

定义顶点负载与其最小最大值

$$
L_b(a)=\sum_{c:c\sim b}a_{c\leftarrow b}^{2},\qquad
\kappa_n=\min_a\max_{b\in B_n}L_b(a).
\tag{1.2}
$$

可行集是每条边选择一个方向后得到的有限闭区间乘积，非空且紧；目标连续，所以最小值存在。这些是公开图上的共同分配变量，不是知道真实 $b$ 后另选的策略。$L_b$ 记图负载，$L$ 仍记源的整数校准参数。

**定义 1.6（首项最优的协议族）。** 固定 $n$，沿合法整数合同且 $x>0$、$x\to0$ 的参数族，准备、有限参考和随机化可随合同变化。若协议的均匀平均错误满足

$$
\frac{M^{-1}\sum_b\eta_b}{x^2}\longrightarrow C_n,
$$

称该族为 Bayes 首项最优；若

$$
\frac{\max_b\eta_b}{x^2}\longrightarrow\kappa_n,
$$

称其为 minimax 首项最优。这是错误系数的最优性；成功率都趋于一时，其比值趋于一不足以定义这里的最优性。$O_n$ 的常数和适用邻域只需对固定 $n$ 成立，$o_n$ 沿所述族解释；两者均不承诺对增长的 $n$ 一致。

## 2. 完整来源上的定量定理

**定理 2.1（全协议类 minimax 首项与目标不相容性）。** 在定义 1.2–1.6 的不变合同下，下列结论成立。

(A) 对每个原整数合同，

$$
\delta_n(L,q)\ge v_n(x),\qquad
v_n(x)=\frac{4\kappa_nx^2}{\bigl(1+\sqrt{1+4\kappa_nx}\bigr)^2}.
\tag{2.1}
$$

这是对全部共同输入、有限参考、末端 POVM 和源无关随机化的不可超越界，不断言它是精确有限参数最优值。

(B) 对每个固定 $n=3N$，沿原合法合同且 $x\to0$，

$$
\delta_n(L,q)=\kappa_nx^2+O_n(x^3).
\tag{2.2}
$$

一个共同的 $|+\rangle^{\otimes n}$ 乘积准备、不使用输入参考、一个末端正交测量达到该首项。它同时服务所有合法来源，不是分别达到的二元最优策略拼接。

(C) 每个 $n=3N$ 都有严格界

$$
C_n<\kappa_n
\le\max\left\{\frac{49n}{256},\frac n4-\frac{47}{256}\right\}
<\frac n4.
\tag{2.3}
$$

因此完整协议类的两个优化目标满足

$$
\beta_n(L,q)-\beta_n^{\mathrm{mm}}(L,q)
=(\kappa_n-C_n)x^2+O_n(x^3)>0
\tag{2.4}
$$

其中严格正号适用于原合法合同下充分小的正 $x$，不是全部内部 $q$ 的断言。

(D) 对任一 Bayes 首项最优协议族，即使准备、有限参考和随机化随合同任意变化，对每个 $b\in B_n$ 都必有

$$
\eta_b=\frac{d_b}{4}x^2+o_n(x^2),\qquad
\max_b\eta_b=\frac n4x^2+o_n(x^2).
\tag{2.5}
$$

故没有协议族同时达到 Bayes 与 minimax 两种错误首项最优性。这不声称 minimax 接收器逐来源改善全部错误。

(E) 完整五标签情形 $n=3$ 有解析表征。令 $\tau$ 为区间 $(1/\sqrt2,3/4)$ 内方程

$$
f(t)=\left(1-\sqrt{t-\frac12}\right)^2
+\left(1-\frac{t}{\sqrt2}\right)^2-t^2=0
\tag{2.6}
$$

的唯一根，则

$$
\kappa_3=\tau^2,\qquad \frac12<\kappa_3<\frac9{16}.
\tag{2.7}
$$

此值对应完整 $B_3$ 的所有五个原标签，没有限制子族或数值最优候选。

(F) 每个固定整数 $r\ge1$，取 $q=L-r$ 且 $L\to\infty$，有

$$
\delta_n(L,L-r)=\frac{\pi^2r^2\kappa_n}{4L^2}
+O_{n,r}(L^{-3}).
\tag{2.8}
$$

因而严格目标分离出现在真正的内部整数调用合同中。

(G) 在 [Recovery][Recovery] 定义 4.2 的全部有限历史正确性要求下，整词取得、完整索引五窗服务安装及其指针版本的优化错误相同，以上系数、界和分离分别传递到整条服务。

## 3. 定理 2.1 的完整普通证明

### 3.1 图负载的严格上下界

任意可行分配的负载总和为

$$
\begin{aligned}
\sum_bL_b(a)
&=\sum_{\{b,c\}\in E_n}
\left(a_{c\leftarrow b}^{2}+a_{b\leftarrow c}^{2}\right)\\
&=\frac e2+2\sum_{\{b,c\}\in E_n}
\left(a_{c\leftarrow b}-\frac12\right)^2.
\end{aligned}
\tag{3.1}
$$

最后一行每条边任选一个方向；平方与该选择无关。最大负载至少为平均负载，故 $\kappa_n\ge e/(2M)=C_n$。若某个最小化分配使 $\kappa_n=C_n$，式（3.1）和 $\sum_bL_b\le M\kappa_n=e/2$ 强制每条边的两向分配都为 $1/2$。这时 $L_b=d_b/4$，平均值为 $C_n$；所有负载都不超过其平均值，强制所有度数相等。

但全零词 $0^n$ 的度数为 $n$，唯一的 $1$ 在位置 $2$ 的合法词度数为 $n-2$：可删除该 $1$，或在位置 $4,\ldots,n$ 中任一处添加 $1$。两词都属于完整 $B_n$，所以 $\kappa_n>C_n$。

为取得严格小于 $n/4$ 的显式上界，在每条与 $0^n$ 相接的边上设置

$$
a_{c\leftarrow0^n}=\frac7{16},\qquad
a_{0^n\leftarrow c}=\frac9{16};
$$

其余边的两向分配都为 $1/2$。全零词的负载为 $49n/256$。每个非零合法词都至少有一个与 $1$ 相邻的零位不能翻转，故度数至多 $n-1$。全零词的每个邻点，其唯一相接特殊边把负载增加

$$
\left(\frac9{16}\right)^2-\frac14=\frac{17}{256},
$$

故负载至多 $(n-1)/4+17/256=n/4-47/256$；其余顶点至多 $(n-1)/4$。得到式（2.3），两项都严格小于 $n/4$。

### 3.2 同一个真实决策律的同时邻边约束

先固定一个协议及其与源无关的随机种子。输入密度态可用额外有限参考纯化，原测量通过忽略该参考嵌入纯化协议，保持决策概率。记共同纯输入为 $\psi$、各源输出代表为 $\psi_b=(U_{s(b)}^q\otimes I)\psi$。相邻 $b,c$ 仅在位置 $i$ 不同，所以相对系统酉为 $\exp(\pm2iq\theta Z_i)$。复用 [Recovery][Recovery] 式（3.2）：

$$
\begin{aligned}
\langle\psi_b,\psi_c\rangle
&=\cos(2q\theta)
\ \pm i\sin(2q\theta)\langle\psi,(Z_i\otimes I)\psi\rangle,\\
\operatorname{Re}\langle\psi_b,\psi_c\rangle&=x.
\end{aligned}
\tag{3.2}
$$

$Z_i$ 的期望为实数。这对每个共同输入及其参考成立；固定酉代表的相位仅用于内积书写，没有授予对未知酉的 controlled 访问。

设末端效果为 $(Q_j)_{j\in B_n}$。用显式等距映射和正交结果投影

$$
Vv=\sum_j|j\rangle\otimes\sqrt{Q_j}v,
\qquad \Pi_j=|j\rangle\langle j|\otimes I.
$$

因为 $\sum_jQ_j=I$，有 $V^\dagger V=I$，内积和决策概率均保持。下文仍以 $\psi_b$ 记映射后的向量。令 $P(c\mid b)=\|\Pi_c\psi_b\|^2$、$\eta_b=1-P(b\mid b)$。把内积分成结果 $b$ 空间、结果 $c$ 空间及共同正交补，Cauchy–Schwarz 给出

$$
\begin{aligned}
x&\le|\langle\psi_b,\psi_c\rangle|\\
&\le\|\Pi_b\psi_b\|\,\|\Pi_b\psi_c\|
+\|\Pi_c\psi_b\|\,\|\Pi_c\psi_c\|\\
&\quad+\|(I-\Pi_b-\Pi_c)\psi_b\|
\,\|(I-\Pi_b-\Pi_c)\psi_c\|\\
&\le\sqrt{P(b\mid c)}+\sqrt{P(c\mid b)}
+\sqrt{\eta_b\eta_c}.
\end{aligned}
\tag{3.3}
$$

前两项把正确空间的范数各界为一；共同补空间包含于每个来源的错误空间，所以最后一项有效。正交答案空间与重叠的这种估计方法来自 [Ambainis][Ambainis] §3、引理 1；此处保留同一协议全部条件决策概率的同时约束。

现在对源无关种子平均。在每个种子下应用式（3.3），再用

$$
\mathbb E\sqrt{P}\le\sqrt{\mathbb EP},\qquad
\mathbb E\sqrt{\eta_b\eta_c}
\le\sqrt{(\mathbb E\eta_b)(\mathbb E\eta_c)},
$$

得到最终平均决策概率仍满足式（3.3）。这里没有交换种子平均和逐来源最大值；此后 $P,\eta$ 一律指同一个随机化协议的最终条件概率。

置

$$
T_{c\leftarrow b}=\sqrt{P(c\mid b)}\quad(c\ne b),
\qquad \delta=\max_b\eta_b.
$$

对每个 $b$ 有 $\sum_{c\ne b}T_{c\leftarrow b}^2=\eta_b$；每条合法边同时满足

$$
T_{c\leftarrow b}+T_{b\leftarrow c}\ge x-\delta,
\tag{3.4}
$$

因为 $\sqrt{\eta_b\eta_c}\le\delta$。这些有向量属于同一个实际决策律，不能分别为不同边更换探针。

### 3.3 对全部探针和参考的有限参数下界

若 $0\le\delta<x$，式（3.4）使每条边的以下分母严格为正，定义

$$
a_{c\leftarrow b}
=\frac{T_{c\leftarrow b}}
{T_{c\leftarrow b}+T_{b\leftarrow c}}.
$$

这是可行分配。对每个来源，

$$
\eta_b\ge\sum_{c\sim b}T_{c\leftarrow b}^2
\ge(x-\delta)^2L_b(a).
$$

取最大值，得到

$$
\delta\ge\kappa_n(x-\delta)^2.
\tag{3.5}
$$

函数 $t\mapsto\kappa_n(x-t)^2-t$ 在 $[0,x]$ 严格递减，起点为正、终点为负，只有一个零点。解方程并有理化，其零点为

$$
\frac{4\kappa_nx^2}{(1+\sqrt{1+4\kappa_nx})^2}=v_n(x),
$$

所以 $\delta\ge v_n(x)$。若 $\delta\ge x>0$，因该零点在 $(0,x)$，仍有 $\delta\ge v_n(x)$。$x=0$ 时下界为零。于是对每个合同和每个协议都成立，对全部准备、有限参考、测量及随机化取下确界仍成立，证明 (A)。固定 $n$ 下

$$
v_n(x)=\kappa_nx^2+O_n(x^3).
\tag{3.6}
$$

没有假定最优探针的存在、连续性或收敛。

### 3.4 一个共同接收器同时达到首项

固定一个只依赖公开图的最小化分配 $a^{\mathrm{opt}}$。以输出标签为行、真实标签为列，定义实矩阵

$$
D_{cb}=\begin{cases}
a^{\mathrm{opt}}_{c\leftarrow b},&c\sim b,\\
0,&\text{其余情形},
\end{cases}
\qquad K=D-\frac A2.
$$

分配恒等式使 $D+D^T=A$，故 $K^T=-K$。

准备 $|+\rangle^{\otimes n}$ 并恰好连续调用 $q$ 次，令 $\Phi$ 的列为 $\phi_b=U_{s(b)}^q|+\rangle^{\otimes n}$。复用 [Recovery][Recovery] §3.4：$q>0$ 时

$$
G=\Phi^\dagger\Phi,\qquad G_{bc}=x^{h(b,c)},\qquad G>0.
\tag{3.7}
$$

对角项为一，包括 $x=0$ 时。正定性来自每个位点的两个候选向量线性无关，其完整张量积族成基，合法子族也线性无关。$\Phi G^{-1/2}$ 是 [Eldar–Forney][EF] 定理 3 的成熟 SRM 正交列构造。将其旋转为末端测量列矩阵

$$
H=\Phi G^{-1/2}\exp(-xK).
\tag{3.8}
$$

$\exp(-xK)$ 是实正交矩阵，所以 $H^\dagger H=I$。测量这些列的一维正交投影，将正交补并入任一固定合法标签。所有候选态都在 $H$ 的列空间，故该补全不改变其决策概率。

精确决策振幅矩阵为

$$
H^\dagger\Phi=\exp(xK)\sqrt G.
\tag{3.9}
$$

因此这个共同接收器的精确可达最坏错误是

$$
\max_b\left\{1-
\left|[\exp(xK)\sqrt G]_{bb}\right|^2\right\}.
\tag{3.10}
$$

式（3.10）是指定接收器分数，不是精确有限参数 minimax 最优值。

固定 $n$ 时，距离一的项给出

$$
G=I+xA+O_n(x^2).
$$

邻近 $I$ 的收敛矩阵平方根级数及矩阵指数给出

$$
\begin{aligned}
\sqrt G&=I+\frac x2A+O_n(x^2),\\
\exp(xK)&=I+xK+O_n(x^2),\\
H^\dagger\Phi&=I+xD+O_n(x^2).
\end{aligned}
\tag{3.11}
$$

这些余项可只依赖 $n$：$K$ 的绝对行和、列和至多为 $n/2$，且 $\|G-I\|_{\mathrm{op}}\le(1+x)^n-1$。固定标签数有限，近 $x=0$ 时上述级数的范数余项可统一界定。

每列的总测量概率为一，故将列 $b$ 的非对角振幅平方求和即为来源 $b$ 的错误。式（3.11）给出

$$
\eta_b=x^2L_b(a^{\mathrm{opt}})+O_n(x^3),\qquad
\max_b\eta_b=\kappa_nx^2+O_n(x^3).
\tag{3.12}
$$

于是 $\delta_n\le\kappa_nx^2+O_n(x^3)$。与式（3.6）的下界合并，证明全原协议类的 (B)。无需输入参考，也没有独立二元接收器的相容性假定。

### 3.5 两种目标的严格分离与 Bayes 刚性

复用式（1.1）的最优均匀 Bayes 展开，从式（2.2）相减得到式（2.4）；§3.1 的严格系数差使其在充分小正 $x$ 上严格为正，证明 (C)。

未旋转 SRM 对应 $D=A/2$、$K=0$，式（3.11）使其逐源错误为 $(d_b/4)x^2+O_n(x^3)$，最大度数为 $n$，故最坏错误首项为 $n/4$。§3.4 的接收器在 $x^2$ 阶严格改善这一最坏分数。但以下刚性更强：这个度数错误轮廓属于每个 Bayes 首项最优族，而不只是 SRM。

取任意这样的协议族，沿用 §3.2 的最终条件概率记号，令 $E=\sum_b\eta_b$。定义 1.6 给出

$$
E=\frac e2x^2+o_n(x^2).
\tag{3.13}
$$

非负性使 $\delta\le E=O_n(x^2)$，充分小的正 $x$ 满足 $x-\delta>0$。令 $R_{\mathrm{non}}$ 为所有 $c\ne b$ 且 $c\not\sim b$ 的有序非边上 $T_{c\leftarrow b}^2$ 之和。逐边使用两平方的和差恒等式，得到精确等式

$$
\begin{aligned}
E-\frac e2(x-\delta)^2
&=R_{\mathrm{non}}\\
&\quad+\frac12\sum_{\{b,c\}\in E_n}
\left[(T_{c\leftarrow b}+T_{b\leftarrow c})^2-(x-\delta)^2\right]\\
&\quad+\frac12\sum_{\{b,c\}\in E_n}
(T_{c\leftarrow b}-T_{b\leftarrow c})^2.
\end{aligned}
\tag{3.14}
$$

由式（3.4），右边每一项非负。式（3.13）与 $\delta=O_n(x^2)$ 使左边为 $o_n(x^2)$。因此 $R_{\mathrm{non}}=o_n(x^2)$，每条边的和为 $x+o_n(x)$、差为 $o_n(x)$，所以

$$
T_{c\leftarrow b}=\frac x2+o_n(x)
\quad\text{对每条有向合法边成立}.
$$

对每个固定来源将平方相加，非边总量至多为 $R_{\mathrm{non}}$，得到

$$
\eta_b=\frac{d_b}{4}x^2+o_n(x^2).
$$

固定 $n$ 的顶点数有限，最大度数为 $n$，故最坏错误为 $(n/4)x^2+o_n(x^2)$。式（2.3）给出 $\kappa_n<n/4$，从而不可能同时首项最优，证明 (D)。该论证直接作用于随机化后的共同概率律，允许任意变化的探针和有限参考。

### 3.6 完整五标签图的解析最优解

命名五词为

$$
o=000,\quad u=100,\quad v=001,\quad w=101,\quad z=010.
$$

全部边恰为 $ou,ov,oz,uw,vw$。五个原窗口标签分别是 $o\leftrightarrow\mathrm{null}$、$u\leftrightarrow2$、$z\leftrightarrow3$、$w\leftrightarrow2\ 5$、$v\leftrightarrow5$，没有删去 null 或挑选子族。

反射交换 $u,v$ 并保持其余顶点。把一个分配与反射分配平均，各负载的凸性保证最大负载不增加：反射仅置换原负载，而平均后的每个负载不超过对应两负载的平均。故求最优只需三个变量 $a,b,c\in[0,1]$：从来源 $o$ 向 $u,v$ 各分配 $a$，向 $z$ 分配 $b$；从各来源 $u,v$ 向 $w$ 分配 $c$，反向取补数。各负载为

$$
\begin{aligned}
L_o&=2a^2+b^2,\\
L_u=L_v&=(1-a)^2+c^2,\\
L_w&=2(1-c)^2,\\
L_z&=(1-b)^2.
\end{aligned}
\tag{3.15}
$$

对式（2.6）的 $f$，在 $[1/\sqrt2,3/4]$ 上

$$
f'(t)=1-\frac1{\sqrt{t-1/2}}-\sqrt2-t<0.
$$

$t=1/\sqrt2$ 时第二个平方为 $1/4$、$t^2=1/2$，且 $\sqrt{t-1/2}<1/2$，故 $f(t)>0$。另一端有

$$
f(3/4)=\frac{31}{32}-\frac{3\sqrt2}{4}<0.
$$

连续性与严格单调性给出该区间内唯一根 $\tau$。取

$$
a=\sqrt{\tau-\frac12},\qquad
b=1-\tau,\qquad c=1-\frac\tau{\sqrt2}.
\tag{3.16}
$$

它们属于 $[0,1]$。代入得到 $L_o=L_w=L_z=\tau^2$；$L_u=L_v=\tau^2$ 正是 $f(\tau)=0$。故 $\kappa_3\le\tau^2$。

反向，若存在可行分配最大负载为 $t^2<\tau^2$，令 $t\ge0$ 并先作上述对称化；对称化后每个负载仍至多 $t^2$。平均负载界给出 $t\ge1/\sqrt2$，又有 $t<\tau<3/4$。叶 $z$ 的约束使 $b\ge1-t$。结合 $L_o\le t^2$，有

$$
2a^2\le t^2-(1-t)^2=2t-1,
\qquad a\le\sqrt{t-\frac12}.
$$

$w$ 的约束给出 $c\ge1-t/\sqrt2$。在该区间各下界非负，且 $a\le\sqrt{t-1/2}<1$，因此

$$
L_u\ge\left(1-\sqrt{t-\frac12}\right)^2
+\left(1-\frac t{\sqrt2}\right)^2
=t^2+f(t)>t^2,
$$

矛盾。于是 $\kappa_3=\tau^2$，由根所在开区间得到式（2.7），证明 (E)。这是图分配问题的解析全局证书；§§3.2–3.4 将它同时提升为原全来源、全协议类的 minimax 首项，而非一次数值测量样本。

此例中的平衡接收器把叶 $z$ 的错误首项从 SRM 的 $1/4$ 提高至 $\tau^2$，同时把全零词 $o$ 的最坏首项从 $3/4$ 降至 $\tau^2$。改变目标确实需要误差重新分配，不能理解为逐来源支配。

### 3.7 端点、零误差与原整数合同

$q=0$ 时输出与来源无关，均匀平均成功率为 $1/M$，最小逐源成功率不超过该平均；均匀猜词对每个来源达到 $1/M$。因此 Bayes 与 minimax 错误都为 $1-1/M$，不使用退化 Gram 矩阵的逆平方根。

$q=L$ 时 $x=0$，乘积输出的 Gram 矩阵为 $I$，§3.4 的接收器是精确正交译码，两种错误都为零。$q<L$ 时 $x>0$ 且 $\kappa_n>C_n>0$，式（2.1）严格为正，恢复原一块式合同在 $L$ 以下不能零误差恢复的结论。

固定整数 $r\ge1$，对 $L\ge r$ 令 $q=L-r$，则

$$
x=\sin\left(\frac{\pi r}{2L}\right)
=\frac{\pi r}{2L}+O_r(L^{-3}).
$$

代入式（2.2）得到式（2.8），证明 (F)。充分大 $L$ 有 $0<q<L$，并由式（2.4）严格分离。这一极限比较不同但分别合法的设备合同；它没有允许在同一固定已校准实验内自由改变角度。

### 3.8 完整索引服务、指针服务及全部有限历史

沿用 [Recovery][Recovery] 定义 4.2，将合法词分为窗口

$$
W_j(b)=(b_{3j-2},b_{3j-1},b_{3j}),\qquad 1\le j\le N.
$$

每窗属于全部五种 $\{000,100,010,101,001\}$，读作 $\mathrm{null},2,3,2\ 5,5$，并保持所有接缝约束 $b_{3j}b_{3j+1}=0$。安装后服务闭合、确定，不再调用源或读取源相关建议，安装及每个合法回复均有限终止；随机化只用于安装。整条成功要求对每条有限合法查询历史都正确，包括重复索引与依回复自适应的查询，并保持合法域和更新。

从估计合法词 $\widehat b$ 安装确定索引表，索引 $j$ 返回 $W_j(\widehat b)$。指针版本另保留初始 $a=1$，索引读不改 $a$；$\mathrm{Next}$ 恰在 $a\le N$ 时合法，返回 $W_a$ 后递增 $a$。没有 $\mathrm{End}$，尾部 null 照常占三位。

若 $\widehat b=b$，对任意有限混合查询历史作长度归纳：初始词和指针相同；索引读给相同窗口且保持指针；$\mathrm{Next}$ 两边的合法域相同，合法时给相同窗口并同步递增。故回复、域和更新始终一致。若 $\widehat b\ne b$，至少一窗不同，一次对应索引查询就见证服务失败。所以这种安装逐源保持整词成功事件。

反向，任取原合同内服务安装器，安装后作固定有限索引扫描 $1,\ldots,N$，将回复译为词，非法回复串归给固定合法词。全部有限历史正确必推出该扫描恢复 $b$；故扫描译码对每个来源的成功概率至少为原安装的整条成功概率。扫描不调用源，属于终端经典后处理，最终标签有限，因此诱导原合同内的整词决策 POVM。它是上界归约，不是任意服务全部历史正确性的有限认证。

正向逐源保分，反向逐源不降低分，分别取均匀平均或最小逐源成功，再取协议上确界，得到优化整词和服务分数相等。指针服务具有同一索引扫描，且正向安装已在所有有限混合历史上保持指针更新，故同样成立。这复用并展开 [Recovery][Recovery] 推论 4.3 的服务归约，证明 (G)。定理 2.1 证毕。

## 4. 白盒质量的任务解释与资源假设

**数学引文 4.1（质量目标须随任务读数、合法域和更新指定）。** [FIB 白盒卷][Whitebox] 定义 8.1 要求解释同时保留读数、合法域和更新。此处的任务表示 $(s(b),a)\mapsto(b,a)$ 保持 §3.8 的所有规定窗口读数、合法域和指针后继；全零、尾部 null 和跨窗接缝全部保留。定理 2.1(D) 对这一明确服务质量问题的含义是：对先恢复整词再按 §3.8 安装服务的协议族，在同一理想源和资源合同下，即使平均整条服务错误达到最优首项，也必产生度数决定的逐来源不均匀错误，最坏来源首项严格高于 minimax 最优首项。平均质量与最坏来源保障不能用同一个“首项最优”标签混同。

式（3.1）与式（3.14）给出这种不相容的机制：均匀 Bayes 首项耗尽总合法边错误预算，迫使每条边均分；完整合法图不规则，于是均分产生不同顶点负载。minimax 必须重新分配同一决策律上的错误振幅，以增加平均首项为代价降低最大首项。完整 $B_3$ 的叶与全零词在 §3.6 中展示该取舍。这是固定 $n$、$x\to0$ 的错误目标解释，不给出全部有限参数或实际训练系统的最优质量。

**数学引文 4.2（原生来源仅作各自合同内的动机）。** 仓内 [FixedScalarFiberDiscovery][Native] 的来源是有序 $\alpha/\beta$ 树和地址观察，涉及同一实际树上的共同证书；[KBonacci 四标签续卷][KBonacci] 使用 INITIAL 标签、付费完整块端点观察及共同延续词。它们说明“各自可取得”与“同一策略共同达到”须分开核对，但此处没有建立与这些来源、读出、合法操作和更新的对应。不转移其数值费用、证书价格或源最优值；也不把该量子承诺族等同于原生 FIB 读者、网络训练状态或真实机器学习系统。上述白盒质量解释不宣称实际网络改善。

**假设 4.3（普通调用、准备、参考与公开知识）。** 达到首项的接收器先准备 $n$ 个零态，以 $n$ 个已知 $H$ 门得到 $|+\rangle^{\otimes n}$；不使用输入参考，随后恰好作 $q$ 次不中断的普通完整系统调用，再作一次已知集体末端测量。其图和矩阵仅依赖公开的 $n,L,q$ 与完整合法域。上界构造与下界允许的任意参考类分开：不使用参考的一个接收器达到首项，并不意味着每个有限参数最优准备都不需参考。

已知因子、带符号基准、源承诺和校准是必要条件。计算公开 Gram 矩阵的逆平方根不是调用未知逆源；列出所有候选输出是公开模型描述，不需要从源取得那些标签的样本。没有未知 controlled-$U$、复位、重新抽样、调用间系统控制或标签建议。

**假设 4.4（读出、计算、存储与未定价格）。** 原合同允许任意理想联合末端 POVM。§3.4 的正交列可补成系统正交基，故这一数学构造不要求输入参考。校准、集体测量综合、控制和读出各有未求出的独立价格；集体测量不沿用局部方案的 $3n$ 门费。图优化和测量矩阵描述都是有限维对象，但没有计算效率、硬件成本或数值收益率结论，随 $n$ 增长的费用不由本卷控制。

显式服务表保留 $n$ 位，指针版本再保留有限指针；这不是最小存储定理。若另限全局测量为局部或 LOCC，§3.4 的可达性不直接传递。噪声、失校准、记忆源及物理实现均不在假设内。

## 5. 数学供应、增量边界与未解问题

**数学引文 5.1（既有供应及其精确范围）。** 以下既有结果仅承担对应推导步骤，不单列为本卷新定理。

| 来源 | 数学供应与边界 |
| --- | --- |
| [Recovery][Recovery] 定义 1.2–1.4、式（2.4）–（2.5）、式（3.2）、§3.4、定义 4.2 及推论 4.3 | 不变来源、一块式合同、Fibonacci 合法图计数、全协议类均匀 Bayes 首项、共同输入邻边实部、乘积 Gram 构造和整条服务归约；其式（4.1）与开放问题 6.3 不供应本卷的 $\kappa_n$ 或 Bayes 刚性。 |
| [Eldar、Forney，*On Quantum Detection and the Square-Root Measurement*][EF]，定理 3 | `literature-attested`：SRM 正交列框架；特殊最小错误最优性另需其态族对称性假设，不确定本来源的 minimax 最优值。 |
| [Ambainis，*Quantum lower bounds by quantum arguments*][Ambainis]，§3、引理 1 | `literature-attested`：正交答案空间分解及 Cauchy–Schwarz 重叠估计；本卷的新增推导是实际共同决策振幅在全部合法边上的同时分配与匹配旋转。 |
| [Tyson，*Error rates of Belavkin weighted quantum measurements and a converse to Holevo’s asymptotic optimality theorem*][Tyson]，版本 v1、§§1.2–1.4 | `literature-attested`：带权平方根测量与固定先验近正交态族的渐近最优性；不直接给出对全部共同准备及参考的源整体下界。 |
| [D’Ariano、Sacchi、Kahn，*Minimax quantum state discrimination*][DSK]，版本 v5、§III、定理 3–4 | `literature-attested`：固定态族的 minimax/Bayes 联系及完全协变态族的相等情形；不视为本共同输入渠道辨识问题的显式解，也不用一般凸规划替代源特定最优证明。 |
| [Montanaro，*On the Distinguishability of Random Quantum States*][Montanaro]，版本 v2、§2.2、式（8） | `literature-attested`：Gram 平方根的逐来源成功率界；是指定接收器保障，不是优化 minimax 系数。 |
| [Montanaro 仓内条目][MontanaroNote]；[Contextual Spacetime Arithmetic Quantum][CSAQ] §16.5；[EquiprobablePgmActiveSetRefutation][ActiveSet] | 前两者提供逐来源 SRM 界；第三者是不同的三混态 active-set 反例，不供应此合法边系数或准备无关的下界。 |
| mathlib 固定提交 [`db584cd6d46c92f209a44c0f1c829460d327499d`](https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d)，输入版本 v4.33.0 的 [凸集拓扑][MathConvex]、[矩阵正定][MathPosDef]、[Hermitian 函数演算][MathCFC] | 通用紧性、凸性和谱演算供应；不归属本卷源特定 minimax 定理，也不作为本卷经过编译的形式证据。 |
| [原生树来源][Native]与 [KBonacci INITIAL 续卷][KBonacci] | 各自合同下的共同证书与相容延续动机；没有量子源／操作对应或数值价格传递。 |

**数学引文 5.2（本卷综合推导的归属）。** 定理 2.1 的全准备及有限参考 minimax 下界、匹配首项的共同末端旋转、严格系数差、任意 Bayes 首项最优族的逐源刚性和完整五标签解析证书为本卷普通证明给出的 `repo-derived` 综合。图紧性、矩阵平方根、反对称旋转、有限维凸性、SRM、既有 Bayes 首项及服务等价均不单独宣称新知识。增量相对于以上明确来源和 [Recovery][Recovery] 的未解范围；所列定向供应不构成 D5、Library 或文献的穷尽清单，不据此声称世界优先性。

**开放问题 5.3（精确有限参数最优）。** 一般内部整数 $0<q<L$ 上的完整 $B_{3N}$ 精确 Bayes 与 minimax 最优值仍未确定，即使 $B_3$ 远离正交端点亦未由本卷解决。式（3.10）是一个接收器的精确可达最坏错误，式（2.1）是全部协议的下界；首项相同不证明它们在有限参数处相等。最优准备、最优末端测量及更高阶优化项仍未确定。

**开放问题 5.4（词长、限制操作与实际资源）。** 一般 $n$ 的 $\kappa_n$ 由式（1.2）有限图问题精确表征，但没有给出其 Fibonacci 闭式；只有完整 $B_3$ 得到式（2.6）–（2.7）的解析解。增长 $n$ 的一致估计、全局最优有限 $q$ 准备、所有局部或 LOCC 类的最优值、稳健性和完整物理资源价格均未解决。固定词长的 $O_n$ 首项结论不能替代这些问题的答案。

[Recovery]: https://github.com/the-omega-institute/trureturing/blob/7772839e6bdae1ed339d9a35f2932f300081c7f1/docs/develop/theory/FIB_ATOM_WHITEBOX_CORRELATED_WORD_RECOVERY.md
[Whitebox]: https://github.com/the-omega-institute/trureturing/blob/7772839e6bdae1ed339d9a35f2932f300081c7f1/docs/develop/theory/FIB_ATOM_MACHINE_LEARNING_WHITEBOX.md
[Native]: https://github.com/the-omega-institute/trureturing/blob/7772839e6bdae1ed339d9a35f2932f300081c7f1/D5/S3/Arith/FibonacciAtomic/FixedScalarFiberDiscovery.lean
[KBonacci]: https://github.com/the-omega-institute/trureturing/blob/7772839e6bdae1ed339d9a35f2932f300081c7f1/docs/develop/theory/KBONACCI_FOUR_LABEL_ROOT_ZERO_INTERSECTION_PRICE.md
[MontanaroNote]: https://github.com/the-omega-institute/trureturing/blob/7772839e6bdae1ed339d9a35f2932f300081c7f1/Library/Quantum/montanaro2007distinguishability.md
[CSAQ]: https://github.com/the-omega-institute/trureturing/blob/7772839e6bdae1ed339d9a35f2932f300081c7f1/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md
[ActiveSet]: https://github.com/the-omega-institute/trureturing/blob/7772839e6bdae1ed339d9a35f2932f300081c7f1/D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.lean
[EF]: https://arxiv.org/abs/quant-ph/0005132
[Ambainis]: https://arxiv.org/abs/quant-ph/0002066
[Tyson]: https://arxiv.org/abs/0907.1884v1
[DSK]: https://arxiv.org/abs/quant-ph/0504048v5
[Montanaro]: https://arxiv.org/abs/quant-ph/0607011v2
[MathConvex]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Convex/Topology.lean
[MathPosDef]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Matrix/PosDef.lean
[MathCFC]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean

## 追加锚（本行以下为增补区）
