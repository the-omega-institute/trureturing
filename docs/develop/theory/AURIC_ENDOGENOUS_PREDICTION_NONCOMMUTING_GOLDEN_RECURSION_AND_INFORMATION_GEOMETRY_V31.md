<a id="auric-v31"></a>

# AURIC：内生预测、非交换黄金递归与信息几何

**未知记录质量、经典稳定化与可辨识时钟**

**定义、定理与纸面证明**

**v31.0 · 2026 年 10 月 30 日 · Asia/Singapore**

> **转换说明（编者）。** 本文完整转写原作者提供的 v31.0 XeLaTeX 稿件。作者关于固定快照、来源核读、历史统计、纸面结果及项目进展的陈述仍归属于原作者，不构成本次转换的新认证。字体、页眉、页码与分页排版由 Markdown 替代；数学宏按 TeX 参数规则展开为独立表达。陈述沿用各节共享计数器，四个无编号小节保留；仅保留源稿显式公式标签 (1)–(48)，全部证明保留可见终止符。原始固定来源、外部链接及先行研究归属照录。

<a id="sec-abstract"></a>

## 摘要

沿用 v30 的单一静态本体前提：观察者、程序、基底、参数、记录与时钟均为同一整体中的内部关系。
本轮把“预测等于递归、变分、增长”分解成可以逐项证明的命题。
项目新增的未知记录质量定理保留第二读口的仿射自由 $G=cq+d$；
本文给出两项内部校准的锐度判据、有限校准误差界及整个质量序列的定量收敛。
非零仿射对比度仍可在全控制下辨识整个矩阵态；十三维秩五读口有显式稳健常数。

内部记录的平方最优预测何时为正，有一个精确相容性判据；
对记录相容代数，预测同时成为完全正条件期望与变分最优解。
未来仪器效果的递归闭包给出最粗充分预测状态。
在持久二元目标模型中，后验剩余方差与尚未取得的 Fisher 信息满足精确恒等式，
说明经典读出稳定和全部量子信息取得具有不同的条件。

黄金递归不再要求各层门彼此对易。本文构造一个前缀自适应的 $\operatorname{SU}(2)$ 门族，
证明其普通门像、射影门像及固定内部参考读出像的 Hausdorff 维数均为
$\log2/(2\log\varphi)$；在一个已知内部前缀下，同一四结果读口
即可保留整个条件门族的统计几何，固定正仿射对比度保持此维数。
有限实际精度给出明确的可辨识尺度。正规化有限前缀程序给出一致误差界，
完整永久时钟记录则可以继续增长而不在范数中收敛。
最后从内部条件态的可辨识性构造量子几何张量，
把预测精度、生成元方差、非交换闭路和参考系协变性联系起来。
这些是有假设的表示与推断定理；信息几何仍需额外内部因果、度量和动力学关系，
才能成为时空引力理论。

<a id="sec-1"></a>

## 1. 单一静态本体与本轮固定项目来源

固定含单位元的复 $C^*$ 代数及正归一态 $(\mathcal{A},\omega)$：

$$
\omega(I)=1,\qquad \omega(a^*a)\ge0.
$$

一切物理角色均由该整体的内部关系表达；子代数、矩阵因子和程序坐标不被解释为
宇宙之外的对象或物理边界。向量表示可写成
$\omega(a)=\langle\Omega,\pi(a)\Omega\rangle$。
局部密度矩阵 $\rho$ 是内部矩阵代数上的态限制或条件态；
它可以是混态，即使整体向量 $\Omega$ 固定且纯。
v30 已证明相容内部态的共同表示、持久相容目标的鞅稳定化、
静态门历史及关系时钟；本稿着重推进其尚未处理的非交换预测与资源接口。

<a id="statement-1-1"></a>

#### 定义 1.1（本文区分的两种论证层次）

<a id="def:layers"></a>

“未知响应重构层”沿用项目的 Hilbert 门运动学，但不预给所有实际读口的 Born/CP 规则，
由明确的实际响应合同推断某些终端律。
“正态读出层”规定实际效果的概率为 $\omega(E)$，内部仪器具有所列完全正语义，
然后证明预测、信息和几何结论。
同一本体可以作为两层的共同研究对象；第二层的概率规则不能被回填为第一层已经无条件证明的结果。

例如 $G_w(\psi)=c|\psi_w|^2+d_w$ 本身是效果 $cE_w+d_wI$ 的 Born 形式。
其与旧尖锐坐标律不同，并不等于它违反所有 POVM 意义的量子概率。
源 §107 的更弱反模型另指定计算记录的非线性概率规则；
不能一面把该记录固定为正态上的指定投影读出，一面又把它的平方权重当作尚未输入。
本文在每一节声明所用层次，保留这一区分。

本轮固定快照为项目 `dev` 提交：

`ae852c6f2df9ac7779afc168cb1a1850327e217b`

提交时间为 2026-10-30 22:44:57（Asia/Singapore），PR #24257。
对比 v30 固定提交：

`75c5f3c4aea976b089df5070a2f9f24f2905ee3a`

完整树差分为 32 个提交、654 个文件，其中 5 个 theory 文档变化；
没有 D5/Quantum 代码变化。与本稿直接相关的是量子续卷 II 新增 §§104--108，
当前完整文件的 Git blob 为：

`07b42c289db08b527554cc7890c7932212c8558a`

以及二元读出、全框架相融与 E8 桥梁 v28 的归档，
blob 为：

`defd31085c26411dbd3088a51a8701cce89b38a3`。
后者是既有作者稿转写，不能把归档动作当作新的独立数学认证。（[1](#ref-repohead)、[2](#ref-quantumii)、[3](#ref-v28)）

本轮使用固定来源、完整相关增量及其真实依赖作纸面推导；
未运行数学程序、数值实验、门字枚举、CAS 或 Lean。
下面一般线性代数、条件期望和信息几何结果属于标准结构的独立证明与本项目中的组合，
不作全球文献优先权主张。

<a id="sec-2"></a>

## 2. 未知记录质量：新分类、校准与整列收敛

### 项目 §§104--108 的精确输入

记

$$
x=\varphi^{-1}=\frac{\sqrt5-1}{2},\quad y=\sqrt x,\quad
 \zeta=e^{3\pi i/5},\quad H=V_8^{\mathbf1},\quad\dim H=13.
$$

原七个门的有限正向字为 $K_p,K_f$。源中的秩五投影为 $\Pi$，
$D=I-\Pi+\zeta\Pi$；保留全部 $\Omega_{10}=\{0,1\}^{10}$ 标签。
十三个合法标签 $w_\beta=10\beta010$ 的旧坐标律为
$q_{w_\beta}(\psi)=|\langle e_\beta,\psi\rangle|^2$，其余 $1011$ 标签为零。
扩大载体为 $\mathcal K=V_{12}^{\mathbf1}$，$\dim\mathcal K=89$，
$J:H\otimes\mathbb{C}^2\hookrightarrow\mathcal K$ 的代码维数为 $26$；
全部 $63$ 维补空间继续保留。

取同一个连续、相位不变、完整终端响应
$\mathfrak P:S(\mathcal K)\to\Delta(\Omega_{10})$，令

$$
F(\psi)=\mathfrak P(J(\psi,0))=P(\psi),\qquad
 G(\psi)=\mathfrak P(J(\psi,1)).
$$

只有 $F$ 被锚定到旧未知读口，并接受全部十三基射线和全部标签的独立旧校准。
源设置的四个指数为 $(t_{00},t_{01},t_{10},t_{11})=(0,1,4,3)$。
固定 $v=e_{00100}$，真实一字制备 $p_*=1$ 给 $\eta=K_1v$，其在 $\ker\Pi$ 和 $\operatorname{ran}\Pi$
两方向的幅度模分别为 $x,y$。

源理想合同要求每个正质量分支及每个正质量细档案的实际保留后继恰为

$$
[J(K_fD^{t_{si}}K_pv,i)],
$$

条件终端律恰为同一 $\mathfrak P$ 在该射线的值，
要求完整终端边缘对设置无关，并要求该制备下记录质量
$a_0,a_1\in(0,1)$ 对每个后续接续选项 $f$ 保持不变。
原文“外生接续”在完全内生模型中必须由一族真实内部程序情境来供给，
保留共同先前制备、相同记录接口与接续干预稳定性。
它不要求本体之外有一个选择者，却也不能用任意相关联合分布中的
条件化 $\Pr(i\mid f)$ 代替这份合同。
这些要求可以表述为静态整体中的相容关系和因果偏序，不需要外部绝对时间。

<a id="statement-2-1"></a>

#### 定理 2.1（源 §104.3 的未知质量分类，作为本轮前置）

<a id="thm:source"></a>

在上述全部源合同下，

$$
\boxed{
 \begin{aligned}
 F&=q,\qquad a_0=a_1=a\in(0,x],\\
 G&=cq+d,\quad c=\frac{ax}{1-a}\in(0,1].
 \end{aligned}
 }
 \qquad
 \begin{gathered}
 d_w\ge0,\\ \sum_wd_w=1-c.
 \end{gathered}
 \tag{1}
$$

在该合同内，

$$
G=F\ \Longleftrightarrow\ c=1\
 \Longleftrightarrow\ a=x\
 \Longleftrightarrow\ (a,1-a)=(x,x^2).
$$

最后的数值质量只针对指定制备与两个设置，未分类一切内部仪器。

**源证明的依赖与核心。**

完整分支全概率关系在 $p_*$ 上为

$$
a_0F_w(U\eta)+(1-a_0)G_w(UD\eta)
 =a_1F_w(UD^4\eta)+(1-a_1)G_w(UD^3\eta).                 \tag{2}
$$

最初 $U=K_f$；原生射影密度和固定响应连续性给全部数学酉的关系，
不把这些酉增添为精确可执行菜单。
源 §§85--86 的完备无重数调和分解和 §99 的两个等价副本法，
把每个次数 $j\ge2$ 的候选分量归约为四次多项式

$$
Q(z)=a_0\alpha+(1-a_0)\beta z-(1-a_1)\beta z^3-a_1\alpha z^4.
$$

适当非零点值调和单项式给五个不同根
$1,\zeta,\zeta^{-1},\zeta^2,\zeta^{-2}$，故 $Q=0$。
正质量于是消去所有高次分量；剩余为 Hermitian 二次型。
源以紧群特征投影先在连续函数空间操作，避免将任意 $L^2$ 展开直接代入点值。
旧完整校准与正矩阵的零对角元性质给 $F=q$。
一次分量的权零和权 $\pm1$ 关系再给 $a_0=a_1$ 以及
$c=ax/(1-a)$。逐标签非负和完整归一给 $d_w\ge0$、
$\sum d_w=1-c$，从而 $a\le x$。
这里消费的是源的完整调和前置与新五根论证；
其精确证明位于固定版本 §§104.1--104.3，而非把有限核对当全域证明。（[2](#ref-quantumii)）

∎

<a id="statement-2-2"></a>

#### 定理 2.2（两项内部校准与有限误差界）

<a id="thm:anchors"></a>

在式 (1) 的响应族中，取 $m\ge2$ 个不同合法基标签 $w_j$。
令 $\varepsilon_j=1-G_{w_j}(e_j)$。则

$$
1-c\le\frac{\sum_{j=1}^m\varepsilon_j}{m-1}.             \tag{3}
$$

尤其两个不同的确定正确基读出就迫使 $G=q$。
一个这样的校准不够。

**证明。**

由 $G_{w_j}(e_j)=c+d_{w_j}$，

$$
\sum_j\varepsilon_j
 =m(1-c)-\sum_jd_{w_j}\ge(m-1)(1-c).
$$

当两个误差均零时 $c=1$，所有 $d_w=0$。
反例取 $0<c<1$ 及 $d=(1-c)\delta_{w_1}$，即可精确通过第一项而保留噪声。

∎

<a id="statement-2-3"></a>

#### 定理 2.3（第二读口的操作直径）

<a id="thm:diam"></a>

对于式 (1) 的同一固定 $c,d$，

$$
\operatorname{TV}(G(\psi),G(\chi))=c\,\operatorname{TV}(q(\psi),q(\chi)),\qquad
 \sup_{\psi,\chi}\operatorname{TV}(G(\psi),G(\chi))=c.                  \tag{4}
$$

所以存在两种完全可区分的第二读口输出，当且仅当 $c=1$；
若某对输出总变差至少为 $1-\varepsilon$，则 $1-c\le\varepsilon$。

**证明。**

相减消去同一个 $d$；总变差的齐次性给第一式。
两个不同合法基输入使 $q$ 的总变差为一，得到上确界及后果。

∎

两项校准或可区分性是额外内部关系。
它们不是从“所有事物都内生”这一句话免费取得。
同时源 §107 已构造 $c<1$ 的完整扩大响应与计算记录规则，
满足所列较弱合同，因此此自由是真正的数学剩余量。（[2](#ref-quantumii)）

### 源 §106 的有限供应合同及新的定量后果

保留所有失败、拒绝、停止和泄漏档案。
源有限协议还分别要求：固定扩大响应的同一连续模 $\nu$；
实际成功纯分支射线误差 $\kappa_n\to0$；
全部失败质量 $\beta_n\to0$；
不同后续下实际成功质量变化 $\gamma_n\to0$；
完整设置边缘总变差 $\sigma_n\to0$；
以及两个成功记录均有共同的持久正下界。
令

$$
a_{ns}=m_{n,s0}(p_*,\epsilon),\qquad
 \epsilon_n=\sigma_n+2\nu(\kappa_n)+\gamma_n+2\beta_n.
$$

源式 (106.7) 对式 (2) 给一致残差 $\epsilon_n$，不删除失败后再归一，
也没有将比较模型的泄漏质量当作实际失败质量。
源以同一系数子序列取得定理 [2.1](#thm:source)。

<a id="statement-2-4"></a>

#### 定理 2.4（整个记录质量序列的定量收敛）

<a id="thm:mass"></a>

满足上述完整渐近合同后，令分类中固定的 $c$ 给
$a=c/(x+c)$。则整个序列均有

$$
\max_{s=0,1}|a_{ns}-a|
 \le
 \frac{(1+c)\epsilon_n}
 {xy\sin(3\pi/5)[1+x(2c-c^2)]}
 \le\frac{2\epsilon_n}{xy\sin(3\pi/5)}.                  \tag{5}
$$

因此无需依接续或子序列改变极限质量。
此结论是在整套渐近合同已确定 $F=q,G=cq+d$ 后的质量稳定性，
不是有限数据对任意未知响应的全域 Born 认证。

**证明。**

记 $A=a_{n0}-a$、$B=a_{n1}-a$、
$\rho_t=\lvert D^t\eta\rangle\langle D^t\eta\rvert$。固定一个合法标签 $w$。
以精确关系减去有限残差，并用连续性延拓全部接续，有

$$
|\operatorname{Tr}(E_wUR_nU^*)|\le\epsilon_n,\qquad
 R_n=A(\rho_0-c\rho_1)-B(\rho_4-c\rho_3)+(B-A)d_wI.
$$

全部酉将 $E_w$ 遍历秩一投影，$R_n$ 自伴，故 $\left\lVert R_n\right\rVert\le\epsilon_n$。
在 $\eta$ 的两个谱方向中，非对角元等于一个模为 $xy$ 的系数乘

$$
A\alpha_c-B\beta_c,\qquad
 \alpha_c=1-c\bar\zeta,\quad
 \beta_c=\bar\zeta^4-c\bar\zeta^3.
$$

常数标量项未消失，但不影响该非对角元。于是
$|A\alpha_c-B\beta_c|\le\epsilon_n/(xy)$。
用
$\cos(3\pi/5)=-x/2$、
$\cos(\pi/5)=1/(2x)$、
$\sin(\pi/5)=x\sin(3\pi/5)$，
直接展开得到

$$
|\operatorname{Im}(\bar\alpha_c\beta_c)|
 =\sin(3\pi/5)[1+x(2c-c^2)].
$$

这是两个复系数作为实二维向量的非零行列式。
对实未知量 $A,B$ 解二元线性方程，使用
$|\alpha_c|,|\beta_c|\le1+c$，即得第一界。
$0<c\le1$ 给第二界及整列收敛。

∎

<a id="sec-3"></a>

## 3. 递归噪声、持久指针与经典稳定性的区别

<a id="statement-3-1"></a>

#### 命题 3.1（串联同一仿射通道可能不断遗忘）

<a id="prop:noiseiterate"></a>

若 $0<c<1$，$T(p)=cp+d$、$\sum d=1-c$，
令 $r_0=d/(1-c)$，则

$$
T^n(p)=c^np+(1-c^n)r_0,\qquad
 \operatorname{TV}(T^n(p),T^n(q))=c^n\operatorname{TV}(p,q).
$$

**证明。**

对 $n$ 归纳；相减后只余 $c^n(p-q)$。

∎

<a id="statement-3-2"></a>

#### 定理 3.2（有噪单轮读口仍可递归辨认持久正交标签）

<a id="thm:noisyqnd"></a>

在正态读出层，设 $\{E_j\}_{j=1}^{13}$ 为完整正交基投影。
对全部 $1024$ 标签置合法效果 $E_w=E_j$、非法效果 $E_w=0$，
令

$$
M_w=\sqrt{cE_w+d_wI},\qquad 0<c\le1,\quad
 d_w\ge0,\quad\sum_wd_w=1-c.
$$

这些 Kraus 算符定义一个完整仪器。若输入为持久基标签 $j$，
每轮输出律为
$\ell_j(w)=c\mathbf1_{\{w=w_j\}}+d_w$，
且正概率分支的归一后继仍是同一基标签。
若同一内部结构供应 $n$ 次该仪器及持续记录，
存在仅使用经验频率的分类器，其条件误判概率满足

$$
\Pr_j(\widehat j_n\ne j)\le\min\left\{1,\frac{13}{nc^2}\right\}.
 \tag{6}
$$

**证明。**

正性给平方根，$\sum_wM_w^*M_w=I$。
每个 $M_w$ 在基向量 $e_j$ 上乘以 $\sqrt{\ell_j(w)}$，
故完整记录词的概率为 $\prod_t\ell_j(w_t)$。
对十三个合法坐标的经验频率选最近的向量
$(\ell_j(w_k))_{k=1}^{13}$，以 $\ell^\infty$ 距离比较。
不同标签分布的该距离为 $c$。
若每个经验坐标偏差都严格小于 $c/2$，分类必正确。
每个坐标的方差不超过 $1/(4n)$，Chebyshev 不等式给偏差至少 $c/2$
的概率不超过 $1/(nc^2)$；对十三坐标取并集界即得。
非法标签仍计入样本总数和完整档案，未作成功后选择。

∎

定理 [3.2](#thm:noisyqnd) 的可重复仪器与内部容量是额外供应，
不能仅由源 §105 的一次有限原生协议推出。
它说明单轮锐度 $c=1$ 与多轮对持久正交标签的可辨识性不同：
后者在 $c>0$ 时即可成立。
反过来，若只有一份非正交候选态，增加处理层数不自动增加输入信息。
固定五相位 qubit 输入的任意完整自适应二元树都等价于原输入上的一个 POVM，
等先验成功率至多 $2/5$；这个已存在的 v28 结果将在
第 [8](#sec:geometry) 节的 Fisher 讨论中使用其一般机制。（[3](#ref-v28)）

<a id="sec-4"></a>

## 4. 预测、变分与正性：精确的内部相容条件

本节在正态读出层工作。取同一整体内的矩阵角色 $M_D(\mathbb{C})$，
$\rho\ge0$、$\operatorname{Tr}\rho=1$，记录投影 $P_h$ 满足
$\sum_hP_h=I$、$P_hP_k=0$（$h\ne k$）、
$p_h=\operatorname{Tr}\rho P_h>0$。令 $\mathcal{D}=\operatorname{span}\{P_h\}$。
这里大写 $D$ 仅表示矩阵维数，不是第 2 节的相位门。

<a id="statement-4-1"></a>

#### 定义 4.1（内部平方预测）

对 $A=A^*$ 和经典记录预测 $X=\sum_hx_hP_h$，$x_h\in\mathbb{R}$，
定义

$$
R_\rho(A,X)=\operatorname{Tr}\rho(A-X)^2,\qquad
 \left\lVert A\right\rVert_\rho^2=\operatorname{Tr}\rho A^2.
$$

半内积取 $(A,B)_\rho=\operatorname{Re}\operatorname{Tr}\rho AB$；
零范数方向按等价类处理。

<a id="statement-4-2"></a>

#### 定理 4.2（平方最优预测及递归下降）

<a id="thm:ls"></a>

唯一最优预测为

$$
Q_{\mathcal{D}}(A)=\sum_h
 \frac{\operatorname{Re}\operatorname{Tr}(\rho P_hA)}{p_h}\,P_h.
 \tag{7}
$$

而且

$$
R_\rho(A,X)=R_\rho(A,Q_{\mathcal{D}}A)
 +\sum_hp_h\bigl(x_h-q_h(A)\bigr)^2.
$$

若 $\mathcal{D}_n\subseteq\mathcal{D}_m$ 为嵌套记录代数，则

$$
Q_nQ_m=Q_n,\qquad
 R_\rho(A,Q_nA)-R_\rho(A,Q_mA)
 =\left\lVert Q_mA-Q_nA\right\rVert_\rho^2\ge0.
 \tag{8}
$$

**证明。**

$X^2=\sum_hx_h^2P_h$，交叉项为
$\operatorname{Tr}\rho(AX+XA)=2\sum_hx_h\operatorname{Re}\operatorname{Tr}\rho P_hA$。
逐项配方给式 (7) 及唯一性。
这些映射是实半内积商空间中的正交投影；
嵌套子空间的正交分解给塔式等式与平方差恒等式。

∎

<a id="statement-4-3"></a>

#### 定理 4.3（最优预测为正的充要条件）

<a id="thm:positive"></a>

$Q_{\mathcal{D}}$ 的复线性延拓为正映射，当且仅当

$$
[\rho,P_h]=0\quad\text{对所有 }h.
 \tag{9}
$$

条件成立时，它是完全正、保单位、保持态的条件期望。

**证明。**

第 $h$ 个系数泛函的密度矩阵为
$B_h=(\rho P_h+P_h\rho)/(2p_h)$。
$Q_{\mathcal{D}}$ 为正恰好等价于每个 $B_h\ge0$。
相对于 $P_h\oplus(I-P_h)$，

$$
2p_hB_h=
 \begin{pmatrix}2\rho_{11}&\rho_{12}\\ \rho_{21}&0\end{pmatrix}.
$$

正矩阵中零对角块迫使对应非对角块为零：
对向量 $u+tv$ 的二次型选择 $t$ 的复相位和充分大模即可证明。
所以 $[\rho,P_h]=0$。
反之此时 $B_h=P_h\rho P_h/p_h$ 为一个态；
各块态值乘输出投影给完全正映射。保单位、幂等、双模及保持态性质直接代入验证。

∎

例如取 $0<s<1$，

$$
\rho=\frac{I+sX}{2},\quad P_0=\frac{I+Z}{2},\quad
 A=\frac12\left(I-\frac{sX+Z}{\sqrt{1+s^2}}\right).
$$

$\rho$ 忠实，$A$ 是投影，但
$q_0(A)=(1-\sqrt{1+s^2})/2<0$。
负的是指定平方损失下的最优估计系数，不是一个负的量子测量概率。
因此“存在、递归、最优化”本身不自动供应任意预测系数的概率正性。

<a id="statement-4-4"></a>

#### 定理 4.4（记录中心上的正预测）

<a id="thm:center"></a>

取内部记录相容代数

$$
\mathcal{C}=\mathcal{D}'\cap M_D(\mathbb{C})=\bigoplus_hP_hM_D(\mathbb{C})P_h.
$$

其中心为 $\mathcal{D}$。对任意满足上述 $p_h>0$ 的 $\rho$，映射

$$
\mathcal E_{\rho,\mathcal{D}}(A)
 =\sum_h\frac{\operatorname{Tr}(\rho P_hAP_h)}{p_h}P_h,\qquad A\in\mathcal{C},
 \tag{10}
$$

是完全正、保单位、保持态的条件期望，且是式 (7) 的最优预测。
若 $0\le A\le I$，每个系数属于 $[0,1]$。

**证明。**

$A\in\mathcal{C}$ 给 $A=\sum_hP_hAP_h$。
每块上的 $P_h\rho P_h/p_h$ 是态，故式 (10) 完全正、保单位；
各块求和保持 $\operatorname{Tr}\rho A$。中心双模性与幂等性直接成立。
$AP_h=P_hA$ 使其与式 (7) 相同。

∎

这给一个完全内生的经典结构：观察者按持久记录组织其可访问关系，
记录成为这部分代数的中心，每个记录块内仍可保留非交换量子关系。
此处没有需要从宇宙外部引入的环境，也没有把整个 $\mathcal{C}$ 压成其中心。

<a id="statement-4-5"></a>

#### 命题 4.5（单态零误差的支持判据）

<a id="prop:support"></a>

令 $s_\rho=\operatorname{supp}\rho$。对自伴 $A,X$，

$$
\left\lVert A-X\right\rVert_\rho=0
 \ \Longleftrightarrow\ (A-X)\rho^{1/2}=0
 \ \Longleftrightarrow\ (A-X)s_\rho=0.
 \tag{11}
$$

若 $\rho$ 忠实，则这等价于 $A=X$。
所以忠实态下，给定记录 $\mathcal{D}$ 可同时精确重建一族自伴目标，
当且仅当所有目标均属于 $\mathcal{D}$。

**证明。**

$\operatorname{Tr}\rho(A-X)^2=\left\lVert (A-X)\rho^{1/2}\right\rVert_{\mathrm{HS}}^2$，
有限维中 $\rho^{1/2}$ 的像为 $s_\rho\mathcal{H}$，即得。

∎

非忠实情形不能任意传递乘积：取
$\Omega=\lvert +\rangle$、$A=\lvert -\rangle\langle -\rvert$、$B=Z$、
$X_0=0$、$Y_0=Z$，记录为 $Z$ 对角代数。
两个预测在 $\Omega$ 上分别零误差，然而
$[A,B]\Omega=\lvert -\rangle\ne0$，且 $AB\Omega\ne X_0Y_0\Omega$。
若额外给 $[s_\rho,\mathcal{D}]=0$，
则 $(A_j-X_j)s_\rho=0$、$X_j\in\mathcal{D}$ 使各目标保持该支持；
对单词长度归纳才可得到所有多项式的支持上相等。

<a id="statement-4-6"></a>

#### 命题 4.6（共同经典预测的不相容代价）

<a id="prop:jointloss"></a>

记 $X_0=Q_{\mathcal{D}}(A)$、$Y_0=Q_{\mathcal{D}}(B)$，
$\varepsilon_A=\left\lVert A-X_0\right\rVert_\rho$、$\varepsilon_B=\left\lVert B-Y_0\right\rVert_\rho$，
$\sigma_A^2=\operatorname{Var}_\rho(A)$、$\sigma_B^2=\operatorname{Var}_\rho(B)$。则

$$
\sigma_B\varepsilon_A+\sigma_A\varepsilon_B
 \ge \frac12|\operatorname{Tr}\rho[A,B]|.
 \tag{12}
$$

**证明。**

减去均值不改变误差与交换子。正交投影收缩给
$\left\lVert X_0\right\rVert_\rho\le\sigma_A$。
因 $X_0,Y_0$ 对易，
$[A,B]=[A-X_0,B]+[X_0,B-Y_0]$。
逐项用正态 Cauchy--Schwarz 的
$|\operatorname{Tr}\rho[C,D]|\le2\left\lVert C\right\rVert_\rho\left\lVert D\right\rVert_\rho$ 即得。

∎

作为三轴例子，若内部 qubit 的限制态为 $\rho=I/2$，
非平凡交换记录为
$\mathcal{D}=\operatorname{span}\{I,\mathbf n\cdot\boldsymbol\sigma\}$、
$|\mathbf n|=1$，则

$$
Q_{\mathcal{D}}(\sigma_j)=n_j\,\mathbf n\cdot\boldsymbol\sigma,\qquad
 \sum_{j=x,y,z}R_\rho(\sigma_j,Q_{\mathcal{D}}\sigma_j)=2.
 \tag{13}
$$

证明只用 $\operatorname{Tr}\sigma_i\sigma_j=2\delta_{ij}$ 及 $\sum_jn_j^2=1$。
该式讨论同一记录情境下的算符重建，不否定三个统计读出或分别选基的合法性；
三轴坐标、一次结果和同时保留全部量子关系必须各有定义。

<a id="sec-5"></a>

## 5. 允许全部未来时，观察者需要保留什么状态

<a id="statement-5-1"></a>

#### 定义 5.1（未来效果的递归闭包）

<a id="def:future"></a>

在有限内部载体 $M_D(\mathbb{C})$ 上，给有限标签菜单 $\ell\mapsto\Phi_\ell$，
各 $\Phi_\ell$ 为完全正迹不增分支，同一设置的分支之和保持迹。
控制记忆若影响菜单，也须计入该载体。
定义实自伴线性空间

$$
\mathcal{S}_0=\operatorname{span}_\mathbb{R}\{I\},\qquad
 \mathcal{S}_{n+1}
 =\operatorname{span}_\mathbb{R}\!\left(\mathcal{S}_n\cup\bigcup_\ell\Phi_\ell^*(\mathcal{S}_n)\right).
 \tag{14}
$$

对词 $w=\ell_1\cdots\ell_k$，
$E_w=\Phi_{\ell_1}^*\cdots\Phi_{\ell_k}^*(I)$，
$p_\rho(w)=\operatorname{Tr}\rho E_w$。

<a id="statement-5-2"></a>

#### 定理 5.2（最粗充分预测状态及其闭合更新）

<a id="thm:sufficient"></a>

$\mathcal{S}_\infty=\bigcup_n\mathcal{S}_n$ 是全部有限未来记录效果的实线性包。
两个态对所有这些记录给相同概率，当且仅当它们在 $\mathcal{S}_\infty$ 上的限制相同。
记该限制为 $\nu_\rho$，正概率分支上的更新完全闭合：

$$
\nu_\rho'(A)=
 \frac{\nu_\rho(\Phi_\ell^*(A))}
 {\nu_\rho(\Phi_\ell^*(I))}.
 \tag{15}
$$

任何能决定全部未来概率的摘要，都不得合并在 $\mathcal{S}_\infty$ 上不同的态。
而且 $\dim_\mathbb{R}\mathcal{S}_\infty\le D^2$；一旦 $\mathcal{S}_n=\mathcal{S}_{n+1}$，
此后不再扩张。

**证明。**

对词长归纳，式 (14) 恰好生成全部效果。
概率的相等性对其实线性包等价。
该空间在每个 $\Phi_\ell^*$ 下不变，因此条件后态的限制只需要
$\nu_\rho$ 自身，给式 (15)。
若某摘要合并一对限制不同的态，某个未来概率必不同，违反其充分性。
维数界来自 Hermitian 矩阵空间的实维数。
若某层不变，它已在所有生成映射下封闭，归纳得永久不变。

∎

这个定理把“观察者就是预测递归”转成一个明确的数学对象：
观察者当前需要保留的是其允许未来效果上的态限制。
递归闭包的有限维数不提供实际枚举门字、学习该限制或完成校准的统一计算代价。

<a id="statement-5-3"></a>

#### 命题 5.3（线性摘要的精确维数要求）

<a id="prop:linearstat"></a>

对自伴 $F_j$，线性摘要 $(\operatorname{Tr}\rho F_1,\ldots,\operatorname{Tr}\rho F_m)$
在全部 $D$ 维密度态上决定 $\mathcal{S}_\infty$ 的所有态值，
当且仅当

$$
\mathcal{S}_\infty\subseteq\operatorname{span}_\mathbb{R}\{I,F_1,\ldots,F_m\}.
 \tag{16}
$$

若 $\mathcal{S}_\infty=M_D(\mathbb{C})_{\mathrm{sa}}$，则 $m\ge D^2-1$。

**证明。**

包含关系给线性重建。反之，取与 $I,F_j$ 正交却与某
$A\in\mathcal{S}_\infty$ 不正交的 Hermitian 矩阵 $X$。
充分小的 $t>0$ 使 $\rho_\pm=I/D\pm tX$ 都为密度矩阵。
二者摘要相同而目标不同，矛盾。

∎

<a id="statement-5-4"></a>

#### 定理 5.4（稠密控制、非零对比度与稳健可辨识性）

<a id="thm:tomography"></a>

设 $1\le r_0\le D-1$，$\Pi_{r_0}$ 为秩 $r_0$ 投影，
内部控制在 $\operatorname{PU}(D)$ 中稠密。令

$$
R_U(\rho)=c\,\operatorname{Tr}(\rho U^*\Pi_{r_0}U)+b
$$

采用同一固定 $c\ne0,b$。这些读出分离全部密度态。
若 $\Delta=\rho-\sigma$ 的特征值按
$\lambda_1\ge\cdots\ge\lambda_D$ 排列，则

$$
d_{r_0}(\rho,\sigma)
 :=\sup_U|\operatorname{Tr}(\Delta U^*\Pi_{r_0}U)|
 =\max\left\{\sum_{j=1}^{r_0}\lambda_j,
              -\sum_{j=D-r_0+1}^{D}\lambda_j\right\}.
 \tag{17}
$$

记 $D_{\mathrm{tr}}(\rho,\sigma)=\left\lVert \rho-\sigma\right\rVert_1/2$，则

$$
\frac{\min(r_0,D-r_0)}{D-1}D_{\mathrm{tr}}
 \le d_{r_0}\le D_{\mathrm{tr}},\qquad
 \sup_U|R_U(\rho)-R_U(\sigma)|=|c|d_{r_0}.
 \tag{18}
$$

**证明。**

连续性将稠密菜单的上确界延拓至全部酉。
在 $\Delta$ 的本征基中，投影的对角权重 $w_j$ 满足
$0\le w_j\le1$、$\sum_jw_j=r_0$。
将权重移动到较大特征值可增加和，因此最大值为前 $r_0$ 项之和，
最小值为后 $r_0$ 项之和，均由本征子空间达到。
上界由 $\Delta$ 的正负部分给出。
若 $\Delta\ne0$，正特征值个数为 $p$，其和为 $D_{\mathrm{tr}}$。
若 $p\ge r_0$，前 $r_0$ 项之和至少
$r_0D_{\mathrm{tr}}/p\ge r_0D_{\mathrm{tr}}/(D-1)$。
若 $p<r_0$，加入的 $r_0-p$ 个最大非正项之和至少
$-(r_0-p)D_{\mathrm{tr}}/(D-p)$，故总和至少
$(D-r_0)D_{\mathrm{tr}}/(D-p)$。
这给所述统一下界。最后相减消去 $b$；下界说明零读出差只可能有 $\rho=\sigma$。

∎

在源式 (1) 中，将对应 $\Pi$ 的五个合法输出聚合，得到
$c\Pi+bI$ 的效果；其它所有输出仍在补事件中。
在其标准效果表示的矩阵态延拓内，项目十三维秩五情形给

$$
\boxed{
 \frac5{12}cD_{\mathrm{tr}}(\rho,\sigma)
 \le\sup_U|R_U(\rho)-R_U(\sigma)|
 \le cD_{\mathrm{tr}}(\rho,\sigma).
 }
 \tag{19}
$$

故全控制读出差至多 $\varepsilon$ 时，
$D_{\mathrm{tr}}\le12\varepsilon/(5c)$。
这里是效果表示的数学仿射延拓；若要将其用于实际混态制备，
还须供应该制备与效果语义，不能声称源已额外证明所有混态操作的仿射性。
全控制的上确界也不是有限样本已经检验完。
对应全部 Hermitian 效果的精确线性摘要至少需 $13^2-1=168$ 个实坐标；
该结论只针对完整凸密度态族与线性摘要，不用于单个实际 $\Omega$、
仅纯态族、任意编码或存储比特下界。

<a id="statement-5-5"></a>

#### 定理 5.5（态与未知读尺的联合可辨识商）

<a id="thm:jointcalibration"></a>

设 $D\ge2$、$\rho$ 为密度矩阵。
在全部内部控制下，采用同一组固定 $c,d$ 的模型族

$$
G_w(U;\rho,c,d)=c\,\operatorname{Tr}(E_wU\rho U^*)+d_w,
 \quad 0<c\le1,\quad d_w\ge0,\quad\sum_wd_w=1-c,
$$

其中合法 $E_w$ 是 $D$ 个秩一基投影，非法 $E_w=0$。
定义

$$
X=c(\rho-I/D),\qquad
 \beta_w=
 \begin{cases}c/D+d_w,&w\text{ 合法},\\d_w,&w\text{ 非法}.\end{cases}
 \tag{20}
$$

两个三元组给出全部相同的控制读出，当且仅当 $X=X'$、$\beta=\beta'$。
若所有候选已由额外内部依据限制为局部纯态，则可恢复

$$
c=\sqrt{\frac{D}{D-1}\operatorname{Tr}X^2},\qquad
 \rho=I/D+X/c.
 \tag{21}
$$

**证明。**

对酉群取归一 Haar 平均，平均态与所有酉对易，且迹为一，故为 $I/D$。
因此每个平均输出恰是 $\beta_w$。
减去平均后，合法输出为 $\operatorname{Tr}(E_wUXU^*)$；
秩一投影轨道分离所有自伴矩阵，故其相等迫使 $X=X'$。
反向直接代入。
若 $\rho$ 纯，则 $\operatorname{Tr}(\rho-I/D)^2=(D-1)/D$，
代入 $X$ 得式 (21)，再由 $c>0$ 恢复 $\rho$。

∎

一般确实存在不能区分的态与读尺。
取只在合法标签上的均匀噪声 $d_j=(1-c)/D$。
对任意 $c'\in[c,1]$，令

$$
\rho'=\frac c{c'}\rho+\left(1-\frac c{c'}\right)\frac ID,\qquad
 d_j'=\frac{1-c'}D.
$$

二者给相同的 $X,\beta$，且 $\rho'$ 仍正归一。
所以所有控制统计只能恢复可观测组合，不能一般将态的不纯与读尺对比度独立拆开。
两项内部校准、可信的局部纯性或其它供应关系可以进一步解除自由；
整体 $\Omega$ 纯并不自动保证这个内部限制态纯。
这正是“量与尺子都需要预测”的一个精确可辨识版本。

更具体地，给定一个可实现的 $(X,\beta)$，其全部剩余参数恰由

$$
0<c'\le1,\qquad
 -D\lambda_{\min}(X)\le c'\le
D\min_{j\text{ 合法}}\beta_j                              \tag{22}
$$

参数化，其中
$\rho'=I/D+X/c'$、
$d_j'=\beta_j-c'/D$（合法）、
$d_w'=\beta_w$（非法）。
证明分别检查 $\rho'\ge0$、$d'\ge0$；
迹及质量归一自动成立，故这些条件同时必要且充分。
此处内部预测剩余的是一个明确的可行纤维，而不是任意无约束的猜测。

<a id="sec-6"></a>

## 6. 记录递归的 Fisher 收支与稳定化

本节给定正归一的内部记录概率模型，再证明其信息恒等式；
不是从逻辑递归单独发明概率。
参数 $\lambda$ 是内部程序或条件态族的数学坐标，
可由一个固定整体中的程序条件化表示（见第 [8](#sec:geometry) 节）。
对每个有限深度，假设记录律对 $\lambda$ 为 $C^1$，
具有参数无关的共同有限支持，支持上概率为正。
所有停止及失败保持在记录中；停止后可补吸收标签。

<a id="statement-6-1"></a>

#### 定义 6.1（内部记录得分与 Fisher 信息）

对深度 $n$ 的完整记录 $H_n$，置

$$
S_n(h)=\partial_\lambda\log p_\lambda(h),\qquad
 \mathcal I_n(\lambda)=\mathbb{E}_\lambda S_n^2.
$$

若下一层的条件核为 $k_\lambda(o\mid h)$，
则 $p_\lambda(ho)=p_\lambda(h)k_\lambda(o\mid h)$。
允许该核依赖全部已保留记录，不要求独立同分布。

<a id="statement-6-2"></a>

#### 定理 6.2（递归得分的正交增量）

<a id="thm:fisherchain"></a>

令 $\xi_{n+1}=\partial_\lambda\log k_\lambda(O_{n+1}\mid H_n)$。
则

$$
S_{n+1}=S_n+\xi_{n+1},\qquad
 \mathbb{E}_\lambda[\xi_{n+1}\mid H_n]=0,
$$

$$
\boxed{
 \mathcal I_{n+1}-\mathcal I_n
 =\mathbb{E}_\lambda\xi_{n+1}^2\ge0.
 }                                                        \tag{23}
$$

若只保留一个参数无关的固定粗化 $Y=f(H_n)$，其得分为
$S_Y=\mathbb{E}_\lambda[S_n\mid Y]$，并且

$$
\mathcal I_n-\mathcal I_Y
 =\mathbb{E}_\lambda\operatorname{Var}_\lambda(S_n\mid Y)\ge0.                  \tag{24}
$$

**证明。**

路径概率的乘法在对数下变为加法，给第一式。
对 $\sum_ok_\lambda(o\mid h)=1$ 求导给条件零均值，
所以旧得分与新增得分的交叉期望为零，平方展开即得式 (23)。
对粗化律
$p_\lambda(y)=\sum_{h:f(h)=y}p_\lambda(h)$ 求导并除以它，
得到条件得分；条件方差分解给式 (24)。

∎

这给此前“加法、乘法、对数与勾股”直觉一个明确对应：
记录分支用加法汇总、路径用乘法组合、对数得分相加，
而零条件均值使新增得分在平方范数中正交。
它们全是一个内部记录模型的性质，不需要外部时间轴。

<a id="statement-6-3"></a>

#### 定理 6.3（经典稳定化的精确信息缺口）

<a id="thm:missing"></a>

设同一内部模型中有持久二元目标 $Z$，

$$
\Pr_\lambda(Z=1)=\pi(\lambda)\in(0,1).
$$

给定 $Z$ 的完整记录核 $Q_n(h\mid Z)$ 为同一嵌套记录族的相容边缘，
不依赖 $\lambda$，
但可依赖记录历史且相互相关。
令 $q_n(h)=\Pr_\lambda(Z=1\mid H_n=h)$。则

$$
\boxed{
 \mathcal I_n
 =
 \frac{\pi'^2}{\pi(1-\pi)}
 -
 \frac{\pi'^2}{\pi^2(1-\pi)^2}
 \mathbb{E}_\lambda[q_n(1-q_n)].
 }                                                       \tag{25}
$$

特别地，若完整记录最终辨识 $Z$，则

$$
\mathcal I_n\longrightarrow
 \mathcal I_Z=\frac{\pi'^2}{\pi(1-\pi)}.
$$

在 $\pi'\ne0$ 处，达到该极限等价于完整记录辨识 $Z$。

**证明。**

联合律为
$p_\lambda(z,h)=\pi_z(\lambda)Q_n(h\mid z)$。
由于条件核参数无关，其联合得分只依赖 $Z$：

$$
s_1=\frac{\pi'}{\pi},\qquad
 s_0=-\frac{\pi'}{1-\pi}.
$$

对 $z$ 求和给 $S_n=\mathbb{E}_\lambda[s_Z\mid H_n]$。
所以
$\mathcal I_Z-\mathcal I_n=\mathbb{E}_\lambda\operatorname{Var}(s_Z\mid H_n)$。
二值变量的条件方差为
$(s_1-s_0)^2q_n(1-q_n)$，即得式 (25)。
嵌套记录下 $q_n$ 是有界鞅；
v30 的条件期望证明给
$q_n\to q_\infty=\mathbb{E}[Z\mid\mathcal D_\infty]$，
且
$\mathbb{E}(Z-q_n)^2=\mathbb{E}q_n(1-q_n)$。
支配收敛和该恒等式给最后两项。

∎

因此无限多的记录可以最终确定一个指针标签，
却不因此从这个标签取得无限多的参数信息。
若读尺的条件核也含未知参数，即 $Q_n=Q_{n,\lambda}$，
其导数必须加入联合得分；式 (25) 的假设不再满足。
这恰好将量的不确定与关系、校准参数的不确定分别记入信息收支，
并未预设尺子总是准确。

例如内部 qubit 条件态
$\psi_\lambda=\cos(\lambda/2)\lvert 0\rangle+\sin(\lambda/2)\lvert 1\rangle$，
$0<\lambda<\pi$，以 $Z$ 基标签为持久目标，
有 $\pi=\sin^2(\lambda/2)$，故
$\pi'^2/[\pi(1-\pi)]=1$。
再多的参数无关 QND 记录也只将该目标的信息预算推进到一；
它们可以辨认本次标签，而不能从本次标签精确求出未知 $\lambda$。

<a id="sec-7"></a>

## 7. 非交换、前缀自适应的黄金递归门族

本节构造一个新的内部控制模型。系数是以弧度计的递归角，
不是项目根单位相位 $\zeta=e^{3\pi i/5}$。
与项目原生门的连接将在明确的联合控制与误差条件下进行；
共同使用黄金比例不自动意味着两个门菜单相同。

<a id="statement-7-1"></a>

#### 定义 7.1（相干前缀程序）

令 $X_{\rm prog}=\{0,1\}^{\mathbb{N}}$，在内部代数
$C(X_{\rm prog},\mathcal{A})$ 中取自伴场 $A_k(b)$，
它只依赖前 $k$ 位，且 $\sup_{k,b}\left\lVert A_k(b)\right\rVert\le M$。
对 $0<r<1$，置

$$
c_k=(1-r)r^{k-1},\quad
 V_k(b)=e^{-ic_kA_k(b)},\quad U_n(b)=V_n(b)\cdots V_1(b).
$$

程序标签的投影可以对易，而数据操作不要求对易；
整体控制保持相干，未将叠加程序先变成一个外部经典选择。

<a id="statement-7-2"></a>

#### 定理 7.2（非交换递归的一致极限）

<a id="thm:noncommuting"></a>

存在内部酉场 $U$，使

$$
\sup_b\left\lVert U(b)-U_n(b)\right\rVert\le Mr^n.
 \tag{26}
$$

若 $b,b'$ 的前 $n$ 位相同，则
$\left\lVert U(b)-U(b')\right\rVert\le2Mr^n$。
对另一自伴场族 $A'_k$ 及其极限 $U'$，还有

$$
\sup_b\left\lVert U(b)-U'(b)\right\rVert
 \le\sum_kc_k\sup_b\left\lVert A_k(b)-A'_k(b)\right\rVert.
$$

**证明。**

$\left\lVert e^{-itA}-I\right\rVert\le|t|\left\lVert A\right\rVert$。
用酉乘积的伸缩求和，
$\left\lVert U_m-U_n\right\rVert\le\sum_{k=n+1}^m\left\lVert V_k-I\right\rVert\le Mr^n$。
一致极限存在；乘法与伴随的范数连续性给极限酉性。
共同前缀的有限乘积相同，两个尾界给第二项。
对有界自伴 $A,B$，
对 $e^{-i(t-s)A}e^{-isB}$ 积分得到
$\left\lVert e^{-itA}-e^{-itB}\right\rVert\le|t|\left\lVert A-B\right\rVert$；
逐层伸缩并取极限给最后一式。

∎

<a id="statement-7-3"></a>

#### 命题 7.3（效果与完整输出律的锐化误差界）

<a id="prop:effectbound"></a>

对任意正归一态、酉 $U,V$ 和效果 $0\le E\le I$，

$$
|\omega(U^*EU)-\omega(V^*EV)|\le\left\lVert U-V\right\rVert.              \tag{27}
$$

固定完整有限 POVM 的总变差也至多为该门距。

**证明。**

令 $F=E-I/2$，$\left\lVert F\right\rVert\le1/2$，标量项相消。
展开
$(U^*-V^*)FU+V^*F(U-V)$ 即得界。
每个 POVM 输出事件的效果仍在 $[0,I]$，对事件取上确界给总变差。
附带内部参考坐标时张量恒等不改变范数。

∎

<a id="statement-7-4"></a>

#### 定理 7.4（真正非交换的黄金 Cantor 门嵌入）

<a id="thm:goldencantor"></a>

取 $r=\varphi^{-2}$，每个长度 $k-1$ 的前缀 $s$ 选择

$$
H_{k,s}=H_{k,s}^*,\qquad H_{k,s}^2=I,\qquad
 \operatorname{Tr}H_{k,s}=0,\qquad H_{k,s}\in M_2(\mathbb{C}).
$$

定义

$$
V_k(b)=
 \exp[-ic_k(2b_k-1)H_{k,b|_{k-1}}],\qquad
 U(b)=\lim_nV_n(b)\cdots V_1(b).
 \tag{28}
$$

若两程序共有 $n$ 个初始位，令 $d_r(b,b')=r^n$，相同程序距离为零。
则 $U(b)\in\operatorname{SU}(2)$，且

$$
\boxed{
 \frac{5-11r}{3}\,d_r(b,b')
 \le\left\lVert U(b)-U(b')\right\rVert\le2d_r(b,b').
 }                                                        \tag{29}
$$

可取奇数层轴 $X$、偶数层轴 $Z$，获得相邻层不对易的实例；
轴也可以依赖全部此前程序。

**证明。**

各指数无迹，故有限乘积及其极限都在 $\operatorname{SU}(2)$。
设首差位为 $k=n+1$。此前两分支同轴同乘积，
当前位采用相反号，局部门距为 $2\sin c_k$。
后续两尾各至多 $r^k$，所以

$$
\left\lVert U(b)-U(b')\right\rVert\ge2\sin c_k-2r^k.
$$

因 $0<c_k<1$，$\sin t\ge t-t^3/6\ge5t/6$，得到下界
$[(5-11r)/3]r^{k-1}$。
$\varphi>3/2$ 给 $\varphi^2=\varphi+1>5/2$，
所以 $r<2/5<5/11$，常数严格正。
上界来自定理 [7.2](#thm:noncommuting)。

∎

<a id="statement-7-5"></a>

#### 定理 7.5（射影门像及其精确分形维数）

<a id="thm:projectivefractal"></a>

令

$$
d_{\rm p}(U,V)=\inf_{|\lambda|=1}\left\lVert U-\lambda V\right\rVert,\quad
 q_*=2\sin\frac{1-r}{2}+r<1,
$$

$$
a_*=\min\{(5-11r)/3,\ 2-2q_*\}>0.
$$

则

$$
a_*d_r(b,b')\le d_{\rm p}(U(b),U(b'))\le2d_r(b,b').
$$

普通门像与射影门像的 Hausdorff 维数均为

$$
\boxed{
 s_*=\frac{\log2}{\log(1/r)}
 =\frac{\log2}{2\log\varphi}.
 }                                                        \tag{30}
$$

**证明。**

第一步误差精确为 $2\sin[(1-r)/2]$，剩余尾至多 $r$，
故 $\left\lVert U(b)-I\right\rVert\le q_*<1$。
若 $U^*V$ 的特征值为 $e^{\pm i\theta}$，
对整体相位最优化等价于最大化
$\cos t\cos\theta-|\sin t\sin\theta|$，其最大值为 $|\cos\theta|$。
因此在 $\operatorname{SU}(2)$ 中

$$
d_{\rm p}(U,V)=\min\{\left\lVert U-V\right\rVert,\left\lVert U+V\right\rVert\}.
$$

第二项至少 $2-2q_*$，而 $d_r\le1$，
结合式 (29) 即得射影双边界。

为直接证明维数，$2^n$ 个前缀柱集的直径为 $r^n$，
给上界 $s_*$。给每个柱集质量 $2^{-n}$。
若一个集合直径 $\delta$ 满足
$r^n\le\delta<r^{n-1}$，其中各点必共有前 $n$ 位，
故其质量至多 $2^{-n}=(r^n)^{s_*}\le\delta^{s_*}$；
单点质量为零。对任意可数细覆盖求和，给正的 $s_*$ 维 Hausdorff 测度下界。
双 Lipschitz 不等式逐覆盖传递维数，得到式 (30)。

∎

普通参数具有 Cantor 结构，并不能自动推出门像具有相同维数。
例如取交替轴 $H_j=X,Z$，令
$A_{2j-1}(b)=r b_jH_j$、$A_{2j}(b)=-b_jH_j$。
因 $c_{2j}=rc_{2j-1}$，每对门恰好相消，极限恒为 $I$；
不同对子中的轴仍可不对易。
定理 [7.4](#thm:goldencantor) 中首差位的分离条件因此不可删除。

<a id="statement-7-6"></a>

#### 命题 7.6（固定内部参考保留门的分形几何）

<a id="prop:bell"></a>

在同一整体内取
$\Phi=(\lvert 00\rangle+\lvert 11\rangle)/\sqrt2$，
$\Psi_U=(U\otimes I)\Phi$。
对 $U,V\in\operatorname{SU}(2)$，

$$
\frac1{\sqrt2}d_{\rm p}(U,V)
 \le D_{\mathrm{tr}}(\Psi_U,\Psi_V)
 \le d_{\rm p}(U,V).
 \tag{31}
$$

所以这些相对纯态读出的像也具有式 (30) 的精确维数。

**证明。**

$\langle\Psi_U,\Psi_V\rangle=\operatorname{Tr}(U^*V)/2=\cos\theta$。
两纯态投影差在其二维跨度中的特征值为
$\pm\sqrt{1-|\langle\Psi_U,\Psi_V\rangle|^2}$，
故迹距为 $|\sin\theta|$。
而

$$
|\sin\theta|
 =\sqrt{2-2|\cos\theta|}
  \sqrt{\frac{1+|\cos\theta|}{2}},
$$

第一因子为 $d_{\rm p}$，第二因子在 $[1/\sqrt2,1]$ 内。

∎

这是成对可辨识几何；不声明单次就能完美解码所有非正交读出。
第二矩阵坐标是内部参考角色，不是本体外辅助物。

<a id="statement-7-7"></a>

#### 命题 7.7（正规化有限前缀程序）

<a id="prop:prefix"></a>

在 $X_{\rm prog}$ 上取非原子、满支撑概率测度 $\nu$。
同一整体的内部程序坐标为 $L^2(X_{\rm prog},\nu)$。
乘法算符 $(Gf)(b)=U(b)f(b)$ 为酉；
有限前缀受控乘法算符 $G_n$ 满足 $\left\lVert G-G_n\right\rVert\le r^n$。
对前缀 $s$ 的正规化程序
$p_s=1_{[s]}/\sqrt{\nu([s])}$，所有单位数据向量均满足

$$
\left\lVert G(p_s\otimes\psi)-p_s\otimes U_n(s)\psi\right\rVert\le r^n.
 \tag{32}
$$

**证明。**

逐点酉性保持积分范数，逆算符由 $U(b)^*$ 给出。
一致尾界给乘法算符范数界。
在柱集 $[s]$ 上有限乘积恒为 $U_n(s)$，
将点态误差平方并对正规化柱集积分即得。

∎

每个有限前缀均有普通正规化程序；单条无限路径为零测集，
没有非零正规化点程序。选择 $\nu$ 构造一个数学表示，
不把公平测度当成已由黄金比推出的物理概率。

<a id="statement-7-8"></a>

#### 定理 7.8（有限编译与全部保留误差）

<a id="thm:compile"></a>

若在正确的联合受控载体上，实际酉实现
$\widetilde V_k$ 满足 $\left\lVert \widetilde V_k-V_k\right\rVert\le\delta_k$，则

$$
\left\lVert U-\widetilde V_N\cdots\widetilde V_1\right\rVert
 \le Mr^N+\sum_{k=1}^N\delta_k.                          \tag{33}
$$

若 $M>0$，使尾至多 $\varepsilon/2$ 的一个深度为

$$
N=\max\left\{0,
 \left\lceil\frac{\log(2M/\varepsilon)}{\log(1/r)}\right\rceil
 \right\}.
$$

**证明。**

在无限极限与实际有限乘积之间插入理想有限乘积，
分别用尾界与酉伸缩求和。再解 $Mr^N\le\varepsilon/2$。

∎

这个对数界是分辨率细化深度，不自动给原生门数、寻找门字的成本或物理钟时。
逐个经典分支存在逼近字，也不自动给一个保持所有分支相对相位的相干受控实现。
项目 §§100、105 的代码范围和误差范数必须逐项对应：
ready 输入上的等距误差不能直接升级为整个载体的算符或 diamond 范数误差。
相干控制之外的实际概率合同仍按定义 [1.1](#def:layers) 单列。

<a id="sec-8"></a>

## 8. 固定整体中的相对态与信息几何

<a id="sec:geometry"></a>

### 连续参数的内生表示及其额外前提

令 $\Lambda$ 为标准 Borel 的光滑数学参数图表，
$\nu$ 为其上满支撑的概率测度，
$\lambda\mapsto\psi_\lambda$ 为强可测单位向量场。
在同一整体的内部坐标
$L^2(\Lambda,\nu;\mathcal{H})$ 中取固定正规化向量

$$
\boldsymbol\Omega(\lambda)=\psi_\lambda.
$$

参数记录 $P_B$ 为集合 $B$ 的乘法投影。对固定数据效果 $E$，

$$
\omega(P_BE)
 =\int_B\langle\psi_\lambda,E\psi_\lambda\rangle\,d\nu(\lambda).
 \tag{34}
$$

由积分直接验证它是一个固定整体态。
在 $\nu(B)>0$ 时，有限窗口 $B$ 的条件律是右侧除以 $\nu(B)$；
连续参数的单点通常为零质量，$\psi_\lambda$ 是正则条件态的版本，
不能写成不可数个正规化正交点程序。
若此条件态族在向量范数中为 $C^2$，可在该图表研究微分几何。
满支撑保证其连续条件版本不因零质量区域的任意修改而改变。
第 7 节的 Cantor 程序空间自身没有自动提供这种光滑结构。

如果制备和读出基底都在内部变化，设两族酉为 $A(\lambda),B(\lambda)$，
固定内部参考向量为 $\psi_0$。相对态为

$$
\psi_\lambda=B(\lambda)^*A(\lambda)\psi_0,\qquad
 p_j(\lambda)=\langle\psi_\lambda,E_j\psi_\lambda\rangle
 \tag{35}
$$

其中 $E_j$ 固定。
共同左乘任意 $V(\lambda)$ 使 $B^*A$ 逐点不变，
所以这种相对几何没有选择一个本体外的绝对基底。
若读口的效果本征值也变化，不能仅靠基底旋转吸收；
必须将它的程序并入联合输入与固定联合读口，或直接使用完整经典概率族。
所有相关导数都要保留。

<a id="statement-8-1"></a>

#### 定义 8.1（相对量子几何张量）

对一个 $C^2$ 单位向量图表，置
$P_\lambda=\lvert \psi_\lambda\rangle\langle \psi_\lambda\rvert$，
$\eta_\mu=(I-P_\lambda)\partial_\mu\psi_\lambda$，定义

$$
\chi_{\mu\nu}=\langle\eta_\mu,\eta_\nu\rangle,\qquad
 g_{\mu\nu}=\operatorname{Re}\chi_{\mu\nu},\qquad
 \mathscr F_{\mu\nu}=2\operatorname{Im}\chi_{\mu\nu}.
 \tag{36}
$$

$g$ 是读出射线可辨识性的半正定形式；不可辨识方向可以在其中为零。

<a id="statement-8-2"></a>

#### 定理 8.2（几何、生成元方差与固定约束）

<a id="thm:qgt"></a>

$\chi$ 是正半定 Hermitian 张量，局部相位变换不改变它。
若 $U(\lambda)$ 是算符范数 $C^2$ 的酉族且
$\psi_\lambda=U(\lambda)\psi_0$，
$G_\mu=iU^*\partial_\mu U$，则

$$
\chi_{\mu\nu}
 =\langle\psi_0,G_\mu G_\nu\psi_0\rangle
  -\langle G_\mu\rangle\langle G_\nu\rangle.              \tag{37}
$$

因此

$$
g_{\mu\mu}=\operatorname{Var}_{\psi_0}(G_\mu),\qquad
 \mathscr F_{\mu\nu}=-i\langle[G_\mu,G_\nu]\rangle,
$$

$$
\boxed{
 g_{\mu\mu}g_{\nu\nu}-g_{\mu\nu}^2
 \ge\frac14\mathscr F_{\mu\nu}^2.
 }                                                       \tag{38}
$$

定义实连接一形式 $\mathscr A_\mu=-i\langle\psi,\partial_\mu\psi\rangle$，
则 $\partial_\mu\mathscr A_\nu-\partial_\nu\mathscr A_\mu=\mathscr F_{\mu\nu}$。

**证明。**

$\chi$ 是向量族 $\eta_\mu$ 的 Gram 矩阵，所以正半定。
相位 $\psi'=e^{i\alpha}\psi$ 的导数中，
$i(\partial_\mu\alpha)\psi$ 被 $I-P$ 消去，故 $\eta'_\mu=e^{i\alpha}\eta_\mu$。
$U^*\partial_\mu U=-iG_\mu$ 给 $\partial_\mu\psi=-iUG_\mu\psi_0$，
投影后的 Gram 式即为中心化生成元乘积，得到式 (37)。
其虚部为交换子期望除以 $2i$。
二阶主子式非负给式 (38)。
最后对 $\mathscr A$ 求导，混合二阶导数相消，余下
$-i(\langle\partial_\mu\psi,\partial_\nu\psi\rangle -\langle\partial_\nu\psi,\partial_\mu\psi\rangle)$。
去除垂直相位分量只改变实部，因此该式恰为 $2\operatorname{Im}\chi_{\mu\nu}$。

∎

这是一套标准量子信息几何结构在内部相对读出中的使用；
统计可辨识度与量子态几何的关系见 Braunstein--Caves，
生成元方差与射影路径长度的关系见 Anandan--Aharonov。（[8](#ref-braunstein)、[10](#ref-anandan)）
这里没有从五点关联图单独导出复数或连续微分结构；
所证明的是一旦这些结构被内部模型供应，其度量、相位曲率与不确定性具有同一个 Gram 来源。

<a id="statement-8-3"></a>

#### 命题 8.3（二维相对读出的几何约束）

<a id="prop:qubitgeom"></a>

对
$\psi_{\theta,\phi}=\cos(\theta/2)\lvert 0\rangle+ e^{i\phi}\sin(\theta/2)\lvert 1\rangle$，

$$
\chi=\frac14
 \begin{pmatrix}
 1&i\sin\theta\\-i\sin\theta&\sin^2\theta
 \end{pmatrix},\qquad
 ds^2=\frac14(d\theta^2+\sin^2\theta\,d\phi^2),\qquad
 \mathscr F_{\theta\phi}=\frac12\sin\theta.
 \tag{39}
$$

式 (38) 在此取等。

**证明。**

直接求两个偏导：
$\langle\psi,\partial_\theta\psi\rangle=0$、
$\langle\psi,\partial_\phi\psi\rangle=i\sin^2(\theta/2)$、
$\langle\partial_\theta\psi,\partial_\phi\psi\rangle=i\sin\theta/4$。
投去相位分量给式 (39)；其行列式为零。

∎

这把二元态的三维 Bloch 读出与一个两局部坐标的几何联系起来：
归一化、度量和相位曲率共享同一约束。
它是 v28 二元读出结构的几何延伸，不是物理空间恰好三维的证明。（[3](#ref-v28)）

<a id="statement-8-4"></a>

#### 定理 8.4（固定内部读口的 Fisher 上界及局部达到）

<a id="thm:qfi"></a>

沿一条参数曲线取固定完整有限 POVM $\{E_w\}$，
$p_w=\langle\psi_\lambda,E_w\psi_\lambda\rangle$。
在正支持上定义的 Fisher 信息满足

$$
\boxed{
 \mathcal I_E(\lambda)=\sum_{w:p_w>0}\frac{(p_w')^2}{p_w}
 \le4\left\lVert (I-P)\psi_\lambda'\right\rVert^2=4g_{\lambda\lambda}.
 }                                                       \tag{40}
$$

在每个给定点，存在对该一参数方向达到上界的局部读口。

**证明。**

令 $\eta=(I-P)\psi'$。由正规化，
$p_w'=2\operatorname{Re}\langle\eta,E_w\psi\rangle$。
对 $E_w^{1/2}\eta,E_w^{1/2}\psi$ 用 Cauchy--Schwarz，
得 $(p_w')^2/p_w\le4\langle\eta,E_w\eta\rangle$。
求和即得上界；零概率项的导数为零。
若 $\eta\ne0$，在所讨论点取
$e_\pm=(\psi\pm\eta/\left\lVert \eta\right\rVert)/\sqrt2$ 的投影及正交补。
两项概率均为 $1/2$，导数分别为 $\pm\left\lVert \eta\right\rVert$，
故 Fisher 信息为 $4\left\lVert \eta\right\rVert^2$。
当 $\eta=0$ 时上界为零。

∎

达到上界的读口可以依赖所讨论的未知点；
它不是一个无需内部校准即可全域最优的统一仪器。
式 (40) 要求效果固定。若 $E_w=E_w(\lambda)$，
还存在 $\langle\psi,E_w'\psi\rangle$ 项；
应使用式 (35) 的相对态或包含读口程序的整个输入。

<a id="statement-8-5"></a>

#### 推论 8.5（递归读取同一输入的总信息预算）

<a id="cor:oneinput"></a>

若有限自适应记录协议的全部分支仪器不依赖未知 $\lambda$，
且所有可用的参数相关内部自由度已计入初始输入，
则完整记录等价于该输入上的固定 POVM。
因此不论记录层数多大，其 Fisher 信息均受初始输入的式 (40) 约束。

**证明。**

每个完整记录词对应 Heisenberg 效果
$E_h=\Phi_{h_1}^*\cdots\Phi_{h_n}^*(I)$。
从末端向前求和，完整仪器使 $\sum_hE_h=I$；
自适应设置按既有记录选择，不依赖未知参数，所以这些效果固定。
对该 POVM 应用定理 [8.4](#thm:qfi)。

∎

若读取了编码 $\lambda$ 的内部程序标签、新取得的关联寄存器，
或再次调用未知参数门，输入及资源模型已经扩大，
必须在扩大模型上重新计算预算。
不能用条件数据分支的 QFI 限制整个含参数程序的本体，
也不能把原输入的重复处理层数当作独立副本数。

同理，对 $N$ 个等先验、单份 $D$ 维候选态 $\rho_j$，
任意完整递归判别协议的成功率满足

$$
p_{\rm succ}=\frac1N\sum_j\operatorname{Tr}(E_j\rho_j)
 \le\frac1N\sum_j\operatorname{Tr}E_j=\frac DN,
 \tag{41}
$$

因为 $0\le\rho_j\le I$。
取 $D=2,N=5$ 即为 v28 的五相位上界。
它与定理 [3.2](#thm:noisyqnd) 的正交持久指针没有冲突。

<a id="statement-8-6"></a>

#### 命题 8.6（两个相对方向不能同时取得各自全部局部信息）

<a id="prop:twoparam"></a>

在 qubit 图表的一个点选择局部坐标，使
$\psi=\lvert 0\rangle$、
$\partial_x\psi=\lvert 1\rangle/2$、
$\partial_y\psi=i\lvert 1\rangle/2$。
两方向的量子 Fisher 矩阵为 $I_2$。
对同一个固定 POVM 的正支持点态 Fisher 矩阵，

$$
\mathcal I_{xx}+\mathcal I_{yy}\le1.
 \tag{42}
$$

**证明。**

写
$E_w=\begin{pmatrix}a_w&z_w\\\bar z_w&b_w\end{pmatrix}$。
概率为 $a_w$，两个导数为 $\operatorname{Re}z_w$、
$-\operatorname{Im}z_w$。
正性给 $|z_w|^2\le a_wb_w$，故

$$
\mathcal I_{xx}+\mathcal I_{yy}
 =\sum_{a_w>0}\frac{|z_w|^2}{a_w}
 \le\sum_wb_w=1.
$$

当 $a_w=0$ 时 $z_w=0$，其点态导数无贡献。
若需要统计渐近结论，另要求共同支持和相应正则性；
此处只证明所列局部信息界。

∎

这是多参数量子估计权衡的基本 qubit 版本；
相关一般理论由 Gill--Massar 给出。（[9](#ref-gillmassar)）
两个方向分别可达到信息一，不等于一个共同读口可以同时在两方向达到一。
因此“正交坐标存在”与“全部坐标可同时无损读取”不同。

<a id="statement-8-7"></a>

#### 命题 8.7（未知态与读尺的共同扰动是 Fisher 零方向）

<a id="prop:fishernull"></a>

在定理 [5.5](#thm:jointcalibration) 的内部点，
设 $\rho>0$、$0<c<1$ 且全部合法 $d_j>0$。
对充分小实 $t$，令

$$
c(t)=c+t,\qquad
 \rho(t)=I/D+\frac{c}{c+t}(\rho-I/D),\qquad
 d_j(t)=d_j-t/D
$$

且非法 $d_w$ 不变。
所有单次控制响应均严格不变。
因此仅由这些响应构成、设计与参数无关的统计模型，沿该方向 Fisher 信息为零。

**证明。**

严格正性使小邻域仍合法。
式 (20) 的 $X,\beta$ 逐项不变，所有概率的方向导数为零，
故相应 Fisher 二次型为零。

∎

要在这组观测关系上讨论非退化信息几何，应先降到可辨识商 $(X,\beta)$，
或取得解除自由的额外内部校准。
本命题没有为尚未规定后态更新的全部顺序仪器声称同律。

<a id="statement-8-8"></a>

#### 命题 8.8（三轴门参数的完全内部联合读出）

<a id="prop:bellthree"></a>

若供应同一整体内的 Bell 参考
$\Phi=(\lvert 00\rangle+\lvert 11\rangle)/\sqrt2$，令

$$
\psi_{\boldsymbol\theta}
 =\left[
 e^{-i(\theta_xX+\theta_yY+\theta_zZ)/2}\otimes I
 \right]\Phi .
$$

在 $\boldsymbol\theta=0$，
$\chi_{ij}=\delta_{ij}/4$、$\mathscr F_{ij}=0$。
存在同一个四结果联合投影读口，在此点同时达到
$\mathcal I_{ij}=\delta_{ij}=4g_{ij}$，
并在一个原点邻域保持 $\mathcal I_{ij}=4g_{ij}$。

**证明。**

令 $e_0=\Phi$、$e_j=-i(\sigma_j\otimes I)\Phi$。
由 $\langle\Phi,(A\otimes I)\Phi\rangle=\operatorname{Tr}A/2$，
这四个向量为正交单位基，且
$\partial_j\psi=e_j/2$、$\langle e_0,\partial_j\psi\rangle=0$，
得到 $\chi$。
取四个符号三元组
$(+++),(+--),(-+-),(--+)$，
定义 $h_a=(e_0+\sum_js_{aj}e_j)/2$。
符号正交性使 $h_a$ 成为正交基。
在所讨论点 $p_a=1/4$、$\partial_jp_a=s_{aj}/4$，
故 $\mathcal I_{ij}=\sum_as_{ai}s_{aj}/4=\delta_{ij}$。
令 $t=|\boldsymbol\theta|$，则完整状态为
$\cos(t/2)e_0+[\sin(t/2)/t]\sum_j\theta_je_j$，
在这组固定基中系数为实，原点取连续延拓。
Hadamard 读出的四振幅在原点均为 $1/2$，
故在一个邻域内均非零。
若这些实振幅为 $z_a$，则
$\mathcal I_{ij}=4\sum_a(\partial_i z_a)(\partial_j z_a)$；
正规化给 $\langle\psi,\partial_i\psi\rangle=0$，
所以该式等于 $4g_{ij}$。

∎

这是一个三轴可稳定组织信息的正面模型：参考、门参数和联合读口都在内部。
所估计的是三个局部门参数，不是三个 Pauli 本征值的同时尖锐赋值；
同一读口的局部信息达到也不意味着一次样本精确确定三个参数。
Bell 参考与联合测量是明列的内部资源。

<a id="statement-8-9"></a>

#### 定理 8.9（黄金门谱到四概率读出的局部完整桥）

<a id="thm:classicalfractal"></a>

固定一个长度 $n\ge1$ 的程序前缀 $s$，
令 $\Gamma_s=U_n(s)$、$\delta=r^n$。
对柱集 $[s]$ 中的每个条件门纤维 $b$，
使用同一个内部联合读口
$h_{a,s}=(\Gamma_s\otimes I)h_a$，
其中 $h_a$ 是命题 [8.8](#prop:bellthree) 的四个向量。
令

$$
p_a^s(b)=|\langle h_{a,s},(U(b)\otimes I)\Phi\rangle|^2,
 \qquad
 m_\delta=\frac{1-\delta^2/2-\sqrt3\,\delta}{2}>\frac3{50}.
$$

那么四个读出振幅在固定实基下均为正，
其概率律在整个柱集上唯一确定条件门 $U(b)$，并满足

$$
m_\delta\left\lVert U(b)-U(b')\right\rVert
 \le\operatorname{TV}(p^s(b),p^s(b'))
 \le\left\lVert U(b)-U(b')\right\rVert.
$$

故该四概率响应像的 Hausdorff 维数也恰为
$\log2/(2\log\varphi)$。

**证明。**

相对门 $V_b=\Gamma_s^*U(b)$ 满足
$\left\lVert V_b-I\right\rVert\le\delta$。
每个 $\operatorname{SU}(2)$ 矩阵唯一写成
$V_b=a_0I-i\mathbf a\cdot\boldsymbol\sigma$，
其中四系数为实，$a_0^2+|\mathbf a|^2=1$。
有 $\left\lVert V_b-I\right\rVert^2=2(1-a_0)$，所以
$a_0\ge1-\delta^2/2$、$|\mathbf a|\le\delta$。
四个振幅是
$z_a=(a_0+\mathbf s_a\cdot\mathbf a)/2\ge m_\delta$。
因 $\delta\le r<2/5$ 且 $\sqrt3<2$，所列严格正下界成立。
因此可先取 $z_a=\sqrt{p_a^s}$ 的正根，
再以逆正交 Hadamard 变换恢复 $(a_0,\mathbf a)$，
进而恢复 $V_b$ 和 $U(b)$。

两实四元数矩阵之差的算符范数恰等于其四实系数差的 Euclidean 范数，
Hadamard 变换保持该范数。
又每个 $z_a+z_a'\ge2m_\delta$，故
$\left\lVert p-p'\right\rVert_2\ge2m_\delta\left\lVert U-U'\right\rVert$。
使用 $\operatorname{TV}=\left\lVert p-p'\right\rVert_1/2\ge\left\lVert p-p'\right\rVert_2/2$ 给下界；
上界为命题 [7.3](#prop:effectbound)。
柱集是整个二进制超度量空间的缩放副本，
结合定理 [7.4](#thm:goldencantor) 的双 Lipschitz 界给维数。

∎

这里基底只依赖已知有限前缀，不依赖未知后缀。
四个概率有一个归一化约束，局部组织三个门参数；
参考 $\Phi$、三个正交切向 $e_x,e_y,e_z$ 与预测向量 $\Psi_U$
也给 AURIC 五角色一个可研究的内部表示。
这是一个明确构造，尚不是从原五点关联图唯一推出该表示或物理三维空间的定理。

若实际输入是命题 [7.7](#prop:prefix) 的正规化程序 $p_s$，
后缀仍相干存在而读口只作用于数据和参考，
实际边缘为

$$
\bar p_a^s
 =\frac1{\nu([s])}\int_{[s]}p_a^s(b)\,d\nu(b).
$$

这四个平均数不能重建整个后缀分布或波函数，也不会选定一条无限程序。
上述注入性针对固定但未知条件门的概率函数，
不表示一次随机结果就能精确读取连续门参数。

<a id="statement-8-10"></a>

#### 推论 8.10（仿射读尺保维数，有限误差限制可辨识尺度）

<a id="cor:readoutscale"></a>

若上述新联合读口另已取得固定响应关系

$$
R(b)=c\,p^s(b)+d,\qquad 0<c\le1,\quad d\ge0,\quad\sum_w d_w=1-c,
$$

其中四概率可在其余完整标签上补零，$c,d$ 与未知后缀无关，
则 $R$ 仍为柱集上的双 Lipschitz 注入，具有同一 Hausdorff 维数。
若还对全部 $b\in[s]$ 证明了实际近似的完整终端误差
$\operatorname{TV}(\widehat R(b),R(b))\le\varepsilon$，则

$$
\operatorname{TV}(\widehat R(b),\widehat R(b'))
 \ge c\,m_\delta\frac{5-11r}{3}\,d_r(b,b')-2\varepsilon.
$$

因此在右侧严格为正的尺度上，实际概率律必可区分。

**证明。**

公共偏置抵消，给
$\operatorname{TV}(R(b),R(b'))=c\,\operatorname{TV}(p^s(b),p^s(b'))$。
结合定理 [8.9](#thm:classicalfractal) 与定理 [7.4](#thm:goldencantor)
得双 Lipschitz 界；三角不等式再扣除两个 $\varepsilon$ 即得实际误差界。

∎

未知 $c,d$ 会妨碍观察者实施反演，但不改变固定响应族的上述数学注入性。
固定非零误差不能证明无限细尾仍然注入，也不能证明实际近似像保留精确分形维数。
本推论明确要求新联合读口具有所列响应与误差合同；
旧 $J$ 接口上的源分类并不自动把合同转移给任意新编码与新测量。
这正是把项目的未知读尺、理想黄金几何和有限原生取得接起来时需要补齐的接口。

<a id="sec-9"></a>

## 9. 非交换闭路、分辨率收敛与真实时钟增长

<a id="statement-9-1"></a>

#### 定理 9.1（闭路交换子及显式余项）

<a id="thm:loop"></a>

对有界自伴 $A,B$，实数 $t,s$，置

$$
C(t,s)=e^{-itA}e^{-isB}e^{itA}e^{isB}.
$$

则

$$
\left\lVert C-I\right\rVert\le |ts|\left\lVert [A,B]\right\rVert,
$$

$$
\boxed{
 \left\lVert C-I+ts[A,B]\right\rVert
 \le2|ts|(|t|\left\lVert A\right\rVert+|s|\left\lVert B\right\rVert)\left\lVert [A,B]\right\rVert.
 }                                                        \tag{43}
$$

若 $ts\ne0$、$[A,B]\ne0$ 且
$2(|t|\left\lVert A\right\rVert+|s|\left\lVert B\right\rVert)<1$，闭路严格非平凡。

**证明。**

令 $V=e^{-itA}$、$W=e^{-isB}$，则
$C-I=[V,W]V^*W^*$。两次 Duhamel 积分给

$$
[V,B]=-i\int_0^t e^{-i(t-u)A}[A,B]e^{-iuA}\,du,
$$

$$
[V,W]=-i\int_0^s e^{-i(s-v)B}[V,B]e^{-ivB}\,dv.
$$

周围因子均酉，双积分给第一界。
将各酉因子换成恒等后，双积分为 $-ts[A,B]$。
以酉伸缩估计比较每个被换因子，积分核误差至多
$2(|t|\left\lVert A\right\rVert+|s|\left\lVert B\right\rVert)\left\lVert [A,B]\right\rVert$，
乘积分面积得式 (43)。负参数用有向积分及绝对值处理。
反三角不等式给最后结论。

∎

对 $A=X,B=Z$，主项为 $2itsY$。
相邻黄金层从 $k\ge2$ 起满足
$c_k+c_{k+1}\le r<1/2$，
所以这些尺度上确实存在严格非平凡闭路。
它们是内部输运的算符关系。
若所有边只是完整参考框架的差 $U_{uv}=F_vF_u^*$，
闭路乘积逐项抵消为 $I$，不能把纯坐标更换误作这种输运。

<a id="statement-9-2"></a>

#### 命题 9.2（记录持续增长与完整过程的范数收敛）

<a id="prop:clock"></a>

若 $W_n$ 为同一固定表示中的酉，单位向量 $\Omega_0$ 的
$W_n\Omega_0$ 携带彼此正交的保留钟标签，则当 $m\ne n$，

$$
\left\lVert W_m\Omega_0-W_n\Omega_0\right\rVert=\sqrt2,\qquad
 \left\lVert W_m-W_n\right\rVert\ge\sqrt2.
 \tag{44}
$$

所以完整过程不能同时在该向量上 Cauchy 或在算符范数中收敛。

**证明。**

标签正交使两个单位向量内积为零，展开距离平方并用算符范数定义即可。

∎

例如内部双向计数器 $S\lvert j\rangle=\lvert j+1\rangle$ 给
$W_n=S^n\otimes U_n$。
数据修正 $U_n$ 可满足黄金尾界，而完整记录继续增长。
固定权重 $\alpha_n>0$、$\sum_{n\in\mathbb{Z}}\alpha_n^2=1$
可将相容条件态族写成一个静态整体
$\boldsymbol\Omega=\sum_n\alpha_n\lvert n\rangle\otimes\psi_n$；
v30 已给其正约束核和静态变分表示。
这里没有要求本体在外部时间中改变。
需要分别表述的是：全部历史、特定读口的分辨率极限、以及记录条件下的相对态。

<a id="statement-9-3"></a>

#### 命题 9.3（内部可辨识长度与钟的标定）

<a id="prop:length"></a>

对光滑内部参数路径 $\lambda(u)$，定义

$$
L(\lambda)=\int
 \sqrt{g_{\mu\nu}(\lambda)\dot\lambda^\mu\dot\lambda^\nu}\,du.
 \tag{45}
$$

它在单调光滑重参数化下不变。
若另已供应内部钟 $\tau$、常数 $\hbar>0$ 与有界自伴能量生成元解释
$i\hbar\partial_\tau\psi=H\psi$，则

$$
\frac{ds}{d\tau}=\frac{\Delta_\psi H}{\hbar},\qquad
 \mathcal I_{\tau}\le\frac{4(\Delta_\psi H)^2}{\hbar^2}.
 \tag{46}
$$

**证明。**

链式法则使被积线元不变。
由 Schrödinger 关系，
$(I-P)\partial_\tau\psi=-i(H-\langle H\rangle)\psi/\hbar$；
其平方范数即方差除以 $\hbar^2$。
应用式 (40) 得第二式。

∎

式 (45) 是无量纲可辨识长度，式 (46) 还需要所列钟标定与能量解释。
它们不把未标定的矩阵字长自动变为物理秒。
完整带记录门的增长仍可给计数钟，但计数、信息增量和射影长度是三个不同的量，
可以在同一静态整体内相互关联。

本稿的 $g$ 正半定，$\mathscr F$ 是态射线的相位曲率；
式 (43) 是算符输运闭路。它们均不是已经取得的 Lorentz 时空度量或 Riemann 曲率。
要进入引力，还需从内部钟、距离、光因果和适当输运对象取得时空几何，
并从内部动力学约束选择其方程。
v30 的钟率函数 $N$ 在已给静态度量下产生测地线加速度，
属于这条路线中的条件桥梁；本稿补的是可辨识性、参数程序和关系曲率的前端。

<a id="sec-10"></a>

## 10. 与原生门的有限接口及整体理论的闭合范围

### 源 §105 的新增供应确实支付了哪些资源

本轮源的短种子精确使用记录 $1$，
而实际供应的 ready 输入是 $J(v,0)$。
源因此先用有限记录字 $B_I$ 逼近记录翻转，
再用完整载体字 $C_C$ 逼近受控

$$
U_c=I_H\otimes\lvert 0\rangle\langle 0\rvert+D\otimes\lvert 1\rangle\langle 1\rvert .
$$

记录相干向量为 $u=(y,x)^{\mathsf T}$，两设置的理想分支分别为
$yJ(\psi,0)+xJ(D\psi,1)$ 与
$yJ(D^4\psi,0)+xJ(D^3\psi,1)$。
这里实际质量仍由第 2 节的未知响应合同处理，未自动认定为平方权重。

若两近似字的有符号长度为 $L_I,L_C$，源的九倍正向逆字规则给

$$
N_{\rm new}\le9L_I+9L_C+2+2s.
 \tag{47}
$$

记录读取是另行供应的保留仪器，不在这些酉调用数内。
相干向量误差必须包括输入、初始化、耦合、种子、读者及所有实际调用的累计误差。
理想两分支较小范数为 $x$；总误差 $\Delta<x$ 时，
归一射线误差至多 $2\Delta/x$。
在指定 Born 比较模型中，完整输出总变差至多 $\Delta$，
代码外质量至多 $\Delta^2$。
这些比较界不是任意未知实际读者的概率界，
因此第 2 节的 $\beta_n,\gamma_n,\sigma_n$ 不能由它们替代。（[2](#ref-quantumii)）

<a id="statement-10-1"></a>

#### 定理 10.1（固定八十九维载体中的有限前缀酉实现）

<a id="thm:nativeprefix"></a>

消费源 §100 的全 $\operatorname{PU}(89)$ 原生密度。
对 $0\le N\le4$，取一个内部等距编码

$$
L:\mathbb{C}^{2^N}\otimes\mathbb{C}^2\otimes\mathbb{C}^2\hookrightarrow\mathcal K,
 \qquad 2^{N+2}\le64<89.
$$

程序、数据、参考分别占这三个内部坐标。
定义有限前缀联合目标

$$
\Gamma_N=\sum_{s\in\{0,1\}^N}\lvert s\rangle\langle s\rvert\otimes U_N(s)\otimes I_2,
$$

并在补空间取恒等。则对每个 $\varepsilon>0$，
存在一个有限原生门字 $W_\varepsilon$ 及一个共同相位 $\alpha$，使

$$
\left\lVert W_\varepsilon-
 \alpha[L\Gamma_NL^*+(I-LL^*)]\right\rVert\le\varepsilon.
 \tag{48}
$$

该界对全部程序叠加、全部数据及保留内部参考同时有效。

**证明。**

所列维数保证等距编码存在；$\Gamma_N$ 由正交程序块上的酉组成，
故其与补空间恒等的直和是整个 $\mathcal K$ 上的酉。
全载体射影密度给任意精度的单个共同相位逼近，
不能用分别为各程序分支选择的相位替代。

∎

定理 [10.1](#thm:nativeprefix) 是一个有明确维数范围的原生消费者。
$L$ 是新编码，不是旧 $J$ 的二十六维记录接口；
它不供应旧读者的响应转移、实际测量或保留记录合同。
该定理
没有把第 7 节无限程序空间塞入固定 $89$ 维载体。
若需要从给定 ready 态取得指定程序与参考初态，还要另外支付制备逼近；
较大前缀须另外供应足够内部载体及相应全载体控制定理。
式 (48) 是有限精度存在性，不给最短字、编译算法复杂度或物理时间。
原 §103 的完整代码奇次受控相位精确障碍仍有效。

<a id="statement-10-2"></a>

#### 定理 10.2（固定整体内的条件综合）

<a id="thm:synthesis"></a>

假设同一整体 $(\mathcal{A},\omega)$ 内同时供应：
持久记录及记录相容代数；
所列内部仪器与未来效果菜单；
相干前缀程序和第 7 节的控制关系；
必要时的光滑相对条件态图表；
以及采用源重构结论时第 2 节的全部实际合同。
则下列结论可以同时成立：

1.  相容记录中的预测是正的平方最优条件期望；
全部未来所需状态由 $\mathcal{S}_\infty$ 上的限制给出。

2.  读口仿射自由有明确的校准判据和联合可辨识纤维；
非零对比度可保留全控制辨识性。

3.  持久目标的后验稳定化具有式 (25) 的精确信息收支；
完整递归处理服从其初始可访问输入的信息预算。

4.  非交换黄金修正给一致极限、精确分形门像及有限前缀误差；
已知前缀下的四概率读口保留条件门族几何，
额外固定仿射响应与实际误差合同给推论 [8.10](#cor:readoutscale) 的可辨识尺度，
而永久记录仍可增长。

5.  光滑相对读出给统一的度量、生成元方差和相位曲率；
内部输运闭路有式 (43) 的可控非交换效应。

这些结论不要求改变整体 $\omega$ 或引入任何本体外的物理角色。

**证明。**

各对象都是同一代数中的元素、子代数、受控算符、内部条件态或记录律。
各节定理只调用其明确的内部关系。
在同时满足这些前提的整体中逐项应用即可。
该条件综合不声称任意分别指定的局部数据都可相容拼接，
也不将正态读出层的规则当成未知响应层的无条件推论。

∎

本轮新增的可继续消费对象已经具体化：
未知读尺的完整可辨识纤维、实际记录质量的整列误差界、
非交换黄金门像及其正规化程序、持久记录的信息缺口恒等式，
以及可变基底全部内生后的信息几何。
后续需要证明的连接是：更深前缀的原生联合取得，
记录和校准合同的具体内部动力学来源，
以及从可辨识几何到时空因果与引力作用量的关系。
这些问题均留在同一个整体内部，不通过增加外部观察者来解决。

<a id="sec-bibliography"></a>

## 文献与固定来源

<a id="ref-repohead"></a>

**[1]** 
The Omega Institute, trureturing.
[固定 dev 快照 ae852c6f…](https://github.com/the-omega-institute/trureturing/tree/ae852c6f2df9ac7779afc168cb1a1850327e217b)，
2026-10-30 22:44:57 Asia/Singapore，PR #24257。

<a id="ref-quantumii"></a>

**[2]** 
项目，
[《AURIC FIB ATOM 与量子基本原则：原生预测秩与终端响应（续卷 II）》](https://github.com/the-omega-institute/trureturing/blob/ae852c6f2df9ac7779afc168cb1a1850327e217b/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md)。
本轮新增 §§104--108；消费 §§77--79、85--86、99--103 的明确前置。
Git blob：

`07b42c289db08b527554cc7890c7932212c8558a`。

<a id="ref-v28"></a>

**[3]** 
项目，
[《AURIC：二元读出、全框架相融与 E8 黄金门桥梁》](https://github.com/the-omega-institute/trureturing/blob/ae852c6f2df9ac7779afc168cb1a1850327e217b/docs/develop/theory/AURIC_BINARY_READOUT_FULL_FRAME_COMPATIBILITY_AND_E8_GOLDEN_GATE_BRIDGE_V28.md)，v28 归档。
消费二元树仪器、完整 POVM 汇总和单份五相位判别范围；
归档未被当作新的独立验证。

<a id="ref-v15"></a>

**[4]** 
项目，
[《AURIC 黄金门、NAND 类通用性与算术边界》](https://github.com/the-omega-institute/trureturing/blob/ae852c6f2df9ac7779afc168cb1a1850327e217b/docs/develop/theory/AURIC_GOLDEN_GATE_NAND_UNIVERSALITY_AND_ARITHMETIC_LIMITS_V15.md)，v15。
本稿经量子续卷 II 的明确接口消费全扇区射影密度、
逆字规则与精确取得边界，未重证全部编织密度。

<a id="ref-omega"></a>

**[5]** 
项目，
[《AURIC $\Omega$ 静态相融纤维理论》](https://github.com/the-omega-institute/trureturing/blob/ae852c6f2df9ac7779afc168cb1a1850327e217b/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)，
以及
[《静态量子历史、内生观察者与关系时钟》](https://github.com/the-omega-institute/trureturing/blob/ae852c6f2df9ac7779afc168cb1a1850327e217b/docs/develop/theory/AURIC_STATIC_QUANTUM_HISTORIES_ENDOGENOUS_OBSERVERS_AND_RELATIONAL_CLOCKS_V21.md)，v21。
v30 的共同态、静态历史和记录基线以此为前置。

<a id="ref-galley"></a>

**[6]** 
T. D. Galley and L. Masanes,
Classification of all alternatives to the Born rule in terms of informational properties,
*Quantum* **1**, 15 (2017).
[arXiv:1610.04859v3](https://arxiv.org/abs/1610.04859v3)。
项目源指定的表示论前置；本稿不将其有限维操作假设补入未知响应合同。

<a id="ref-masanes"></a>

**[7]** 
L. Masanes, T. D. Galley and M. P. Müller,
The measurement postulates of quantum mechanics are operationally redundant,
*Nature Communications* **10**, 1361 (2019).
[arXiv:1811.11060v2](https://arxiv.org/abs/1811.11060v2)。
项目源指定的不可约分解参考；其完整重构公理未被自动移用。

<a id="ref-braunstein"></a>

**[8]** 
S. L. Braunstein and C. M. Caves,
Statistical Distance and the Geometry of Quantum States,
*Physical Review Letters* **72**, 3439 (1994).
[doi:10.1103/PhysRevLett.72.3439](https://doi.org/10.1103/PhysRevLett.72.3439)；
[作者全文](https://www-users.york.ac.uk/~sb54/papers/bc94.pdf)。
本稿独立证明使用的纯态 Fisher 上界及其一参数局部达到。

<a id="ref-gillmassar"></a>

**[9]** 
R. D. Gill and S. Massar,
State estimation for large ensembles,
*Physical Review A* **61**, 042312 (2000).
[arXiv:quant-ph/9902063](https://arxiv.org/abs/quant-ph/9902063)；
[doi:10.1103/PhysRevA.61.042312](https://doi.org/10.1103/PhysRevA.61.042312)。
本稿给出基本 qubit 点态信息权衡的直接证明，未移用全部渐近估计结论。

<a id="ref-anandan"></a>

**[10]** 
J. Anandan and Y. Aharonov,
Geometry of Quantum Evolution,
*Physical Review Letters* **65**, 1697--1700 (1990).
[doi:10.1103/PhysRevLett.65.1697](https://doi.org/10.1103/PhysRevLett.65.1697)；
[作者全文](https://www.tau.ac.il/~yakir/yahp/yh64)。
射影路径长度与生成元方差的经典来源；钟的物理标定仍为明确输入。
