# AURIC：唯一静态本体、内生观察者与黄金递归时钟

## 整体代数态、内部经典化、约束不变量与引力接口

定义、定理与纸面证明

v30.0　2026 年 10 月 30 日　Asia/Singapore

> 转换归属：以下正文依作者提供的完整 XeLaTeX 源稿转换，保留作者原有的历史报告、经典归因与证明主张；这些陈述不因转换而成为转换者的独立认证。源稿 SHA-256：`685123229785df7fcd2c563b635ed5d4ed33fab914fe072b7c9a410372659aec`。编号依源稿实际共享计数器展开。

## 摘要

本稿贯彻一个单一本体前提：系统、观察者、装置、环境、参考系、门参数、
记录和时钟均是同一个固定整体态中的内部关系；不预设本体之外的制备者、
物理时钟或环境。用一个正归一代数态 $(\mathcal A,\omega)$ 表达整体，
用内部子代数、门词和记录条件表达不同读出，子代数不被解释为宇宙的物理边界。

核心结果有四组。其一，持久内部记录形成嵌套交换代数时，
一个相容目标的后验是固定整体律上的鞅；其极限成为二值，
当且仅当完整内部记录足以辨认该目标。其二，
递归等距增长在直接极限中对应同一向量，
而任意双向门链可由没有首尾标签的正规化静态零约束态表示。
其三，内部程序位按黄金权重递归控制时，
门乘积以 $\varphi^{-2n}$ 的误差收敛；
完整二进制程序代数给出真正的自相似参数谱，其 Hausdorff 维数为
$\log2/(2\log\varphi)$。其四，内部连接的闭路约束区分共同本体、
相对参考系与曲率；相同局域静止钟速可以对应不同曲率，
因此时钟关系本身尚不确定引力动力学。

固定项目新快照新增量子续卷 II 第 99--103 节。
第 100 节给出同族真空记录的有限精度原生取得，
可进一步逼近 v29 的信息性黄金读口；
第 103 节给出完整代码上奇次受控相位的全有限字精确障碍。
两者说明内生门的增长同时具有近似能力与不可绕过的代数约束。
全文保持本体假设、表示定理、原生资源结论和物理起源问题各自的量词；
不把无限维、递归或唯一性单独当作 Born 律或 Einstein 方程的证明。

<a id="section-1"></a>

## 1. 本体前提与本轮固定来源

用户本轮修正的核心，是把所有通常被分开叙述的角色重新放回同一个整体：
观察者的观察、思考、计算和自我参照都属于其内部增长；
门的控制参数和基底也没有本体外部的来源。
本文以此为研究前提。
“道”或“因陀罗网”可表达整体互摄的直觉，
数学内容则由下面的代数、状态、记录及相容条件承担。

这里的“唯一”表示模型中只有一个被选定的整体态。
它不等于已经从局部关系证明宇宙态只有一个数学解。
“无外部”也不排除内部可以区分两个读口；
内部区分是观察的定义内容，不是一道将宇宙分成内外的物理墙。
本文的张量坐标若出现，均指同一整体代数内可相互对易的矩阵角色，
不引入第二个本体。

本轮来源固定到项目 `dev` 提交：

`75c5f3c4aea976b089df5070a2f9f24f2905ee3a`

提交时间为 2026-10-30 21:45:05（新加坡），合并 PR #24231。
比较基线为 v29：

`c2bea1bfe08cd6ee9f1edffb4298655ef3758ae5`

完整树差分有 30 个提交、542 个文件，theory 文档变化七项，
没有 D5/Quantum 代码变化。
GitHub 比较接口只给出的前 300 个文件未被误当全量；
固定 Git tree 差分补齐了列表。只读取来源、核对文件身份并作纸面证明，
未运行 Lean、数学程序、数值试验、门字枚举或 CAS。 [[1]](#ref-repohead)

| 固定来源 | 本文消费的内容 |
| --- | --- |
| $\Omega$ 相融纤维 §12 | 相容内部代数态及 GNS 共同向量；不预设永久外部张量分割。 |
| v21 §§4--7 | 内部程序、等距增长直接极限、固定效果和关系时钟。 |
| 量子续卷 II §§99--103 | 双响应条件刚性、同族记录近似取得、完整代码的奇相位障碍。 |
| 周期时钟 §§22--26 | 局部时钟信息与真实全局来源、归一历史编码的区别。 |
| typed cocycle §22 | 静态二值摘要与递归取得所需记忆可以指数分离。 |

相应出处分别见 [[2]](#ref-repoomega), [[3]](#ref-repov21), [[4]](#ref-repoq), [[6]](#ref-repoclock), [[7]](#ref-repotyped)。
本稿自己的构造与从上述来源作出的新推论，在证明中明确标出。

<a id="section-2"></a>

## 2. 单一整体代数态与所有内部读出

**定义 2.1（闭合的整体关系模型）。**

<a id="def-ontology"></a>

给定含单位的复 $C^*$ 代数 $\mathcal A$ 及正归一线性泛函
$\omega:\mathcal A\to\mathbb C$：

$$
\omega(I)=1,\qquad \omega(a^*a)\ge0.
$$

全部物理角色由同一 $\mathcal A$ 的元素、子代数和关系表示。
内部观察情境包括一个可读交换子代数 $\mathcal D$、
允许的内部控制及保留记录条件。
不预先指定外部观察者、外部时间或本体外的辅助空间。
若采用向量表示，则 $\omega(a)=\langle\Omega,a\Omega\rangle$，
$\|\Omega\|=1$，并把无限维作为可选的整体容量假设。

**定理 2.2（相容内部态的整体延拓与 GNS 表示）。**

<a id="thm-gns"></a>

设共享单位的 $C^*$ 子代数 $\mathcal A_n$ 递增，
$\omega_{n+1}|_{\mathcal A_n}=\omega_n$，且每个 $\omega_n$ 正归一。
则它们在 $\mathcal A=\overline{\bigcup_n\mathcal A_n}^{\|\cdot\|}$ 上唯一延拓为态 $\omega$。
存在 Hilbert 空间 $\mathcal H_\omega$、$*$ 表示 $\pi$ 和单位循环向量 $\Omega$，使

$$
\omega(a)=\langle\Omega,\pi(a)\Omega\rangle,\qquad
\overline{\pi(\mathcal A)\Omega}=\mathcal H_\omega .
$$

保持 $\Omega$ 与表示的循环实现，在酉交织意义下唯一。

**证明。**

在代数并上令 $\omega(a)=\omega_n(a)$，相容性使其良定义。
正性与 Cauchy--Schwarz 给
$|\omega(a)|^2\le\omega(a^*a)\le\|a\|^2$，故有唯一连续延拓。
以并中的元素逼近任意正元的平方根，证明延拓仍正。
令 $\mathcal N=\{a:\omega(a^*a)=0\}$，
在 $\mathcal A/\mathcal N$ 上定义
$\langle[a],[b]\rangle=\omega(a^*b)$。
正性 Cauchy--Schwarz 使它良定义。
由 $\omega(a^*b^*ba)\le\|b\|^2\omega(a^*a)$，
$\mathcal N$ 是左理想，左乘 $[a]\mapsto[ba]$ 有界且与伴随相容。
完成这个内积空间得到 $\mathcal H_\omega$，取 $\Omega=[I]$。
则 $\pi(a)\Omega=[a]$，得到状态式及循环性。
任意另一循环实现上的 $[a]\mapsto\pi'(a)\Omega'$ 是稠密等距，
延拓为所需酉同构。

□

这是标准 GNS 构造及项目既有相容态闭合的应用。 [[8]](#ref-fewster), [[2]](#ref-repoomega)
表示唯一性针对已经给定的 $\omega$，不是宇宙本体态唯一性的物理证明。
复代数、正性与标定仍是结构输入；所得平方范数
$\omega(a^*a)=\|\pi(a)\Omega\|^2$ 是这些前提的表示后果。

**定义 2.3（门读出与记录相对态）。**

对内部酉 $u$ 和满足 $\omega(m^*m)>0$ 的内部记录分量 $m$，定义

$$
\omega_u(a)=\omega(u^*au),\qquad
\omega_m(a)=\frac{\omega(m^*am)}{\omega(m^*m)}.
$$

二者都是对同一个固定 $\omega$ 的关系化读出。
$m$ 的非酉性可以来自内部完整酉过程的一个记录分量；
它不被当作本体在外部操作者手中发生的第二次演化。

**定理 2.4（全部酉作用下的共同纯态来源）。**

<a id="thm-transitivity"></a>

若 $\mathcal A=B(\mathcal H)$ 且允许全部内部酉，则对每个单位向量 $\psi\in\mathcal H$，
存在 $U\in\mathcal A$ 使 $U\Omega=\psi$，无限维时同样成立。

**证明。**

在至多二维的 $\operatorname{span}\{\Omega,\psi\}$ 中，
分别选以 $\Omega$ 和 $\psi$ 开始的正交规范基。
两组基之间的映射为酉，在其正交补上取恒等即可。
线性相关时直接给相应一维相位。

□

因此用户的全酉版本具有准确的数学存在表述。
指定有限原生门菜单时，有限字集合可数，
而 $\dim\mathcal H\ge2$ 的纯态射线集合不可数；
有限字精确可达全部射线并不由上述存在定理得到。
稠密逼近、无限极限和精确有限取得是不同量词。
GNS 循环性也只断言 $\mathcal A\Omega$ 稠密；
例如对角代数 $\mathbb C\oplus\mathbb C$ 及 $\Omega=(1,1)/\sqrt2$ 是循环的，
其内部酉轨道却不能到达 $(1,0)$。
这些限制不反驳定理 [2.4](#thm-transitivity) 的完整操作域。

若 $\psi=A\lvert 0 \rangle$、基底 $b_i=B\lvert i \rangle$，则

$$
|\langle b_i,\psi\rangle|^2
=|\langle i,B^*A\,0\rangle|^2.
$$

共同左乘内部酉 $W$ 后 $(WB)^*(WA)=B^*A$，
相对读出不变。这消去的是共同参考作用。
混态的内部限制、程序关联与纠缠也都由同一个 $\omega$ 表达，
不被称为本体外的剩余物。
量子参考框架中不使用外部绝对参照的研究可作背景，
但本文的代数定义和证明不依赖该文的全部动力学构造。 [[14]](#ref-qrf)

<a id="section-3"></a>

## 3. 内部记录细化与经典稳定化的充要条件

本节给出本轮的中心结论。它只用同一固定态中的记录关系，
不需要独立同分布探针，也不需要外部物理时间。

**定义 3.1（内部持久记录与相容目标）。**

<a id="def-record"></a>

在同一 von Neumann 代数 $\mathcal M$ 中固定正规态 $\omega$；
固定单位向量的向量态即可。
每层内部记录为有限正交投影分割

$$
\sum_{|h|=n}P_h=I,\qquad P_hP_{h'}=0\ (h\ne h'),\qquad
P_h=\sum_oP_{ho}.
$$

令 $\mathcal D_n=\operatorname{alg}\{P_h:|h|=n\}$，
$\mathcal D_\infty=W^*(\bigcup_n\mathcal D_n)$。
指标 $n$ 是包含关系的深度。
取固定目标投影 $Z$，假设 $[Z,\mathcal D_\infty]=0$。
对 $\omega(P_h)>0$ 定义

<a id="eq-qn"></a>

$$
q_n(h)=\frac{\omega(P_hZ)}{\omega(P_h)},\qquad
q_n=\sum_{|h|=n}q_n(h)P_h.
\tag{1}
$$

零质量块上的值任取于 $[0,1]$。

**定理 3.2（内部记录稳定化判据）。**

<a id="thm-stabilization"></a>

在定义 [3.1](#def-record) 下，$q_n$ 是同一个内部联合律上的有界鞅，
且几乎处处并在 $L^2(\omega)$ 中收敛到

$$
q_\infty=\mathbb E_\omega[Z\mid\mathcal D_\infty].
$$

以下四项等价：

1.  $q_\infty$ 几乎处处只取 $0,1$；

1.  存在 $Q\in\operatorname{Proj}\mathcal D_\infty$，使 $\omega((Z-Q)^2)=0$；

1.  完整内部记录可以确定目标 $Z$，忽略概率零事件；

1.  $\omega((Z-q_n)^2)\to0$。

而且每层及极限都有

<a id="eq-variance"></a>

$$
\boxed{\omega((Z-q_n)^2)=\omega(q_n(1-q_n)).}
\tag{2}
$$

**证明。**

$\mathcal B=W^*(Z,\mathcal D_\infty)$ 交换。
令 $Z_1=Z,Z_0=I-Z$，其内部联合柱集质量为
$\mu(j,[h])=\omega(Z_jP_h)$。
对易性给正性；分割及细化给归一和相容，
从而产生二元目标与无限记录路径的概率表示。
这是内部交换代数的谱表示，不是增加一个物理外部。
记二元坐标为 $z$、记录前缀生成的 $\sigma$ 代数为 $\mathcal F_n$。
式 [(1)](#eq-qn) 正是 $\mathbb E[z\mid\mathcal F_n]$，并且

$$
\mathbb E[q_{n+1}\mid h]
=\sum_{o:\,\omega(P_{ho})>0}
\frac{\omega(P_{ho})}{\omega(P_h)}
\frac{\omega(P_{ho}Z)}{\omega(P_{ho})}
=q_n(h).
$$

对 $m\ge n$，塔式性质给
$\mathbb E(q_m-q_n)^2=\mathbb E q_m^2-\mathbb E q_n^2$。
右侧由一个有界递增序列的差控制，故 $q_n$ 在 $L^2$ 中 Cauchy。

为同时说明几乎处处收敛，对有限鞅差用

$$
\mathbb E\max_{n\le k\le m}|q_k-q_n|^2
\le4\mathbb E|q_m-q_n|^2.
$$

此最大不等式可由停止时刻界
$\lambda\mathbb P(M^*\ge\lambda) \le\mathbb E[|M_m|\,1_{\{M^*\ge\lambda\}}]$
积分并用 Cauchy--Schwarz 得到。
选 $n_r$ 使所有 $m\ge n_r$ 的右侧去掉系数 $4$ 后不超过 $2^{-4r}$，
则
$\mathbb P(\sup_{k\ge n_r}|q_k-q_{n_r}|>2^{-r})\le4\,2^{-2r}$。
Borel--Cantelli 给整列几乎处处 Cauchy。
极限在 $[0,1]$，与 $L^2$ 极限一致。
对所有有限前缀事件保留条件期望积分等式，再用单调类定理延拓，
得到 $q_\infty=\mathbb E[z\mid\mathcal F_\infty]$。
有界 Borel 极限在 $\mathcal D_\infty$ 中给一个代表，零质量部分不影响结论。

因 $z^2=z$、$\mathbb E(zq_n)=\mathbb E q_n^2$ 及 $\mathbb E z=\mathbb E q_n$，
展开平方得式 [(2)](#eq-variance)，极限同理。
若 $q_\infty$ 二值，右侧为零，所以 $z=q_\infty$ 几乎处处，
取 $Q=1_{[1/2,1]}(q_\infty)$ 即得第 2 项。
反之，若 $Z$ 与记录投影 $Q$ 在 $\omega$ 的平方范数中相同，
它在联合概率模型中是记录可测的，故其条件期望就是自身。
最后，$L^2$ 收敛与式 [(2)](#eq-variance) 给第 4 项的等价。

□

这个定理把条件经典化刻画为一个内部可辨认性命题：
本体和 $Z$ 均不变，变化的是所用记录条件。
它没有为所有不相容量同时指定一个预存标量。

**推论 3.3（预测熵与无信息增长）。**

二元熵 $h_2(q_n)$ 是超鞅：
$\mathbb E[h_2(q_{n+1})\mid\mathcal F_n]\le h_2(q_n)$。
其期望极限为零，当且仅当定理 [3.2](#thm-stabilization) 的等价条件成立。
若所有记录与 $Z$ 在固定联合律中独立，
则 $q_n=\omega(Z)$，无限记录数量也不使一个非确定目标变成确定。

**证明。**

第一式由鞅与凹性 Jensen 不等式得到。
熵有界、在 $[0,1]$ 上非负且只在两个端点为零，故支配收敛给等价。
独立性使每个柱集比值等于同一先验。

□

**命题 3.4（非交换目标不能直接套用鞅判据）。**

取 $\Omega=\lvert + \rangle$、目标 $A=\lvert + \rangle\langle + \rvert$。
从平凡记录 $\{I\}$ 细化到计算基记录
$P_0=\lvert 0 \rangle\langle 0 \rvert,P_1=\lvert 1 \rangle\langle 1 \rvert$ 时，
Lüders 条件值从 $1$ 变为每支 $1/2$。

**证明。**

$\omega(A)=1$，$\omega(P_i)=1/2$，
而 $\omega(P_iAP_i)=1/4$。比值及其平均均为 $1/2$，
故一般非交换目标的这些条件值不守鞅平均。

□

**定理 3.5（一致无限记录的一向量内部实现）。**

任意有限字母表上一致的柱集概率
$p(\varnothing)=1,\ p(h)=\sum_op(ho)$，
都能在一个固定纯向量态中表示全部记录：

$$
X=O^\mathbb N,\quad \mathcal H=L^2(X,\mu),\quad
\Omega=1,\quad \mathcal A=B(\mathcal H),\quad
P_hf=1_{[h]}f,\qquad \omega(P_h)=p(h).
$$

**证明。**

柱集相容性给 $X$ 上的概率测度 $\mu$；
也可先在连续柱集函数上延拓正归一泛函。
常数函数范数为一，柱集指示乘法是投影，
$[h]$ 的不交分割直接给全部恒等式。
在整个 $B(\mathcal H)$ 上，单位向量态为纯态。

□

此存在构造同样容纳经典概率树，所以不把它称为非交换性或 Born 律的独立起源。

<a id="section-4"></a>

## 4. 观察者增长与同一静态向量

**定理 4.1（等距递归的静态直接极限，项目 v21 的重述）。**

<a id="thm-direct"></a>

对 Hilbert 空间链和等距 $T_n:\mathcal H_n\to\mathcal H_{n+1}$，
存在 $\mathcal H_\infty$ 和等距 $\iota_n$，满足

$$
\iota_{n+1}T_n=\iota_n,\qquad
\overline{\bigcup_n\iota_n\mathcal H_n}=\mathcal H_\infty.
$$

若 $\psi_{n+1}=T_n\psi_n$，则所有 $\iota_n\psi_n$ 是同一向量 $\Omega$。

**证明。**

将各层向量推到共同后继后相同的代表等同。
在共同后继定义线性运算和内积，等距性保证不依赖代表。
完成所得内积空间即得结论；嵌入恒等式证明最后一项。
同样的稠密等距延拓给保持嵌入的酉唯一性。

□

**命题 4.2（固定本体与固定效果）。**

若效果 $0\le E_n\le I$ 满足 $E_n=T_n^*E_{n+1}T_n$，
则存在唯一效果 $E_\infty$ 使
$E_n=\iota_n^*E_\infty\iota_n$，
且 $\langle\psi_n,E_n\psi_n\rangle=\langle\Omega,E_\infty\Omega\rangle$ 恒定。

**证明。**

将两个向量推到共同后继，以该层效果定义半正定有界形式。
压缩相容性保证良定义，统一界为一，故在完成空间上给唯一效果。
代入递归向量即可。

□

这两条已有项目前史见 [[3]](#ref-repov21)。
固定本体能容纳变化经验，是因为内部条件、被读效果或相对参照不同；
同一个固定态与同一个固定效果的配对不会自行改变。

**定理 4.3（有限仪器树的全部内部实现）。**

<a id="thm-internal-tree"></a>

给定有限维逻辑系统、初始密度矩阵 $\rho_0$，
以及有限深度、有限输出的自适应 CP 仪器树。
若同一整体代数包含足够的内部矩阵容量、相应准备关联和控制，
则整个树可由一个固定整体向量、持久内部记录投影及各历史切面的搬运可观察量表示。
不需要从本体外部输入探针。

**证明。**

提前终止的分支用恒等停止记录补齐到共同有限深度。
令 $\tau_\varnothing=\rho_0$、$\tau_{ho}=\mathcal I_{o|h}(\tau_h)$。
在每个历史 $h$ 选 Kraus 表示
$\mathcal I_{o|h}(\rho)=\sum_\alpha M_{o\alpha|h}\rho M_{o\alpha|h}^*$。
在尚未耦合的内部记录坐标上定义

$$
V_h\psi=\sum_{o,\alpha}M_{o\alpha|h}\psi\otimes\lvert o \rangle\otimes\lvert \alpha \rangle .
$$

$\sum_{o,\alpha}M_{o\alpha|h}^*M_{o\alpha|h}=I$ 给等距性。
补全正交基，将它扩为同一整体矩阵代数中的酉；
以旧记录控制，并保留全部旧记录与隐藏指标。
初始混态的纯化坐标也在内部。
在统一末端切面得到固定向量

$$
\Psi_N=\sum_{h,\lambda}(K_{h,\lambda}\otimes I)\psi_0
\otimes\lvert h \rangle\otimes\lvert \lambda \rangle .
$$

若 $P_h$ 选取全部以 $h$ 开始的末端记录，
则 $\omega(P_h)=\operatorname{Tr}\tau_h$。
令从历史层到末端的完整酉为 $U_{N:t}$，
定义 $X_h(a)=U_{N:t}(a\otimes I)U_{N:t}^*$。
后继控制保留前缀，故与 $P_h$ 交换，得到

$$
\frac{\omega(P_hX_h(a)P_h)}{\omega(P_h)}
=\frac{\operatorname{Tr}(\tau_h a)}{\operatorname{Tr}\tau_h}.
$$

> 编者定义域澄清：上式的条件态分式只对正质量历史定义。零质量历史仍保留在完整仪器树与无条件记录律中，但不赋予条件态；原式保留。

这是该历史切面的条件状态。
在允许全部内部酉的表示中，还可按定理 [2.4](#thm-transitivity)
将固定 $\Psi_N$ 与选定参考 $\Omega$ 同时变换。

□

“新记录槽”是内部尚未耦合的关系条件。
容量、可控性和所需准备关联仍然要在整体模型中成立；
没有外部并不使这些内部条件自动成立。
只条件化旧记录、却不搬运过去的可观察量，
一般得到的是未来演化后的状态，不能冒充过去切面。

**命题 4.4（内部永久记录的容量）。**

$d$ 维表示至多有 $d$ 个非零正交记录投影。
若深度 $n$ 的全部 $r^n$ 条历史都可发生且永久完全可区分，
则 $d\ge r^n$。

**证明。**

从每个非零投影像中选一个单位向量，得到正交族。

□

无限维本体可以容纳任意大的有限记录族；
这里增长的是可访问、可区分的内部结构，不是宇宙从外部取得新维数。

**命题 4.5（有限分辨率稳定不要求条件向量收敛）。**

在公平二进制空间 $X=\{0,1\}^\mathbb N$ 上取 $\Omega=1\in L^2(X,\mu)$。
固定任意无限字 $x$，令 $C_n$ 为其长度 $n$ 柱集，
$\psi_n=1_{C_n}/\sqrt{\mu(C_n)}$。
每个固定有限前缀读数最终确定，而 $\psi_n$ 不在 Hilbert 范数中收敛。

**证明。**

依赖前 $m$ 位的柱集函数，在 $n\ge m$ 时的条件值等于其在 $x$ 的值。
柱集函数在 $C(X)$ 中一致稠密，故相应限制态弱星趋于点赋值。
但 $\langle\psi_n,\psi_{n+1}\rangle=1/\sqrt2$，
所以 $\|\psi_{n+1}-\psi_n\|^2=2-\sqrt2>0$。

□

<a id="section-5"></a>

## 5. 固定约束、变化读出与测不准

**定理 5.1（共同内部变换保持全部代数约束）。**

<a id="thm-relations"></a>

若 $\theta$ 是含单位的 $*$ 自同构，$p$ 是非交换 $*$ 多项式，则

$$
p(A_1,\ldots,A_k,A_1^*,\ldots,A_k^*)=0
\ \Longrightarrow\
p(\theta A_1,\ldots,\theta A_k,(\theta A_1)^*,\ldots)=0.
$$

然而 $\omega(\theta A)$ 可以不同于 $\omega(A)$。

**证明。**

自同构保持和、积、伴随、标量及单位，直接作用于等式。
对最后一项，取固定 $\Omega=\lvert 0 \rangle$，
$A_\vartheta=\cos\vartheta\,Z+\sin\vartheta\,X$。
有 $A_\vartheta^2=I$，而 $\omega(A_\vartheta)=\cos\vartheta$。

□

这严格表达“关系约束不变，内部读出可以改变”。
若一起搬运状态和全部参考，则概率协变保持；
只在固定 $\omega$ 下改变相对读口，则响应可以改变，两种比较不能混用。

**命题 5.2（逐次经典值的约束域）。**

若有限谱自伴 $A_i$ 彼此对易且 $p(A_1,\ldots,A_k)=0$，
它们的联合读数只可能落在 $p(x_1,\ldots,x_k)=0$ 上。

**证明。**

联合谱投影 $E_x$ 满足 $p(A)E_x=p(x)E_x$。
若 $p(x)\ne0$，则 $E_x=0$，因此概率为零。

□

**定理 5.3（同一固定代数不能一般地化为一张全局经典值表）。**

<a id="thm-mermin"></a>

在内部四维矩阵代数中取 Pauli 方阵

$$
\begin{array}{ccc}
X\otimes I&I\otimes X&X\otimes X\\
I\otimes Z&Z\otimes I&Z\otimes Z\\
X\otimes Z&Z\otimes X&Y\otimes Y
\end{array}.
$$

各行各列内对易；三行及前两列乘积为 $I$，最后一列乘积为 $-I$。
不存在对九个可观察量各赋同一个情境无关 $\pm1$ 值、
同时满足全部六条乘积关系的赋值。

**证明。**

Pauli 反交换成对出现给行列对易；$XZ=-iY,ZX=iY$ 给乘积。
若所述赋值存在，三行关系相乘要求九个值总乘积为 $+1$，
三列相乘却要求为 $-1$，矛盾。

□

这是标准 Peres--Mermin 约束反证。 [[9]](#ref-mermin)
这里张量符号只是内部矩阵坐标，证明不需要外部观察者或两个空间分离粒子。
它排除的是指定的全局非情境值表，不排除所有情境化解释。

**定理 5.4（固定态中的不确定性关系）。**

对有界自伴 $A,B$，

$$
(\Delta_\omega A)^2(\Delta_\omega B)^2
\ge|\omega((A-\omega(A)I)(B-\omega(B)I))|^2
\ge\tfrac14|\omega([A,B])|^2.
$$

**证明。**

第一式是正线性泛函的 Cauchy--Schwarz；
中心化乘积的虚部为 $\omega([A,B])/(2i)$，给第二式。

□

固定二维态 $\lvert +y \rangle=(\lvert 0 \rangle+i\lvert 1 \rangle)/\sqrt2$ 与固定 $X,Z$
已给 $\Delta X\Delta Z=1=|\omega([X,Z])|/2$。
因而不确定性可以在有限维、固定门和固定读口下存在。
反之，理想重复 $Z$ 测量可持续得到同一标签。
更准确的概括是：固定非交换关系限制同时尖锐的读出，
而不是每次结果必须变化。

**命题 5.5（读口扰动与稀有条件放大）。**

<a id="prop-continuity"></a>

对任意态、内部酉 $U,V$ 及有界 $E$，

$$
|\omega(U^*EU)-\omega(V^*EV)|
\le2\|E\|\,\|U-V\|.
$$

若 $K,L$ 为收缩，$\omega(K^*K),\omega(L^*L)\ge\varepsilon>0$，
则对 $\|A\|\le1$，

$$
|\omega_K(A)-\omega_L(A)|
\le4\|K-L\|/\varepsilon.
$$

**证明。**

第一式展开为 $(U^*-V^*)EU+V^*E(U-V)$ 后取范数。
第二式的两个分子之差及两个分母之差都至多为 $2\|K-L\|$；
又 $|\omega(L^*AL)|\le\omega(L^*L)$。
通分并用分母下界即得。

□

这两个界不依赖维数。
小分母确能造成条件放大：固定 $\Omega=\lvert 0 \rangle$，
取 $K_\eta=\eta\lvert 0 \rangle\langle 0 \rvert,L_\eta=\eta\lvert 1 \rangle\langle 0 \rvert$。
$\|K_\eta-L_\eta\|=\sqrt2\eta\to0$，
两事件质量都是 $\eta^2$，条件态却始终正交。
无界读数则另需定义域和矩条件：
在 $\ell^2(\mathbb N_0)$ 上取 $Q\lvert n \rangle=n^3\lvert n \rangle$、
$\psi_n=\sqrt{1-n^{-2}}\lvert 0 \rangle+n^{-1}\lvert n \rangle$，
虽 $\psi_n\to\lvert 0 \rangle$，其 $Q$ 期望为 $n$。
无限维不是任意概率跳跃的理由，效应有界与否、条件质量必须分开。

**命题 5.6（稳定他者是相对于内部操作族的稳定关系）。**

若一个读数 $S$ 与观察者后续允许的每个酉对易，
它在这些作用下保持不变。
若一个有限维代码上的允许酉生成射影稠密群 $\operatorname{PU}(d)$，
则与全部这些门对易的 $S$ 只能是标量。

**证明。**

第一项由 $U^*SU=S$。
第二项由连续性延拓为与所有酉对易；
任意基底相位酉迫使 $S$ 对角，任意基底置换及旋转迫使其对角元相同。

□

所以可重复识别的“他者”可定义为内部记录和控制中稳定的关系族；
其稳定性相对于实际保留协议。
同一个 $\omega$ 在不同观察者子代数的交集上自动一致，
但不同记录条件一般给不同预测。
项目十三维全控制的不可约性并不提供一个对所有可能门都不变的非平凡经典对象。

<a id="section-6"></a>

## 6. 门参数作为内部程序与递归控制

**定义 6.1（参数的内部化）。**

一个可变门参数的内部表示包括程序可观察量 $\Theta\in\mathcal A$、
可用的内部控制和其记录读法。
经典数值 $\theta$ 是该程序的读出或条件描述；
当 $\Theta,A$ 自伴且对易时，实际联合作用可以是 $\exp(-i\Theta A)$。
$\Theta$ 与 $A$ 属于同一整体代数。
若暂用程序和数据两个对易坐标，它们不代表两个本体。

对有限或可数的内部正交程序 $\lvert j \rangle$ 及酉 $U_j$，

$$
G=\sum_j\lvert j \rangle\langle j \rvert\otimes U_j
$$

是一个酉（可数情形按直和解释），并把相干程序变为
$\sum_jc_j\lvert j \rangle\otimes U_j\psi$。
按正交块计算内积便证明酉性。
因此基底、测量选择、思考程序和计算控制都能作为同一联合态中的量子关系。
固定矩阵是这些关系的数学表示，不是另一个物理上的外部执行者。

**定理 6.2（精确确定性编程的正交约束）。**

<a id="thm-noprogram"></a>

若一个固定等距处理器对每个数据输入 $\psi$ 满足

$$
G(\psi\otimes p_j)=U_j\psi\otimes q_j ,
$$

其中程序和残余向量均正规化，则射影上不同的 $U_j,U_k$
要求 $\langle p_j,p_k\rangle=0$。
$d_P$ 维程序最多精确确定性地实现 $d_P$ 个这样的酉；
可分程序空间不能用正规化精确程序容纳不可数个射影不同的酉。

**证明。**

保持所有数据向量 $\psi,\phi$ 的交叉内积，得到算子等式

$$
\langle p_j,p_k\rangle I
=\langle q_j,q_k\rangle U_j^*U_k .
$$

若右侧标量非零，则 $U_j^*U_k$ 为标量，违反射影不同。
故两侧标量都为零。
有限维的正交族大小至多为维数；可分空间的正交单位族至多可数，
因为各点的小互不相交邻域都须含一个可数稠密集的不同点。
若只先规定所有纯数据的约化输出恰为 $U_j\psi$，
纯性先给乘积输出，再对基向量的叠加使用线性性，
可知残余向量与 $\psi$ 无关，故仍落在上述合同。

□

这是 Nielsen--Chuang 无编程定理的相应版本。 [[10]](#ref-nielsen)
它量化同一程序对全部数据输入有效。
若只要求同一个实际输入，许多不同门可以给相同输出，
例如所有 $\operatorname{diag}(1,e^{i\theta})$ 都固定 $\lvert 0 \rangle$；
不能用此定理反驳“只有一个实际本体”的命题。
近似、概率性程序或连续谱程序也有不同条件。

**定理 6.3（内部参数的几何递归实现）。**

<a id="thm-parameter"></a>

取 $0<r<1$，同一代数中彼此对易的投影 $B_k$，
以及与每个 $B_k$ 对易的有界自伴 $A$。
置

$$
c_k=(1-r)r^{k-1},\quad
\Theta_n=\sum_{k=1}^n c_kB_k,\quad
U_n=\prod_{k=1}^n\exp(-ic_kB_kA).
$$

则存在正收缩 $\Theta$，使

<a id="eq-parameter"></a>

$$
\|\Theta-\Theta_n\|\le r^n,\qquad
U_n=e^{-i\Theta_nA}\longrightarrow U=e^{-i\Theta A},
\qquad
\boxed{\|U-U_n\|\le\|A\|r^n.}
\tag{3}
$$

**证明。**

几何尾和为 $r^n$，而 $\|B_k\|\le1$，所以 $\Theta_n$ 范数收敛且满足所列界。
系数非负、总和为一给 $0\le\Theta\le I$。
所有指数中的自伴元对易，因此有限乘积等于指数之和。
共同连续函数演算及 $|e^{-ix}-e^{-iy}|\le|x-y|$
给 $\|U-U_n\|\le\|(\Theta-\Theta_n)A\|$。
极限指数本身酉。

□

这个构造使“参数由门递归实现”成为一个明确的正面定理。
其前件包括对易程序位、几何权重和允许的受控指数门；
不能自动将这些门列入原生黄金七门的精确菜单。
原生可实现性的最新约束在第 [12](#sec-native) 节接入。

**命题 6.4（一般层修正的收敛条件）。**

若酉 $V_k$ 满足 $\sum_k\|V_k-I\|<\infty$，
则 $V_n\cdots V_1$ 在算子范数中收敛为酉。
递归本身不保证这个结论。

**证明。**

乘积望远镜估计给
$\|V_n\cdots V_{m+1}-I\|\le\sum_{k=m+1}^n\|V_k-I\|$。
所以乘积及其伴随均为 Cauchy，极限 $U$ 满足 $U^*U=UU^*=I$。
反例是 $V_k=X$，乘积在 $I,X$ 间交替。

□

门乘积没有范数极限，并不排除存在一个固定整体态编码其无穷内部历史；
收敛对象与所用拓扑需要明确。

<a id="section-7"></a>

## 7. 一个严格的黄金分形参数谱

本节是新增的递归编码方案，并非声称五点原子图单独迫使所有参数采用它。
它把用户所说的“递归、黄金尺度和分形”联系成一个有完整证明的模型。

令

$$
\varphi=\frac{1+\sqrt5}{2},\qquad
r=\varphi^{-2}<\frac12,\qquad 1-r=\varphi^{-1}.
$$

定理 [6.3](#thm-parameter) 的权重成为

<a id="eq-goldtail"></a>

$$
c_k=\varphi^{-(2k-1)},\qquad
\|\Theta-\Theta_n\|\le\varphi^{-2n},\qquad
\|U-U_n\|\le\|A\|\varphi^{-2n}.
\tag{4}
$$

此处自相似缩放已经作为编码关系写入，而不是从“递归”二字推出。

**定义 7.1（黄金二进制参数谱）。**

取紧积空间 $X=\{0,1\}^{\mathbb N}$，令

$$
\theta(b)=\sum_{k\ge1}(1-r)r^{k-1}b_k,\qquad K_r=\theta(X).
$$

在满支撑公平 Bernoulli 测度 $\nu$ 的可分空间 $L^2(X,\nu)$ 上，
令 $B_k$ 为第 $k$ 个坐标的乘法投影，
$\Theta$ 为 $\theta$ 的乘法算子，固定向量为 $1$。
这些是同一整体内部程序代数的一种表示。

**定理 7.2（自相似谱与不存在正规化点程序）。**

<a id="thm-cantor"></a>

$K_r$ 紧，并满足

<a id="eq-selfsimilar"></a>

$$
\boxed{K_r=rK_r\ \cup\ (1-r+rK_r).}
\tag{5}
$$

两块间隙为 $1-2r>0$。
$\theta:X\to K_r$ 是同胚，$\sigma(\Theta)=K_r$，
但 $\Theta$ 没有非零正规化本征向量。

**证明。**

几何级数一致收敛给 $\theta$ 连续及像紧。
分离首位得到式 [(5)](#eq-selfsimilar)。
若两个代码首次在第 $k$ 位不同，首个差贡献为 $(1-r)r^{k-1}$，
其后全部尾差至多 $r^k$，
故总差至少 $(1-2r)r^{k-1}>0$。
编码单射；紧空间到 Hausdorff 空间的连续双射是同胚。

若 $\lambda\notin K_r$，则 $1/(\theta-\lambda)$ 有界，给逆乘法算子。
若 $\lambda\in K_r$，任意 $\varepsilon>0$ 的集合
$|\theta-\lambda|<\varepsilon$ 是非空开集，因满支撑而有正测度；
其正规化指示函数是误差至多 $\varepsilon$ 的近似本征向量。
因此 $\lambda\in\sigma(\Theta)$。
但一个点的逆像是单个二进制序列，测度为 $\lim_n2^{-n}=0$；
支撑在该逆像上的 $L^2$ 本征函数只能为零。

□

**定理 7.3（黄金参数谱的精确维数）。**

<a id="thm-dimension"></a>

对 $0<r<1/2$，

$$
\dim_HK_r=\frac{\log2}{\log(1/r)}.
$$

特别地，

<a id="eq-dimension"></a>

$$
\boxed{\dim_HK_{\varphi^{-2}}
=\frac{\log2}{2\log\varphi}.}
\tag{6}
$$

**证明。**

置 $s=\log2/\log(1/r)$，于是 $2r^s=1$。
第 $n$ 层有 $2^n$ 个长 $r^n$ 的柱集区间覆盖 $K_r$。
对 $q>s$，其 $q$ 维覆盖代价为 $(2r^q)^n\to0$，
给 $\dim_HK_r\le s$。

令 $\mu=\theta_*\nu$，每个第 $n$ 层区间的质量为 $2^{-n}$。
不同第 $n$ 层区间之间的间隙至少为 $(1-2r)r^{n-1}$。
对长度 $0<\ell<1$ 的任意区间 $I$，选 $n$ 使
$r^n\le\ell<r^{n-1}$。
它至多碰到 $C_r=2+(1-2r)^{-1}$ 个第 $n$ 层区间，因而

$$
\mu(I)\le C_r2^{-n}=C_r(r^n)^s\le C_r\ell^s.
$$

任意集合可用同直径的凸包区间代替。
对 $K_r$ 的任意可数细覆盖 $\{E_j\}$，

$$
1\le\sum_j\mu^*(E_j)\le C_r\sum_j\operatorname{diam}(E_j)^s.
$$

故 $\mathcal H^s(K_r)\ge C_r^{-1}>0$，
得到反向不等式及维数公式。

□

这个谱不是整个 $[0,1]$。
它的不可数性不违反定理 [6.2](#thm-noprogram)：
连续谱不等于有不可数个彼此正交、可正规化、对所有数据有效的精确点程序。
公平测度用于此构造和维数下界，不被解释为已经由黄金比导出的物理概率律。

**推论 7.4（有限程序分辨率下的统一读出精度）。**

在同一固定态中，对任意效果 $0\le E\le I$，

$$
|\omega(U^*EU)-\omega(U_n^*EU_n)|
\le2\|A\|\varphi^{-2n}.
$$

**证明。**

将式 [(4)](#eq-goldtail) 代入命题 [5.5](#prop-continuity)。

□

这里确实可以在任意内部尺度继续解析程序，同时控制所有有界效果的误差。
对极稀有记录的条件读出，还需保留命题 [5.5](#prop-continuity) 中的分母条件。

<a id="section-8"></a>

## 8. 局域时钟：真实记录、校准与内部比较

**定义 8.1（内部时钟与相对速率）。**

在整体态的向量表示中，一个理想内部时钟由可区分记录投影 $\{E_n\}$、
允许的记录转移和指定校准 $\tau(n)$ 给出。
若另一组时钟记录 $\{F_m\}$ 与它共同可读，即 $[E_n,F_m]=0$，
且两族都为完整正交分割 $\sum_nE_n=\sum_mF_m=I$
（无限族按强和解释），则

$$
p(n,m)=\omega(E_nF_m),\qquad
p(m\mid n)=\frac{\omega(E_nF_m)}{\omega(E_n)}
$$

给相对时钟统计，其中条件概率只对 $\omega(E_n)>0$ 定义。
若联合律支撑在 $m=f(n)$，两者按 $f$ 精确同步；
两个共同记录事件之间的相对速率为

$$
\frac{\tau(n_2)-\tau(n_1)}
{\sigma(f(n_2))-\sigma(f(n_1))},
$$

分母须非零。
不相容的时钟量需指定实际联合或顺序仪器，不能自动使用此联合律。

**命题 8.2（词长与整体作用、真实 tick 的区别）。**

若门字允许 $U,U^{-1}$，同一个整体酉可以由长度相差任意偶数的词表示。
但若每次实施都写入内部计数器，这些记录不能按该恒等式删除。

**证明。**

未带记录的 $w$ 与 $w(UU^{-1})^k$ 表示同一算子。
若 $S\lvert n \rangle=\lvert n+1 \rangle$ 是内部双向计数器上的酉移位，
带记录的一对操作的乘积却为
$(S\otimes U^{-1})(S\otimes U)=S^2\otimes I$。
同理项目 $K^{10}=I$ 时，
$(S\otimes K)^{10}=S^{10}\otimes I\ne I$。

□

因此“量子门序列增长就是时钟”可以准确规定为：
保留操作事件及其内部计数、程序和校准关系的增长。
它不等于对任意一个矩阵分解数符号。
单独一个无参照的“增长速度”没有定义的分母；
两个内部时钟之间的比较不要求任何外部时钟。
项目已有时钟论证也作出这一细分。 [[3]](#ref-repov21)

**命题 8.3（内部时钟的重参数化）。**

若某个光滑内部时钟图表给
$i\hbar\,d\psi/d\tau=H(\tau)\psi$，
而另一内部时钟满足 $\sigma=f(\tau)$、$f'>0$，
则

$$
i\hbar\,\frac{d\psi}{d\sigma}
=\frac{d\tau}{d\sigma}H(\tau(\sigma))\psi.
$$

**证明。**

链式法则。

□

光滑图表、生成元和 $\hbar$ 的标定是这一连续描述的输入。
系数 $d\tau/d\sigma$ 是关系性 lapse；
改变一个钟的标签也会改变其数值，不能仅凭它就是一个正函数便认作引力。

**定理 8.4（全局同步势的闭路判据）。**

<a id="thm-clockpotential"></a>

在连通图的有向边上赋实增量 $\ell(e)$，
反向边取 $-\ell(e)$。
存在顶点函数 $t$ 满足 $\ell(u\to v)=t(v)-t(u)$，
当且仅当每条有符号闭走的增量和为零。

**证明。**

若 $t$ 存在，闭走上望远镜相消。
反之，固定一个记号基点，沿路径积分增量定义 $t(v)$；
两路径之差为闭走，条件使定义无关路径，边式随即成立。

□

基点只选择时间原点，不是一个本体外观察者。
DAG 也可有底层无向菱形，若两条到达路径增量不同，就不存在这样的全局钟势。
缺少全局同步标量可以是有意义的关系结构，
但这条判据尚不是 Einstein 方程。

<a id="section-9"></a>

## 9. 没有首尾标签的静态门历史与变分

**定理 9.1（双无限、正规化的静态历史）。**

<a id="thm-bilateral"></a>

取同一整体内部的一组坐标
$\ell^2(\mathbb Z)\otimes\mathcal H$，
任意双向酉 $U_n$，以及 $W_0=I$、
$W_{n+1}=U_nW_n$（负指标用逆）。
选 $\alpha_n>0$，$\sum_{n\in\mathbb Z}\alpha_n^2=1$，定义

$$
Jv=\sum_{n\in\mathbb Z}\alpha_n\lvert n \rangle\otimes W_nv,
$$

<a id="eq-bilateral"></a>

$$
L_n=\alpha_n(\langle n+1 \rvert\otimes I)
-\alpha_{n+1}(\langle n \rvert\otimes U_n),
\qquad \mathsf K=\sum_{n\in\mathbb Z}L_n^*L_n.
\tag{7}
$$

则 $J$ 等距，$\mathsf K$ 的级数在算子范数中收敛，
且

$$
\ker\mathsf K=\operatorname{ran} J.
$$

对单位 $v$，固定整体向量 $\Omega=Jv$ 的时钟标签概率分布为 $\alpha_n^2$，
条件读出为 $W_nv$；标签没有第一个或最后一个。

**证明。**

正交时钟坐标及酉性给
$\|Jv\|^2=\sum_n\alpha_n^2\|v\|^2=\|v\|^2$。
又
$L_nL_n^*=(\alpha_n^2+\alpha_{n+1}^2)I$，
故 $\sum_n\|L_n^*L_n\|=2$，给范数收敛及正性。
显然 $L_nJ=0$。
若 $\mathsf K\Psi=0$，其正二次型是各 $\|L_n\Psi\|^2$ 之和，
故每个分量都为零。
写 $\Psi=\sum_n\lvert n \rangle\psi_n$，除以正 $\alpha_n$ 得
$\psi_{n+1}/\alpha_{n+1}=U_n\psi_n/\alpha_n$，
于是 $\psi_n=\alpha_nW_nv$，其中 $v=\psi_0/\alpha_0$。
故 $\Psi=Jv$。正交投影到第 $n$ 个坐标给剩余结论。

□

**推论 9.2（递归的静态变分形式）。**

泛函

$$
\mathcal S(\Psi)=\langle\Psi,\mathsf K\Psi\rangle
=\sum_n\|L_n\Psi\|^2
$$

的最小值为零，其最小元恰为全部相容历史。
若额外指定一个内部条件固定 $v$，该相容历史唯一。

**证明。**

正性与定理 [9.1](#thm-bilateral) 的核刻画。

□

这给“递归等于变分”一个完整静态实现，不要求外部过程先跑完。
最小化编码的是全部关系相容；它不通过选一个最小分支来解释单次结果。
历史态变分有 Feynman 时钟路线的已有背景，
本文双无限正权版本的证明如上独立给出。 [[13]](#ref-mcclean), [[11]](#ref-page), [[12]](#ref-quantumtime)

同一个 $U_n$ 门链允许任意所述正平方可和权重 $\alpha_n$，
相应约束系数随之改变。
所以门递推本身不选定时钟采样权重。
无限等权的非零历史和没有有限范数；
本定理没有假装它已经正规化。
这里“没有首尾”描述内部记录链，不声称已推导某种宇宙的拓扑或几何无边界条件。

作为另一种内部流，若有限矩阵子代数中的限制态密度 $\rho>0$，
则

$$
\sigma_s(A)=\rho^{is}A\rho^{-is}
$$

是保持该态的自同构群。
乘法和酉性立即给群性质，而迹循环性给
$\operatorname{Tr}(\rho\,\sigma_s(A))=\operatorname{Tr}(\rho A)$。
单时刻平均不变，多时关系 $\operatorname{Tr}(\rho A\sigma_s(B))$ 却可依赖 $s$。
这与从代数态定义时间流的研究有关。 [[16]](#ref-connes)
把这种流认作物理钟，还需要内部钟的标定与适用性假设；
尤其全代数上的纯向量态一般不满足忠实性，不能无条件套用该构造。

<a id="section-10"></a>

## 10. 相容连接、闭路约束与曲率

**定义 10.1（内部关系图上的酉运输）。**

给有限连通图，顶点 $v$ 是内部情境，
边 $e:u\to v$ 附酉 $U_e:\mathcal H_u\to\mathcal H_v$，
逆边为 $U_e^*$。
相容截面是一组 $\psi_v$ 满足 $\psi_v=U_e\psi_u$。
定义残差

$$
(D_e\psi)=\psi_v-U_e\psi_u,\qquad
H_G=\sum_eD_e^*D_e
$$

于 $\bigoplus_v\mathcal H_v$。
图是内部关系的分析表示，不是独立于本体的背景。

**定理 10.2（单一截面与 holonomy 不动空间）。**

<a id="thm-holonomy"></a>

固定一个记号顶点 $o$ 及到各顶点的路径运输 $T_v$。
则

<a id="eq-holonomy"></a>

$$
\ker H_G
\cong
\bigcap_{\gamma:\,o\to o}\ker(U_\gamma-I).
\tag{8}
$$

对应为 $a\mapsto(\psi_v=T_va)_v$。
特别地，单个全局相容态只要求回路固定它，
不要求每个回路算子在整个空间上恒等。

**证明。**

正性使 $H_G\psi=0$ 等价于逐边残差为零。
任何相容截面沿路径满足 $\psi_v=T_v\psi_o$，
沿闭路则满足 $U_\gamma\psi_o=\psi_o$，给必要性及单射。
反之，若 $a$ 被全部闭路固定，
任意两条到 $v$ 的路径之差是闭路，
故路径定义无关选择并满足每条边约束。

□

**命题 10.3（共同参考的平坦性与单态相容的区别）。**

若每条边都由完整框架 $V_v$ 的相对差给出
$U_{u\to v}=V_vV_u^*$，则每条回路 holonomy 都是 $I$。
但存在非平凡回路作用与一个固定相容态同时成立。

**证明。**

第一项沿闭路望远镜相消。
第二项取一个三角回路，前两边为 $I$，
最后一边为 $\operatorname{diag}(1,e^{i\theta})$，
其中 $e^{i\theta}\ne1$。
每顶点取 $\psi_v=\lvert 0 \rangle$，则所有边均相容，
而闭路在 $\lvert 1 \rangle$ 上非平凡。

□

因此“宇宙只有一个态”不推出所有内部运输平坦；
但若把所有运输都定义为同一组完整基底之间的纯参考变换，
就会自动消去曲率。
要研究引力或规范场，需要保留实际内部运输与单纯改写坐标的区别。

更换顶点参考 $G_v$ 时，
$U_e$ 变为 $G_vU_eG_u^*$，
回路变为 $G_oU_\gamma G_o^*$，
所以其谱及不动空间维数不变。
这由矩阵乘法直接证明，给出内部约束的另一类不变量。
这种酉连接可描述许多规范关系；
识别为时空曲率还需内部空间、因果、度量和输运对象的对应。

<a id="section-11"></a>

## 11. 引力接口：把时钟与几何一并内生化

“时钟也是观察者结构”确实使时间选择成为理论内部问题。
关系性时间、量子参考框架及引力量子时钟已有直接相关的研究。 [[11]](#ref-page), [[12]](#ref-quantumtime), [[14]](#ref-qrf), [[15]](#ref-gravityclocks)
这些工作支持研究内部时钟与几何的共同关系，
不提供“门计数已经确定引力”的定理。
低能量子引力本身也有有效场论描述；其存在不解决完整高能理论，
但使问题应表述为几何动力学、量子相容性及适用尺度的统一。 [[18]](#ref-donoghue)

**定理 11.1（相同内部静止钟率不能确定曲率）。**

<a id="thm-gravitycounter"></a>

在没有流形边界的 $\mathbb R\times T^3$ 上，
取周期坐标 $x,y,z$，比较

<a id="eq-metrics"></a>

$$
g_0=-dt^2+dx^2+dy^2+dz^2,
\qquad
g_1=-dt^2+dx^2+a(x)^2dy^2+dz^2,\quad a(x)=2+\cos x.
\tag{9}
$$

全部静止空间世界线在两者中均有 $d\tau=dt$，
但 $g_0$ 平坦，$g_1$ 非平坦。
$t$ 在这个比较中可由一个内部参考钟校准。

**证明。**

沿静止线令 $dx=dy=dz=0$，两度量都给固有时增量 $d\tau=dt$。
二维因子 $dx^2+a^2dy^2$ 的相关 Christoffel 符号为
$\Gamma^x_{yy}=-aa'$、
$\Gamma^y_{xy}=\Gamma^y_{yx}=a'/a$。
按 $R^\rho{}_{\sigma\mu\nu} =\partial_\mu\Gamma^\rho_{\nu\sigma} -\partial_\nu\Gamma^\rho_{\mu\sigma} +\Gamma^\rho_{\mu\lambda}\Gamma^\lambda_{\nu\sigma} -\Gamma^\rho_{\nu\lambda}\Gamma^\lambda_{\mu\sigma}$ 的约定，

$$
R^x{}_{yxy}
=\partial_x(-aa')-(-aa')\,a'/a
=-aa''=a(x)\cos x.
$$

它在 $x=0$ 非零，乘积的另两个方向不消除此分量。

□

该反例精确排除的是“所有静止内部钟率已经决定全部几何”的推断。
运动钟、光传播、距离及回路运输可以区分这两个模型；
因此下一步要把这些内部关系一并纳入约束。
单一整体性允许这样做，但不会自动选出某个特定动力学。

**定理 11.2（内部钟率与已取得空间关系的条件几何桥）。**

<a id="thm-lapsebridge"></a>

另行假设内部距离、同步和因果读出已经给出静态局部度量

<a id="eq-lapsemetric"></a>

$$
ds^2=-c^2N(x)^2dt^2+\delta_{ij}dx^idx^j,
\qquad c>0,\quad N\in C^2,\quad N>0,
\tag{10}
$$

其中 $t$ 是一个已校准的内部参考钟。
该度量的静止钟比较为
$d\tau_x/d\tau_{x_0}=N(x)/N(x_0)$。
对 $dt/d\lambda\ne0$ 的仿射测地线，记 $v^i=dx^i/dt$，
则相对于参考钟 $t$ 的坐标加速度为

<a id="eq-clockacc"></a>

$$
\frac{d^2x^i}{dt^2}
=-c^2N\,\partial_iN
+2v^iv^j\partial_j\log N.
\tag{11}
$$

按前述曲率约定，

$$
R^i{}_{tjt}=c^2N\,\partial_i\partial_jN.
$$

若类时轨迹瞬间 $v=0$ 且 $N=1+\Phi/c^2$，则精确有

$$
\frac{d^2x}{dt^2}
=-\nabla\Phi-\frac{\Phi}{c^2}\nabla\Phi.
$$

**证明。**

相关非零联络为
$\Gamma^t_{ti}=\partial_i\log N$、
$\Gamma^i_{tt}=c^2N\partial_iN$。
仿射参数方程为

$$
\ddot t+2(\partial_j\log N)\dot t\,\dot x^j=0,\qquad
\ddot x^i+c^2N\partial_iN\,\dot t^2=0.
$$

将 $d^2x^i/dt^2=(\ddot x^i\dot t-\dot x^i\ddot t)/\dot t^3$
代入即得式 [(11)](#eq-clockacc)。
曲率直接为

$$
R^i{}_{tjt}
=\partial_j(c^2N\partial_iN)
-(c^2N\partial_iN)\frac{\partial_jN}{N}
=c^2N\partial_i\partial_jN.
$$

最后一式是把 $N=1+\Phi/c^2$ 代入静止瞬间的坐标加速度。

□

当 $|\Phi|/c^2$ 小时，主项为 $-\nabla\Phi$。
这是一个正面的研究接口：内部钟率与已取得的空间和测地线关系
可以共同产生 Newton 型坐标加速度。
自由落体自身的四维固有加速度仍为零；
维持静止的参考钟需要的固有空间加速度则是 $c^2\nabla\log N$。
在 $N>0$ 的局部图表中，仿射函数 $N$ 可以有非零梯度而全部曲率为零，
所以钟梯度、参考系加速与潮汐曲率必须区分。
本定理不推出 $\nabla^2\Phi=4\pi G\rho$，
也没有从门词直接推出式 [(10)](#eq-lapsemetric) 的空间度量条件。

**命题 11.3（几何动力学需要的明确额外输入）。**

若另行从内部关系取得四维光滑 Lorentz 度量、
物质泛函，固定 $\kappa\ne0$ 与 $\Lambda$，
并假定下式的一阶局部度量变分良定义：

$$
S[g,\chi]
=\frac1{2\kappa}\int \sqrt{-g}\,(R-2\Lambda)
+S_m[g,\chi],
\qquad
T_{\mu\nu}=-\frac2{\sqrt{-g}}\frac{\delta S_m}{\delta g^{\mu\nu}},
$$

在非紧整体上可将它解释为紧支撑扰动的局部或相对作用变分，
不要求绝对积分有限。
则对所有支撑于流形内部的紧支撑度量变分的驻点满足

$$
G_{\mu\nu}+\Lambda g_{\mu\nu}=\kappa T_{\mu\nu}.
$$

**证明。**

使用
$\delta\sqrt{-g}=-\frac12\sqrt{-g}\,g_{\mu\nu}\delta g^{\mu\nu}$
及 $\delta R=R_{\mu\nu}\delta g^{\mu\nu}+\nabla_\mu V^\mu$，
紧支撑变分的散度项积分为零。
剩余为

$$
\delta S=\frac1{2\kappa}\int\sqrt{-g}
(G_{\mu\nu}+\Lambda g_{\mu\nu}-\kappa T_{\mu\nu})\,\delta g^{\mu\nu}.
$$

对任意紧支撑对称变分为零，给出方程。

□

这是一条条件性变分结论：作用量、度量和物质对应已经作为前件。
它没有从一个量子门计数公式推导上述作用量。
任意酉连接也不自动是时空的切向或自旋连接；
还需 Lorentz 结构、局域因果和普适时钟耦合的对应。
这些都可以是内部关系，毋须重新引入本体外的几何。

<a id="section-12"></a>

## 12. 最新 AURIC 原生接口：近似取得与精确约束

<a id="sec-native"></a>

### 固定黄金记录及本轮原生取得推论

沿用项目的整个十三维来源 $H=V_8^{\mathbf1}$。
令 $P_1=\Pi$ 秩五、$P_0=I-\Pi$ 秩八，并设

$$
\zeta=e^{3\pi i/5},\quad D=P_0+\zeta P_1,\quad
a=\frac{5+\sqrt5}{10},\quad b=\frac{5-\sqrt5}{10}.
$$

原共同等距是

$$
V\eta=\sqrt a\,D^3\eta\otimes\lvert 0 \rangle
+\sqrt b\,D\eta\otimes\lvert 1 \rangle.
$$

令

$$
u=(\sqrt a,\sqrt b)^{\mathsf T},\qquad
z=(\sqrt a\,\zeta^3,\sqrt b\,\zeta)^{\mathsf T},\qquad
Q=\lvert u \rangle\langle u \rvert-\lvert z \rangle\langle z \rvert .
$$

由 $ab=1/5$ 及 $|\langle u,z\rangle|^2=b$，
有 $Q^2=aI$。于是 v29 的信息性读口为

<a id="eq-goldport"></a>

$$
F_\pm=\tfrac12(I\pm Q/\sqrt a),\qquad
\ell_0=\left(\frac{1+\sqrt a}{2},\frac{1-\sqrt a}{2}\right),
\quad
\ell_1=\left(\frac{1-\sqrt a}{2},\frac{1+\sqrt a}{2}\right).
\tag{12}
$$

这组似然严格正且不同，保持两个指针扇区。
这里的两个扇区不是十三维来源的两个一维基态。

项目新增 §100 在同一 Fibonacci 规范中取得

$$
\mathcal K=V_{12}^{\mathbf1},\quad \dim\mathcal K=89,\qquad
J:H\otimes\mathbb C^2\hookrightarrow\mathcal K .
$$

代码 $\mathcal C$ 维数 $26$，其余 $63$ 条合法路径保留为泄漏。
字面基映射是 $J(e_\beta\otimes\lvert i \rangle)=\lvert 10\,\beta\,010\,i010 \rangle$。
原七地址不变，增加四个同类控制地址；
准备关系为同族真空 ready 路径。
新增资源可以在本稿本体中解释为取得新的内部可访问支持，
而不是向宇宙附加外部物质。 [[4]](#ref-repoq)

**定理 12.1（信息性黄金读口的有限精度原生取得）。**

<a id="thm-nativeport"></a>

消费项目 §100 的完整 $89$ 维射影密度、真空嵌入与准备关系，
以及其记录地址 $8,9$ 的代码保持 $\operatorname{PU}(2)$ 密度。
对任意 $\varepsilon_A,\varepsilon_R>0$，
存在固定有限正向同族门字，使原 $V$ 及式 [(12)](#eq-goldport)
在完整 $89$ 维载体中的记录分支在每个单位输入 $\eta\in H$ 上，
以 $\delta=\varepsilon_A+\varepsilon_R$ 的分支向量误差统一逼近。
在明确的 Born 比较仪器中，完整记录与终端律的总变差至多 $\delta$，
接口泄漏质量至多 $\delta^2$。

**证明。**

选 $Q$ 的正交单位本征向量 $f_+,f_-$，
令二维酉 $R$ 把它们分别送到计算基 $\lvert 0 \rangle,\lvert 1 \rangle$。
先施 $R$ 再读计算记录，
系统 Kraus 分量就是 $\langle f_\pm|V$；
记录保留为计算态，避免把此仪器误认成保留 $f_\pm$ 的另一仪器。
项目 §100 的共同取得字在 ready 子空间上逼近 $V$，
算子误差为 $\varepsilon_A$。
同节记录二维密度适用于任意 $R$，故可在整个代码上
用代码保持的记录字以误差 $\varepsilon_R$ 逼近 $I_H\otimes R$。
取共同整体相位后，复合等距在 ready 输入子空间上的
算子范数误差至多 $\delta$。
具体地，令 $M_i$ 为完整 $\mathcal K$ 中记录计算位的投影，
则比较的两个向量都是完整载体中的向量：

$$
\chi_i=M_iR_\varepsilon A_\varepsilon J(\eta\otimes\lvert 0 \rangle),\qquad
y_i=J\bigl(((I_H\otimes\langle f_i \rvert)V\eta)\otimes\lvert i \rangle\bigr).
$$

记录投影及后续旧酉均不增向量误差，故 $\|\chi_i-y_i\|\le\delta$。
两个完整纯输出的迹距离至多其共同相位下的向量距离；
共同测量与后续通道收缩迹距离，所以完整律总变差至多 $\delta$。
理想输出无代码补分量，实际补分量范数至多 $\delta$，
其 Born 质量至多 $\delta^2$。

□

这条推论应用 §100 的任意记录旋转能力；
源的字面定理首先针对原 §91 的指定旋转 $T$，
并没有直接把 $F_\pm$ 写成结论。
所有概率误差属于明示的比较仪器；
不由矩阵近似自动控制一个未知非 Born 读者。

**定理 12.2（固定有限观察深度的误差传播）。**

<a id="thm-finiteerror"></a>

设两个保留全部记录的有限仪器过程，在每个深度的完整通道
（含对旧记录的控制）之间半 diamond 距离至多 $\delta_t$。
则深度 $N$ 的完整输出半迹距离及任意完整记录律总变差均至多

$$
\sum_{t=1}^N\delta_t.
$$

若初始态的半迹距离至多 $\delta_0$，在右侧加 $\delta_0$。
任意取值于 $[0,1]$ 的固定记录损失，其期望差不超过同一界。

**证明。**

将两个复合通道之差写成逐层望远镜和。
每个其余 CPTP 因子的 diamond 范数为一，
故半 diamond 距离不超过逐层之和。
作用于含任意内部旁观坐标的共同态，
再作任意记录测量，收缩给半迹距离和总变差。
$[0,1]$ 损失的积分差由总变差控制。

□

**推论 12.3（只在理想可达内部代码上比较也可传播误差）。**

令实际完整通道为 $\mathcal A_t$、理想通道为 $\mathcal I_t$，
共同初态对应的实际和理想切面态为 $\rho_t,\sigma_t$。
若每层只对理想可达的完整态（包含保留记录和相关内部参考）保证
$D(\mathcal A_t\sigma_{t-1},\mathcal I_t\sigma_{t-1})\le\delta_t$，
其中 $D(\rho,\sigma)=\frac12\|\rho-\sigma\|_1$，
则仍有 $D(\rho_N,\sigma_N)\le D(\rho_0,\sigma_0)+\sum_t\delta_t$。

**证明。**

由实际完整 CPTP 通道的收缩性，

$$
D(\mathcal A_t\rho_{t-1},\mathcal I_t\sigma_{t-1})
\le D(\mathcal A_t\rho_{t-1},\mathcal A_t\sigma_{t-1})+\delta_t
\le D(\rho_{t-1},\sigma_{t-1})+\delta_t.
$$

归纳即可。实际泄漏保留在 $\rho_t$ 中，未作回码后选择。

□

在理想黄金重复协议中，v29 的 QND 收敛给固定深度的错误概率趋零。

> 编者量词澄清：上句“固定深度的错误概率趋零”中的趋零，指理想协议的错误概率随观察深度增加而趋零；随后是在给定容差下选定一个有限深度，再分配该有限过程的编译误差。它不表示固定同一深度时仅靠减小编译误差即可令理想判别误差为零。原句保留。

这也可直接从固定内部记录律证明：对正先验 $\pi_j$，
记录 $h_n=(o_1,\ldots,o_n)$ 的概率为
$\sum_j\pi_j\prod_{t\le n}\ell_j(o_t)$，故

$$
p_n(j)=\frac{\pi_j\prod_{t\le n}\ell_j(o_t)}
{\sum_k\pi_k\prod_{t\le n}\ell_k(o_t)}.
$$

在分量 $j$ 上，强大数定律给
$n^{-1}\log[p_n(k)/p_n(j)]\to-D_{\mathrm{KL}}(\ell_j\Vert\ell_k)<0$。
所以最大后验判别的错误概率趋零；这是固定相容协议内的统计分解，
不是全部不相容情境的全局隐藏值表。相应标准理论见 [[17]](#ref-bauer)。
因此给定总容差，可以先选一个足够大的有限深度，
再为该有限协议选足够小的总编译误差预算。
只要相应内部记录容量和可控支持已供应，且每层完整保留过程
满足上述完整通道界或理想可达代码比较界，
就获得同一本体内的有限分辨率稳定读出。
单次 ready 输入的误差界不自动给整个 $89$ 维载体的 diamond 界，
也不自动供应任意多轮的内部记录准备。
这里没有把固定非零逐步误差无限重复后，直接宣称仍有精确 QND 极限：
非零泄漏或扇区混合的长期稳定性需要另一条定理。

### 内生门词增长不能越过全部代数约束

固定项目 §103 的完整 $26$ 输入代码，令

$$
U_m=(I-\Pi)\otimes I_2+
\Pi\otimes\operatorname{diag}(1,\zeta^m).
$$

源定理 103.2 证明：对每个奇整数 $m$，
全部十一地址上任意有限原生字 $W_w$ 都不能满足
$W_wJ=\alpha JU_m$，其中 $\alpha$ 是全部输入共同的整体相位。 [[4]](#ref-repoq)

为说明其约束机制，保留该证明的承重链：
整权重规范使字矩阵落在 $\mathbb Z[\zeta]$；
环同态 $\zeta\mapsto-1,\ \varphi^{-1}\mapsto2$
把它约化到 $\mathbb F_5$。
实际原门约化为 $S_{12}$ 表示。
完整真空代码投影由记录四元集的换位和恢复；
源内迹恒等式

$$
\operatorname{Tr}\bigl((Z_A-Z_{A'})^2\bigr)=4-|A\cap A'|\quad\text{于 }\mathbb F_5
$$

区分所有不同四元集，故代码稳定子只能保持
前八与后四载体的划分。
其代码作用为 $A\otimes B$。
奇次 $U_m$ 的两个系统地址和两个记录地址的四个对角元却组成

$$
\epsilon\begin{pmatrix}1&1\\1&-1\end{pmatrix},
\qquad \det=-2\epsilon^2\ne0,
$$

而 $A\otimes B$ 对应四项为外积，行列式为零，矛盾。
此处引用的是源内已逐局部块证明的表示与代码稳定子引理，
不以有限字搜索替代全词长论证。

该结果不使用概率律，也不排除近似、偶次相位、
更多内部载体、额外操作或仅指定十三个 ready 输入列的目标。
尤其原 $V$ 的指数 $3,1$ 对应差 $m=-2$，
不在奇次障碍的范围内。
有限域约化也不给复算子范数的正距离下界。
所以“可以任意精度逼近”与“所有有限字均不能精确实现某接口”
完全相容。

### 单锚的条件 Born 桥与内生概率前提

源 §99 保留两套未知连续、相位不变、正归一响应 $P^{(0)},P^{(1)}$。
若全部原生制备 $p$、接续 $f$ 与全部 $1024$ 标签满足

<a id="eq-pairresponse"></a>

$$
aP^{(0)}_w(K_fD^3K_pv)+bP^{(1)}_w(K_fDK_pv)
=aP^{(0)}_w(K_fK_pv)+bP^{(1)}_w(K_fD^2K_pv),
\tag{13}
$$

源的不可约调和分解给正效果表示及

$$
E_w^{(1)}=E_w^{(0)}+c_wI,\qquad \sum_wc_w=0.
$$

该推断使用全原生上下文的密度与连续性，
而非有限试验已经认证全部关系。

**命题 12.4（一个内部记录的校准消去共同常数差）。**

在上述正效果关系下，
若仅 $P^{(0)}$ 对全部十三计算基和全部标签完成独立的基态校准，
则两响应相同并等于原 Born 终端律。

**证明。**

校准使合法 $E_w^{(0)}$ 的对角为一个 $1$ 与其余 $0$，
非法标签全部为 $0$。
正矩阵满足 $|E_{ij}|^2\le E_{ii}E_{jj}$，
故合法效果为对应秩一投影，非法为零。
这些效果在十三维中均有非零核；
$E_w^{(1)}\succeq0$ 在该核上要求 $c_w\ge0$。
全部 $c_w$ 之和为零，故逐个为零。

□

源 §101 通过有限原生取得序列接到式 [(13)](#eq-pairresponse)，
仍要求共同扩大历史上的连续响应充分性、
一个 ready 锚、实际记录概率与更新、全域设置隔离，
并保留全部失败与泄漏质量。
这些都是可以在同一整体内部表述的关系，
没有被“无外部”取消。
推进之处是第二记录的响应转移成为条件结论；
它没有从本体唯一性单独推出所有量子概率规则。

### 最新时钟与递归记忆结果的接入

周期时钟新 §§22--26 给出同一局部成熟锥及全部局部未来、钟信息
仍可对应不同真实全局算子像的来源；
其精确归一时刻历史数为 $F_{t+1}$，物理切面叶数为 $F_{t+2}$。
这些数学归一时间未自动成为物理钟的取得协议。 [[6]](#ref-repoclock)
typed cocycle 新 §22 则在固定二元操作名、单位边时长
及 $\pm1/4$ 钟误差的来源族中，以精确最终端点为共同侧信息、
在线更新只读取操作名且把所有持久控制计入状态时，证明

$$
(C_{\rm stat},C_{\rm on})=(2,2^k).
$$

静态终端二值摘要与递归取得所需的 $2^k$ 个内部状态不同。 [[7]](#ref-repotyped)
这两项支持一个明确的方法要求：
从静态图看见一个简短切面，不能直接推断内生观察者
怎样取得该切面、要记住多少历史、以及其本地钟怎样校准。

<a id="section-13"></a>

## 13. 综合理论的范围与下一步的数学对象

现在可以在同一个固定 $(\mathcal A,\omega)$ 内给出如下完整分工，
每一行都只涉及内部关系。

| 对象 | 数学定义 | 已证明的后果 |
| --- | --- | --- |
| 本体 | 固定正归一态与代数 | GNS 共同向量；不预设外部张量分割。 |
| 观察者增长 | 控制、程序、记录的内部扩展 | 等距直接极限可为同一向量；精确记录有容量要求。 |
| 经典稳定化 | 相容目标对记录代数的条件期望 | 二值极限当且仅当目标可由完整记录辨认。 |
| 参数递归 | $\Theta=\sum c_kB_k$ 与内部受控门 | 几何尾界；黄金权重给 $\varphi^{-2n}$ 误差。 |
| 自相似谱 | 完整二进制程序与指定收缩比 | Cantor 谱、精确 Hausdorff 维数、无正规化点程序。 |
| 局域钟 | 可区分记录与内部共同校准 | 相对速率、重参数化与同步闭路判据。 |
| 关系曲率 | 内部边运输与 holonomy | 固定一个截面允许非平凡回路；纯参考差则平坦。 |
| 原生门实现 | 指定代码、地址、准备及读口 | 有限精度黄金信息性读口；奇次全码精确相位障碍。 |

**定理 13.1（固定本体下的相容综合）。**

设上述整体模型内部同时供应：
定义 [3.1](#def-record) 的持久记录与相容目标、
定理 [6.3](#thm-parameter) 的黄金程序关系、
已校准的内部时钟比较和相容酉运输，
以及适用时第 [12](#sec-native) 节指定的原生接口条件。
则内部条件经典化、递归参数极限、固定代数约束、
关系时钟和有限精度黄金读出可以同时描述，
不要求改写本体态或引入本体外变量。
其中经典化的充要条件、参数误差、闭路相容和有限误差传播
分别正是定理 [3.2](#thm-stabilization)、
[6.3](#thm-parameter)、[10.2](#thm-holonomy)、[12.2](#thm-finiteerror) 的结论。

**证明。**

每个对象都是同一代数中的元素、子代数或状态限制。
各定理只对其列出的内部关系应用正性、等距、函数演算或条件期望，
不改变 $\omega$。
共同参考变换由定理 [5.1](#thm-relations) 保留全部代数关系；
相同记录条件的配对由固定态定义。
因此各结论在同时满足其前件的模型中并行成立。

□

这是一条条件综合，不声称任意独立指定的局部资料都能无矛盾地拼合；
相容整体本身是前件，不能用它跳过原生可实现性。

后续最集中的问题有三个。
第一，在允许的原生资源中，为内部参数递归给出可取得的受控门族，
并保留 §103 的精确障碍和整体误差预算。
第二，从内部记录、因果传播、距离比较和 holonomy
共同构造可检验的几何，而不只指定一个钟速函数。
第三，选择并证明一个内部动力学约束的物理消费者，
使其低能读出给出明确的物质耦合与引力关系。

本稿因此接受并贯彻“没有本体外部”的研究前提，
把变化放在同一整体中的相对读口、条件记录和程序结构上。
已经得到的是一套可证明的内生观察模型与黄金递归构造。
宇宙态的经验选择、复正结构的更深起源、
概率标定的全部物理理由以及完整引力动力学，
尚须由额外的内部约束和可核对证据决定。

## 文献与固定项目来源

<a id="ref-repohead"></a>

**[1]** 
The Omega Institute, *trureturing*.
[固定 dev 快照 75c5f3c4…](https://github.com/the-omega-institute/trureturing/commit/75c5f3c4aea976b089df5070a2f9f24f2905ee3a)，
2026-10-30 21:45:05 Asia/Singapore，PR #24231。

<a id="ref-repoomega"></a>

**[2]** 
项目，[《AURIC $\Omega$ 静态相融纤维理论》](https://github.com/the-omega-institute/trureturing/blob/75c5f3c4aea976b089df5070a2f9f24f2905ee3a/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)，尤其 §12；
当前 Git blob：`40806fc692c91bd90684a556fed5468f1562268c`。

<a id="ref-repov21"></a>

**[3]** 
项目，[《静态量子历史、内生观察者与关系时钟》](https://github.com/the-omega-institute/trureturing/blob/75c5f3c4aea976b089df5070a2f9f24f2905ee3a/docs/develop/theory/AURIC_STATIC_QUANTUM_HISTORIES_ENDOGENOUS_OBSERVERS_AND_RELATIONAL_CLOCKS_V21.md)，v21，§§4--7；
当前 blob：`a3b63441a4f6390e89557b70fb3686807848217b`。

<a id="ref-repoq"></a>

**[4]** 
项目，[《AURIC FIB ATOM 与量子基本原则：原生预测秩与终端响应（续卷 II）》](https://github.com/the-omega-institute/trureturing/blob/75c5f3c4aea976b089df5070a2f9f24f2905ee3a/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md)，
本轮新增 §§99--103，继承 §§77、91、93；
当前 blob：`af41ad5241634914b2ecd5882205b03ecb554a48`。

<a id="ref-repov15"></a>

**[5]** 
项目，[《AURIC 黄金门、NAND 类通用性与算术边界》](https://github.com/the-omega-institute/trureturing/blob/75c5f3c4aea976b089df5070a2f9f24f2905ee3a/docs/develop/theory/AURIC_GOLDEN_GATE_NAND_UNIVERSALITY_AND_ARITHMETIC_LIMITS_V15.md)，v15，§§4、6、9--10。
本文通过量子续卷 II §100 消费其完整合法扇区射影密度，
不宣称重证全部旧稿。

<a id="ref-repoclock"></a>

**[6]** 
项目，[《Recursive Relational Observation: Periodic Clock Rigidity》](https://github.com/the-omega-institute/trureturing/blob/75c5f3c4aea976b089df5070a2f9f24f2905ee3a/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PERIODIC_CLOCK_RIGIDITY.md)，
新增 §§22--26；
blob：`86c26ba488701013859aa6118629790368fc07b1`。

<a id="ref-repotyped"></a>

**[7]** 
项目，[《Recursive Relational Observation: Typed Residual Cocycle Reconstruction》](https://github.com/the-omega-institute/trureturing/blob/75c5f3c4aea976b089df5070a2f9f24f2905ee3a/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TYPED_RESIDUAL_COCYCLE_RECONSTRUCTION.md)，
新增 §22；
blob：`326829179c75d53c883c4409d83222f9e1192fe1`。

<a id="ref-fewster"></a>

**[8]** 
C. J. Fewster and K. Rejzner,
*Algebraic Quantum Field Theory -- an introduction*,
[arXiv:1904.04051v2](https://arxiv.org/abs/1904.04051) (2019)，§2.3。
本文自足证明所用有界 $C^*$ 版本，未移用全部 AQFT 公理。

<a id="ref-mermin"></a>

**[9]** 
N. D. Mermin,
*Hidden variables and the two theorems of John Bell*,
Rev. Mod. Phys. **65**, 803--815 (1993)，§ V；
[作者综述全文](https://cqi.inf.usi.ch/qic/Mermin1993.pdf)，
[doi:10.1103/RevModPhys.65.803](https://doi.org/10.1103/RevModPhys.65.803)。

<a id="ref-nielsen"></a>

**[10]** 
M. A. Nielsen and I. L. Chuang,
*Programmable quantum gate arrays*,
Phys. Rev. Lett. **79**, 321--324 (1997)，
[arXiv:quant-ph/9703032](https://arxiv.org/abs/quant-ph/9703032)。
精确确定性、全部数据输入的无编程合同。

<a id="ref-page"></a>

**[11]** 
D. N. Page and W. K. Wootters,
*Evolution without evolution: Dynamics described by stationary observables*,
Phys. Rev. D **27**, 2885--2892 (1983)，
[doi:10.1103/PhysRevD.27.2885](https://doi.org/10.1103/PhysRevD.27.2885)。
本轮核对官方摘要；本文双无限构造自带证明。

<a id="ref-quantumtime"></a>

**[12]** 
V. Giovannetti, S. Lloyd and L. Maccone,
*Quantum Time*,
Phys. Rev. D **92**, 045033 (2015)，
[arXiv:1504.04215v3](https://arxiv.org/abs/1504.04215)。

<a id="ref-mcclean"></a>

**[13]** 
J. R. McClean, J. A. Parkhill and A. Aspuru-Guzik,
*Feynman's clock, a new variational principle, and parallel-in-time quantum dynamics*,
[arXiv:1301.2326v2](https://arxiv.org/abs/1301.2326) (2013)，
[doi:10.1073/pnas.1308069110](https://doi.org/10.1073/pnas.1308069110)。

<a id="ref-qrf"></a>

**[14]** 
F. Giacomini, E. Castro-Ruiz and Č. Brukner,
*Quantum mechanics and the covariance of physical laws in quantum reference frames*,
Nat. Commun. **10**, 494 (2019)，
[arXiv:1712.07207v2](https://arxiv.org/abs/1712.07207)。

<a id="ref-gravityclocks"></a>

**[15]** 
E. Castro-Ruiz, F. Giacomini, A. Belenchia and Č. Brukner,
*Quantum clocks and the temporal localisability of events in the presence of gravitating quantum systems*,
Nat. Commun. **11**, 2672 (2020)，
[arXiv:1908.10165v2](https://arxiv.org/abs/1908.10165)。

<a id="ref-connes"></a>

**[16]** 
A. Connes and C. Rovelli,
*Von Neumann Algebra Automorphisms and Time-Thermodynamics Relation in General Covariant Quantum Theories*,
Class. Quantum Grav. **11**, 2899--2918 (1994)，
[arXiv:gr-qc/9406019](https://arxiv.org/abs/gr-qc/9406019)；
[作者全文](https://alainconnes.org/wp-content/uploads/carlotime.pdf)。
本文仅将模流作为带忠实性条件的背景。

<a id="ref-bauer"></a>

**[17]** 
M. Bauer and D. Bernard,
*Convergence of repeated quantum non-demolition measurements and wave function collapse*,
Phys. Rev. A **84**, 044103 (2011)，
[arXiv:1106.4953](https://arxiv.org/abs/1106.4953)。

<a id="ref-donoghue"></a>

**[18]** 
J. F. Donoghue,
*General relativity as an effective field theory: The leading quantum corrections*,
Phys. Rev. D **50**, 3874--3888 (1994)，
[arXiv:gr-qc/9405057](https://arxiv.org/abs/gr-qc/9405057)。
支持低能量子引力有效理论的存在，不替代完整高能动力学。
