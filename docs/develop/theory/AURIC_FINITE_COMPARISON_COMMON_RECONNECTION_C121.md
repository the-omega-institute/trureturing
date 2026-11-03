** AURIC 量子关系研究续篇**

# 有限比较的共同回接

**候选 C121：从二元误差到整体内容的恢复**

**本轮的核心关系**

同一来源的有限二元比较，必须能在同一次完整转接中共同成立。保住基本区别，再保住连通图上的相干区别，便存在一个不依赖未知输入的共同回接：

$$
\boxed{\qquad\exists\mathcal R\quad\forall Z,\rho_{HZ},\qquad
 ((\mathcal RN)\otimes\operatorname{id}_Z)(\rho_{HZ})=\rho_{HZ}.\qquad}
$$

当比较带有误差时，先得到内部记录对输入依赖的全参考界，再得到同一个恢复器：

$$
\|N^c-\mathcal S_\tau\|_\diamond\le\delta
 \quad\Longrightarrow\quad
 \|\mathcal RN-\operatorname{id}\|_\diamond
 \le2\sqrt{\delta-\delta^2/4}.
$$

**几何与观察者**

量子比特的完整混合态在 Bures 角下是半径 $1/2$ 的三维上半球。任意三态的二元根保真数值可以作实三维提升，但共同最佳纯化会受到闭环约束。对已标定的共同来源，两观察者可用各自的回接与编码建立转换；第三个观察者的恢复误差控制转换三角的缺陷。

**结论的准确范围**

这是一份含定义、条件、定理、证明与删除反例的有限量子理论工作稿。对象闭包、概率拆并、内部参考与实际资源供应均明确列出。它重构通常有限量子接口并证明有限误差证书，不声称从“一切属于 $\Omega$”独自推出标准模型，也不把已有数学结果认领为新发现。

 仓库快照：`86172888e706177b6c1d135cb12aec3b6d2cdce8`。

 提交时间：2026 年 11 月 3 日 23:34:14；核查起点：11 月 4 日 00:12。

 本页时间均为 Asia/Singapore。相关源码已核读；未执行 Lean 编译。

2026 年 11 月 4 日

## 目录

- [1. 本轮推进与唯一候选：有限比较的共同回接](#section-1)
- [2. 从内部参考相容到完整过程：必要的基础证明](#section-2)
- [3. 有限二元证书：从实际判别误差到共同恢复](#section-3)
- [4. 补端余量怎样给出同一个恢复器](#section-4)
- [5. 不同观察者之间：有标定的转换、三角关系与误差累积](#section-5)
- [6. 共同回接的几何：三维半球、三态提升与共同对齐的边界](#section-6)
- [7. 候选与通常有限量子力学的完整推导接口](#section-7)
- [8. 内生观察、有限证据与量子场接口](#section-8)
- [9. 这一轮完成了什么，以及候选的完整白话表述](#section-9)
- [10. 有限量子原子的实关系选择：前提与完整证明](#section-10)
- [参考文献](#references)

<a id="section-1"></a>

## 1. 本轮推进与唯一候选：有限比较的共同回接

<a id="sec-c121-candidate"></a>

### 1.1 固定仓库版本后，真正需要推进的缺口

本稿固定于仓库提交 `86172888e706177b6c1d135cb12aec3b6d2cdce8`，提交时刻为新加坡时间 2026 年 11 月 3 日 23:34:14；本轮于 11 月 4 日 00:12 起核查。最新 HEAD 的合并主题与本问题无关，故不把提交顺序当成理论进展。与本轮直接相关的新增正文是 V96 续篇 §§140–149，合并提交 `e54a4512cdaf`，新加坡时间 11 月 3 日 23:24:42 [1](#ref-repo-orientation)。

该稿把未知返回闭环的校正，改成检验前已经固定的二十四项立方旋转词目录。对同一个词、同一个成功率，三向回读的和满足

$$
\det O=-1\Longrightarrow\max_g\operatorname{score}_g\le2,
 \qquad
 \det O=+1\Longrightarrow\max_g\operatorname{score}_g
 \ge\frac{7+2\sqrt2}{4}>2.
$$

这依赖完整的原细记录、指定支持双返回、实际有限校准包和全部有限闭环量词。三维 Rodrigues 基本胞是正截角立方体；它是旋转参数的胞，不是把量子态球截成立方体。§146 的误差定理只容许精确实现下的概率读数误差；§148.2 仍保留从原生关系构造载体、记录、校准和复合接口的义务。

另外，当前源码 `NMLWMeasuredFidelitySeparation.lean` 给出同一 POVM 的三态分离命题。对

$$
R=I/2,\qquad A=(I+Z/2)/2,\qquad B=(I+X/2)/2,
$$

源码的 `result` 以这组见证给出

$$
F_U(R,A,B)=\frac{2\sqrt6+2\sqrt2+\sqrt{14}}{12}
 <\frac{24}{25}\le F_M(R,A,B).
$$

其中 $F_U$ 是逐对根保真度的平均，$F_M$ 对作用于整组三态的*同一个*任意有限 POVM 取下确界；它不是对每一对分别选测量。原论文 Remark 5.45 提出了严格分离问题 [3](#ref-nmlw)，项目源码报告上述见证 [2](#ref-repo-nmlw)。本文核读定义、见证及结论，未重新执行 Lean 编译；以下核心恢复证明不把这项仓库声明作为前件。

本轮从这些材料提取的联系是：**同一控制、同一读口与同一回接都要求先固定共同实现，再量化全部比较。**这是一条本稿的综合判断，不是说三种数学命题彼此等价。C121 推进的是已具备完整参考相容性的实际通道，在有限比较带误差时还能共同恢复多少内容；它不声称解决一般正映射的近似校准，也不把固定维数的有限证书扩成无界菜单的证书。

### 1.2 定义的输入必须可见，不能藏进“内生”二字

### 定义 1.1（内部有限关系体系及其接口）

记 $\Omega$ 为包含对象、准备、读口、过程、记录标签及合法接续关系的同一个体系。主文的一个来源部门为 $M_d(\mathbb C)$；局部复对象可由附录的实球形二元块、非平凡方向回路与结合闭包*在其明列前提下*构造。独立部门的复合要求共同复中心、交换嵌入与生成性。概率对效果 $0\le F\le I$ 正、归一化，并对可合并效果可加。

过程起初是状态锥上正、保迹的线性映射。若将同一个过程接到任意声明的内部参考 $M_n(\mathbb C)$，联合正关系仍须为正；矩阵表示中为

$$
(N\otimes\operatorname{id}_n)(X)\succeq0\quad(X\succeq0).
$$

这叫*完整参考相容*。每个所用参考都是 $\Omega$ 内的一个部门，并非外部裁判。要求所有必要有限参考的对象与联合关系存在，仍是一项实质性闭包条件。

实际菜单是已供应的准备、读口和箭头的集合。数学上存在一个效果、等距或恢复映射，不自动把它加入实际菜单。以下“可表示”与“已经可执行”始终分开。

复线性、概率拆并、独立复合和参考相容不是由一句“一切在 $\Omega$ 内”推出的逻辑定理。可以把它们写成定义间的约束，使每个符号都有内部用途；却不能借改名消除其模型选择作用。没有这份前件清单，所谓从单一新公理推出量子力学会是循环论证。

### 定义 1.2（二元比较、共同误差与同一内容）

对状态 $\rho,\sigma$ 定义

$$
D(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1,
 \qquad f(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1.
$$

前者量化二元读口可区分程度，后者是*未平方*根保真度。对同源的两个过程 $L_1,L_2$ 定义完整比较误差

$$
\|L_1-L_2\|_\diamond
 =\sup_{Z,\rho_{HZ}}
 \|((L_1-L_2)\otimes\operatorname{id}_Z)(\rho_{HZ})\|_1.
$$

对通道之差，这就是通常 diamond 范数，取 $\dim Z=d$ 已足够。主文所有通道误差均不除以二，范围是 $[0,2]$。

若存在一个与未知输入无关的通道 $\mathcal R$，使

$$
\mathcal R N=\operatorname{id}_{M_d},
$$

便称 $N$ 保留同一来源的完整内容。此式自动在任意内部参考下成立；含误差版本是 $\|\mathcal R N-\operatorname{id}\|_\diamond\le\varepsilon$。名称“同一内容”由可接续关系固定，而不由外部观察者指定两份内容碰巧相同。

### 定义 1.3（唯一候选 C121：有限比较的共同回接）

<a id="def-c121-axiom"></a>

在上述对象、概率及参考接口中，原菜单须指明哪些箭头是*包含其完整内部记录的内容转接*。每个来源在未知转接之前固定一组正交原子 $e_1,\ldots,e_d$ 与一张连通图 $G$。对同一个指定完整转接 $T$，要求以下两类二元关系均保持完全可区分：

1. 所有原子对 $e_r,e_s$，$r<s$；

2. 每条图边的平衡对 $(e_r+\zeta_{rs}e_s)/\sqrt2$ 与 $(e_r-\zeta_{rs}e_s)/\sqrt2$，其中 $|\zeta_{rs}|=1$ 为该边已固定的制备关系。

用于同一对的读口必须是同一个二元效果；不同对可以有不同读口。同一个 $T$ 不能按未知输入或测试标签换成另一个过程。实际准备和相应读口需供应；有限实验种类不等于有限次抽样能证明零误差。

局部箭头若称为这次完整转接的一个窗口，必须有原菜单中的同一记录和遗忘 $d_E$，满足

$$
N=d_E\,T.
$$

忽略另列的实际供应义务，上述有限二元可区分条件等价于存在*同一个数学回接* $\mathcal R$ 对全部输入及参考保住内容；下面证明这一数学等价。数学回接只保证相应判别效果存在，不能反向自动供应实际读口。若将该回接继续用于实际操作，还须它属于实际菜单，或给出由已有门编译它的过程。其准确量词为

$$
\boxed{\quad\exists\mathcal R\;\forall Z\;\forall\rho_{HZ},\qquad
 ((\mathcal R T)\otimes\operatorname{id}_Z)(\rho_{HZ})=\rho_{HZ}.\quad}
$$

这里给的是*一份*候选：对象与概率定义为它提供语义，有限二元清单刻画完整内容，原记录遗忘解释局部读出。后文的带误差不等式是这份合同的稳定性定理，不另立第二个物理公理。也不把任意有损的局部通道都强行判为必须可恢复；只有指定的完整内容转接承担零误差条件。

完整有限量子模型是其满足模型：取所有有限复矩阵部门、通常效果及通道；每个局部通道选择等距扩充作为完整转接，原记录取该扩充的环境，遗忘取偏迹。恢复可用等距支持上的逆并在支持外补一个固定态。因此候选一致且覆盖通常有限量子操作。一个稀疏的实际门菜单是否具有这些完整记录和回接，则仍须逐项构造。

### 1.3 为何“每个都能回去”还远远不够

### 命题 1.4（量词交换把擦除误判成保存）

对完全擦除 $N(\rho)=\sigma_0$，每个预先知道的 $\rho$ 都有一个准备映射 $\mathcal R_\rho$ 使 $\mathcal R_\rho N(\rho)=\rho$。但当 $d\ge2$ 时，不存在共同 $\mathcal R$ 恢复全部未知输入；任意共同回接至少有 diamond 误差 $1$。

**证明。**
逐态映射直接准备对应的 $\rho$ 即可。共同映射只可能将 $\sigma_0$ 变成一个固定态 $\omega$。选正交纯态 $P,Q$，则

$$
2=\|P-Q\|_1\le\|P-\omega\|_1+\|\omega-Q\|_1.
$$

至少一项不小于 $1$，故共同通道的最坏输入误差不小于 $1$。

**白话。**先给同一份内容起几个可比较的名字，再检验名字之间的区别，以及把两个名字平衡叠起来后的区别。只要这些叠加联系把整个菜单连通，同一个完整过程都保得住，就存在一条统一的回路把未知内容接回来。不能先偷偷知道输入是什么，再为它另做一份；那样一台擦除机也能被说成保留了信息。整体内生的关键，落实在“同一个过程、同一个来源、同一个回接”的量词次序上。

<a id="section-2"></a>

## 2. 从内部参考相容到完整过程：必要的基础证明

<a id="sec-c121-process"></a>

### 2.1 为什么普通二元检验还要带内部参考

### 定理 2.1（参考相容给出 Kraus 与等距表示）

<a id="thm-c121-kraus"></a>

设 $N:M_d(\mathbb C)\to M_k(\mathbb C)$ 复线性、保迹。在声明的联合矩阵关系上完整参考相容，当且仅当存在有限组 $K_a:\mathbb C^d\to\mathbb C^k$，使

$$
N(X)=\sum_aK_aXK_a^*,\qquad \sum_aK_a^*K_a=I.
$$

这也等价于存在有限内部记录空间 $E$ 和等距 $V:\mathbb C^d\to\mathbb C^k\otimes E$，使 $N(X)=\operatorname{Tr}_E(VXV^*)$。

**证明。**
取来源同维参考，令 $\lvert \Gamma\rangle=\sum_re_r\otimes e_r$。参考相容给

$$
C_N=(\operatorname{id}_d\otimes N)(\lvert \Gamma\rangle\langle \Gamma\rvert)
 =\sum_{r,s}\lvert r\rangle\langle s\rvert\otimes N(\lvert r\rangle\langle s\rvert)\succeq0.
$$

有限正矩阵分解为 $C_N=\sum_aw_aw_a^*$，写 $w_a=\sum_re_r\otimes K_ae_r$。比较每个矩阵块，得到 Kraus 等式；保迹等价于 $\sum K_a^*K_a=I$。反向，将联合正元夹在 $K_a\otimes I$ 之间并求和仍为正，故满足全部参考相容。

置 $V\psi=\sum_aK_a\psi\otimes\lvert a\rangle$，便有 $V^*V=I$ 及偏迹公式。反向把任何等距按记录基展开，同样得到 Kraus 形式。该有限证明是 Choi–Stinespring 结构的具体版本 [5](#ref-choi1975)、[4](#ref-stinespring1955)。

取二阶转置 $\Theta(X)=X^{\mathsf T}$。它对单系统保持正性、迹距、所有混合态的根保真度及任意两纯态的正交性，也通过定义 [1.3](#def-c121-axiom) 的两类零误差普通比较。但是

$$
(\Theta\otimes\operatorname{id})(\lvert \Phi^+\rangle\langle \Phi^+\rvert)=\tfrac12\mathsf S,
 \qquad\lvert \Phi^+\rangle=(\lvert 00\rangle+\lvert 11\rangle)/\sqrt2,
$$

交换算子 $\mathsf S$ 在反对称向量上为 $-1$，所以输出有本征值 $-1/2$。删除参考相容就会允许一条把合法联合正关系变成负概率方向的“门”。在 Bloch 坐标中转置是 $(r_x,r_y,r_z)\mapsto(r_x,-r_y,r_z)$ 的反射，保持后文的全部单系统半球几何，却不能保持联合正性。本候选不以普通二元测试偷偷代替这项约束；仓库最新闭环路线在另一份明确供应下取得相容 CP 表示，也不能省去其原记录和取向前提。

### 2.2 补读口也是整体内部的关系

固定上一定理的一个完整等距 $V$，定义

$$
N^c(X)=\operatorname{Tr}_K(VXV^*).
$$

$N^c$ 记录的是同一次完整过程在另一部门的边际；它不是假定某个外部观察者拥有环境。在记录基下，其元素为

$$
(N^c(X))_{ab}=\operatorname{Tr}(K_b^*K_aX).
$$

改变扩充会在记录端引入等距或无关因子，不改变下面关于来源内容的结论。核心问题是这个部门是否还能分辨输入。

### 定理 2.2（零泄漏、共同回接与完整内容的正常形）

<a id="thm-c121-exact-form"></a>

对一个通道 $N$，下列条件等价：

1. 存在共同通道 $\mathcal R$，$\mathcal RN=\operatorname{id}$；

2. 对一个完整等距扩充，存在状态 $\tau$，$N^c(X)=\operatorname{Tr}(X)\tau$；

3. 存在状态 $\tau_0$ 和等距 $W:H\otimes\operatorname{supp}\tau_0\to K$，使


   $$
   N(\rho)=W(\rho\otimes\tau_0)W^*.
   $$

输入输出维数相同的情形强制 $N(\rho)=U\rho U^*$。若要求完整转接对纯输入仍为纯输出，则一般维数下也有单一等距形式 $N(\rho)=W\rho W^*$。

**证明。**
从 1 出发，给 $\mathcal R$ 选等距 $A:K\to H\otimes F$。则 $(A\otimes I_E)V$ 扩充恒等通道。对每个纯 $\psi$，来源输出纯且等于 $\lvert \psi\rangle\langle \psi\rvert$，故扩充值为 $\psi\otimes\eta_\psi$。对正交基的任意平衡和使用线性，迫使所有 $\eta_{e_r}$ 相同，记为 $\eta$；因此整个等距为 $\psi\mapsto\psi\otimes\eta$。对 $H,F$ 偏迹给固定的 $E$ 态，证明 2。

从 2 出发，比较上式每个 $X$ 的矩阵元，得

$$
K_a^*K_b=\alpha_{ab}I,\qquad\alpha\succeq0,\quad\operatorname{Tr}\alpha=1.
$$

记录态是 $\alpha^{\mathsf T}$；不可漏掉这里的指标转置。对 Kraus 标签作酉变换，令 $\alpha$ 对角，非零项满足 $L_a^*L_b=p_a\delta_{ab}I$。于是 $U_a=L_a/\sqrt{p_a}$ 是像空间两两正交的等距。定义 $W(\psi\otimes\lvert a\rangle)=U_a\psi$ 及 $\tau_0=\operatorname{diag}(p_a)$，便得 3。

从 3 出发，在 $P=WW^*$ 支撑上先用 $W^*(\cdot)W$，再忘掉附加因子；支撑外补固定态 $\rho_*$，即

$$
\mathcal R(Y)=\operatorname{Tr}_{\operatorname{supp}\tau_0}(W^*YW)
       +\operatorname{Tr}[(I-P)Y]\rho_*.
$$

这是保迹完全正映射，且 $\mathcal RN=\operatorname{id}$。最后，$d\,\operatorname{rank}\tau_0\le\dim K$；同维时 $\operatorname{rank}\tau_0=1$，$W$ 为酉。若纯输入输出必须纯，正常形的输出秩等于 $\operatorname{rank}\tau_0$，同样迫使其为一。

该定理是量子纠错与补性理论的已知结构 [6](#ref-knill1997)、[9](#ref-beny2010)，这里给出与本候选接口一致的有限证明。下一节把条件 2 从有限个实际二元读口推出，并在非零误差下保留一个完整参考范数估计。

### 推论 2.3（回接给出二元判别的数学逆向）

若 $\mathcal RN=\operatorname{id}$，对任意两个正交源纯态 $P_u,P_v$，效果
$F=\mathcal R^*(P_u)$ 满足 $0\le F\le I$、$\operatorname{Tr}(FN(P_u))=1$、$\operatorname{Tr}(FN(P_v))=0$。
因此有限二元清单的每一对都有一个数学上的完美判别效果。
若要它成为实际证书，仍需供应这个效果，或供应可执行的 $\mathcal R$ 及原来的源测试。

**证明。**
通道伴随正且保单位，所以把效果送到效果；其余直接由 $\mathcal RN=\operatorname{id}$ 与正交性得到。

**白话。**一条完整门若真保存内容，另一份内部记录就不能另留一份可以区分未知输入的副本；否则共同回接会和原来的量子关系冲突。完整保存允许附带一份与输入无关的记录，所以一般过程是“内容加固定附页，再整体搬运”。只有当输出没有多余空间，或要求完整原子保持纯态，才进一步成为通常的酉门或等距门。

<a id="section-3"></a>

## 3. 有限二元证书：从实际判别误差到共同恢复

<a id="sec-c121-binary-graph"></a>

本节研究已经满足前述完整参考相容条件、因而完全正保迹的真实过程
$\mathcal N:M_d(\mathbb C)\to\mathcal B(K)$。噪声属于这个实际通道，而不是仅给一个精确理想门的读数另加误差。源维数 $d\ge2$、同一来源正交基及所用制备均已声明；输出维数可以任意有限。这里不处理一般正映射能否由近似校准变成完全正的另一问题。

取内部等距实现

$$
V:H\longrightarrow K\otimes E,\qquad H=\mathbb C^d,
 \qquad \mathcal N(\rho)=\operatorname{Tr}_E(V\rho V^*),
$$

并记补读口为 $\Gamma(\rho)=\operatorname{Tr}_K(V\rho V^*)$。$E$ 仍在整体内部；观察者不需要先测遍 $E$，就可以利用下面的可见端证书约束它。

### 3.1 一个实际二元效果能约束另一端多少交叉关系

### 定义 3.1（二元判别证据）

对已制备的单位向量 $u,v$，实际供应一个二元效果 $0\le F\le I_K$，把结果 $F$ 判为 $u$，把 $I-F$ 判为 $v$。令

$$
e_u=1-\operatorname{Tr}(F\mathcal N(P_u)),\qquad
 e_v=\operatorname{Tr}(F\mathcal N(P_v)),\qquad P_u=\lvert u\rangle\langle u\rvert,
$$

并定义该证据给出的交叉上界

<a id="eq-c121-binary-eta"></a>

$$
\eta(F;u,v)=\sqrt{(1-e_u)e_v}+\sqrt{e_u(1-e_v)}\in[0,1].
\tag{1}
$$

不要求 $F$ 是未知通道的最优判别效果；每对输入可以使用不同的已声明效果。

### 引理 3.2（可见判别约束补端交叉）

<a id="lem-c121-binary-cross"></a>

上述实际二元证据满足

<a id="eq-c121-cross-bound"></a>

$$
\left\|\Gamma(\lvert u\rangle\langle v\rvert)\right\|_1
 \le \eta(F;u,v).
\tag{2}
$$

特别地，若两个错误概率均不超过 $0\le\varepsilon\le1/2$，则

<a id="eq-c121-uniform-eta"></a>

$$
\left\|\Gamma(\lvert u\rangle\langle v\rvert)\right\|_1
 \le2\sqrt{\varepsilon(1-\varepsilon)}.
\tag{3}
$$

**证明。**
记 $v_u=Vu,v_v=Vv$。迹范数的极分解变分式给出

$$
\|\Gamma(\lvert u\rangle\langle v\rvert)\|_1
 =\max_{U\text{ 酉}}
   |\langle v_v,(I_K\otimes U)v_u\rangle|.
$$

在内积中插入 $F+(I-F)$，再分别对两个平方根分量使用 Cauchy–Schwarz：

$$
|\langle v_v,(I\otimes U)v_u\rangle|
 \le\sqrt{\operatorname{Tr}(F\mathcal N(P_u))\operatorname{Tr}(F\mathcal N(P_v))}
 +\sqrt{\operatorname{Tr}((I-F)\mathcal N(P_u))\operatorname{Tr}((I-F)\mathcal N(P_v))}.
$$

环境酉与这两个可见效果交换，故右侧与 $U$ 无关，恰为
式 [(1)](#eq-c121-binary-eta)。
若 $e_u=\sin^2\alpha,e_v=\sin^2\beta$，则该式为
$\sin(\alpha+\beta)$。在 $e_u,e_v\le\varepsilon\le1/2$ 时，
$0\le\alpha,\beta\le\arcsin\sqrt\varepsilon\le\pi/4$，
故最大值为 $\sin(2\arcsin\sqrt\varepsilon)$，即所述上界。

若只拥有不同的上界 $e_u\le\varepsilon_u,e_v\le\varepsilon_v$，始终可以使用
$\eta\le\min\{1,\sqrt{\varepsilon_u}+\sqrt{\varepsilon_v}\}$。
式中的概率是模型概率或带明示置信保证的界，不是把一次实验结果当作精确概率。

### 引理 3.3（根保真度的有限矩阵对应）

<a id="lem-c121-cross-fidelity"></a>

对同一 $V$，

<a id="eq-c121-cross-fidelity"></a>

$$
\|\Gamma(\lvert u\rangle\langle v\rvert)\|_1
 = f\bigl(\mathcal N(P_u),\mathcal N(P_v)\bigr),
 \qquad f(\rho,\sigma):=\|\sqrt\rho\sqrt\sigma\|_1.
\tag{4}
$$

这里采用未平方的根保真度。

**证明。**
按 $K,E$ 的基把 $Vu,Vv$ 写成振幅矩阵 $A,B:E\to K$。
可见约化态为 $AA^*,BB^*$，补端交叉为 $(B^*A)^{\mathsf T}$。
极分解写为 $A=\sqrt{AA^*}\,U_A$、$B=\sqrt{BB^*}\,U_B$，其中
$U_AU_A^*=\operatorname{supp}(AA^*)$，$U_BU_B^*=\operatorname{supp}(BB^*)$。
因此 $B^*A=U_B^*\sqrt{BB^*}\sqrt{AA^*}U_A$；这两个部分等距在该乘积的左右支撑上保持全部非零奇异值。
转置也保持奇异值，故两边迹范数相同。

由迹距离–根保真度不等式 [7](#ref-fuchs1999)（有限证明见引理
[4.2](#lem-c121-fidelity-contraction)），若两个输出的半迹距离至少为
$1-\epsilon$，也可取 $\eta\le\sqrt{2\epsilon-\epsilon^2}$。
但本节主体直接使用实际效果的错误概率，不依赖观察者能够实现最优 Helstrom 测量。

**白话。**在这一端能把两个输入分得很清楚，就说明另一端不能同时保留很大的输入交叉。这个判断只用一个实际二元效果及它的错误概率；不必先知道环境的全部状态，也不必声称这个效果已经最优。

### 3.2 相干图把二元证据接成整个来源

固定源基 $e_1,\ldots,e_d$，记

$$
R_{rs}:=\Gamma(\lvert e_r\rangle\langle e_s\rvert),\qquad R_{sr}=R_{rs}^*.
$$

每个 $R_{rr}$ 是内部记录端的一个状态。下面使用两类实验。

1. 对每个 $r<s$，比较 $e_r,e_s$，从实际二元证据取得
   $\|R_{rs}\|_1\le a_{rs}=a_{sr}$。

2. 选择一张顶点为 $1,\ldots,d$ 的连通无向图 $G$。
   对每条边 $\{r,s\}$，准备


   $$
   u_{rs}=\frac{e_r+\zeta_{rs}e_s}{\sqrt2},\qquad
    v_{rs}=\frac{e_r-\zeta_{rs}e_s}{\sqrt2},\qquad |\zeta_{rs}|=1,
   $$


   并从其二元判别取得
   $\|\Gamma(\lvert u_{rs}\rangle\langle v_{rs}\rvert)\|_1\le\eta_{rs}$。

相干图可以只是一棵树，所以仍只需 $d-1$ 个相干对。
各条边允许各自选择相位 $\zeta_{rs}$；判定可恢复性不需要预先指定外部的绝对相位取向。不过这些制备必须来自同一个已声明来源，不能把互不相容的两态描述分别拼入证明。

### 引理 3.4（边证据约束内部记录的距离）

<a id="lem-c121-edge-diagonal"></a>

对每条相干边有

<a id="eq-c121-edge-distance"></a>

$$
\|R_{rr}-R_{ss}\|_1\le b_{rs}:=2\eta_{rs}.
\tag{5}
$$

**证明。**
令 $C_{rs}=\Gamma(\lvert u_{rs}\rangle\langle v_{rs}\rvert)$，则

$$
C_{rs}=\frac12
 (R_{rr}-\bar\zeta_{rs}R_{rs}+\zeta_{rs}R_{sr}-R_{ss}),
 \qquad C_{rs}+C_{rs}^*=R_{rr}-R_{ss}.
$$

三角不等式给出所述上界。相位因子在 Hermitian 部分中恰好消去。

为边赋权 $b_{rs}\ge0$。选择锚顶点 $c$，令
$\ell_r^{(c)}$ 为 $c$ 到 $r$ 的最短路权重和，$\ell_c^{(c)}=0$。
零边权允许出现，因而这些距离可为伪距离。
沿路径相加得到

<a id="eq-c121-path-distance"></a>

$$
\|R_{rr}-R_{cc}\|_1\le\ell_r^{(c)}.
\tag{6}
$$

所以基对约束补端的非对角关系，相干边则把全部对角记录状态连到同一个内部锚。

### 3.3 从有限图到任意参考：谱矩阵证书

对锚 $c$，定义非负对称实矩阵

<a id="eq-c121-certificate-matrix"></a>

$$
M^{(c)}_{rr}=\ell_r^{(c)},\qquad
 M^{(c)}_{rs}=a_{rs}\quad(r\ne s),
 \qquad L_c=\lambda_{\max}(M^{(c)}).
\tag{7}
$$

定义固定态替换映射 $\mathcal S_\tau(X)=\operatorname{Tr}(X)\tau$。
全篇 diamond 范数采用未除二的约定，两个通道之差的该范数至多为 $2$。

### 定理 3.5（有限二元相干图的完整参考证书）

<a id="thm-c121-graph"></a>

在上述条件下，对每个锚 $c$，存在内部记录态 $\tau_c=R_{cc}$，使

<a id="eq-c121-graph-decoupling"></a>

$$
\|\Gamma-\mathcal S_{\tau_c}\|_\diamond
 \le\delta_c:=\min\{2,L_c\}.
\tag{8}
$$

因此，选取使 $L_c$ 最小的锚，并应用定理
[4.4](#thm-c121-common-recovery)，得到同一个 CPTP 恢复映射
$\mathcal R$，满足

<a id="eq-c121-graph-recovery"></a>

$$
\boxed{
 \|\mathcal R\mathcal N-\operatorname{id}_{M_d}\|_\diamond
 \le\min\{2,2\sqrt{\delta}\},\qquad
 \delta=\min\{2,\min_c L_c\}.}
\tag{9}
$$

该恢复同时控制全部来源态及任意有限纠缠参考。
还可使用较易计算的上界

<a id="eq-c121-row-sum"></a>

$$
L_c\le\max_r\left(\ell_r^{(c)}+\sum_{s\ne r}a_{rs}\right).
\tag{10}
$$

**证明。**
取任意有限参考 $Q$ 及联合密度矩阵
$\rho=\sum_{r,s}\lvert e_r\rangle\langle e_s\rvert\otimes\rho_{rs}$。
令 $p_r=\operatorname{Tr}\rho_{rr}$，则 $p_r\ge0$、$\sum_rp_r=1$。
对 $\rho$ 取正平方根并按源指标分块，可写成
$\rho_{rs}=A_rA_s^*$，且 $\|A_r\|_2^2=p_r$。
Schatten 范数的 Cauchy–Schwarz 不等式给出

<a id="eq-c121-state-block-bound"></a>

$$
\|\rho_{rs}\|_1\le\sqrt{p_rp_s}.
\tag{11}
$$

取 $\tau_c=R_{cc}$。逐块展开与迹范数三角不等式给出

$$
\begin{aligned}
&\|((\Gamma-\mathcal S_{\tau_c})\otimes\operatorname{id}_Q)(\rho)\|_1\\
 &\quad\le\sum_r p_r\ell_r^{(c)}
       +\sum_{r\ne s}a_{rs}\sqrt{p_rp_s}
       =v^{\mathsf T}M^{(c)}v\le L_c,
 \qquad v_r=\sqrt{p_r},\quad\|v\|_2=1.
\end{aligned}
$$

这里从未限制参考维数或要求来源与参考独立。

为从密度矩阵推广到 diamond 范数定义中的任意输入 $X$，
先以 $\frac12\left(\begin{smallmatrix}0&X\\X^*&0\end{smallmatrix}\right)$
作 Hermitian 化；其迹范数为 $\|X\|_1$，映射后亦有同一对应。
再将 Hermitian 输入分成正、负两部分并各自归一化，二者迹之和就是输入迹范数。因此上面的全参考态上界同样控制所有输入，得到 $L_c$ 界；通道差的普遍上界 $2$ 给出 $\delta_c$。

矩阵 $M^{(c)}$ 的最大特征值不超过最大绝对行和，因其条目非负即得式 [(10)](#eq-c121-row-sum)。
若想在非负向量上考察该证书的 Rayleigh 上界，亦无损失：将任意实向量逐项取绝对值不会降低二次型。因此存在非负的最大特征向量。
最后，统一恢复定理给出式 [(9)](#eq-c121-graph-recovery)。

谱矩阵给出的是由这些误差界推出的保证，不声称它等于真实通道的最优恢复误差。实际通道还可能有使该三角上界严格变小的结构。
内部锚态的存在也不等于观察者已经读出了它；恢复定理对固定实际通道给出一个对全部输入共同有效的恢复，不自动给出一个仅凭这些标量误差就识别出的控制程序。

**白话。**先用基态对压住记录端的交叉，再用连通图上的相加、相减对，把各个记录状态拉到同一个锚附近。每条边的误差沿路径累积；把这些误差装进一张有限矩阵，就能得到一个对所有输入、连同纠缠参考都有效的保证。这里真正统一的是同一个通道和同一个恢复，不能给每个输入临时换一条找回办法。

### 3.4 星形清单与单量子比特的简式

若所有基对都有 $a_{rs}\le\eta$，并在以 $1$ 为中心的星形图上有
$\eta_{1r}\le\eta$，则

$$
M^{(1)}\le_{\rm entrywise}\eta(J+I-2P_1),
$$

其中 $J$ 为全一矩阵，$P_1$ 投影到第一个坐标。因最大特征向量可以取非负，逐项上界也给出最大特征值上界。在第一个坐标与其余坐标等权方向张成的平面中，该矩阵化为

$$
\eta\begin{pmatrix}0&\sqrt{d-1}\\\sqrt{d-1}&d\end{pmatrix}.
$$

其余方向的特征值为 $\eta$，故

<a id="eq-c121-star-bound"></a>

$$
\delta\le
 \min\left\{2,\frac{d+\sqrt{d^2+4d-4}}2\,\eta\right\}
 \le\min\{2,(d+1)\eta\}.
\tag{12}
$$

若每个实际二元判别的两个错误概率均不超过
$\varepsilon\in[0,1/2]$，可以取
$\eta=2\sqrt{\varepsilon(1-\varepsilon)}$，从而得到较简洁的保证

<a id="eq-c121-quarter-root"></a>

$$
\|\mathcal R\mathcal N-\operatorname{id}\|_\diamond
 \le\min\left\{2,
  2\sqrt{2(d+1)}\,[\varepsilon(1-\varepsilon)]^{1/4}\right\}.
\tag{13}
$$

这一第四根界是本证明链提供的充分保证，不宣称指数或常数最优。

对 $d=2$，可以使用两个记录态的中点
$\tau=(R_{00}+R_{11})/2$，而非取某个顶点。
设基对证据为 $\eta_Z$，相加、相减对证据为 $\eta_X$。
边引理给两个对角差均不超过 $\eta_X$，非对角差不超过 $\eta_Z$；
相应证书矩阵为

$$
M=\begin{pmatrix}\eta_X&\eta_Z\\\eta_Z&\eta_X\end{pmatrix}.
$$

因此

<a id="eq-c121-qubit-decoupling"></a>

$$
\|\Gamma-\mathcal S_\tau\|_\diamond
 \le\min\{2,\eta_X+\eta_Z\}.
\tag{14}
$$

在相同的逐态错误上界 $\varepsilon$ 下，统一恢复满足

<a id="eq-c121-qubit-recovery"></a>

$$
\|\mathcal R\mathcal N-\operatorname{id}\|_\diamond
 \le\min\{2,4[\varepsilon(1-\varepsilon)]^{1/4}\}.
\tag{15}
$$

当所有误差为零时，连通图迫使全部 $R_{rr}$ 相同、全部
$R_{rs}=0$（$r\ne s$），补通道恰好为固定态替换。
于是恢复 C120 的精确完整恢复结论；输入输出同维时，实际通道为酉共轭。

### 3.5 反向删除条件：连通性与维数为何不能省

### 例 3.6（相干图断开就只保住各连通块）

<a id="ex-c121-disconnected"></a>

若相干图有至少两个连通分量，令 $P_\alpha$ 为各分量基向量张成空间的投影，取

$$
\mathcal N(\rho)=\sum_\alpha P_\alpha\rho P_\alpha.
$$

全部基对保持完全可区分，任何已测相干边两态都保持原态，故全部已列实验错误为零。
但跨两个分量的 $u_\pm=(e_r\pm e_s)/\sqrt2$ 被送到同一态，整个来源不能恢复。
准确可恢复代数为 $\bigoplus_\alpha\mathcal B(P_\alpha H)$。
连通性因此承担了把局部量子关系接成一个完整来源的实质条件。

### 例 3.7（输入维数增长时，逐对误差趋零仍会丢失全局相位）

<a id="ex-c121-dimension-necessary"></a>

对 $d\ge2$，令

$$
s=d^{-1/2}\sum_{r=1}^de_r,\qquad P=\lvert s\rangle\langle s\rvert,\quad Q=I-P,
 \qquad \mathcal N_d(\rho)=P\rho P+Q\rho Q.
$$

对任意两个不同的基指标 $r,t$，写 $q_r=Qe_r$。有

$$
\mathcal N_d(P_{e_r})=d^{-1}P+\lvert q_r\rangle\langle q_r\rvert,\qquad
 \|q_r\|^2=1-1/d,\qquad \langle q_r,q_t\rangle=-1/d.
$$

两输出的共同 $P$ 项相消，因此它们的半迹距离为

<a id="eq-c121-dimension-pair"></a>

$$
D_{rt}=\frac12\|\mathcal N_d(P_{e_r})-\mathcal N_d(P_{e_t})\|_1
 =\sqrt{1-2/d}\longrightarrow1.
\tag{16}
$$

该公式由两个等范数秩一算符之差在其二维张成空间中的特征值直接得到。
交换 $r,t$ 的对称性还给出一个实际二元效果，使两个错误概率相同，均为
$\varepsilon_d=(1-\sqrt{1-2/d})/2\to0$：可取两态差之符号算符的
$(I+\operatorname{sgn}\Delta)/2$，并在零空间上取 $I/2$。

此外，对每一对实平衡态
$u=(e_r+e_t)/\sqrt2,v=(e_r-e_t)/\sqrt2$，均有
$v\perp s$ 及 $v\perp u$，故 $v$ 与 $Pu,Qu$ 都正交。
这些相干对的输出严格正交，所以即使检查全部实平衡边，错误也全为零。

然而对任意单位 $h\perp s$，输入
$w_\pm=(s\pm h)/\sqrt2$ 被送到同一混合态。
任意一个恢复映射都对二者给出同一个输出 $\sigma$，而

$$
2=\|P_{w_+}-P_{w_-}\|_1
 \le\|P_{w_+}-\sigma\|_1+\|\sigma-P_{w_-}\|_1.
$$

因此任意恢复满足
$\|\mathcal R\mathcal N_d-\operatorname{id}\|_\diamond\ge1$。
这排除了完全不含源维数、只要求这些逐对错误趋零就承诺全来源恢复误差趋零的界；它不宣称式 [(13)](#eq-c121-quarter-root) 的具体维数因子最优。

### 例 3.8（Hilbert–Schmidt 重叠需要额外尺度信息）

<a id="ex-c121-hs-dilution"></a>

固定源维数 $d\ge2$，令输出维数 $k$ 增长，并取完全替换通道
$\mathcal T_k(\rho)=\operatorname{Tr}(\rho)I_k/k$。
任何两输入的输出 Hilbert–Schmidt 重叠都为 $1/k\to0$，
但两输出完全相同，其半迹距离为零，实际最优判别平均错误为 $1/2$。
任何统一恢复的 diamond 误差仍至少为 $1$，可用任意两个源正交态的上述三角证明。
所以仅凭小 Hilbert–Schmidt 重叠无法获得输出维数无关的恢复保证。
若另外给定补端有效维数 $r_E$，则
$\|X\|_1\le\sqrt{r_E}\|X\|_2$ 可以把相应重叠转换成带维数的证书；本节直接使用实际二元判别，因而避免了该输出尺度依赖。

**白话。**先问两份内容还能不能分开，再问它们的相加和相减还能不能分开。第一问压住另一端的交叉，第二问把另一端的两份记录拉近。沿一张连通的关系图这样检查，所有记录就被约束在同一个内部状态附近；一张有限误差矩阵把这件事变成对全部输入和参考都有效的恢复保证。图断开，就可能丢掉块与块之间的相位；维数无限增长，许多看起来很小的局部误差也可能藏住一项全局损失。因此二元关系要接成整体，既要连通，也要把规模和误差一同带着走。

<a id="section-4"></a>

## 4. 补端余量怎样给出同一个恢复器

<a id="sec-c121-common-recovery"></a>

上一节把有限个二元测试的误差变成了一个*全参考*界。本节补齐其中最容易被省略的一步：逐个输入都能选择合适的纯化，不等于存在一个对所有未知输入都有效的恢复器。下面用有限维凸分离证明后一个结论；不把依赖未知状态的选择藏进量词。

### 定义 4.1（统一恢复与补端泄漏）

设 $H,K,E$ 是有限维非零复 Hilbert 空间，固定等距

$$
V:H\longrightarrow E\otimes K,\qquad
 \mathcal N(X)=\operatorname{Tr}_E(VXV^*),\qquad
 \widehat{\mathcal N}(X)=\operatorname{Tr}_K(VXV^*).
$$

记 $\mathfrak S(H)$ 为 $H$ 上的密度算子集合，
$\mathcal S_\tau(X)=\operatorname{Tr}(X)\tau$ 为固定状态 $\tau\in\mathfrak S(E)$ 的替代通道。本文使用*不除以二*的 diamond 距离：

$$
\|\mathcal M-\mathcal L\|_\diamond
 =\max_{\omega\in\mathfrak S(H\otimes H)}
 \|[(\mathcal M-\mathcal L)\otimes\operatorname{id}_H](\omega)\|_1\in[0,2].
$$

它同时控制任意有限参考系统：先把混合输入纯化，再由 Schmidt 秩不超过 $\dim H$ 压缩参考即可。定义

$$
e(\mathcal N)=\min_{\mathcal R\ {\rm CPTP}}
       \|\mathcal R\mathcal N-\operatorname{id}_H\|_\diamond,
 \qquad
 \ell(\mathcal N)=\min_{\tau\in\mathfrak S(E)}
       \|\widehat{\mathcal N}-\mathcal S_\tau\|_\diamond.
$$

有限维中，相关通道集及状态集紧，故最小值均可达到。

这里的参考系统是检验相关性是否保留的数学变量，可以是模型内部的另一个有限记录；它不意味着增加一个能读取 $\Omega$ 全貌的外部观察者。数学定理检验所有合法参考，实验中的有限证书则须由前述有限测试定理负责连接。

### 4.1 两个有限引理：纯化重叠与统一选择

### 引理 4.2（根保真度、收缩与迹距离）

<a id="lem-c121-fidelity-contraction"></a>

定义未平方的根保真度

$$
f(a,b)=\operatorname{Tr}\sqrt{\sqrt a\,b\sqrt a}=\|\sqrt a\sqrt b\|_1.
$$

若单位向量 $v\in Q\otimes K$、$j\in Q\otimes L$ 分别纯化 $a,b$，则

<a id="eq-c121-uhlmann-contraction"></a>

$$
f(a,b)=\max_{A:K\to L,\ \|A\|_\infty\le1}
       \operatorname{Re}\langle j,(I_Q\otimes A)v\rangle .
\tag{17}
$$

此外

<a id="eq-c121-fvg"></a>

$$
1-f(a,b)\le\tfrac12\|a-b\|_1
        \le\sqrt{1-f(a,b)^2}.
\tag{18}
$$

**证明。**
把 $v,j$ 写成系数矩阵 $X,Y$，则 $XX^*=a$、$YY^*=b$。展开内积后，式~[(17)](#eq-c121-uhlmann-contraction) 左侧的最优化成为迹范数对偶
$\max_{\|B\|\le1}\operatorname{Re}\operatorname{Tr}(BY^*X)=\|Y^*X\|_1$；这里 $B$ 与 $A$ 相差基约定造成的转置。由 $X,Y$ 的极分解，$Y^*X$ 与 $\sqrt b\sqrt a$ 有相同的非零奇异值，得到等式。这也证明矩形收缩足够，不要求原有纯化空间维数相同。

为证第一个不等式，先设 $a>0$，令

$$
L=a^{-1/2}(a^{1/2}ba^{1/2})^{1/2}a^{-1/2},\qquad LaL=b.
$$

在 $L$ 的特征基中，$p_i=\langle i,a i\rangle$、
$q_i=\langle i,b i\rangle=\lambda_i^2p_i$，因而
$\sum_i\sqrt{p_iq_i}=\operatorname{Tr}(aL)=f(a,b)$。于是

$$
1-f(a,b)=\tfrac12\sum_i(\sqrt{p_i}-\sqrt{q_i})^2
 \le\tfrac12\sum_i|p_i-q_i|\le\tfrac12\|a-b\|_1.
$$

最后一步是迹范数对偶，测试算子取对角元素差的符号。以
$a_\epsilon=(1-\epsilon)a+\epsilon I/\dim Q$ 逼近可去掉可逆性条件。
第二个不等式来自式~[(17)](#eq-c121-uhlmann-contraction) 的最优纯化：把最优收缩扩张为等距、允许共同增加纯化空间，便有两单位纯化重叠 $f(a,b)$；它们的迹距离为 $2\sqrt{1-f(a,b)^2}$，部分迹只会减小迹距离。

### 引理 4.3（有限凸分离保证一个共同选择）

<a id="lem-c121-uniform-separation"></a>

设 $\mathcal Y$ 是 $H$ 上 Hermitian 算子的非空紧凸集。若对每个
$\rho\in\mathfrak S(H)$ 都有
$\max_{Y\in\mathcal Y}\operatorname{Tr}(\rho Y)\ge t$，则存在*同一个*
$Y_0\in\mathcal Y$ 满足 $Y_0\succeq tI$。因此

<a id="eq-c121-finite-minimax"></a>

$$
\min_\rho\max_{Y\in\mathcal Y}\operatorname{Tr}(\rho Y)
 =\max_{Y\in\mathcal Y}\min_\rho\operatorname{Tr}(\rho Y).
\tag{19}
$$

**证明。**
若 $\mathcal Y$ 与闭凸集 $\mathcal Z=tI+\{P:P\succeq0\}$ 不相交，紧性给出 Hilbert–Schmidt 距离严格正的最近点 $Y_0,Z_0$。
令 $Q=Z_0-Y_0\ne0$。沿两集合中线段对距离平方求单侧导数，得到

$$
\sup_{Y\in\mathcal Y}\operatorname{Tr}(QY)
 \le\operatorname{Tr}(QY_0)<\operatorname{Tr}(QZ_0)
 \le\inf_{Z\in\mathcal Z}\operatorname{Tr}(QZ).
$$

右端有有限下界迫使 $Q\succeq0$；否则沿负特征向量方向增加 $Z$ 会使右端趋于 $-\infty$。以 $\rho=Q/\operatorname{Tr} Q$ 代入，右端为 $t$，便与假设矛盾。由此存在共同 $Y_0$。令 $t$ 等于式~[(19)](#eq-c121-finite-minimax) 左侧，结合始终成立的 ``$\max\min\le\min\max$'' 即得等式。

### 4.2 统一恢复定理及其显式有限构造

### 定理 4.4（补端近常量 $\Longrightarrow$ 同一 CPTP 恢复器）

<a id="thm-c121-common-recovery"></a>

若存在 $\tau\in\mathfrak S(E)$ 使

$$
\|\widehat{\mathcal N}-\mathcal S_\tau\|_\diamond\le\delta,
 \qquad 0\le\delta\le2,
$$

则存在一个与未知输入及参考系统无关的 CPTP 映射
$\mathcal R:K\to H$，满足

<a id="eq-c121-common-recovery-bound"></a>

$$
\|\mathcal R\mathcal N-\operatorname{id}_H\|_\diamond
 \le 2\sqrt{\delta-\delta^2/4}
 \le\min\{2,\,2\sqrt\delta\}.
\tag{20}
$$

特别地，$\delta=0$ 时得到整份源代数的精确恢复。

**证明。**
**第一步：给常量补端一个保留源的纯化。**
取 $\tau=\sum_ap_a\lvert a\rangle\langle a\rvert$，选 $F$ 容纳这组基，令 $L=H\otimes F$，并定义

$$
J\psi=\sum_a\sqrt{p_a}\lvert a\rangle_E\otimes(\psi_H\otimes\lvert a\rangle_F).
$$

于是 $J:H\to E\otimes L$ 是等距，$\operatorname{Tr}_LJXJ^*=\operatorname{Tr}(X)\tau$。
给定任意 $\rho\in\mathfrak S(H)$，取其纯化 $\psi_\rho$。
两个环境–参考输出之间的迹距离至多 $\delta$。引理~[4.2](#lem-c121-fidelity-contraction) 给出

<a id="eq-c121-pointwise-alignment"></a>

$$
\max_{\|A:K\to L\|\le1}
 \operatorname{Re}\operatorname{Tr}\!\left[\rho J^*(I_E\otimes A)V\right]
 \ge 1-\delta/2 .
\tag{21}
$$

**第二步：把逐态选择升级为同一个收缩。**
令

$$
\mathcal Y=
 \left\{\operatorname{Re}[J^*(I_E\otimes A)V]:\|A\|\le1\right\},
 \qquad \operatorname{Re} X=(X+X^*)/2.
$$

这是紧凸集。由式~[(21)](#eq-c121-pointwise-alignment) 和
引理~[4.3](#lem-c121-uniform-separation)，存在一个固定 $A$，满足

<a id="eq-c121-uniform-alignment"></a>

$$
\operatorname{Re}[J^*(I_E\otimes A)V]\succeq (1-\delta/2)I_H.
\tag{22}
$$

这一步证明的是 $\exists A\ \forall\rho$，不是仅有 $\forall\rho\ \exists A_\rho$。
当 $V,\tau$ 的坐标已经供应，寻找这个 $A$ 是一个有限半正定可行性问题：
式~[(22)](#eq-c121-uniform-alignment) 加上
$\left(\begin{smallmatrix}I_L&A\\mathcal A^*&I_K\end{smallmatrix}\right)\succeq0$
即可，后一个条件等价于 $\|A\|\le1$。

**第三步：显式扩张环境，而不偷换最小纯化。**
定义等距

$$
U:K\to L\oplus K,\qquad
 U\xi=A\xi\oplus\sqrt{I_K-A^*A}\,\xi,
$$

并设 $\widetilde V=(I_E\otimes U)V$，
$\widetilde J=(I_E\otimes\iota_L)J$。两者进入同一个增大的空间，且

$$
(\widetilde V-\widetilde J)^*(\widetilde V-\widetilde J)
 =2I-2\operatorname{Re}[J^*(I_E\otimes A)V]\preceq\delta I.
$$

故 $\|\widetilde V-\widetilde J\|_\infty\le\sqrt\delta$。
这里允许的共同扩张已经写出；并未声称任意预先固定的两个最小环境都具有同样的最优对齐。

**第四步：显式定义一个 CPTP 数学映射。**
固定 $\rho_0\in\mathfrak S(H)$，令 $P_L,P_K$ 为 $L\oplus K$ 的块投影，定义

$$
\mathcal D(X)=\operatorname{Tr}_F(P_LXP_L)+\operatorname{Tr}(P_KX)\rho_0,
 \qquad \mathcal R=\mathcal D\circ\operatorname{Ad}_U.
$$

在第一项中自然把 $L$ 块看成 $H\otimes F$。两项都是 CP，迹之和等于 $\operatorname{Tr} X$，故 $\mathcal D,\mathcal R$ 都是 CPTP；$\mathcal D$ 把 $\widetilde J$ 的可见边缘恰好解码为输入。

对于任意纯输入连同任意参考，$\widetilde V$ 与 $\widetilde J$ 产生的两单位向量，其重叠实部由式~[(22)](#eq-c121-uniform-alignment) 至少为 $1-\delta/2\ge0$。纯态迹距离公式给出
$2\sqrt{1-(1-\delta/2)^2}$。再取环境部分迹并施加同一个 $\mathcal D$，距离不会增加；混合输入由凸性处理，得到式~[(20)](#eq-c121-common-recovery-bound)。所有构造只依赖 $V,\tau$ 及固定的 $\rho_0$，不依赖未知 $\rho$。

这是有限维信息–扰动关系的直接证明；维度无关的 $2\sqrt\delta$ 界属于 Kretschmann、Schlingemann 与 Werner 的 Stinespring 连续性理论 [8](#ref-ksw2008)。本文的新候选若使用这一步，应把它标为所依赖的已知量子结构内的定理，而不把该恢复界称为新发现。

**白话。**每一种未知内容都能单独找到一种修法，还不够。我们需要一套事先固定的修法，输入是什么都不用先知道。凸分离证明了：只要丢掉的一边连同任何内部参考都几乎分不清输入，那么这些逐态的修法能够合成一个共同修法。把缺少的空间补齐后，这个修法成为一个合法通道。

### 推论 4.5（接回有限二元证书）

若上一节的二元测试给出
$\delta_E=\min\{2,(d+1)\eta\}$，则同一个恢复器满足

$$
\|\mathcal R\mathcal N-\operatorname{id}\|_\diamond
 \le2\sqrt{\delta_E-\delta_E^2/4}
 \le\min\{2,\,2\sqrt{(d+1)\eta}\}.
$$

若每个二元效果的两个条件错误均不超过 $\varepsilon\le1/2$，可代入
$\eta\le2\sqrt{\varepsilon(1-\varepsilon)}$。其小误差保证为
$O(\sqrt d\,\varepsilon^{1/4})$；这只是这条证明链的保守上界，尚未证明为最佳误差指数或最佳维数依赖。

### 4.3 精确对偶：两边其实是同一个最坏态优化

### 定义 4.6（最坏输入的根保真度）

若 $\Psi_\rho=\lvert \psi_\rho\rangle\langle \psi_\rho\rvert$ 是 $\rho$ 的任一纯化，定义

$$
F_\rho(\mathcal M,\mathcal L)
 =f((\mathcal M\otimes\operatorname{id})\Psi_\rho,
       (\mathcal L\otimes\operatorname{id})\Psi_\rho),
 \qquad
 F(\mathcal M,\mathcal L)=\min_\rho F_\rho(\mathcal M,\mathcal L).
$$

此处 $F$ 仍未平方。令
$b(\mathcal M,\mathcal L)=\sqrt{2-2F(\mathcal M,\mathcal L)}$，即最坏输入的 Bures 距离。

### 定理 4.7（B
'eny–Oreshkov 对偶，恒等目标的有限证明）

<a id="thm-c121-fidelity-duality"></a>

<a id="eq-c121-fidelity-duality"></a>

$$
\max_{\mathcal R\ {\rm CPTP}}F(\mathcal R\mathcal N,\operatorname{id}_H)
 =\max_{\tau\in\mathfrak S(E)}F(\widehat{\mathcal N},\mathcal S_\tau).
\tag{23}
$$

因此 $\min_{\mathcal R}b(\mathcal R\mathcal N,\operatorname{id})
=\min_\tau b(\widehat{\mathcal N},\mathcal S_\tau)$。
该等式是已知 B
'eny–Oreshkov 定理的 $\mathcal M=\operatorname{id}$ 特例 [9](#ref-beny2010)。

**证明。**
取 $F$ 足够大，使 $\dim F\ge\max\{\dim E,\dim H\dim K\}$。
所有恢复通道均可由某个等距 $K\to H\otimes F$ 表示；同时 $F$ 足以纯化 $E$ 上任意状态。固定必要的张量因子换序，令
$A:K\to H\otimes F$ 遍历收缩，$t\in E\otimes F$ 遍历单位球。令 $J_t$ 表示 ``保留 $H$ 并附加向量 $t$'' 的映射，定义

$$
g_\rho(A,t)=\operatorname{Tr}\!\left[\rho J_t^*(I_E\otimes A)V\right].
$$

它的实部对 $\rho,A,t$ 各自都是实线性的。具体写成
$V\psi=\sum_i\lvert i\rangle_E\otimes E_i\psi$、
$A\xi=\sum_\alpha A_\alpha\xi\otimes\lvert \alpha\rangle_F$，则

$$
(z_A(\rho))_{i\alpha}=\operatorname{Tr}(\rho A_\alpha E_i),\qquad
 \max_{\|t\|\le1}\operatorname{Re} g_\rho(A,t)=\|z_A(\rho)\|_2.
$$

其平方正好是
$\langle\psi_\rho|[(\mathcal R_A^0\mathcal N)\otimes\operatorname{id}]
(\Psi_\rho)|\psi_\rho\rangle$，其中
$\mathcal R_A^0(X)=\operatorname{Tr}_F(AXA^*)$ 是迹不增 CP 映射。把它补为

$$
\mathcal R_A(X)=\operatorname{Tr}_F(AXA^*)
   +\operatorname{Tr}[(I_K-A^*A)X]\rho_0
$$

只会增加与该理想纯态的重叠。因此收缩优化不会超过所有 CPTP 恢复的最优值；反过来，每个 CPTP 恢复的等距表示也在收缩集合内。记最优恢复保真度为 $q$，便有

$$
q=\max_A\min_\rho\max_t\operatorname{Re} g_\rho(A,t).
$$

固定 $A$ 时，引理~[4.3](#lem-c121-uniform-separation) 可对 $t$ 单位球的 Hermitian 像使用；固定 $t$ 时又可对 $A$ 单位球的像使用。故

$$
\begin{aligned}
q&=\max_A\max_t\min_\rho\operatorname{Re} g_\rho(A,t)\\
  &=\max_t\max_A\min_\rho\operatorname{Re} g_\rho(A,t)
   =\max_t\min_\rho\max_A\operatorname{Re} g_\rho(A,t).
\end{aligned}
$$

当 $\|t\|=1$ 时，引理~[4.2](#lem-c121-fidelity-contraction) 把最内层识别为
$F_\rho(\widehat{\mathcal N},\mathcal S_{\tau_t})$，其中
$\tau_t=\operatorname{Tr}_F\lvert t\rangle\langle t\rvert$。最内层非负且随 $\|t\|$ 正齐次，故最外层可限于单位球面。单位 $t$ 覆盖所有 $\tau$ 的纯化，得到式~[(23)](#eq-c121-fidelity-duality)。两次交换都发生在紧凸集与双线性函数之间；不存在把未知 $\rho$ 当作恢复器输入的步骤。

### 推论 4.8（恢复与泄漏互相控制）

定义 $h(s)=2\sqrt{s-s^2/4}$，$0\le s\le2$，则

$$
e(\mathcal N)\le h(\ell(\mathcal N)),\qquad
 \ell(\mathcal N)\le h(e(\mathcal N)).
$$

特别地
$\ell^2/4\le e\le2\sqrt\ell$，且 $e=0$ 当且仅当 $\ell=0$。

**证明。**
引理~[4.2](#lem-c121-fidelity-contraction) 对所有输入纯化给出

$$
2(1-F(\mathcal M,\mathcal L))
 \le\|\mathcal M-\mathcal L\|_\diamond
 \le2\sqrt{1-F(\mathcal M,\mathcal L)^2}.
$$

两边最优 $F$ 由式~[(23)](#eq-c121-fidelity-duality) 相等。以达到最小 diamond 误差的通道得到共同最优 $F\ge1-e/2$ 或 $F\ge1-\ell/2$，再以达到最优 $F$ 的通道控制另一边，即得结论。

**白话。**可恢复多少，等价于丢掉的一边还能辨认出多少输入。这不是为每个状态分别挑一个答案：左边先选定同一恢复器，再让最不利输入来检验；右边先选定同一常量背景，再让最不利输入来检验。两个最优化精确相等。二元读取的容错定理因而可以约束关系的全部延伸，而不只约束眼前的一对读数。

<a id="section-5"></a>

## 5. 不同观察者之间：有标定的转换、三角关系与误差累积

<a id="sec-c121-observer-transport"></a>

### 命题 5.1（共同来源的观察者转换）

<a id="prop-c121-observer-transport"></a>

设*已给定*同一有限源 $H$ 与各观察者的编码
$\mathcal N_A:H\to K_A$、恢复器 $\mathcal R_A:K_A\to H$，且
$\|\mathcal R_A\mathcal N_A-\operatorname{id}_H\|_\diamond\le e_A$。定义
$\mathcal T_{BA}=\mathcal N_B\mathcal R_A$。则

<a id="eq-c121-calibration"></a>

$$
\begin{aligned}
\|\mathcal T_{BA}\mathcal N_A-\mathcal N_B\|_\diamond
       &\le e_A,
\end{aligned}
\tag{24}
$$

<a id="eq-c121-triangle-defect"></a>

$$
\begin{aligned}
\|\mathcal T_{CB}\mathcal T_{BA}-\mathcal T_{CA}\|_\diamond
       &\le e_B,
\end{aligned}
\tag{25}
$$

<a id="eq-c121-roundtrip"></a>

$$
\begin{aligned}
\|\mathcal T_{AB}\mathcal T_{BA}\mathcal N_A-\mathcal N_A\|_\diamond
       &\le\min\{2,e_A+e_B\}.
\end{aligned}
\tag{26}
$$

这些不等式均包括与任意参考保有的相关性。

**证明。**
CPTP 前后复合收缩 diamond 距离。第一式来自
$\mathcal N_B(\mathcal R_A\mathcal N_A-\operatorname{id})$。
第二式直接展开为

$$
\mathcal T_{CB}\mathcal T_{BA}-\mathcal T_{CA}
 =\mathcal N_C(\mathcal R_B\mathcal N_B-\operatorname{id}_H)\mathcal R_A.
$$

它甚至控制 $K_A$ 上任意输入，因为 $\mathcal R_A$ 把它们送回 $H$。
往返式在恒等源中插入两次恢复，并用三角不等式即可。

这里有一个明确的三元有限提升：直接从 $A$ 转到 $C$，与经 $B$ 转到 $C$ 的差，恰由中间观察者 $B$ 的源恢复余量控制。$e_B=0$ 时三角交换严格成立。然而通常
$\mathcal T_{AA}\ne\operatorname{id}_{K_A}$；只能保证
$\|\mathcal T_{AA}\mathcal N_A-\mathcal N_A\|_\diamond\le e_A$。
观察者空间中与所声明源无关的其他记录，不受本命题保证。

### 命题 5.2（顺序恢复的累积界）

设 $\mathcal N_j:H_{j-1}\to H_j$ 与
$\mathcal R_j:H_j\to H_{j-1}$ 满足
$\|\mathcal R_j\mathcal N_j-\operatorname{id}_{H_{j-1}}\|_\diamond\le e_j$。
则

$$
\|\mathcal R_1\cdots\mathcal R_n
       \mathcal N_n\cdots\mathcal N_1-\operatorname{id}_{H_0}\|_\diamond
 \le\min\left\{2,\sum_{j=1}^n e_j\right\}.
$$

**证明。**
每次把最内层 $\mathcal R_j\mathcal N_j$ 换成恒等，产生的差被其前后的 CPTP 通道收缩。逐层望远镜展开并用三角不等式即得。若某步只在一个受限源子空间成立，则须先证明前序输出确实落在该子空间；不能直接套用本式。

对于给定的实际恢复序列，不能把此处普遍改为误差平方相加。例如在 $H=\mathbb C^2$ 上取 $Z=\operatorname{diag}(1,-1)$，令所有
$\mathcal R_j=\operatorname{id}$、$\mathcal N_j=\operatorname{Ad}_{\exp(-i\theta Z)}$，则单步误差为
$2|\sin\theta|$，$n$ 步误差为 $2|\sin(n\theta)|$；当 $n\theta$ 很小时按 $n$ 线性积累。前卷的正交缺陷分解不自动成为恢复通道误差的勾股定理。

### 例 5.3（一个状态始终纯净，整份内容仍可完全丢失）

设 $d=\dim H\ge2$，令 $\mathcal N(\rho)=\operatorname{Tr}(\rho)\lvert 0\rangle\langle 0\rvert$。
它固定 $\lvert 0\rangle$ 并把每个输入都变成纯态，但任意恢复后的通道仍是常量替代。对最大纠缠态
$\lvert \Omega_d\rangle=d^{-1/2}\sum_i\lvert i\rangle\lvert i\rangle$，恢复输出为
$\sigma\otimes I/d$，而
$\langle\Omega_d|(\sigma\otimes I/d)|\Omega_d\rangle=1/d^2$。
用 $\lvert \Omega_d\rangle\langle \Omega_d\rvert$ 作二元测试，得到每个恢复器都满足

$$
\|\mathcal R\mathcal N-\operatorname{id}_H\|_\diamond\ge2(1-d^{-2}).
$$

所以一个已知自指状态的不动性或纯度，不能替代全源、全参考的恢复条件。

所有上述存在性定理仍须与项目中的*供应条件*分开：数学上存在的 CPTP $\mathcal R$，不保证观察者当前可调用的门菜单已经实现它；有限测试的几个误差数值也未必足以重建它。若只保留无坐标的保真度数值，所有酉通道都给出零误差，但恒等通道与 $\operatorname{Ad}_Z$ 需要不同的逆。实现时还须提供输出坐标、编码标定与恢复电路。

同样，命题~[5.1](#prop-c121-observer-transport) 的共同源识别是明确的输入数据或内部证书，并非由 ``没有上帝模式'' 自动推出来。它不声称一个观察者能据此发现所有未知观察者的实际交集。观察者可以靠共同制备、挑战–应答和给定嵌入证明*有限的*共同内容；完整包含另一观察者结构只是更强的充分条件，不是认证任何有限共同部分的必要条件。

**白话。**两个观察者不必走相同的门序列，也不必知道彼此全部内容。只要对一块已标定的共同来源，各自都能用固定方法把内容找回来，就能先找回这块内容、再用对方的编码表达。绕第三个观察者一圈会多出多少误差，由第三个观察者保存这块内容的程度来控制。这里比较的是有证书的共同片段；并没有从有限读数推出谁掌握了整个 $\Omega$。

<a id="section-6"></a>

## 6. 共同回接的几何：三维半球、三态提升与共同对齐的边界

<a id="sec-c121-geometry"></a>

本节把“同一回接保住全部二元关系”画成可以计算的几何。输入仍是有限维复矩阵态与量子通道；所证明的是这些定义之间的约束，不把一个漂亮的几何图形当作复数域或复合规则的独立来源。需要分清三个层次：两态之间的最佳比较数值、若干比较数值的抽象几何实现，以及保留原来各态的同一组实际纯化。后两者有可证明的差别。

### 6.1 二元关系给出角度，而无须预先固定公共相位

### 定义 6.1（根保真度、角度与振幅）

对同一有限维空间上的态 $\rho,\sigma$，定义

$$
f(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1,\qquad
 A_B(\rho,\sigma)=\arccos f(\rho,\sigma),\qquad
 d_B(\rho,\sigma)=\sqrt{2-2f(\rho,\sigma)}.
$$

其中 $f$ 是*未平方*的保真度，$A_B$ 称为 Bures 角。
态 $\rho$ 的振幅是满足 $WW^*=\rho$ 的矩阵 $W$；允许加零列，使各振幅有共同的辅助空间。向量化后，$W$ 就是 $\rho$ 的一个纯化，且 $\|W\|_2=1$。

奇异值分解直接给出

<a id="eq-c121-polar-fidelity"></a>

$$
\max_{U\text{ 酉}}\operatorname{Re}\operatorname{Tr}(\sqrt\rho\sqrt\sigma U)
 =\|\sqrt\rho\sqrt\sigma\|_1.
\tag{27}
$$

该等式包含奇异态：极分解中的部分等距可在有限维补空间上延拓为酉矩阵。更一般地，写 $W_\rho=\sqrt\rho C_\rho$、$W_\sigma=\sqrt\sigma C_\sigma$，其中极分解可取 $C_\rho,C_\sigma$ 为收缩，则

$$
|\operatorname{Tr}(W_\rho^*W_\sigma)|
 =|\operatorname{Tr}(\sqrt\rho\sqrt\sigma C_\sigma C_\rho^*)|
 \le f(\rho,\sigma).
$$

结合式~[(27)](#eq-c121-polar-fidelity)，这证明了根保真度是两态所有纯化重叠模长的最大值，也等于最大正实重叠。这里的“最大”先针对*这一对*，没有假定不同边的最大值能在一套纯化中同时实现。由 Hilbert–Schmidt Cauchy–Schwarz 不等式，$0\le f\le1$；$f=1$ 时存在相等振幅，故 $\rho=\sigma$。因此 $A_B\in[0,\pi/2]$，且只有相同态的角度为零。

### 引理 6.2（Bures 角的三角不等式与通道收缩）

对任意三态，

$$
A_B(\rho_1,\rho_3)\le A_B(\rho_1,\rho_2)+A_B(\rho_2,\rho_3).
$$

对任意通道 $\mathcal N$，

$$
f(\mathcal N\rho,\mathcal N\sigma)\ge f(\rho,\sigma),\qquad
 A_B(\mathcal N\rho,\mathcal N\sigma)\le A_B(\rho,\sigma).
$$

**证明。**
固定中间振幅 $W_2=\sqrt{\rho_2}$，分别用式~[(27)](#eq-c121-polar-fidelity) 选取 $W_1,W_3$，使其与 $W_2$ 的实内积分别为 $a=f_{12}$、$b=f_{23}$。在实 Hilbert 空间中写

$$
W_1=aW_2+X,\quad W_3=bW_2+Y,\quad
 \operatorname{Re}\operatorname{Tr}(W_2^*X)=\operatorname{Re}\operatorname{Tr}(W_2^*Y)=0.
$$

于是 $\|X\|_2^2=1-a^2$、$\|Y\|_2^2=1-b^2$，从而

$$
f_{13}\ge\operatorname{Re}\operatorname{Tr}(W_1^*W_3)
 \ge ab-\sqrt{(1-a^2)(1-b^2)}.
$$

若 $\alpha=\arccos a$、$\beta=\arccos b$ 满足 $\alpha+\beta\le\pi/2$，右端是 $\cos(\alpha+\beta)$，得到所需结论；若 $\alpha+\beta\ge\pi/2$，结论由 $A_B\le\pi/2$ 直接成立。这里仅同时对齐了与中间点相接的两条边。

对收缩性，选取达到输入保真度的两个纯化。在被作用的系统上施加 $\mathcal N$ 的同一 Stinespring 等距，内积不变；把输出旁边的环境也并入辅助空间，便得到 $\mathcal N\rho,\mathcal N\sigma$ 的两个纯化。因此输出的最大重叠至少等于该输入重叠。

### 6.2 完整 qubit 混合态几何：半径为 1/2 的三维上半球

### 定理 6.3（二维矩阵的球面提升）

写 $\rho_r=(I+r\cdot\boldsymbol\sigma)/2$，其中 $r\in\mathbb R^3$、$|r|\le1$。定义

$$
R(r)=\bigl(r,\sqrt{1-|r|^2}\bigr)\in S^3_+\subset\mathbb R^4.
$$

则

<a id="eq-c121-qubit-fidelity"></a>

$$
\begin{aligned}
f(\rho_r,\rho_s)^2
 &=\frac{1+r\cdot s+\sqrt{1-|r|^2}\sqrt{1-|s|^2}}2,
\end{aligned}
\tag{28}
$$

<a id="eq-c121-qubit-angle"></a>

$$
\begin{aligned}
A_B(\rho_r,\rho_s)
 &=\frac12\arccos\bigl(R(r)\cdot R(s)\bigr).
\end{aligned}
\tag{29}
$$

因此 $r\mapsto R(r)/2$ 把全部 qubit 态的 Bures 角几何等距实现为半径 $1/2$ 的闭上半球，内在维数为 $3$，嵌入空间为 $\mathbb R^4$。在 $|r|<1$ 内，其线元为

<a id="eq-c121-bures-metric"></a>

$$
ds^2=\frac14\left(dr\cdot dr+
       \frac{(r\cdot dr)^2}{1-|r|^2}\right).
\tag{30}
$$

**证明。**
令 $M=\sqrt\rho\,\sigma\sqrt\rho\ge0$，其两个特征值为 $\lambda_1,\lambda_2$，允许为零。则

$$
f(\rho,\sigma)^2
 =(\sqrt{\lambda_1}+\sqrt{\lambda_2})^2
 =\operatorname{Tr}(\rho\sigma)+2\sqrt{\det\rho\det\sigma}.
$$

由 Pauli 矩阵的迹关系，$\operatorname{Tr}(\rho_r\rho_s)=(1+r\cdot s)/2$；又 $\det\rho_r=(1-|r|^2)/4$，得到式~[(28)](#eq-c121-qubit-fidelity)。设 $\theta=\arccos(R(r)\cdot R(s))\in[0,\pi]$，则 $f^2=(1+\cos\theta)/2=\cos^2(\theta/2)$。由于 $f\ge0$，故 $A_B=\theta/2$。

半径 $1/2$ 的球面大圆短弧长正是 $\theta/2$。若两点不对跖，该短弧是端点向量的非负正弦系数组合，其第四坐标保持非负；若对跖，两点必在赤道，可沿赤道取长为 $\pi/2$ 的半圆。因此闭半球内部的最短路距离也等于该角度。最后

$$
dR=\left(dr,-\frac{r\cdot dr}{\sqrt{1-|r|^2}}\right),
 \qquad ds^2=\tfrac14|dR|^2,
$$

给出式~[(30)](#eq-c121-bures-metric)。

<a id="fig-c121-hemisphere"></a>

```latex
\begin{tikzpicture}[x=2.6cm,y=2.6cm,>=Stealth,font=\small]
  \draw[->,gray] (-1.18,0)--(1.22,0) node[right] {$r_\parallel$};
  \draw[->,gray] (0,-0.10)--(0,1.20) node[above] {$\sqrt{1-|r|^2}$};
  \draw[very thick,teal!70!black] (-1,0) arc[start angle=180,end angle=0,radius=1];
  \draw[dashed,gray] (0,0)--(0.6,0.8);
  \draw[dashed,gray] (0.6,0)--(0.6,0.8);
  \draw[very thick,orange!80!black] (0,1) arc[start angle=90,end angle=53.130102,radius=1];
  \fill[teal!80!black] (-1,0) circle(1.3pt) node[below left] {纯态 $-n$};
  \fill[teal!80!black] (1,0) circle(1.3pt) node[below right] {纯态 $+n$};
  \fill[teal!80!black] (0,1) circle(1.3pt) node[above left] {$I/2$};
  \fill[orange!80!black] (0.6,0.8) circle(1.3pt) node[right] {$\rho_{rn}$};
  \node[below] at (0.6,0) {$r$};
  \node[below] at (0,0) {$0$};
  \node[align=center] at (0,-0.45) {$A_B(I/2,\rho_{rn})=\tfrac12\arcsin|r|$};
\end{tikzpicture}
```

**图 1。**三维上半球的一个大圆截面。图中画的是单位球提升 $R(r)$；Bures 度量取其一半。沿一条 Bloch 直径的态映到这条半圆，纯态在两端，最大混合态在顶点。这是一张二维截面图，不把四维嵌入画成通常三维空间中的实体球。

这个半球是已知的 Uhlmann 几何；Sommers–Zyczkowski 给出了同样的线元和提升公式~ [10](#ref-bures-sommers)。这里从 $2\times2$ 特征值完整推出它，固定了保真度与尺度的约定。纯态 $|r|=1$ 位于赤道 $S^2$，最大混合态 $r=0$ 位于极点；后者到每个纯态的 Bures 角都是 $\pi/4$。内部截面曲率为 $4$。沿一条 Bloch 直径移动，提升后走过半圆；所有概率为零或一的端点也被包含。

还要区分两种距离：式~[(29)](#eq-c121-qubit-angle) 是半球的*测地距离*，而

$$
d_B=2\sin(A_B/2)
$$

是最佳纯化之间的 Hilbert 空间弦距。$d_B$ 与 $A_B$ 有相同的局部线元，但远距离时不同；$d_B$ 也不等于上述半径 $1/2$ 球面在 $\mathbb R^4$ 中的欧氏弦长。这个精确半球结论的对象是 qubit，不能仅凭“二元关系”把所有维数的态空间都判为同一个球面。

### 6.3 三态总有抽象实三维提升；四态已可能失败

### 定理 6.4（三态根保真 Gram 正性）

任意三态 $\rho_1,\rho_2,\rho_3$ 的实矩阵

$$
G=\begin{pmatrix}1&a&c\\a&1&b\\c&b&1\end{pmatrix},\qquad
 a=f_{12},\ b=f_{23},\ c=f_{13},
$$

均为半正定。因此存在三个实单位向量 $v_1,v_2,v_3\in\mathbb R^3$，满足 $v_i\cdot v_j=f_{ij}$。

**证明。**
令 $\alpha=\arccos a$、$\beta=\arccos b$、$\gamma=\arccos c$。对三种排列应用三角不等式，得到

$$
|\alpha-\beta|\le\gamma\le\alpha+\beta.
$$

余弦在 $[0,\pi]$ 上单调，故

$$
ab-\sqrt{(1-a^2)(1-b^2)}\le c
 \le ab+\sqrt{(1-a^2)(1-b^2)}.
$$

从而

$$
\det G=(1-a^2)(1-b^2)-(c-ab)^2
       =1+2abc-a^2-b^2-c^2\ge0.
$$

各一阶和二阶主子式也非负，故 $G\ge0$。若 $a<1$，一个显式提升是

$$
\begin{aligned}
v_1&=(1,0,0),\qquad v_2=(a,\sqrt{1-a^2},0),\\
 v_3&=\left(c,\frac{b-ac}{\sqrt{1-a^2}},
                 \sqrt{\frac{\det G}{1-a^2}}\right).
\end{aligned}
$$

若 $a=1$，则 $\rho_1=\rho_2$、$b=c$，可取 $v_2=v_1$、$v_3=(c,\sqrt{1-c^2},0)$。

这一三态正性是 Fannes 等文献中的已知结果~ [11](#ref-fannes)。它说明任意三条根保真关系都能拼成一个抽象的球面三角形。该结论只保持三个数值，并未把 $v_i$ 的某个部分迹指定为原来的 $\rho_i$。

### 例 6.5（四个纯态使实根保真矩阵出现负方向）

按顺序取

$$
u_1=\lvert 0\rangle,\quad u_2=\lvert +\rangle=\frac{\lvert 0\rangle+\lvert 1\rangle}{\sqrt2},\quad
 u_3=\lvert 1\rangle,\quad u_4=\lvert -\rangle=\frac{\lvert 0\rangle-\lvert 1\rangle}{\sqrt2}.
$$

置 $s=1/\sqrt2$。其根保真矩阵是

$$
G_{\mathrm{abs}}=
 \begin{pmatrix}
 1&s&0&s\\s&1&s&0\\0&s&1&s\\s&0&s&1
 \end{pmatrix}.
$$

向量 $(1,-1,1,-1)^\mathsf T$ 的特征值为 $1-\sqrt2<0$；完整谱为 $1+\sqrt2,1,1,1-\sqrt2$。因此不存在任何实或复 Hilbert 空间中的一组单位向量，其内积全部等于这些非负数。实际振幅 Gram 矩阵为

$$
G_{\mathrm{amp}}=
 \begin{pmatrix}
 1&s&0&s\\s&1&s&0\\0&s&1&-s\\s&0&-s&1
 \end{pmatrix}\ge0,
 \qquad\operatorname{rank} G_{\mathrm{amp}}=2.
$$

四边环的振幅乘积为 $-1/4$，在各顶点乘以任意相位后仍不变。把每条边分别取绝对值，丢掉了闭环约束。

上述四态同时存在于同一个 qubit 半球中，两条结论完全一致：半球的角距离不要求其余弦核 $f_{ij}$ 对任意点数都成为正定核。把一个曲面上的距离全部强行改写为同一组平面坐标的内积，是额外要求。

### 6.4 共同纯化更严格：纯态的环相位与混合态的最优模长

### 命题 6.6（三个纯态不能同时作正实最佳对齐）

取 $u_1=\lvert 0\rangle$、$u_2=\lvert +\rangle$、$u_3=\lvert +i\rangle=(\lvert 0\rangle+i\lvert 1\rangle)/\sqrt2$。不存在三个保持这些纯态边缘的纯化 $\Psi_i$，使全部三条边都满足

$$
\langle\Psi_i,\Psi_j\rangle=f_{ij}>0\quad(i<j).
$$

**证明。**
纯态的任何纯化均为 $\Psi_i=u_i\otimes e_i$。各 $\langle u_i,u_j\rangle$ 非零；若三条边的重叠模长达到 $f_{ij}$，则 $|\langle e_i,e_j\rangle|=1$，所以三个辅助向量共线。其环乘积等于 $1$。因此纯化的三边环乘积等于原来的 Bargmann 不变量

$$
\langle0,+\rangle\langle+,+i\rangle\langle+i,0\rangle
 =\frac{1+i}{4}.
$$

三条内积若全为正实数，环乘积必为正实数，矛盾。

这里禁止的是*同时正实对齐*。取相同辅助向量，三条边的重叠*模长*仍能同时最优；不能把上一命题误说成纯态没有共同的模长最优纯化。混合态则会出现更强的障碍。

### 定理 6.7（三个满秩混合态不能共同达到全部模长最优）

令

$$
R=I/2,\qquad A=(I+Z/2)/2=\operatorname{diag}(3/4,1/4),\qquad
 B=(I+X/2)/2.
$$

无论辅助空间取多大，都不存在这三态的一组纯化，使每一对的重叠模长都等于该对的根保真度。

**证明。**
先证明一个等号条件：若 $M>0$ 且 $T$ 是收缩，那么

$$
|\operatorname{Tr}(MT)|=\operatorname{Tr} M\quad\Longrightarrow\quad T=e^{i\theta}I.
$$

在 $M$ 的特征基中，其正特征值为 $\lambda_j>0$。由

$$
\left|\sum_j\lambda_jT_{jj}\right|
 \le\sum_j\lambda_j|T_{jj}|\le\sum_j\lambda_j,
$$

等号强迫每个 $T_{jj}$ 模长为 $1$、相位相同；收缩矩阵每列范数至多为 $1$，故其他列元素全为零，结论成立。

现在假设存在所要求的纯化。用共同辅助空间的一个酉变换，把 $R$ 的振幅写成

$$
W_R=\frac1{\sqrt2}[\,I\ \ 0\,].
$$

因 $A>0$，写 $W_A=\sqrt A\,C_A$，则 $C_AC_A^*=I$。令 $T_A$ 为 $C_A$ 的前两列，故 $T_A$ 为收缩，且

$$
|\operatorname{Tr}(W_R^*W_A)|=\frac1{\sqrt2}|\operatorname{Tr}(\sqrt A\,T_A)|
 \le\frac1{\sqrt2}\operatorname{Tr}\sqrt A=f(R,A).
$$

要达到最优，刚才的等号条件迫使 $T_A=e^{i\alpha}I$；由 $C_AC_A^*=I$，额外的列全为零。因此 $W_A=e^{i\alpha}[\,\sqrt A\ \ 0\,]$。同理，$W_B=e^{i\beta}[\,\sqrt B\ \ 0\,]$。

设 $a=(\sqrt3+1)/4$、$b=(\sqrt3-1)/4$，则 $\sqrt A=aI+bZ$、$\sqrt B=aI+bX$。两个振幅之间只能达到

$$
|\operatorname{Tr}(W_A^*W_B)|=\operatorname{Tr}(\sqrt A\sqrt B)
 =2a^2=\frac{2+\sqrt3}{4}
 <\frac{\sqrt{14}}4=f(A,B).
$$

末式由式~[(28)](#eq-c121-qubit-fidelity) 得到；严格不等式等价于 $4\sqrt3<7$。这与第三条边也达到最优矛盾。

同一组三态恰是项目 NMLW 新模块的分离实例。若 $F_U$ 是三个二元根保真度的平均，$F_M$ 是先选*同一个*有限 POVM，再平均读出分布的三个根保真度并取下确界，则项目给出

$$
F_U(R,A,B)=\frac{2\sqrt6+2\sqrt2+\sqrt{14}}{12}
 <\frac{24}{25}\le F_M(R,A,B).
$$

原始论文的 Proposition~5.44 给出 $F_M\ge F_U$，Remark~5.45 提出能否严格大于的问题；项目模块给出该实例的严格分离~ [3](#ref-nmlw)、[2](#ref-repo-nmlw)。共同 POVM 的障碍与上面共同纯化的障碍分别限制不同对象。本节没有宣称两者等价，也没有用一个三态标量 Gram 矩阵的正性替代其中任何一个共同实现条件。

### 6.5 共同恢复如何保住所有内部参考上的二元角几何

### 引理 6.8（从迹距到角误差的自足界）

令 $D(\rho,\sigma)=\frac12\|\rho-\sigma\|_1$。则

$$
f(\rho,\sigma)\ge\operatorname{Tr}(\sqrt\rho\sqrt\sigma)\ge1-D(\rho,\sigma).
$$

**证明。**
第一步由迹范数支配迹得到。对第二步，令 $A=\sqrt\rho$、$B=\sqrt\sigma$、$C=A-B$，并取 $S=\operatorname{sign}C$。$S$ 是 Hermitian 收缩，故

$$
\|A^2-B^2\|_1\ge\operatorname{Tr}\bigl(S(A^2-B^2)\bigr)
 =\operatorname{Tr}\bigl(|C|(A+B)\bigr)\ge\operatorname{Tr} C^2.
$$

最后一个不等式的差恰为 $2\operatorname{Tr}(C_+B)+2\operatorname{Tr}(C_-A)\ge0$。由于 $\operatorname{Tr} C^2=2-2\operatorname{Tr}(AB)$，所求不等式成立。

### 定理 6.9（共同回接给出全参考近等距）

设 $\mathcal N:A\to B$、$\mathcal R:B\to A$ 是同一对固定通道，且

$$
\|\mathcal R\mathcal N-\operatorname{id}_A\|_\diamond\le\delta,\qquad0\le\delta\le2.
$$

这里的 diamond 范数*没有除以 $2$*。对任意有限内部参考 $Z$，以及任意 $A\otimes Z$ 上的两态 $\rho,\sigma$，记 $\mathcal N_Z=\mathcal N\otimes\operatorname{id}_Z$，则

<a id="eq-c121-angle-stability"></a>

$$
\begin{aligned}
0&\le A_B(\rho,\sigma)-A_B(\mathcal N_Z\rho,\mathcal N_Z\sigma)
 \le2\arccos(1-\delta/2),
\end{aligned}
\tag{31}
$$

<a id="eq-c121-trace-stability"></a>

$$
\begin{aligned}
D(\rho,\sigma)-\delta
 &\le D(\mathcal N_Z\rho,\mathcal N_Z\sigma)\le D(\rho,\sigma).
\end{aligned}
\tag{32}
$$

尤其，$\delta=0$ 时保留全部内部参考上的每一个二元角度与迹距。

**证明。**
记 $M=(\mathcal R\mathcal N)\otimes\operatorname{id}_Z$。diamond 界给出 $D(\rho,M\rho)\le\delta/2$，由前引理

$$
A_B(\rho,M\rho)\le\arccos(1-\delta/2),
$$

对 $\sigma$ 同样成立。连续两次使用三角不等式，再使用 $\mathcal R\otimes\operatorname{id}_Z$ 的角度收缩，得到

$$
A_B(\rho,\sigma)
 \le A_B(\rho,M\rho)+A_B(M\rho,M\sigma)+A_B(M\sigma,\sigma)
 \le2\arccos(1-\delta/2)+A_B(\mathcal N_Z\rho,\mathcal N_Z\sigma).
$$

另一方向来自 $\mathcal N_Z$ 的角度收缩。将角度替换为迹距，同一三角论证给出式~[(32)](#eq-c121-trace-stability)；迹距收缩可由 $D(\rho,\sigma)=\sup_{0\le F\le I}|\operatorname{Tr} F(\rho-\sigma)|$ 及通道伴随保持效果区间直接得到。

式~[(31)](#eq-c121-angle-stability) 描述共同回接的几何后果，无须为每个未知输入重新选择恢复，也无须先把所有态的最佳纯化相位拼成一张全局坐标图。它仍是条件定理：有限比较证书提供的误差与维数界必须真正满足前面的假设；观测者可取得的内部参考也必须按本文接口给定。

**白话。**可以把一个观察者的读出想成把整套关系搬到另一处。只要每两件东西单独比较，往往都能找到一个最好看的角度；三件东西的三个数值，甚至总能画成一个三维球面上的三角形。但这不保证三次比较来自同一套实际对齐：绕一圈可能剩下相位，混合态还可能连三条边的最佳重叠大小都不能同时达到。共同回接要求更具体：观察者用同一套回接方法，把任何输入连同它内部保留的参照关系一起接回来。接得精确，所有这些二元角度都不变；接得有小误差，角度的变化就有统一上界。对于最小的复二态系统，这整套可比较关系恰好住在一个三维半球上：纯态在赤道，混合态往极点走。半球给出画面，共同回接给出约束，闭环与共同实现的反例则告诉我们哪些看似自然的加强其实不能成立。

<a id="section-7"></a>

## 7. 候选与通常有限量子力学的完整推导接口

<a id="sec-c121-qm"></a>

本节只使用已列出的对象、概率与过程接口。完整参考相容已在定理 [2.1](#thm-c121-kraus) 中给出 Kraus 与内部等距表示；完整内容转接的有限比较条件又给出共同恢复与正常形。对象选择及某个门是否实际可用，仍各有自己的前提。

### 7.1 状态也是一个读口：正关系、Hilbert 空间与 Born 规则

### 命题 7.1（从关系核构造振幅空间）

设历史标签集合 $S$ 带复核 $K$，满足所有有限矩阵 $[K(s_i,s_j)]\succeq0$。在有限形式和 $\sum c_s[s]$ 上定义

$$
\left\langle\sum c_s[s],\sum d_t[t]\right\rangle
 =\sum_{s,t}\overline{c_s}d_tK(s,t).
$$

商去零范数向量并完备化，得到 Hilbert 空间 $H_K$ 与向量 $v_s$，满足 $\langle v_s,v_t\rangle=K(s,t)$；以这些向量的闭线性包为全部空间时，该实现唯一到一个酉同构。

**证明。**
有限正性给出非负半内积。对 $u+t v$ 的范数平方使用判别式得到 Cauchy–Schwarz 不等式，所以零范数向量与全部向量正交，商内积良定义。若另一组 $w_s$ 有同一核，映射 $\sum c_sv_s\mapsto\sum c_sw_s$ 保持范数，因而良定义；稠密线性包上的等距延拓给出所述酉映射。

若历史来自有限 $*$-代数 $\mathcal A$，且 $K(a,b)=\omega(a^*b)$，则商空间还保留左作用 $\pi(a)[b]=[ab]$。在 $C^*$-对象中，$a^*a\le\|a\|^2I$ 保证此作用有界，单位向量 $\xi=[I]$ 满足 $\omega(a)=\langle \xi,\pi(a)\xi\rangle$。这就是有限 GNS 构造的具体形式。它重建某个状态的循环表示，不把 $\Omega$ 宣告为该单个向量，也不把满秩混合态的 $d^2$ 维 GNS 空间误当成 $M_d$ 的 $d$ 维不可约振幅空间。

### 定理 7.2（效果概率的 Born 表示）

在 $M_d(\mathbb C)$ 的所有效果上，若 $w(I)=1$、$w(F)\ge0$，且

$$
w(F+G)=w(F)+w(G)\qquad(F,G\ge0,\ F+G\le I),
$$

则存在唯一密度矩阵 $\rho\succeq0$、$\operatorname{Tr}\rho=1$，使

$$
w(F)=\operatorname{Tr}(\rho F).
$$

反向每个密度矩阵给出这样的赋值。极端状态恰好是秩一投影，纯态间的射线测试概率为 $|\langle \phi,\psi\rangle|^2$。

**证明。**
细分可加性给 $w(F/n)=w(F)/n$，继而给有理尺度齐次性；正性给单调性。用有理数从两侧逼近 $t\in[0,1]$，即得 $w(tF)=t w(F)$，无须另假设连续。
对任意 $A\ge0$，取 $n$ 使 $A/n\le I$，定义 $f(A)=n w(A/n)$；齐次性保证不依赖 $n$。再定义 $f(A-B)=f(A)-f(B)$，利用正锥上的可加性验证其良定义，得到自伴部分上的实线性正泛函，再唯一复线性延拓。有限维迹配对给唯一 $\rho$；测试所有秩一投影保证 $\rho\ge0$，$f(I)=1$ 给迹归一化。
若 $\rho$ 至少有两个正本征值，可向两方向转移一个足够小权重，写成两不同状态的平均，故非极端。秩一态若是两正状态的平均，则其正交补在两态中均有零期望，强制两态都支撑于同一条射线，因而相同。

这是效果版 Gleason 论证的有限形式 [12](#ref-busch2003)。作为映射 $\omega:\mathcal A\to\mathbb C$，一个状态正是候选的标量终端读口；其二元比较核是 $K(a,b)=\omega(a^*b)$。复数域和全部效果的可加语义已经列入接口，不能称它们也由“归一化”独自推得。

### 7.2 观测、一般测量及状态更新

经典结果集合含 $m$ 个标签时，其代数为 $\mathbb C^m$。一个合法测量读口 $\Phi:\mathbb C^m\to M_d$ 由 $F_j=\Phi(e_j)$ 给出，满足

$$
F_j\succeq0,\qquad\sum_jF_j=I,\qquad
 p(j|\rho)=\operatorname{Tr}(\rho F_j).
$$

因此 POVM 是同一读口定义的交换输出特例。反向任意这样的效果族都给合法读口：若 $[c_{ij}]\in M_n(\mathbb C^m)$ 为正，则每个标签处的数值矩阵都正，故 $[\sum_j c_{ab}(j)F_j]$ 为正。

锐测量取彼此正交的投影 $P_j$，并给各结果一个实读数 $a_j$，便得到自伴算符 $A=\sum_j a_jP_j$，平均读数为 $\operatorname{Tr}(\rho A)$。反向，有限维自伴算符的谱分解给出这种锐测量。因此“可观测量由自伴算符表示”是效果与实读数的这一对应，而不是把每个一般测量都限制成投影测量。

若同时保留测量后的量子输出，则结果 $j$ 对应完全正分支

$$
\mathcal I_j(\rho)=\sum_rK_{jr}\rho K_{jr}^*,\qquad
 \sum_{j,r}K_{jr}^*K_{jr}=I.
$$

完整输出可以写成 $\bigoplus_j\mathcal I_j(\rho)$，它仍是一条通道。读到 $j$ 后的条件态为 $\mathcal I_j(\rho)/p_j$，前提是 $p_j>0$。这个归一化公式描述已取得记录后的条件化；它不声称选中分支本身仍是线性保迹过程。不同仪器可以给同一个 POVM，因而仅知道概率不能唯一决定扰动。

### 定理 7.3（理想锐读出为何给出 Lüders 更新）

设完全正分支 $\mathcal I$ 的效果是投影 $P$，即 $\operatorname{Tr}\mathcal I(\rho)=\operatorname{Tr}(P\rho)$。再要求对每个单位 $\psi\in\operatorname{Ran} P$，$\mathcal I(\lvert \psi\rangle\langle \psi\rvert)=\lvert \psi\rangle\langle \psi\rvert$。则

$$
\mathcal I(\rho)=P\rho P.
$$

**证明。**
写 $\mathcal I(\rho)=\sum_rK_r\rho K_r^*$。效果等式给 $\sum K_r^*K_r=P$，所以每个 $K_r$ 在 $\ker P$ 上为零。对 $\psi\in\operatorname{Ran} P$，一组正秩一项之和支撑于 $\mathbb C\psi$，迫使每个 $K_r\psi$ 均与 $\psi$ 共线。一个线性映射若保持子空间内每一条射线，就在该子空间上为标量：比较任意两个独立向量及其和即可。故 $K_r=c_rP$，且 $P\ne0$ 时 $\sum|c_r|^2=1$。代回即得结论；$P=0$ 时所有 $K_r=0$。

这里没有预设单 Kraus 算子。额外的理想性条件是“不改变该结果子空间内部的每条射线”；只要求结果可重复，还允许在子空间内作非平凡酉旋转，并不足以指定 Lüders 仪器。

### 7.3 复合系统、纠缠及可逆运动

### 命题 7.4（独立全矩阵部门的复合）

设 $M_d(\mathbb C)$、$M_m(\mathbb C)$ 以含幺复线性 $*$-嵌入进入同一个非零结合 $*$-代数；两个像彼此交换并生成该代数。则所生成代数为 $M_{dm}(\mathbb C)$。

**证明。**
映射 $a\otimes b\mapsto\iota_A(a)\iota_B(b)$ 由交换性成为满射 $*$-同态。矩阵单位的张量乘积是 $M_{dm}$ 的矩阵单位，且 $M_{dm}$ 为单代数：任一非零双边理想中的非零矩阵元，通过左右矩阵单位可生成所有矩阵单位。因此该含幺非零同态的核为零。

“共同复中心、独立子代数、生成性”承担张量复合的输入。不是任意两个内部窗口都独立。由一个二元块反复独立复合得到 $M_{2^n}$，允许秩 $d$ 的角落即可得到任意 $M_d$。张量正态包含纠缠态；例如 Bell 态不能写成产品态的凸和，因为纯态若可凸分解，各分量必须沿同一射线，而该射线不是产品向量。

有限二元证书章节已经从候选的过程条件推得：一个同维过程若保住指定两类完全可区分关系，必须是酉共轭。完整振幅过程的等距性也由 Kraus 扩充直接得到，不另假设“波函数的每个分量必须线性演化”。

若进一步*供应一个*连续的完整酉群 $U(t+s)=U(t)U(s)$、$U(0)=I$，有限维下所有 $U(t)$ 交换且正规，可同时对角化。每个对角元是实加法群的连续单位模特征，故为 $e^{-i\omega_jt}$；由局部连续辐角和加法性可直接证明。于是存在自伴 $H$，

$$
U(t)=e^{-itH/\hbar},\qquad
 i\hbar\,\frac{d}{dt}\psi(t)=H\psi(t).
$$

时间参数、连续群的供应、具体 $H$ 与作用量单位 $\hbar$ 均没有由静态比较关系决定。静态内生关系与具体动力学选择不可互换。

### 7.4 两项直接可算的量子约束

### 命题 7.5（不确定关系来自二元正比较）

对自伴 $A,B$ 与任意状态 $\omega$，有

$$
\operatorname{Var}_\omega(A)\operatorname{Var}_\omega(B)
 \ge\left|\omega\bigl((A-\omega(A)I)(B-\omega(B)I)\bigr)\right|^2
 \ge\frac14|\omega([A,B])|^2.
$$

**证明。**
令 $X=A-\omega(A)I$、$Y=B-\omega(B)I$。状态的二元 Gram 矩阵
$\left(\begin{smallmatrix}\omega(X^2)&\omega(XY)\\\omega(YX)&\omega(Y^2)\end{smallmatrix}\right)$ 为正，行列式非负给出第一项。又 $\omega(YX)=\overline{\omega(XY)}$，所以 $2i\operatorname{Im}\omega(XY)=\omega([A,B])$，给出第二项。

### 命题 7.6（独立两端的 CHSH 约束）

若 $A_0,A_1$ 与 $B_0,B_1$ 分别为两独立量子部门的自伴反射，即平方均为 $I$，则

$$
S=A_0\otimes(B_0+B_1)+A_1\otimes(B_0-B_1)
 \quad\text{满足}\quad \|S\|\le2\sqrt2.
$$

该界在两个量子比特中可以达到。

**证明。**
直接展开得 $S^2=4I-[A_0,A_1]\otimes[B_0,B_1]$；每个交换子范数至多为 $2$，故 $\|S^2\|\le8$。取 $A_0=Z,A_1=X$、$B_0=(Z+X)/\sqrt2,B_1=(Z-X)/\sqrt2$，并在 Bell 态 $(\lvert 00\rangle+\lvert 11\rangle)/\sqrt2$ 上求期望，得到 $2\sqrt2$。若四个结果预先取定为局部数值 $\pm1$，同一表达式绝对值只能为 $2$；对这样的赋值作概率混合仍不超过 $2$。

这些是候选重构出的通常量子理论的约束，不是新的实验偏离预言。要声称不同于现有量子力学的物理预测，还须修改明确的结构输入并计算其可区分后果。

### 7.5 可复用的推导清单

| 通常的量子结构 | 本稿的推导入口 | 仍然承重的输入 |
|---|---|---|
| Hilbert 振幅与射线 | 全有限正核的商空间；$M_d$ 不可约模块 | 复对象选择、可叠加历史语义 |
| 密度矩阵、Born 规则 | 效果的正、归一化及细分可加 | 所有相关效果的同一赋值 |
| POVM 与仪器 | 交换结果代数与带记录的完全正分支 | 实际结果标签与门供应 |
| 完全正性及 Kraus 形式 | 完整参考相容与有限 Choi 构造 | 全部必要有限参考兼容 |
| 张量复合及纠缠 | 共同复中心上的交换生成关系 | 独立性与复合供应 |
| 可逆门 | 有限正交态对证书、满代数恢复 | 同一完整通道、同维时为酉 |
| Lüders 更新 | 锐效果加每条内部射线不受扰动 | 理想测量条件 |
| Schrödinger 方程 | 连续完整酉群的谱分解 | 时间、群、$H$ 及单位选择 |

**白话。**状态是一种读口，测量是一种把问题送到结果标签的读口，运动也是一种把后面的问题回拉到前面的读口。要求同一来源的全部比较在参考接续后仍合法，并要求完整转接保住连通的二元清单，就把读出、完整记录和共同回接接成同一套定义。要得到具体的物理世界，还必须说哪些对象、哪些复合、哪些钟和哪些门实际存在；这部分不会因为把公理改叫定义就自动消失。

<a id="section-8"></a>

## 8. 内生观察、有限证据与量子场接口

<a id="sec-c121-internal-observers"></a>

### 8.1 从有限次数读数取得条件性的恢复保证

前面的 $\varepsilon$ 是真实过程概率的上界，不能把样本频率直接代入当成真值。若额外有重复实验的独立、同分布及装置稳定合同，可以给出有限样本版本；这些统计条件不由静态量子公理自行供应。

### 命题 8.1（固定二元清单的同时置信界）

预先固定 $m$ 对输入与各对的一个二元效果，共有 $2m$ 个逐态错误概率。每种条件独立重复 $n$ 次，误差频率为 $\widehat e_j$。对 $0<\alpha<1$，令

$$
t=\sqrt{\frac{\log(2m/\alpha)}{2n}},\qquad
 \overline e_j=\min\{1,\widehat e_j+t\}.
$$

则以至少 $1-\alpha$ 的概率，所有 $e_j\le\overline e_j$ 同时成立。若这些上界都不超过 $\varepsilon\le1/2$，前文相应的图证书与恢复界便具有同一置信保证。

**证明。**
对 Bernoulli 变量 $X$，$g(s)=\log\mathbb E e^{s(X-\mathbb EX)}$ 有 $g(0)=g'(0)=0$。指数倾斜后的 Bernoulli 方差至多 $1/4$，故 $g''(s)\le1/4$，积分得 $g(s)\le s^2/8$。独立重复与指数 Markov 不等式于是给

$$
\Pr(e_j-\widehat e_j\ge t)\le e^{-2nt^2}.
$$

对 $2m$ 种条件取并集界，失败概率至多 $2m e^{-2nt^2}=\alpha$。无须不同实验条件彼此独立，只有每个条件内部的重复合同被用于此证明。

星形证书有 $m=d(d-1)/2+d-1$ 对输入。这个计数不包括制备和读口本身的标定成本。实际条件若漂移、有记忆或被自适应选择，须使用适合那种协议的统计界，不能沿用本命题。即使观察到零次错误，有限 $n$ 的上界仍通常大于零，所以不能以有限次数宣称精确酉性。

### 8.2 自指观察者可以局部复位，不能全局擦除未知输入

### 命题 8.2（纯自指寄存器的完整实现）

若完整等距 $V:H\to S\otimes E$ 对任意输入纯态都令可见寄存器 $S$ 的约化态为同一纯态 $P_s$，则存在等距 $W:H\to E$，使

$$
V\psi=s\otimes W\psi.
$$

因此 $\dim E\ge\dim H$，所有未知输入关系都转入另一份内部记录。

**证明。**
约化态纯意味着 $V\psi$ 在 $s^\perp\otimes E$ 上没有分量。置 $W=(\langle s\rvert\otimes I)V$ 得到分解；$V^*V=I$ 给 $W^*W=I$。

所以“从任意态，包括某个给定整体态，运行后得到同一个自指起点”有一个合法的*局部*解释：指定寄存器复位，完整输入转入记录。若把它说成没有其他记录的全局酉复位，两正交输入会被映成同一向量，立即违反内积保持。内容地址编码可承担经典可读标志和协议自描述；它不能代替未知量子态的无损复制、共同回接或记录供应证明。

### 8.3 无全知视角应落实为可辨认模型的约束

### 命题 8.3（一个观察者究竟能够认证什么）

设 $\mathcal M$ 为与内部规则相容的模型族，$r(M)$ 为观察者可得记录，$T(M)$ 为他希望确定的目标。存在仅依赖记录的函数 $f$，使 $T=f\circ r$，当且仅当

$$
r(M)=r(M')\Longrightarrow T(M)=T(M').
$$

**证明。**
必要性直接代入。反向，对实际记录像中的每个 $u$，选任一 $r(M)=u$ 的模型，定义 $f(u)=T(M)$；同一记录纤维上目标常值保证良定义。

这比“除非完整包含另一个观察者，否则永远不能确定任何交集”更准确。两人可以有一个已认证的共同经典寄存器 $X$，同时各有对方不知道的私人部门；谁都不完整包含谁，却能确定 $X$ 属于共同内容。若问题改为*完整交集究竟多大*，而两个相容模型具有同样可见记录、不同交集，当前观察者就不能确定完整答案。前节 $T_{BA}=N_B\mathcal R_A$ 的共同来源是已标定数据，不能用转换公式反向凭空认证这一数据。

“两条序列逼近同一个 $\Omega$”也应拆成可证明的部分。若有递增、保单位嵌入的有限代数

$$
\mathcal A_1\subset\mathcal A_2\subset\cdots
$$

及相容状态 $\omega_{n+1}|_{\mathcal A_n}=\omega_n$，则在并集上定义 $\omega(a)=\omega_n(a)$ 良定义、正且归一化。由状态的 Cauchy–Schwarz 不等式，$|\omega(a)|\le\|a\|$，故它唯一连续延拓到并集的 $C^*$ 完备化。这里真正成立的是*相容有限读口有一个共同状态延拓*。一段实际测量历史是否产生这种嵌套、相容性，以及两观察者是否共尾覆盖同一代数，都要另外证明；任意量子门序列并不自动收敛到同一个纯态。

### 8.4 把原来的二次式直觉修成准确的读取几何

对实数 $a,b$，

$$
a^2+xab+b^2=
 \begin{pmatrix}a&b\end{pmatrix}
 \begin{pmatrix}1&x/2\\x/2&1\end{pmatrix}
 \begin{pmatrix}a\\b\end{pmatrix}.
$$

两个特征值为 $1\pm x/2$。所以等值式取 $1$ 时，$x=0$ 才是通常坐标下的圆；$|x|<2$ 是椭圆；$x=2$ 时为 $(a+b)^2=1$，退化成两条平行直线。$ab$ 对 $a,b$ 联合而言是双线性项，不是线性项。

其中可以保留且加强的直觉是：若 $u,v$ 是两个单位关系向量，

$$
\|au+bv\|^2=a^2+b^2+2ab\operatorname{Re}\langle u,v\rangle,
$$

那么交叉项确实在读取二元关系。令 $x=2\operatorname{Re}\langle u,v\rangle$，正 Gram 条件强制 $|x|\le2$；边界 $x=2$ 表示两个方向重合，而不是一个非退化圆。再把振幅提升为

$$
M(a,b)=\begin{pmatrix}a^2&ab\\ab&b^2\end{pmatrix},
$$

二次读取变成 $\operatorname{Tr}(Q_xM)$，对提升后的关系矩阵是线性的。归一化 $a^2+b^2=1$ 给纯态矩阵，混合化给整个凸态空间。这比“只有出现线性关系才能读”更精确：*振幅的二次关系，在状态关系空间中由线性效果读取。*

### 8.5 从有限量子关系到场，还缺哪一步

真空涨落可以通过关系而非某次实际读出定义。例如对某个有定义的涂抹自伴场量 $A$，

$$
\operatorname{Var}_\omega(A)=\omega(A^2)-\omega(A)^2
$$

可能非零，即使 $\omega(A)=0$。这个方差不需要先假定有人完成测量。场的局域观测还需要系统与探针的耦合；Fewster–Verch 的框架把它精确表述为内部耦合诱导的完全正读口和条件仪器 [13](#ref-fewsterverch2018)。

光子的产生、湮灭以及两个物理偏振自由度也应分清：电磁光子中性且自共轭，两个螺旋度不是正、负电荷的两种光子 [14](#ref-tongqed)、[15](#ref-fermilabphoton)。电子与光子对应的场及表示不同，不能从自指复位等式就识别出标准模型的粒子部门。

一个严格的尺度边界已经出现：有限矩阵不可能满足精确玻色对易关系 $[a,a^*]=I$，因为对两边取迹会得到 $0=d$。进入场论必须处理无限维极限、局域性或因果结构、能量条件、场的交换或反交换关系；进入标准模型还要选择规范结构、物质表示和相互作用。本轮的有限重构不决定这些选择，也未给出区别于通常量子力学的实验偏离预测。

**白话。**观察者是在整体内部不断取得记录。记录能认证什么，就看所有仍与它相容的模型是否给出同一个答案；不能靠一句“都来自整体”跳过这一步。自指寄存器可以回到起点，但未知内容必须在整体的别处留下。有限比较可以带着统计误差走向共同恢复；要把这种结构延伸成量子场，还要真的构造无限尺度、局域接续和动力学，不能只把有限门换一个场的名字。

<a id="section-9"></a>

## 9. 这一轮完成了什么，以及候选的完整白话表述

<a id="sec-c121-synthesis"></a>

本轮只有候选 C121：**指定完整内容转接必须保持同一来源的有限连通二元比较，局部读出必须来自这同一次转接的内部记录遗忘。**在明确的对象、概率与完整参考接口中，有限比较保证一个对全部未知输入共同有效的回接。各项噪声界、几何解释与观察者转换都是这份合同的结论，不是互相替换的新公理。

它的主要计算链是

$$
\begin{aligned}
\text{实际二元错误}\ \longrightarrow\
 \|N^c(\lvert u\rangle\langle v\rvert)\|_1\text{ 的界}
 \ \longrightarrow\ \text{相干图的距离与谱矩阵 }M,\\
 \|N^c-\mathcal S_\tau\|_\diamond\le\delta
 \ \longrightarrow\ \exists\mathcal R:
 \|\mathcal RN-\operatorname{id}\|_\diamond\le2\sqrt{\delta-\delta^2/4},\\
 \text{全部内部参考的二元几何近等距}
 \ \longrightarrow\ \text{有标定的观察者转换与三角误差界}.
\end{aligned}
$$

| 删除的关系约束 | 可核算的后果 |
|---|---|
| 同一个回接，先于未知输入 | 完全擦除也能逐态“恢复”；共同恢复误差仍至少为 $1$。 |
| 实际判别尺度，只看小乘积迹 | 常量高维混合输出的重叠趋零，信息仍全部丢失。 |
| 相干图连通性 | 退相干可抹去不同连通块之间的相位，同时通过全部已列零误差测试。 |
| 固定来源维数的控制 | 逐对错误趋零仍能藏住一项全局退相干，任意回接误差不低于 $1$。 |
| 内部参考相容 | 转置保持单系统全部二元几何，却把 Bell 关系变成带负本征值的矩阵。 |
| 共同实现与逐对最优的区分 | 三态的正 Gram 提升仍不足以取得共同最优纯化；四态的根保真矩阵甚至可不正。 |
| 实际供应与数学存在的区分 | 一个存在的逆映射或 POVM 被误当成观察者已有的门和读口。 |

本稿的几何图像有精确的分工。单个 qubit 的态是三维半球；任意三态的根保真数值有抽象实三维 Gram 提升；整张有限证书是有权连通图及其非负谱矩阵；三个有标定的观察者则形成误差可控的接续三角。它们不是同一个“三维宇宙”，也不能彼此替代。

成熟的 Choi–Stinespring、纠错补性、Bures 几何与信息–扰动定理在本文均注明来源。有限图证书、反例与候选组织方式在本稿中逐步推出，但没有完成穷尽文献比对，因此不提出历史首创权声明。已有量子公理的表示接口已经补齐；从更原生的 $\Omega$ 关系唯一选出那些对象与供应条件，仍没有被证明。下一项精确问题应是*在给定实际稀疏门菜单中构造可执行的共同回接，并控制标定误差*，而不是再把数学存在写成一条更强的口号。

subsection*{完整白话}

addcontentsline{toc}{subsection}{完整白话}

把整体想成一套可以继续接下去的关系，观察者只拿到其中一个窗口。一份内容有很多可能的样子；先看任意两个基本样子还能不能分开，再沿一张连通图，看把两个样子相加、相减以后还能不能分开。要求它们走的是同一次过程，比较用的是实际可接的读口，旁边原有的参照也不能被偷偷破坏。这样，另一份内部记录就不能各自藏着不同的输入答案：零误差时，它只能留下同一份与输入无关的附页，于是存在同一条回路把所有未知内容接回来；有误差时，图上的误差会给这条共同回路一个明确上界。两个观察者各自保住同一块有标定的来源，就能在这块内容上互相转换，绕第三个观察者转一圈的误差也能算。对最小二态系统，这些比较关系可以看成一个三维半球，纯态在赤道，混合态向极点移动。但三个角度能拼成三角形，不保证三次最佳对齐能同时发生；绕圈还可能留下相位。所谓公理内生，就是把这些“同一次、同一份、同一个”的接续关系写成定义之间不能互相矛盾的条件。它使每一步都有可检验的含义；并不免除我们证明哪些对象、哪些门、哪些记录和哪些物理极限实际存在。

<a id="section-10"></a>

## 10. 有限量子原子的实关系选择：前提与完整证明

<a id="sec-local-core"></a>

本附录自足重述前两轮实球形二元块的局部选择步骤，说明主文复矩阵部门的来路。它不同于仓库新近使用 C116 编号的闭环三向回读候选。其范围是实球形二元正锥及下列动力标签条件；它没有证明这些条件由一般正核自动强制成立。这里由三方向乘积形成的中心单位记为 $\jmath$，以区别一般线性算子的符号。

### 10.1 实锥与规范对称变化

### 定义 10.1（二元比较块）

令 $W$ 为有限维实欧氏空间，$V=\mathbb R e\oplus W$、$e=(1,0)$。未归一化的正关系为

$$
C=\{(s,r):s\ge\|r\|\},\qquad
 \langle (s,r),(t,u)\rangle_E=st+r\cdot u.
$$

规范滤片是把 $e$ 送到给定严格正元 $x=(s,r)$ 的欧氏正定、自伴、双向保锥线性变换。双向保锥指变换及其逆都保持 $C$。

### 引理 10.2（规范滤片及其导数）

令 $\delta=\sqrt{s^2-\|r\|^2}>0$。唯一的规范滤片是

$$
P_x=\begin{pmatrix}
 s&r^{\mathsf T}\\
 r&\delta I+rr^{\mathsf T}/(s+\delta)
 \end{pmatrix}.
$$

其一阶响应定义对称乘法

$$
(\alpha,a)\circ(\beta,b)
 =\left.\frac{d}{dt}P_{e+t(\alpha,a)}(\beta,b)\right|_{0}
 =(\alpha\beta+a\cdot b,\alpha b+\beta a).
$$

特别地，$L_a(\beta,b)=(a\cdot b,\beta a)$。

**证明。**
写 $\eta=\operatorname{diag}(1,-I)$。保锥可逆变换 $T$ 保持锥边界，所以对所有单位 $n$，$Q(T(1,n))=0$。将 $T^{\mathsf T}\eta T$ 分块，比较 $n,-n$ 消去非对角块，再比较正交基与它们的二元和，得 $T^{\mathsf T}\eta T=c\eta$；$Te$ 在锥内部给 $c>0$。

若 $T=T^{\mathsf T}\succ0$ 且 $Te=x$，写其右下块为 $B$，便有 $c=\delta^2$、$B^2=\delta^2 I+rr^{\mathsf T}$。正定 $B$ 是右侧唯一正平方根，在 $r^\perp$ 上为 $\delta I$、在 $r$ 方向为 $s$，即显示公式。反过来，该公式的特征值为 $s\pm\|r\|$ 及 $\delta$，全为正；直接相乘验证 $P_x\eta P_x=\delta^2\eta$，且 $P_xe=x$，从而双向保锥。对 $s=1+t\alpha,r=ta$ 求导即得乘法。该乘法满足 Jordan 恒等式，因为 $L_{z^2}$ 是 $L_z$ 的线性组合；其平方锥恰为 $C$，可用互补幂等元 $p_\pm=(1,\pm n)/2$ 对正元分解并开平方验证。

这一构造仍承担球形正锥、欧氏标尺和规范滤片的定义。若赋予它物理实现，还要保留成功权重；双向保正滤片不等于确定性的可逆通道。

### 10.2 二元回路为何强制三维

### 定义 10.3（旁观方向条件）

每个实方向 $a$ 产生 $D_a\in\mathfrak{so}(W)$，$a\mapsto D_a$ 实线性，$D_a a=0$，且 $D\ne0$。要求对全部标签及其线性合成，

<a id="eq-c121-local-spectator"></a>

$$
\boxed{[D_a,D_b]z=0\quad(z\perp a,b).}
\tag{33}
$$

这是完整向量等式。只比较 $z\cdot[D_a,D_b]z$ 没有约束力，因为反对称算子的该自比较总是零。

### 定理 10.4（三维选择）

<a id="thm-c121-local-three"></a>

上述条件强制 $\dim W=3$，且存在 $\kappa>0$，使

<a id="eq-c121-local-loop"></a>

$$
\begin{aligned}
[D_a,D_b]&=-\kappa[L_a,L_b],
\end{aligned}
\tag{34}
$$

<a id="eq-c121-local-square"></a>

$$
\begin{aligned}
D_a^2x&=\kappa\bigl((a\cdot x)a-\|a\|^2x\bigr),
\end{aligned}
\tag{35}
$$

<a id="eq-c121-local-triple"></a>

$$
\begin{aligned}
D_aD_bx&=\kappa\bigl((a\cdot x)b-(a\cdot b)x\bigr),
\end{aligned}
\tag{36}
$$

<a id="eq-c121-local-bracket"></a>

$$
\begin{aligned}
D_{D_a b}&=[D_a,D_b].
\end{aligned}
\tag{37}
$$

按 $D$ 选择取向后，$D_ab=\sqrt\kappa\,a\times b$。

**证明。**
标签线性及 $D_aa=0$ 给 $D_ab=-D_ba$，故 $x\cdot D_ab$ 是交替三形式。令

$$
B(a,b)x=(b\cdot x)a-(a\cdot x)b=[L_a,L_b]x.
$$

交换子 $[D_a,D_b]$ 反对称。式 [(33)](#eq-c121-local-spectator) 使它在 $\operatorname{span}(a,b)^\perp$ 上为零，并保持 $\operatorname{span}(a,b)$；二维反对称算子只有一个方向，所以它是 $B(a,b)$ 的实倍数。

这个倍数不能逐对自由选。取正交基 $e_i$，写 $[D_{e_i},D_{e_j}]=\lambda_{ij}B(e_i,e_j)$。在二元合成标签

$$
a=\sum_i e_i,\qquad b=\sum_i\left(i-\frac{n+1}{2}\right)e_i
$$

上展开，其每个基对系数都是非零的 $j-i$。合成对也必须有一个共同平面比例，比较基系数便得全部 $\lambda_{ij}=\lambda$。双线性将它扩到任意 $a,b$。

将交换子等式作用于 $a$ 并使用反对称性，得

$$
\|D_ab\|^2=-\lambda\bigl(\|a\|^2\|b\|^2-(a\cdot b)^2\bigr).
$$

非平凡性排除 $\lambda=0$，故 $\lambda=-\kappa<0$，并得 [(35)](#eq-c121-local-square)。极化该平方式，加上交换子式，给 [(36)](#eq-c121-local-triple)；再由 $D_{D_ab}x=-D_xD_ab$ 得 [(37)](#eq-c121-local-bracket)。

取正交单位 $u,v$，令 $w=D_uv/\sqrt\kappa$。上式说明 $u,v,w$ 正交归一，且

$$
D_w=\sqrt\kappa(vu^{\mathsf T}-uv^{\mathsf T}),\qquad
 D_w^2=-\kappa(P_u+P_v).
$$

另一方面，式 [(35)](#eq-c121-local-square) 给 $D_w^2=\kappa(P_w-I)$。因此

$$
\boxed{I=P_u+P_v+P_w,}
$$

恰好三个方向覆盖整个 $W$。三维交替三形式只有一个尺度，范数式将其大小固定为 $\sqrt\kappa$；取向由其符号决定。

若去掉 $D\ne0$，任意维度都容许 $D=0$。若只查坐标对，模型 $W=\mathbb R^3\oplus\mathbb R$、$D_ab=(a'\times b',0)$ 会通过；但对 $a=e_1+e_4,b=e_2,z=e_1-e_4$，有 $z\perp a,b$ 而 $[D_a,D_b]z=e_2$。这说明必须检验合成标签。此规则只作用于二元球块，不能把它逐字施加到一般高维系统的全部自伴元。

### 10.3 三方向的有向体积成为内部复数

这里把候选中的“由该块生成的结合保星闭包”说精确：它是非零含幺实结合
$*$-代数 $\mathcal B$，带实线性映射 $\iota:V\to\mathcal B$，满足

$$
\iota(e)=1,\qquad \iota(x)^*=\iota(x),\qquad
 \frac{\iota(x)\iota(y)+\iota(y)\iota(x)}2=\iota(x\circ y),
$$

且 $\iota(V)$ 生成整个 $\mathcal B$。结合性、保星与生成性是这里明确保留的闭包条件；以下证明所有这样的非零闭包都给出同一个代数，不先假设它的维数。

作为实结合闭包的显式构造，用实数对构造 $\mathbb C_\jmath=\{s+\jmath t\}$，其中 $\jmath^2=-1$。记 $\mathcal A=\mathbb C_\jmath\oplus\mathbb C_\jmath^3$，在其上定义

<a id="eq-c121-local-product"></a>

$$
(\alpha,a)(\beta,b)
 =(\alpha\beta+a\cdot b,\alpha b+\beta a+\jmath(a\times b)).
\tag{38}
$$

这里的点积、叉积作复双线性延伸。

### 定理 10.5（内部复代数及最小振幅）

<a id="thm-c121-local-complex"></a>

式 [(38)](#eq-c121-local-product) 给出实八维结合 $*$-代数，伴随为逐分量复共轭，自伴部恰为原来的 $V$。对于正向正交基，

$$
e_ie_j+e_je_i=2\delta_{ij}1,
 \qquad \jmath=e_1e_2e_3,
 \qquad \jmath^2=-1.
$$

因此 $\jmath$ 实际属于三个实方向生成的闭包；该闭包是 $\operatorname{Cl}_{3,0}\cong M_2(\mathbb C)$，最小左理想为 $H\cong\mathbb C^2$。

**证明。**
由三线性，只需在三个实向量上核对结合律。两个括号方式的标量项相同，向量差为

$$
(a\cdot b)c-(b\cdot c)a-(a\times b)\times c+a\times(b\times c)=0,
$$

这是定理 [10.4](#thm-c121-local-three) 的三重积恒等式。共轭将 $\jmath$ 变号，交换向量次序也使叉积变号，故 $(xy)^*=y^*x^*$。直接计算得 $e_1e_2=\jmath e_3$，从而 $e_1e_2e_3=\jmath$，没有再添独立复方向。

映射

$$
\alpha1+z\cdot e\longmapsto
 \begin{pmatrix}\alpha+z_3&z_1-iz_2\\z_1+iz_2&\alpha-z_3\end{pmatrix}
$$

保持乘法与伴随，且每个复二阶矩阵唯一具有这种展开，所以是同构。

还须排除其他闭包把这个代数进一步压小。令 $\operatorname{Cl}_{3,0}$ 为由
$e_i^*=e_i$、$e_ie_j+e_je_i=2\delta_{ij}1$ 定义的含幺实结合 $*$-代数。
反交换关系把全部词约到
$1,e_1,e_2,e_3,e_1e_2,e_1e_3,e_2e_3,e_1e_2e_3$，故其维数至多为八。
上述显式模型由三个 $e_i$ 生成，且实维数为八，所以从这个定义代数到模型的满射必为同构。

任意容许闭包 $\mathcal B$ 的三个生成元也满足这些关系，因而是
$\operatorname{Cl}_{3,0}\cong M_2(\mathbb C)$ 的非零含幺商。$M_2(\mathbb C)$ 作为*实*代数仍然简单：
若双边理想含非零矩阵 $A$，选取非零条目 $a_{ij}$，则
$E_{pi}AE_{jq}=a_{ij}E_{pq}$ 属于该理想；再左乘 $(a_{ij}^{-1})I$，得到每个矩阵单位
$E_{pq}$。左乘 $iI$ 又得到全部 $iE_{pq}$，这些矩阵的实线性张成就是整个代数。
所以商映射的核只能为零或全体；非零含幺目标排除后者。
因此任意容许的生成闭包都与显式模型保星同构，不存在更小的非零商。

令 $p=(1+e_3)/2,q=e_1p$。左理想 $\mathcal A p$ 在中心 $\mathbb C_\jmath$ 上由 $p,q$ 张成，且对 $x=\alpha p+\beta q,y=\gamma p+\delta q$，

$$
x^*y=(\bar\alpha\gamma+\bar\beta\delta)p.
$$

这个系数给正定复内积。矩阵表示说明它是二维且为最小左理想，代数在其上忠实作用。

自伴元 $sI+r\cdot\sigma$ 的特征值是 $s\pm\|r\|$，所以构造后的矩阵正锥恰好恢复原来的 $C$。其归一化截面是三维球，极点是球面；概率与纯态的严格对应见第 [7](#sec-c121-qm) 节。

**白话。**先规定两份方向怎样比较，再比较沿它们前后运动的小回路。回路不能暗中推动和这两个方向都垂直的完整参考；对合成方向也这样要求，两个方向就会带出第三个，而且三个已经覆盖整个二元块。把三个方向按顺序相乘，会得到一个再乘自己就反号的内部关系，它承担复数的作用。这样的复结构有了明确来路；观察者的记录守恒接下来才有可用的物理振幅空间。

有限系统类还允许独立复合以及非零投影支持的角代数。由第 [7](#sec-c121-qm) 节的复合定理，$N$ 个二元原子给 $M_{2^N}(\mathbb C)$。对任意 $d\le2^N$，取秩 $d$ 的投影 $p$，角代数 $pM_{2^N}(\mathbb C)p$ 同构于 $M_d(\mathbb C)$，单位为 $p$。因此在这项系统闭包约定下，全部有限复量子系统均得到构造。支持限制与观察窗口的保单位嵌入是两类接口，不能把改变单位的角嵌入误作同一个共同来源接缝。

<a id="references"></a>

## 参考文献

<a id="ref-repo-orientation"></a>

### [1]

The Omega Institute, *AURIC Composite Comparison Reference-Free Filter Relations V96 Continuation*, §§140–149. 固定快照 `86172888e706177b6c1d135cb12aec3b6d2cdce8`。[不可变理论源码](https://github.com/the-omega-institute/trureturing/blob/86172888e706177b6c1d135cb12aec3b6d2cdce8/docs/develop/theory/AURIC_COMPOSITE_COMPARISON_REFERENCE_FREE_FILTER_RELATIONS_V96_CONTINUATION.md)。相关合并 [e54a4512cdaf](https://github.com/the-omega-institute/trureturing/commit/e54a4512cdaf8733f5e522d0ece9a826ec1dfebe)：固定立方控制与闭环取向。本文已核读新增定义、证明、删除模型与适用边界。仓库此段自称 C118；本文 C121 是对话研究稿编号，两者不混同。

<a id="ref-repo-nmlw"></a>

### [2]

The Omega Institute, *NMLWMeasuredFidelitySeparation.lean*. 同一不可变快照，主要定位为 `uhlmann`、`FU`、`FM`、`claim`、`FU_witness_lt`、`FM_witness_ge` 与 `result`。[不可变 Lean 源码](https://github.com/the-omega-institute/trureturing/blob/86172888e706177b6c1d135cb12aec3b6d2cdce8/D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation.lean)；[项目说明页](https://www.trureturing.org/research/nuradha-mishra-leditzky-wilde-measured-fidelity-gap/)。说明页自身标记其发布版本，本文对定义与见证以固定 HEAD 源码为准；未重新执行 Lean 编译。

<a id="ref-nmlw"></a>

### [3]

T. Nuradha, H. K. Mishra, F. Leditzky and M. M. Wilde, ``Multivariate Fidelities'', *Journal of Physics A: Mathematical and Theoretical* **58**, 165304 (2025). [arXiv:2404.16101v3](https://arxiv.org/html/2404.16101v3)。对应 Definition 5.40、Proposition 5.44 与 Remark 5.45；[doi:10.1088/1751-8121/adc645](https://doi.org/10.1088/1751-8121/adc645)。

<a id="ref-stinespring1955"></a>

### [4]

W. F. Stinespring, ``Positive functions on $C^*$-algebras'', *Proceedings of the American Mathematical Society* **6**(2), 211–216 (1955). [doi:10.1090/S0002-9939-1955-0069403-4](https://doi.org/10.1090/S0002-9939-1955-0069403-4)。本文给出有限矩阵构造，不依赖一般算子代数证明。

<a id="ref-choi1975"></a>

### [5]

M.-D. Choi, ``Completely positive linear maps on complex matrices'', *Linear Algebra and its Applications* **10**(3), 285–290 (1975). [doi:10.1016/0024-3795(75)90075-0](https://doi.org/10.1016/0024-3795(75)90075-0)。

<a id="ref-knill1997"></a>

### [6]

E. Knill and R. Laflamme, ``Theory of quantum error-correcting codes'', *Physical Review A* **55**, 900–911 (1997). [quant-ph/9604034](https://arxiv.org/abs/quant-ph/9604034)；[doi:10.1103/PhysRevA.55.900](https://doi.org/10.1103/PhysRevA.55.900)。有限可恢复正常形为其完整源情形。

<a id="ref-fuchs1999"></a>

### [7]

C. A. Fuchs and J. van de Graaf, ``Cryptographic distinguishability measures for quantum-mechanical states'', *IEEE Transactions on Information Theory* **45**(4), 1216–1227 (1999). [quant-ph/9712042](https://arxiv.org/abs/quant-ph/9712042)。本文采用未平方根保真度，并在统一恢复章节重证所用不等式。

<a id="ref-ksw2008"></a>

### [8]

D. Kretschmann, D. Schlingemann and R. F. Werner, ``The Information-Disturbance Tradeoff and the Continuity of Stinespring's Representation'', *IEEE Transactions on Information Theory* **54**(4), 1708–1717 (2008). [quant-ph/0605009](https://arxiv.org/pdf/quant-ph/0605009)。本文共同收缩、共同环境扩张及恢复界是该成熟理论的有限直接证明，不限制在任意预先固定的最小环境中。

<a id="ref-beny2010"></a>

### [9]

C. B
'eny and O. Oreshkov, ``General Conditions for Approximate Quantum Error Correction and Near-Optimal Recovery Channels'', *Physical Review Letters* **104**, 120501 (2010). [arXiv:0907.5391](https://arxiv.org/pdf/0907.5391)。本文证明 Theorem 1 的恒等目标特例；根保真度和范数归一化在正文中明定。

<a id="ref-bures-sommers"></a>

### [10]

H.-J. Sommers and K.
.{Z}yczkowski, ``Bures volume of the set of mixed quantum states''. [quant-ph/0304041v3](https://arxiv.org/pdf/quant-ph/0304041)，式 (2.11)–(2.12) 给出二阶态的 Bures 线元与半径 $1/2$ 的半球提升；该文将相关半球观察归于 Uhlmann 的早期工作。本文给出自足的 $2\times2$ 推导，不主张此几何新颖。

<a id="ref-fannes"></a>

### [11]

M. Fannes, F. de Melo, W. Roga and K.
.{Z}yczkowski, ``Matrices of fidelities for ensembles of quantum states and the Holevo quantity'', *Quantum Information and Computation* **12**, 472–489 (2012). [arXiv:1104.2271](https://arxiv.org/pdf/1104.2271)。本文仅消费三态根保真矩阵正性，不把该原文中作为猜想提出的普遍 Holevo 熵界当作已给前件。

<a id="ref-busch2003"></a>

### [12]

P. Busch, ``Quantum states and generalized observables: a simple proof of Gleason's theorem'', *Physical Review Letters* **91**, 120403 (2003). [quant-ph/9909073](https://arxiv.org/abs/quant-ph/9909073)。本文效果可加的有限证明包括二阶系统，所用赋值域是全部效果，不是仅锐投影。

<a id="ref-fewsterverch2018"></a>

### [13]

C. J. Fewster and R. Verch, ``Quantum fields and local measurements''. [arXiv:1810.06512v3](https://arxiv.org/abs/1810.06512) (2020)。系统–探针内部耦合、完全正诱导读出与按因果顺序合成的仪器。

<a id="ref-tongqed"></a>

### [14]

D. Tong, *Quantum Field Theory*, Chapter 6, ``Quantum Electrodynamics'', §§6.1–6.2. [作者课程原文](https://davidtong.org/pdfs/teaching/quantum-field-theory/qft6.pdf)。电磁场的规范结构、量子化及两个物理偏振自由度。

<a id="ref-fermilabphoton"></a>

### [15]

Fermilab, ``Charge, Spin and Mass of Fundamental Particles'', *Physics Questions People Ask Fermilab*. [机构原始答复](https://www.fnal.gov/pub/science/inquiring/questions/mass_information.html)。本文仅引用光子无电荷且与其反粒子相同的基本区分，不消费该历史页的其他实验数值。
