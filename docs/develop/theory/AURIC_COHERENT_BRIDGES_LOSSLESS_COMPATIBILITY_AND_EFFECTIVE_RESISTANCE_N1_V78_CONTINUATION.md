# 候选 N1：相干桥的整体无损相容

二元三轴、共同记录与有效电阻证书

AURIC v78 后续研究：定义、定理与证明

研究续稿

2026 年 11 月 2 日

## 摘要

本轮只处理一个完整候选：在已声明的内部截口中，单个基方向保持原状之后，
完整量子概念是否无损，应由覆盖全部方向的二元相干比较网来判定；
近似无损则必须同时保留边缺陷与整张网的传播几何。

承接项目已证的复正核、效果、线性分支、内部记录等距、无信息泄漏恢复判据和连通探针刚性，
本文先把基保持过程写成内部记录的 Gram 通道。
每条相干桥的三维读出为 $(\operatorname{Re}g_{jk},\operatorname{Im}g_{jk},0)$。
连通边全部满相干，当且仅当整个过程是一个对角酉；相位校准后为恒等。
此精确机制归于既有结构的直接抽取。

本轮集中推进可带误差使用的接口：对任意加权连通比较网，
校准后桥返回缺陷的总能量为 $\mathcal E_\theta$，
有效电阻半径为 $R_*$，则完整、未除二的 diamond 误差不超过
$\min\{2,4\sqrt{R_*\mathcal E_\theta}\}$。
基方向也仅近似返回时，给出只涉及原始误差平方根的完整扩展。
长链上的可逆相位坡度与真正记录泄漏分别说明图尺度不能删除。
所有记录与参考都处于 $\Omega$ 内，未读取只表示当前截口不保留；
数学比较实现与可用控制仍按项目既有接口区分。

## 目录

- [1. 唯一候选、既有供应与本轮增量](#section-1)
- [2. 共同内部接口与基保持的记录形式](#section-2)
- [3. 每条桥都落在三维球上：相位转动与相干损失](#section-3)
- [4. 零误差闭合：连通满相干等价于整体可逆](#section-4)
- [5. 撤去前件，冲突具体落在哪里](#section-5)
- [6. 同一相位校准下的关系能量](#section-6)
- [7. 更大结构：关系网自身的有效电阻](#section-7)
- [8. 主定理：有限二元缺陷控制整个概念](#section-8)
- [9. 基方向也有误差时：完整扩展而不隐藏理想前件](#section-9)
- [10. 两条长链反例：为什么局部很小不等于整体很小](#section-10)
- [11. 候选属于哪一个更大结构](#section-11)
- [12. 本轮候选的判定与完整白话](#section-12)

<a id="section-1"></a>

## 1. 唯一候选、既有供应与本轮增量

### 1.1 候选 N1 的完整陈述

> **相干桥的整体无损相容。**
> 一个内部截口若把一组可区分方向定义为原来的方向，
> 那么它对这些方向张成的完整量子概念无损，
> 当且仅当一张覆盖全部方向的连通二元比较网保持满相干。
> 同一网中的相位须来自共同的内部记录关系；
> 近似无损的认证同时使用边缺陷与该网的传播几何。

后文把“无损”精确定义为存在全输入 CPTP 左逆，
并在基保持的同维接口中证明上述等价。
允许误差时给充分认证界，不把该上界称为最优充要阈值。
这是一个候选及其精确、近似两个版本，没有另加第二个候选。

在已建成的量子表示内，本候选将被证明可化为定义间的约束，
因而不再需要作为另一条独立物理前件。
本轮不要求所有内部截口都无损：哪些截口可以这样命名，
由它们自身的关系数据决定。

### 1.2 先保留已证结果

本轮公开仓库固定在提交

`59e9df9c5e49bc59e1b46a0240f52820acd0f453`。

定向核读得到下表；它用于准确承接，不作为全库或外部文献优先权认证。

| 已有位置 | 已证内容 | 本轮使用方式 |
| --- | --- | --- |
| OMEGA §8 | 全输入恢复等价于未读记录无逻辑信息 | 作为已完成的恢复接口 |
| OMEGA §10；ProbeComponentRigidity | 张成且非正交图连通的纯探针锁定恒等通道 | 精确零误差传播归于既有机制 |
| Optimal Measurement Recovery §6 | 保留可见旗标时的 KL 条件及全输出解码 | 不重开一般纠错重构 |
| Environment Record Memory §26 | 实际词的最大共同可纠正代数 | 不把对易子判据再次认领为新结果 |
| OMEGA 追加命题 35--37 | 两完整基的谱隙、纠缠保真度和端口界 | 图验证方法已有；本轮改用记录边距离与电阻 |
| 前轮 v78 读出闭合稿 | 事件到效果、指定后继到分支、正核结果树 | 提供当前共同表示与内部记录等距 |

仓库各项的可复核位置见文末固定链接[2](#ref-omega)、[3](#ref-recovery)、[4](#ref-memory)、[5](#ref-lean)；
前轮读出闭合稿为本对话既有续稿，另列于文献[1](#ref-previous)。
纯探针精确刚性亦见 Mayer--Knill 定理 1[8](#ref-mayer)。

本轮的具体推进是

$$
\text{基返回}\ \longrightarrow\
\text{记录 Gram}\ \longrightarrow\
\text{二元边缺陷}\ \longrightarrow\
\text{有效电阻}\ \longrightarrow\
\text{全参考恢复误差}.
$$

随后补上近似基返回，避免把精确校准隐藏在定量结论里。

**白话图景。**本轮只问一个问题：怎样判断一个内部读口真正保住了整个量子概念？
已经有的恢复、复结构和探针结果继续使用。
新工作集中在小误差如何沿关系网传播，让“近似保住”也具有可核对的含义。

<a id="section-2"></a>

## 2. 共同内部接口与基保持的记录形式

<a id="statement-2-1"></a>

#### 定义 2.1（声明的同维截口）

设 $\mathscr H\simeq\mathbb C ^d$，$d\ge2$，固定一组可制备、可读出的正交基
$|j\rangle$，$P_j=|j\rangle \langle j|$。
给实际过程或指定恢复后过程
$T:B(\mathscr H)\to B(\mathscr H)$，它是此前结构所给的 CPTP 映射。
使用其已有内部记录等距

$$
V:\mathscr H\longrightarrow\mathscr H\otimes\mathscr R,\qquad
T(\rho)=\operatorname{Tr} _{\mathscr R}(V\rho V^\dagger).
$$

$\mathscr R$ 属于 $\Omega$，是当前截口未保留的记录。
内积对第二变量线性。

这里“无损”指存在同一个 CPTP 映射 $\mathcal R$ 满足
$\mathcal R T=\operatorname{id}$ 于全部矩阵。
在本接口中，“接近给定目标”先通过声明的目标逆校准变成接近 $\operatorname{id}$。
表示中的辅助空间不自动增加实际控制或记录容量。

<a id="statement-2-2"></a>

#### 引理 2.2（基返回强制内部记录分离）

若

$$
p_j:=\operatorname{Tr} (P_jT(P_j))=1\qquad(j=1,\ldots,d),
$$

则存在单位记录向量 $\eta_j\in\mathscr R$，使

<a id="eq-schur"></a>

$$
V|j\rangle =|j\rangle \otimes\eta_j,\qquad
T(|j\rangle \langle k|)=\overline{g_{jk}}\,|j\rangle \langle k|,\qquad
g_{jk}:=\langle \eta_j,\eta_k\rangle .\tag{2.1}
$$

$G=(g_{jk})$ 是对角为一的共同正 Gram 矩阵。

**证明。**

$p_j=\left\lVert (P_j\otimes I)V|j\rangle\right\rVert ^2=1$，
而 $V|j\rangle$ 为单位向量，所以其正交补分量为零。
这给第一式及 $\left\lVert \eta_j\right\rVert =1$。
对 $|j\rangle \langle k|$ 取偏迹给第二式；
任意 $c$ 满足
$c^\dagger Gc=\left\lVert \sum_jc_j\eta_j\right\rVert ^2\ge0$。

□

反过来，任意这样的单位记录族定义等距，因为系统基标签正交；
因此它给实际量子表示中的一个合法通道。
这正是 Schur 型过程：各基人口不变，交叉关系由记录重叠决定。

**白话图景。**每个单独方向都能原样回来，说明过程没有把它搬到别处。
但它仍可能在别的内部位置留下“刚才是哪一个方向”的记录。
接下来要检查的就是这些记录之间的关系，它决定方向之间的相干是否保住。

<a id="section-3"></a>

## 3. 每条桥都落在三维球上：相位转动与相干损失

<a id="statement-3-1"></a>

#### 定义 3.1（二元相干桥）

对 $j\ne k$，定义

$$
|+_{jk}\rangle =\frac{|j\rangle +|k\rangle }{\sqrt2},\qquad
|-_{jk}\rangle =\frac{|j\rangle -|k\rangle }{\sqrt2}.
$$

记 $P_{\pm_{jk}}$ 为相应投影。
在引理 [2.2](#statement-2-2) 的接口中，桥输出限制在 $\operatorname{span} \{|j\rangle ,|k\rangle \}$，矩阵为

<a id="eq-bridge"></a>

$$
T(P_{+_{jk}})
=\frac12
\begin{pmatrix}
1&\overline{g_{jk}}\\g_{jk}&1
\end{pmatrix}.\tag{3.1}
$$

<a id="statement-3-2"></a>

#### 命题 3.2（二元三轴的直接读出）

采用标准 Pauli 三轴，式 [(3.1)](#eq-bridge) 的 Bloch 坐标为

<a id="eq-bloch"></a>

$$
\boxed{(X_{jk},Y_{jk},Z_{jk})
=(\operatorname{Re}g_{jk},\operatorname{Im}g_{jk},0).}\tag{3.2}
$$

从而 $X_{jk}^2+Y_{jk}^2=|g_{jk}|^2\le1$。
桥返回概率及缺陷为

$$
F_{jk}=\operatorname{Tr} (P_{+_{jk}}T(P_{+_{jk}}))
=\frac{1+\operatorname{Re}g_{jk}}2,\qquad
\delta_{jk}=1-F_{jk}.
$$

有精确恒等式

<a id="eq-edge"></a>

$$
\boxed{\left\lVert \eta_j-\eta_k\right\rVert ^2=4\delta_{jk}.}\tag{3.3}
$$

**证明。**

将二阶密度矩阵写为 $(I+X\sigma_x+Y\sigma_y+Z\sigma_z)/2$，
直接比较交叉项。返回概率取 $|+_{jk}\rangle$ 的二次型。
记录距离平方为 $2-2\operatorname{Re}g_{jk}$，即最后一式。

□

还可定义该对纯记录的最优可分辨度

$$
\mathcal D_{jk}=\frac12\left\lVert |\eta_j\rangle\langle\eta_j|
-|\eta_k\rangle\langle\eta_k|\right\rVert _1.
$$

两纯态差在至多二维空间上的特征值为
$\pm\sqrt{1-|g_{jk}|^2}$，因此

<a id="eq-duality"></a>

$$
\boxed{|g_{jk}|^2+\mathcal D_{jk}^2=1.}\tag{3.4}
$$

这是纯记录情形的双路可见度--路径信息关系；一般理论的经典来源见
Englert[9](#ref-englert)。本文只使用并直接证明上述纯记录等式。

```latex
\begin{center}
\begin{tikzpicture}[>=Latex,scale=.85]
\draw[gray!55] (0,0) circle (1.55);
\draw[->,gray] (-1.85,0)--(1.95,0) node[right] {$X$};
\draw[->,gray] (0,-1.8)--(0,1.85) node[above] {$Y$};
\node[gray,anchor=west] at (1.35,1.30) {$Z=0$};
\draw[very thick,accent,->] (0,0)--(.85,.52);
\fill[accent] (.85,.52) circle (2.6pt);
\draw[densely dashed,warm] (.85,.52)--(1.32,.81);
\fill[warm] (1.32,.81) circle (2.3pt);
\node[align=center,text width=4.2cm] at (0,-2.45)
{\small 同一三轴窗口\\[-1pt]\small 半径 $|g|$：保留的相干};
\begin{scope}[xshift=7cm]
\draw[gray!55] (0,0) arc[start angle=0,end angle=90,radius=1.55];
\draw[gray!55] (-1.55,0)--(0,0);
\draw[gray!55] (-1.55,0)--(-1.55,1.55);
\draw[accent,thick,->] (-1.55,0)--(0,0);
\draw[accent,thick,->] (-1.55,0)--(-.20,.76);
\draw[accent,thick,->] (-1.55,0)--(-.77,1.34);
\draw[warm,thick,->] (-1.55,0)--(-1.55,1.55);
\node[anchor=west] at (.12,0) {$\eta_1$};
\node[anchor=south] at (-1.55,1.65) {$\eta_d$};
\node[align=center,text width=4.8cm] at (-.75,-2.45)
{\small 邻近记录只差很小角度\\[-1pt]\small 长链两端仍可能正交};
\end{scope}
\end{tikzpicture}
\end{center}
```

图中左侧圆是三维球的赤道截面；基保持使 $Z=0$。
右侧仅示意记录方向沿四分之一圆变化，精确反例见第 [10](#section-10) 节。

**白话图景。**同一条桥有两种变化：点沿圆转动，是相位改变；点向圆内缩，是相干减弱。
缩掉的那一部分与内部记录能够区分两端的能力精确对应。
记录仍在 $\Omega$ 内，只是当前读口没有保留它。

<a id="section-4"></a>

## 4. 零误差闭合：连通满相干等价于整体可逆

<a id="statement-4-1"></a>

#### 定义 4.1（覆盖比较网）

令 $\mathcal G=(\{1,\ldots,d\},E)$ 为有限连通无向图。
每条边代表实际声明可制备和读出的二元桥。
边正权 $w_{jk}>0$ 只用于后续误差预算；默认可全部取一。

<a id="statement-4-2"></a>

#### 定理 4.2（候选 N1 的精确等价）

在引理 [2.2](#statement-2-2) 的基保持接口和一个覆盖比较网中，下列条件等价：

1. 全部边满足 $|g_{jk}|=1$；

2. 全部内部记录向量属于同一射线；

3. 存在对角酉 $D_\theta=\operatorname{diag}(e^{i\theta_j})$，

   使 $T=\operatorname{Ad} _{D_\theta}$；
4. $T$ 存在全输入 CPTP 左逆。

其中共同相位只确定到一个全局常数。
校准后 $\operatorname{Ad} _{D_\theta^\dagger}\circ T=\operatorname{id}$。

**证明。**

单位向量 Cauchy--Schwarz 饱和给
$|g_{jk}|=1\Rightarrow\eta_k=e^{i\alpha_{jk}}\eta_j$。
沿连通路径传播，得到固定单位 $\eta$ 及相位 $\theta_j$：
$\eta_j=e^{i\theta_j}\eta$。
于是 $Vx=D_\theta x\otimes\eta$，所以 $T=\operatorname{Ad} _{D_\theta}$。
其左逆为 $\operatorname{Ad} _{D_\theta^\dagger}$。

反向，若 $\mathcal R T=\operatorname{id}$，对任意边比较两个正交输入
$P_{+_{jk}},P_{-_{jk}}$。
它们的迹范数距离为二，而由式 [(3.1)](#eq-bridge)，

$$
\left\lVert T(P_{+_{jk}})-T(P_{-_{jk}})\right\rVert _1=2|g_{jk}|.
$$

CPTP 映射收缩状态迹距离，故
$2\le2|g_{jk}|\le2$，从而全部边满相干。

□

<a id="statement-4-3"></a>

#### 推论 4.3（同一对输入给不可逆性下界）

对任意 $j\ne k$，

$$
\boxed{
\inf_{\mathcal R\ {\rm CPTP}}
\left\lVert \mathcal R T-\operatorname{id}\right\rVert _\diamond
\ge1-|g_{jk}|.
}
$$

**证明。**

记 $a=\left\lVert \mathcal R T-\operatorname{id}\right\rVert _\diamond$。
在两个输入之间插入各自恢复输出，用三角不等式和迹距离收缩，得
$2\le a+2|g_{jk}|+a$。再对 $\mathcal R$ 取下确界。

□

这里使用完整、未除二的 diamond 范数。
物理实施相位逆仍使用已声明的内部控制；
酉表示存在并不自动保证任意预算下可实施。
精确连通传播是项目 OMEGA §10 的既有机制在该二元接口中的抽取，
不作为新的普遍探针定理。

**白话图景。**如果每条连接桥都没有向球内缩，邻接方向留下的记录只能相差一个相位。
整张网连通，就把所有记录锁到同一条射线。
整体过程最多重新排列这些相位，没有把输入区别藏进未读记录。
反过来，一条桥缩短，就有一对原来完全可分的输入被拉近，任何后续恢复都不能把这个距离凭空补回。

### 4.1 相位由树传播，闭路相容由共同正核保证

选一棵生成树，固定根相位 $\theta_r=0$。
沿有向树边 $j\to k$ 令

$$
\theta_k-\theta_j=\arg g_{jk}.
$$

满相干时树边全被对齐。因为它们来自同一记录族，
对任意闭路 $j_0,j_1,\ldots,j_m=j_0$，

<a id="eq-holonomy"></a>

$$
\boxed{\prod_{\ell=0}^{m-1}g_{j_\ell j_{\ell+1}}=1.}\tag{4.1}
$$

证明只须代入 $g_{jk}=e^{i(\theta_k-\theta_j)}$，相位逐项相消。
因此非树边也自动对齐，无需再独立输入一套环路相位规则。

这里的闭路是同一组共线记录的比较环，
不等于一般动力学历史的 Berry 闭路；后者可以有非零几何相位。

**白话图景。**先沿树把每处的相位尺对齐。
若所有边确实来自同一份满相干记录，绕别的路线回来不会得到矛盾刻度。
环路的一致由共同关系表保证，不必逐个环另加规则。

<a id="section-5"></a>

## 5. 撤去前件，冲突具体落在哪里

### 5.1 只保基人口：遗漏相干

完全去相干通道
$T(\rho)=\sum_jP_j\rho P_j$
精确保持全部基态，却把任意桥的 $g_{jk}$ 变成零。
两个内部元 $P_{+_{jk}},P_{-_{jk}}$ 输出相同，无法恢复。

### 5.2 只保桥输出纯：遗漏基身份

在二态空间取
$T(\rho)=\operatorname{Tr} (\rho)P_{+_{12}}$。
桥输出仍是赤道纯态，但不同基输入已经被合并。
所以不能删去基返回前件。

### 5.3 图不连通：遗漏跨分量关系

若图分成两个非空分量，其投影为 $P_A,P_B$，
取
$T(\rho)=P_A\rho P_A+P_B\rho P_B$。
所有已测分量内桥都满相干，跨分量桥却消失。
缺失的是覆盖这两个分量的内部比较。

### 5.4 只有成对正性：相位无法拼成共同对象

考虑候选关系表

$$
G=
\begin{pmatrix}
1&1&-1\\
1&1&1\\
-1&1&1
\end{pmatrix}.
$$

所有二阶主块都半正定且满相干，环路乘积却为 $-1$。
它不是共同正核：取 $c=(1,-1,1)^T$，有
$c^\dagger Gc=-3$。
所以不可能来自共同记录族。
V77 的全部合成二元正性判据已能检测这一层失配[6](#ref-v77)。

**白话图景。**每条前件都对应一个能指出位置的漏项：
只看人口会漏掉相干，只看纯输出会漏掉输入身份，
比较网断开会漏掉跨块关系，只有零散成对数据会漏掉整体拼接冲突。
完整候选保留的正是这些定义之间的连接。

<a id="section-6"></a>

## 6. 同一相位校准下的关系能量

<a id="statement-6-1"></a>

#### 定义 6.1（校准后桥缺陷）

给一个输入无关的共同相位校准
$D_\theta=\operatorname{diag}(e^{i\theta_j})$，
令

$$
T_\theta=\operatorname{Ad} _{D_\theta^\dagger}\circ T,\qquad
\eta'_j=e^{-i\theta_j}\eta_j,\qquad
g'_{jk}=e^{i(\theta_j-\theta_k)}g_{jk}.
$$

定义

<a id="eq-energy"></a>

$$
\delta_{jk}(\theta)=\frac{1-\operatorname{Re}g'_{jk}}2,\qquad
\mathcal E_\theta=\sum_{\{j,k\}\in E}w_{jk}\delta_{jk}(\theta).\tag{6.1}
$$

这些量可以由系统桥读口取得，无需实际读取 $\mathscr R$。
可直接实施声明的校准，也可用已测的 $X,Y$ 计算该目标校准对应的读出。
若把校准用作物理恢复，仍须它属于合法控制范围。
默认零校准 $\theta=0$ 总给一个确定的参考比较。

<a id="statement-6-2"></a>

#### 命题 6.2（相位与读数进入同一个有限正二次型）

令 Hermitian 矩阵 $L_g$ 的对角为
$(L_g)_{jj}=\sum_{k:\{j,k\}\in E}w_{jk}$，
非对角为 $(L_g)_{jk}=-w_{jk}g_{jk}$，非边取 $w_{jk}=0$。
对任意 $q\in\mathbb C ^d$，

$$
q^\dagger L_gq
=\sum_{\{j,k\}\in E}w_{jk}\left\lVert q_j\eta_j-q_k\eta_k\right\rVert ^2
\ge0.
$$

特别地，$q_j=e^{-i\theta_j}$ 时，

<a id="eq-connection"></a>

$$
\boxed{q^\dagger L_gq=4\mathcal E_\theta.}\tag{6.2}
$$

**证明。**

逐边展开范数平方，交叉项恰为
$-\bar q_jw_{jk}g_{jk}q_k$ 及其共轭。
再用式 [(3.3)](#eq-edge) 于校准后的记录。

□

因此同一组三轴读数、相位约定和整体残差已经处于一个有限二次型中。
若只沿生成树对齐相位，树边满足
$\delta_{jk}(\theta)=(1-|g_{jk}|)/2$；
$g_{jk}=0$ 时可任取其相位，等式仍成立。
非树边保留实际相位残差；精确满相干时它们自动为零。

**白话图景。**每条边报告两件事：关系缩了多少、相位转了多少。
选定同一套内部相位刻度后，两者合成一个非负偏差。
整张网的能量就是这些实际比较偏差的加权总量；权重默认全为一，
不需要引入图外的物理参数。

<a id="section-7"></a>

## 7. 更大结构：关系网自身的有效电阻

<a id="statement-7-1"></a>

#### 定义 7.1（比较网的传播几何）

对实函数 $f:\{1,\ldots,d\}\to\mathbb R$ 定义

$$
\mathcal Q_{\mathcal G}(f)
=\sum_{\{u,v\}\in E}w_{uv}(f_u-f_v)^2.
$$

对 $j\ne k$，定义

<a id="eq-R"></a>

$$
R_{\rm eff}(j,k)
=\sup_{\mathcal Q_{\mathcal G}(f)>0}
\frac{(f_j-f_k)^2}{\mathcal Q_{\mathcal G}(f)},
\qquad R_{\rm eff}(j,j)=0.\tag{7.1}
$$

再定义有效电阻半径

$$
R_*=\min_r\max_jR_{\rm eff}(r,j).
$$

连通性使常数之外的二次型正定，所以这些数有限。
若 $L$ 是该实加权图的 Laplacian，则
$R_{\rm eff}(j,k)=(e_j-e_k)^TL^+(e_j-e_k)$；
这只是上述变分式在常数正交补上的 Cauchy--Schwarz 表示。
有效电阻和图二次型是标准工具，参见 Spielman--Srivastava[10](#ref-resistance)；
这里不执行求解器，也不把图比作新的物理电路。

<a id="statement-7-2"></a>

#### 引理 7.2（Hilbert 值的电阻不等式）

任意 Hilbert 空间向量族 $x_j$ 满足

<a id="eq-Dirichlet"></a>

$$
\boxed{
\left\lVert x_j-x_k\right\rVert ^2
\le R_{\rm eff}(j,k)
\sum_{\{u,v\}\in E}w_{uv}\left\lVert x_u-x_v\right\rVert ^2.
}\tag{7.2}
$$

**证明。**

若 $x_j=x_k$，结论直接成立。
否则沿单位方向
$a=(x_j-x_k)/\left\lVert x_j-x_k\right\rVert$ 取
$f_u=\operatorname{Re}\langle a,x_u\rangle$。
于是 $(f_j-f_k)^2=\left\lVert x_j-x_k\right\rVert ^2$，
而每条边有 $|f_u-f_v|\le\left\lVert x_u-x_v\right\rVert$。
代入式 [(7.1)](#eq-R)。

□

对任意连接 $j,k$ 的路径 $\pi$，加权 Cauchy--Schwarz 给

$$
R_{\rm eff}(j,k)\le\sum_{e\in\pi}w_e^{-1}.
$$

多条比较路线允许更强约束；增加正权边使电阻本身不增。
新增边也可能改变已测总能量，所以不能不固定误差预算就宣称最终界必然改善。

**白话图景。**小差异会沿关系网传播。长而细的一条链容易积累差异，
多条互相校验的路线则能限制传播。
有效电阻只根据这张有限比较网定义，衡量同一边能量预算下两端最多能分开多少；
它属于关系的关系，没有额外放进一个外部场。

<a id="section-8"></a>

## 8. 主定理：有限二元缺陷控制整个概念

<a id="statement-8-1"></a>

#### 定义 8.1（全参考误差）

对线性映射 $\Phi$ 使用完整、未除二的 diamond 范数

$$
\left\lVert \Phi\right\rVert _\diamond
=\sup_{m\ge1}\ \sup_{\left\lVert X\right\rVert _1=1}
\left\lVert (\Phi\otimes\operatorname{id} _m)(X)\right\rVert _1.
$$

它同时控制与任意有限内部参考纠缠的输入。
两个通道之差的此范数至多为二。

<a id="statement-8-2"></a>

#### 定理 8.2（相干桥的有效电阻证书）

在精确基保持接口中，对任意共同相位校准 $\theta$，

<a id="eq-main"></a>

$$
\boxed{
\left\lVert T_\theta-\operatorname{id}\right\rVert _\diamond
\le
\min\left\{2,\ 4\sqrt{R_*\mathcal E_\theta}\right\}.
}\tag{8.1}
$$

特别地，若 $\mathcal E_\theta=0$，则 $T_\theta=\operatorname{id}$。
要认证全参考误差不超过 $\varepsilon$，一个充分条件是
$R_*\mathcal E_\theta\le\varepsilon^2/16$。

**证明。**

由式 [(3.3)](#eq-edge) 和引理 [7.2](#statement-7-2)，

$$
\left\lVert \eta'_j-\eta'_r\right\rVert ^2
\le4R_{\rm eff}(r,j)\mathcal E_\theta.
$$

校准后等距为
$V_\theta|j\rangle =|j\rangle \otimes\eta'_j$。
比较同一空间中的
$V_r|j\rangle =|j\rangle \otimes\eta'_r$，它实现恒等通道。
由于不同系统标签正交，

$$
\left\lVert V_\theta-V_r\right\rVert 
=\max_j\left\lVert \eta'_j-\eta'_r\right\rVert 
\le2\sqrt{\max_jR_{\rm eff}(r,j)\mathcal E_\theta}.
$$

对任意辅助空间和迹类 $X$，展开两个等距实现的输出差为

$$
(V_\theta-V_r)XV_\theta^\dagger+
V_rX(V_\theta-V_r)^\dagger,
$$

其中省略辅助恒等。
偏迹收缩迹范数，且两个等距的算子范数均为一，
所以通道差的 diamond 范数不超过 $2\left\lVert V_\theta-V_r\right\rVert$。
选择使电阻半径最小的根，再用通道差上界二，得到结论。

□

这里没有额外乘一个 $d$ 或 $\sqrt d$；维数和结构的影响仍完整保留在
实际比较网及 $R_*$ 中，不能把它解释成任意增长网络上的统一常数。
系数四是本证明给出的明确充分界，不主张最优数值常数。
等距实现控制通道范数的一般背景见 Kretschmann--Schlingemann--Werner[11](#ref-ksw)；
本节已经给出所需方向的直接证明。

**白话图景。**只需读有限条桥，不必逐个测量所有叠加态。
这些桥限制未读记录之间的距离；网的几何再把局部限制传到所有方向。
当所有记录在同一校准下足够接近时，整个量子概念连同任意内部参考都被保住，
误差可以用一个明确式子给出。

<a id="section-9"></a>

## 9. 基方向也有误差时：完整扩展而不隐藏理想前件

### 9.1 构造邻近的基保持比较过程

现在允许

$$
p_j=\operatorname{Tr} (P_jT(P_j))\le1,\qquad \epsilon_j=1-p_j.
$$

本节的 $T$ 已在所声明共同目标框架下；
若使用相位校准，先对该校准后的通道应用下述结论。

<a id="statement-9-1"></a>

#### 定理 9.1（近似基的比较等距）

存在精确保持全部基态的 Schur 通道 $S$，使

<a id="eq-beta"></a>

$$
\left\lVert T-S\right\rVert _\diamond\le\min\{2,2\beta\},\qquad
\beta^2=\sum_j2(1-\sqrt{p_j})\le2\sum_j\epsilon_j.\tag{9.1}
$$

**证明。**

写
$V|j\rangle =|j\rangle \otimes a_j+z_j$，
其中 $(\langle j|\otimes I)z_j=0$。
则 $\left\lVert a_j\right\rVert ^2=p_j$、$\left\lVert z_j\right\rVert ^2=\epsilon_j$。
当 $p_j>0$ 时令 $\eta_j=a_j/\sqrt{p_j}$；
$p_j=0$ 时任取一个单位记录向量。
令
$V_0|j\rangle =|j\rangle \otimes\eta_j$。
系统标签正交保证 $V_0$ 为等距。

每列差的平方为

$$
b_j^2:=\left\lVert (V-V_0)|j\rangle\right\rVert ^2
=2(1-\sqrt{p_j}),
$$

包括 $p_j=0$ 时的值二。
对 $x=\sum_jx_j|j\rangle$，有
$\left\lVert (V-V_0)x\right\rVert \le\sum_j|x_j|b_j\le\beta\left\lVert x\right\rVert$。
等距到通道的同一展开给式 [(9.1)](#eq-beta)。

□

$S$ 是证明中构造的比较通道，不宣称它已由实际控制独立实施。
全部读出仍取原通道的真实基返回与桥返回。

### 9.2 桥的误差直接在振幅层相加

令

$$
\delta_{jk}
=1-\operatorname{Tr} (P_{+_{jk}}T(P_{+_{jk}})),\qquad
\ell_{jk}=\frac{b_j+b_k}{\sqrt2}.
$$

<a id="statement-9-2"></a>

#### 引理 9.2（原始桥缺陷控制比较记录）

<a id="eq-approx-edge"></a>

$$
\boxed{
\frac{\left\lVert \eta_j-\eta_k\right\rVert }2
\le\sqrt{\delta_{jk}}+\ell_{jk}
\le\sqrt{\delta_{jk}}+\sqrt{\epsilon_j}+\sqrt{\epsilon_k}.
}\tag{9.2}
$$

**证明。**

令 $Q_{jk}=I-P_{+_{jk}}$。原等距满足
$\left\lVert (Q_{jk}\otimes I)V|+_{jk}\rangle\right\rVert =\sqrt{\delta_{jk}}$。
而 $V_0|+_{jk}\rangle$ 的未返回分量为
$|-_{jk}\rangle \otimes(\eta_j-\eta_k)/2$。
三角不等式给

$$
\frac{\left\lVert \eta_j-\eta_k\right\rVert }2
\le\sqrt{\delta_{jk}}+\left\lVert (V-V_0)|+_{jk}\rangle\right\rVert 
\le\sqrt{\delta_{jk}}+\frac{b_j+b_k}{\sqrt2}.
$$

由 $b_j\le\sqrt{2\epsilon_j}$ 得后半式。

□

<a id="statement-9-3"></a>

#### 定理 9.3（含基误差的有限整体证书）

对任意加权连通比较网，

<a id="eq-robust"></a>

$$
\boxed{
\left\lVert T-\operatorname{id}\right\rVert _\diamond
\le
\min\left\{
2,\ 
2\beta+
4\sqrt{
R_*\sum_{\{j,k\}\in E}
w_{jk}\bigl(\sqrt{\delta_{jk}}+\ell_{jk}\bigr)^2
}
\right\}.
}\tag{9.3}
$$

**证明。**

用式 [(9.2)](#eq-approx-edge) 界定比较记录的边能量，
再将定理 [8.2](#statement-8-2) 的证明应用于 $S$。
最后加上 $\left\lVert T-S\right\rVert _\diamond\le2\beta$。

□

此式只包含原始误差的平方根，没有先比较概率再开方造成的四次方根损失。
当 $\epsilon_j=0$ 时精确回到式 [(8.1)](#eq-main)。
这里所有概率都在完整输出上读取；
不能先丢弃失败结果再归一化，否则会隐藏正要预算的泄漏。
若输入是统计样本，应先有保证的概率界；本文不把裸频率当成确定性界。

**白话图景。**基方向也会偏，不能只给桥误差收费。
先把每个基方向偏离原位置的部分列出来，
再把它与桥未返回的振幅放在同一层相加。
这样得到的整体保证仍只来自有限内部读数，没有把理想基偷偷放回证明。

<a id="section-10"></a>

## 10. 两条长链反例：为什么局部很小不等于整体很小

### 10.1 可逆相位坡度

取路径图 $1-2-\cdots-d$，令

$$
D=\operatorname{diag}\left(
e^{i\pi(j-1)/(d-1)}
\right)_{j=1}^d,\qquad T=\operatorname{Ad} _D.
$$

全部基态固定，每条相邻桥的返回缺陷为

$$
\delta_{\rm edge}=\sin^2\frac{\pi}{2(d-1)}\longrightarrow0.
$$

但端点桥满足 $D|+_{1d}\rangle =|-_{1d}\rangle$，故

$$
\boxed{\left\lVert T-\operatorname{id}\right\rVert _\diamond=2.}
$$

这是一条整体可逆的相位坡度；
若相位逆属于合法控制，施加 $D^\dagger$ 后所有误差为零。
它说明固定相位参考下的边小误差不能直接替代全网保证。

**白话图景。**每一步只转一点，相邻比较几乎看不出变化；
但走完整条链，端点已经转了半周。
这个例子没有丢信息，只是共同参考没有对齐。

### 10.2 真正泄漏的四分之一圆

仍取同一条路径，给二维内部记录

<a id="eq-quarter-circle"></a>

$$
\eta_j=\cos\vartheta_j\,|0\rangle +\sin\vartheta_j\,|1\rangle ,\qquad
\vartheta_j=\frac{\pi(j-1)}{2(d-1)}.\tag{10.1}
$$

令 $V|j\rangle =|j\rangle \otimes\eta_j$。
于是

$$
T(|j\rangle \langle k|)=
\cos(\vartheta_j-\vartheta_k)\,|j\rangle \langle k|.
$$

所有基态固定，每条邻边缺陷为

$$
\delta_{\rm edge}
=\sin^2\frac{\pi}{4(d-1)}\longrightarrow0.
$$

然而两端记录正交，故

$$
T(P_{+_{1d}})=T(P_{-_{1d}})
=\frac{P_1+P_d}{2}.
$$

对任意恢复 $\mathcal R$，这两个输入的恢复输出仍相同，记为 $\sigma$。
三角不等式给

$$
\left\lVert \sigma-P_{+_{1d}}\right\rVert _1+
\left\lVert \sigma-P_{-_{1d}}\right\rVert _1
\ge\left\lVert P_{+_{1d}}-P_{-_{1d}}\right\rVert _1=2.
$$

从而

<a id="eq-irreversible"></a>

$$
\boxed{
\inf_{\mathcal R\ {\rm CPTP}}
\left\lVert \mathcal R T-\operatorname{id}\right\rVert _\diamond\ge1.
}\tag{10.2}
$$

这里允许任意恢复也不能消掉常数误差。

对单位边权路径，$R_{\rm eff}(j,k)=|j-k|$：
沿唯一路径的 Cauchy--Schwarz 给上界，取在该路径上线性变化、
路径外常值的实函数即可达到。
因此半径随链长增长；边缺陷虽然按链长平方缩小，
它与全网能量、电阻组成的预算并不趋于零。

**白话图景。**内部记录沿四分之一圆缓慢转动。每个邻居只差很小角度，
但走到另一端，记录已经与起点正交，能分清输入来自哪一端。
当前读口不保留这些记录时，端点的正负叠加被合成同一个输出。
这次压掉的是当前保留输出中的相干区别；
只对这个输出做恢复，也不能把正负叠加重新分开。
若重新取得此前未保留的内部记录，那已是另一个恢复接口。

<a id="section-11"></a>

## 11. 候选属于哪一个更大结构

本轮并列出现的量其实都来自同一个内部实现：

$$
\begin{aligned}
&V|j\rangle =|j\rangle \otimes\eta_j,\\
&g_{jk}=\langle \eta_j,\eta_k\rangle ,\\
&(X_{jk},Y_{jk},Z_{jk})=(\operatorname{Re}g_{jk},
\operatorname{Im}g_{jk},0),\\
&4\delta_{jk}(\theta)=\left\lVert \eta'_j-\eta'_k\right\rVert ^2,\\
&q^\dagger L_gq=4\mathcal E_\theta,\\
&\left\lVert T_\theta-\operatorname{id}\right\rVert _\diamond
\le\min\{2,4\sqrt{R_*\mathcal E_\theta}\}.
\end{aligned}
$$

它们依次是：实际分支、记录之间的关系、局部三轴读出、
两条记录的残差、残差的整体二次型、整个概念的全参考稳定性。

因此“无损”不需要再由图外的一句话担保。
精确时，它等价于连通相干桥在共同正核内的满相干；
近似时，式 [(8.1)](#eq-main) 或 [(9.3)](#eq-robust) 给确定的充分证书。
这并不把已有 CP、共同复结构和平方标尺重新当作本轮新前件问题；
它们是本候选明确消费的已完成接口。

| 撤去的关系 | 受影响的两个元 | 更大结构中的失败 |
| --- | --- | --- |
| 基身份保持 | 两个不同基输入 | 纯制备把输入合并 |
| 相干桥保持 | 同一桥的正、负叠加 | 保留读口压缩可分辨度 |
| 覆盖连通 | 跨分量的两个方向 | 内块正确不能决定块间相干 |
| 共同整体正核 | 两条到达同处的相位比较 | 零散满相干块无法拼接 |
| 传播几何预算 | 长链两端的记录或叠加 | 每边缺陷小，整体仍可严重失真 |

**白话图景。**一个概念既有各个方向，也有方向之间怎样叠加的关系。
读口保住每个方向，只完成了一半；相干桥才把它们连成同一个量子概念。
每条桥可以放进一个三维球，但这些球必须来自同一张正关系表。
小偏差怎样沿网传播，再由网自身的几何决定。
这样，“无损”成为内部记录、二元读出和整体稳定之间可证明的约束。

<a id="section-12"></a>

## 12. 本轮候选的判定与完整白话

**候选判定。**
在声明的有限维同维截口、既有 CP/内部记录结构中，
候选 N1 的精确形式已由定理 [4.2](#statement-4-2) 证明，
无需额外列为独立物理公理。
有限误差形式由定理 [8.2](#statement-8-2) 及 [9.3](#statement-9-3) 给出充分保证。
其中全输入恢复、精确纯探针传播与图二次型方法分别保留既有归属；
本轮完成的是二元记录缺陷、电阻传播、相位校准与全参考误差之间的具体组合。
本文不声称最佳常数、最少测试数、普遍外部文献首创或新增形式化验证。

**完整白话图景。**
所有输入、记录和参考都在 $\Omega$ 内。
一个观察者从中选择一个读口，等于决定保留哪些关系。
每个单独方向看起来没有变，并不意味着整个概念没有变：
方向之间可能已在别处留下不同记录。

把两个方向接成一座相干桥，桥的读数就进入一个三维球。
点只沿圆转，是相位需要对齐；点向球里缩，是当前读口保留的相干减少。
如果一张连通比较网里的桥都不缩，所有未读记录就只能指向同一条射线，
整个过程只剩可统一校准的相位。

有小误差时，不能只说每一步都很小。
记录可以沿一条很长的圆弧缓慢转动，最后两端变得正交。
所以完整定义还要保留关系网怎样连接；电阻半径衡量差异能沿这张网放大多少。
有限桥读数和这个内部几何量合在一起，
才给出整个概念连同所有内部参考是否稳定的保证。

## 资料与可复核位置

<a id="ref-previous"></a>

**[1]**
《已证结构的内生闭合：同根有限证书、事件重编码与结果核递归》，
AURIC v78 后续研究，本对话既有续稿。
源文件：`AURIC_v78_Internal_Readout_Closure_and_Constraint_Reduction_ZH.tex`。
[已交付 PDF](https://chatgpt.com/library?file_id=libfile_177048c08d988191b9600678124ea674&account_id=personal)。
它不在本轮固定仓库快照中。
<a id="ref-omega"></a>

**[2]**
[AURIC OMEGA Static Compatibility Fiber Theory](https://github.com/the-omega-institute/trureturing/blob/59e9df9c5e49bc59e1b46a0240f52820acd0f453/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)。
§8 完整恢复与未读记录条件；§10 探针分量及精确刚性；
追加命题 35--37 两基图谱隙与过程误差。以上均作为既有结果承接。
<a id="ref-recovery"></a>

**[3]**
[AURIC FIB Optimal Measurement Quantum Recovery](https://github.com/the-omega-institute/trureturing/blob/59e9df9c5e49bc59e1b46a0240f52820acd0f453/docs/develop/theory/AURIC_FIB_OPTIMAL_MEASUREMENT_QUANTUM_RECOVERY.md)。
§6 定理 6.1，保留可见旗标时的完整交叉 KL 条件和解码补全。
<a id="ref-memory"></a>

**[4]**
[AURIC FIB Environment Record Memory](https://github.com/the-omega-institute/trureturing/blob/59e9df9c5e49bc59e1b46a0240f52820acd0f453/docs/develop/theory/AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md)。
§26 定理 26.2，实际词的最大共同可纠正代数。
<a id="ref-lean"></a>

**[5]**
[ProbeComponentRigidity.lean](https://github.com/the-omega-institute/trureturing/blob/59e9df9c5e49bc59e1b46a0240f52820acd0f453/D5/S3/Quantum/Reduction/ProbeComponentRigidity.lean)。
已读取的既有探针分量形式化文件；本轮未修改或编译该文件。
<a id="ref-v77"></a>

**[6]**
[V77：Reverse Location of Quantum Axioms, Binary Witnesses and Internal Compatibility](https://github.com/the-omega-institute/trureturing/blob/59e9df9c5e49bc59e1b46a0240f52820acd0f453/docs/develop/theory/AURIC_REVERSE_LOCATION_OF_QUANTUM_AXIOMS_BINARY_WITNESSES_AND_INTERNAL_COMPATIBILITY_V77.md)。
§3 全部合成二元球条件与整体正性。
<a id="ref-sharp"></a>

**[7]**
[Sharp Task Retained Environment Memory](https://github.com/the-omega-institute/trureturing/blob/59e9df9c5e49bc59e1b46a0240f52820acd0f453/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SHARP_TASK_RETAINED_ENVIRONMENT_MEMORY.md)。
§13、§18--19，指定实际五维接口的效果到 diamond 误差界；
与本稿任意有限比较网的记录电阻证书范围不同。
<a id="ref-mayer"></a>

**[8]**
K. Mayer and E. Knill,
*Quantum process fidelity bounds from sets of input states*,
Physical Review A 98, 052326 (2018).
[DOI](https://doi.org/10.1103/PhysRevA.98.052326)；
[公开作者稿](https://pmc.ncbi.nlm.nih.gov/articles/PMC7727744/)。
定理 1 为张成连通纯探针的精确刚性；第 V 节给图式近似验证背景。
<a id="ref-englert"></a>

**[9]**
B.-G. Englert,
*Fringe Visibility and Which-Way Information: An Inequality*,
Physical Review Letters 77, 2154 (1996).
[DOI](https://doi.org/10.1103/PhysRevLett.77.2154)。
本稿使用的纯记录等式另给直接证明。
<a id="ref-resistance"></a>

**[10]**
D. A. Spielman and N. Srivastava,
*Graph Sparsification by Effective Resistances*,
[arXiv:0803.0929](https://arxiv.org/abs/0803.0929)。
有效电阻、图 Laplacian 和 Dirichlet 二次型的标准背景；
本稿所用向量值不等式已自足证明。
<a id="ref-ksw"></a>

**[11]**
D. Kretschmann, D. Schlingemann and R. F. Werner,
*The Information-Disturbance Tradeoff and the Continuity of Stinespring's Representation*,
[arXiv:quant-ph/0605009](https://arxiv.org/abs/quant-ph/0605009)。
本稿只使用并直接证明共同等距距离控制完整通道距离的方向。

## 源稿前言与排版元数据

```latex
% !TEX program = xelatex
\documentclass[11pt,a4paper]{article}
\usepackage[margin=24mm,headheight=16pt]{geometry}
\IfFileExists{ctex.sty}{\usepackage[UTF8,fontset=auto]{ctex}}{
  \usepackage{fontspec}
  \IfFontExistsTF{Noto Serif CJK SC}{\setmainfont{Noto Serif CJK SC}[AutoFakeBold=1.7]}{\setmainfont{NotoSerifCJKsc-Regular.otf}[Path=fonts/,AutoFakeBold=1.7,AutoFakeSlant=.15]}
  \XeTeXlinebreaklocale "zh"
  \XeTeXlinebreakskip=0pt plus 1pt
}
\usepackage{amsmath,amssymb,amsthm,mathtools,mathrsfs}
\usepackage{xcolor,booktabs,array,tabularx}
\usepackage{fancyhdr,enumitem,hyperref,needspace,tikz}
\usetikzlibrary{arrows.meta,calc}
\definecolor{ink}{HTML}{17384A}
\definecolor{accent}{HTML}{007D86}
\definecolor{warm}{HTML}{B75B39}
\hypersetup{colorlinks=true,linkcolor=ink,urlcolor=accent,citecolor=ink,
pdftitle={AURIC v78 候选 N1：相干桥的整体无损相容}}
\pagestyle{fancy}\fancyhf{}
\fancyhead[L]{\small AURIC / v78 / 候选 N1}
\fancyhead[R]{\small 二元三轴、内部记录与整体稳定}
\fancyfoot[C]{\thepage}
\setlength{\parindent}{1.8em}
\setlength{\parskip}{4pt}
\setlength{\emergencystretch}{3em}
\setlist{nosep,leftmargin=2em}
\renewcommand{\baselinestretch}{1.10}
\renewcommand{\contentsname}{目录}
\renewcommand{\abstractname}{摘要}
\renewcommand{\refname}{资料与可复核位置}
\renewcommand{\proofname}{证明}
\numberwithin{equation}{section}
\theoremstyle{definition}
\newtheorem{definition}{定义}[section]
\newtheorem{theorem}[definition]{定理}
\newtheorem{lemma}[definition]{引理}
\newtheorem{proposition}[definition]{命题}
\newtheorem{corollary}[definition]{推论}
\newtheorem{remark}[definition]{说明}
\newcommand{\ip}[2]{\langle #1,#2\rangle}
\newcommand{\norm}[1]{\left\lVert #1\right\rVert}
\newcommand{\C}{\mathbb C}
\newcommand{\R}{\mathbb R}
\newcommand{\tr}{\operatorname{Tr}}
\newcommand{\id}{\operatorname{id}}
\newcommand{\Ad}{\operatorname{Ad}}
\newcommand{\Span}{\operatorname{span}}
\newcommand{\rank}{\operatorname{rank}}
\newcommand{\ket}[1]{|#1\rangle}
\newcommand{\bra}[1]{\langle#1|}
\newcommand{\plain}[1]{\par\noindent\textbf{白话图景。}#1\par}
\newcommand{\repo}[2]{\href{https://github.com/the-omega-institute/trureturing/blob/59e9df9c5e49bc59e1b46a0240f52820acd0f453/#1}{#2}}
\title{\color{ink}\bfseries 候选 N1：相干桥的整体无损相容\\[6pt]
\large 二元三轴、共同记录与有效电阻证书\\[4pt]
AURIC v78 后续研究：定义、定理与证明}
\author{研究续稿}
\date{2026 年 11 月 2 日}
```

```latex
\begin{document}
\maketitle
\setcounter{tocdepth}{1}
{\small\setlength{\parskip}{0pt}\tableofcontents}
\newpage
\begin{quote}
\end{quote}
\begin{center}\small\texttt{59e9df9c5e49bc59e1b46a0240f52820acd0f453}。\end{center}
\begin{center}\small
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.25\textwidth}XX@{}}
\toprule
\midrule
\bottomrule
\end{tabularx}
\end{center}
\begin{center}\small
\begin{tabularx}{\textwidth}{@{}p{.24\textwidth}XX@{}}
\toprule
\midrule
\bottomrule
\end{tabularx}
\end{center}
\medskip
\noindent
\clearpage
\begin{thebibliography}{99}\raggedright
\end{thebibliography}
\end{document}
```
