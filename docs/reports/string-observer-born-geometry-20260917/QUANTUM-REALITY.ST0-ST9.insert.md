
---

<a id="string-observer-integration"></a>

# 弦论微观实现、规范相容约化与观察者有效几何

## 第21至30节接口增订 ST：共同传播结构的微观来源与可恢复范围

**日期：2026-09-17。** 本增订接续本卷第21至30节，保留原有章节与编号。定位是将弦论及全息研究的既有结果接入本项目的观察、记忆、响应和几何接口。弦论可以提供具体微观实现；项目的接口理论负责刻画某类实验能恢复哪些结构、约化需要保留什么，以及何处出现可证明的失配。

**证明状态。** ST2、ST3.1至ST3.3、ST5.1至ST5.3、ST6.1至ST6.3给出普通数学证明；ST4.2是引用恢复定理后的有限维推论；ST7重述并勘界此前对话笔记中的有限标量谱结果。所有新声明尚未编译为 Lean，有限核对不替代证明。本文不主张全球新颖性，不把抽象矩阵实例声明为实际弦真空，不宣称已经求出现实宇宙的量子引力理论。正文是对既有理论卷的插入稿；发布或形式化状态由实际仓库记录决定。

**读取基线。** `the-omega-institute/trureturing@e984c77223b55a3cda565c7694098e436926183d`；本卷对应 blob 为 `09df8199fd2cd36a90a8df1cd3dfd6cbe3962b32`。交付前复核 `dev@6be0066797360553a18e35e3907017eede1b8fcf`，目标文件 blob 与插入上下文保持相同。以下真源只承担其已声明的数学范围：

- `D5/S3/Weil/ZetaLinear/SchurComplementAssociativity.lean`：有界算子和显式逆见证下的分层消去结合律。
- `D5/S3/Quantum/Fibers/FutureStatisticsEquivalence.lean`：固定量子通道下，全体未来统计相同与状态差对 Heisenberg 生成空间的迹配对为零的等价。
- `D5/S3/Observer/GoldenCoding/GoldenLorentzUpdate.lean`：黄金更新对二次式的一步反等距与双步等距。
- `D5/S3/Observer/GoldenCoding/GoldenBusemannCoordinate.lean`：黄金零坐标与双步快速度增量。

这些锚点没有自动提供弦 BRST/BV 结构、世界面量子化、连续场积分或全息对偶证明。外部文献结果与本文推论分开标记。

### ST0．四种操作与三个不同的尺度

固定微观模型后，应区别下列操作。

**观察限制**把态限制到可访问代数，或经实际量子通道生成记录。完整系统的作用量与耦合保持不变。

**精确消元**把未显式保留的场积分掉，同时转移相互作用、源、初态与量子行列式。对所覆盖的实验，它应保持完整生成泛函。

**近似截断**舍去若干导数阶、圈阶或有效顶点。它需要明确误差窗口；一般不保持上一项的精确相等。

**改变耦合**例如将质量矩阵的跨块项置零，会改变物理模型。ST7的相对曲率系数属于这种有明确定义的模型比较。

世界面的重整化尺度、时空有效理论的匹配尺度和观察者的物理时间也应分别记录。世界面 beta 函数的零点是量子一致性条件，不能仅凭“固定点”这一名称与任意动力系统的不动点等同。

## ST1．弦论提供什么输入，观察者模型又增加什么问题？

### ST1.1 外部输入：一致背景与有效作用量

在适当的弦模型、规范及微扰范围内，世界面 Weyl 一致性约束背景场。例如最低阶的度量条件具有形式

$$
\bar\beta^G_{\mu\nu}
=\alpha'\left(R_{\mu\nu}+2\nabla_\mu\nabla_\nu\Phi
-\frac14 H_{\mu\rho\sigma}H_\nu{}^{\rho\sigma}\right)
+O(\alpha'^2)=0.
$$

还要满足反对称张量、dilaton及相应模型的其他条件。世界面圈阶与时空弦耦合的 genus 展开是不同展开；高导数修正的首个非零阶依弦模型而异。[ST-Tong7]

一个标准的两导数 NS-NS 背景作用量写成

$$
S_{\mathrm{NSNS}}
=\frac1{2\kappa_D^2}\int d^Dx\sqrt{-G_s}\,e^{-2\Phi}
\left[R_s+4(\nabla\Phi)^2-\frac1{12}H^2+\cdots\right].
$$

省略项不被视为已经消失。实际应用需要固定弦模型、允许背景、紧化、其他场和一致截断。这个已知背景结构可以约束本卷所用的传播矩阵及曲率耦合，不能任意替所有模型选定同一组参数。[ST-Tong7] [ST-SenZwiebach]

### ST1.2 进入本卷的研究窗口

取单位 $c=\hbar=1$ 讨论尺度，令 $M_s=1/\sqrt{\alpha'}$。使用局域低能近似时，应检查实验能标相对实际被积分模式的质量隙、曲率相对弦尺度以及适用的圈展开参数。例如

$$
\alpha' E^2\ll1,\qquad
\alpha'\|\mathrm{Riemann}\|\ll1,\qquad
E^2/M_{\mathrm{gap}}^2\ll1
$$

和所选微扰方案的弱耦合条件。

不存在质量隙的模、未稳定的模量及实验能够激发的绕数/动量模，不能以“隐藏”为由直接删除。精确非局域有效理论允许更一般的消元；有限局域导数展开需要额外控制。非 Wilsonian 的树级同伦转移也已有研究，不能把“有效”一词限定为一个统一能标截断。[ST-Arvanitakis]

本卷的新增问题是：给定这种受一致性约束的微观实现，一个明确的源、记录和钟尺协议能够识别什么？不同协议何时仍能共同通过同一几何描述？

## ST2．带源和几何变分的精确 Schur 约化

本节先在有限维实对称矩阵上完成全部证明。连续算子和规范场版本还须处理定义域、边界、量子测度及正规化。

### 定理 ST2.1：保留任意线性观察接口的响应

设

$$
D=\begin{pmatrix}A&B\\B^{\mathsf T}&C\end{pmatrix}>0,
\qquad S=A-BC^{-1}B^{\mathsf T},
$$

以及完整源读数矩阵 $J=(J_V,J_H)$。定义

$$
J_{\mathrm{eff}}=J_V-J_HC^{-1}B^{\mathsf T}.
$$

则

$$
\boxed{
JD^{-1}J^{\mathsf T}
=J_{\mathrm{eff}}S^{-1}J_{\mathrm{eff}}^{\mathsf T}
+J_HC^{-1}J_H^{\mathsf T}.
}
\tag{ST2.1}
$$

**证明。** 对隐藏变量完成平方，或直接验证块逆：

$$
D^{-1}=
\begin{pmatrix}
S^{-1}&-S^{-1}BC^{-1}\\
-C^{-1}B^{\mathsf T}S^{-1}&
C^{-1}+C^{-1}B^{\mathsf T}S^{-1}BC^{-1}
\end{pmatrix}.
$$

左右乘 $J,J^{\mathsf T}$，按平方项合并即得。$C>0$ 且 $S>0$ 由正定性和完成平方保证。∎

**含义。** 原实验若耦合到隐藏模，约化时需要转移源接口并保留最后的纯隐藏源项。该项在频域模型中可以依赖频率，不能统一当作局域常数。仅保留 $S$ 通常不能复现原实验。

### 定理 ST2.2：消元与几何方向变分的相容性

令上述矩阵光滑依赖实参数 $u$。它可表示固定坐标与固定测度约定下的一条几何扰动方向。定义

$$
L=\begin{pmatrix}I\\-C^{-1}B^{\mathsf T}\end{pmatrix}.
$$

则

$$
\boxed{\frac{dS}{du}=L^{\mathsf T}\frac{dD}{du}L.}
\tag{ST2.2}
$$

**证明。** 有

$$
DL=\begin{pmatrix}S\\0\end{pmatrix},
\qquad S=L^{\mathsf T}DL.
$$

求导时，$dL/du$ 的可见块为零，所以
$(dL/du)^{\mathsf T}DL$ 与其转置均为零。剩余项正是式(ST2.2)。∎

定义有限高斯真空项

$$
W(D)=\frac{\hbar}{2}\log\det D.
$$

由于 $\det D=\det C\det S$，得到

$$
\boxed{
\frac{dW}{du}
=\frac{\hbar}{2}\operatorname{tr}
\left(C^{-1}\frac{dC}{du}
+S^{-1}L^{\mathsf T}\frac{dD}{du}L\right).
}
\tag{ST2.3}
$$

这证明：在这些假设下，同时保留有效算子与隐藏行列式后，先消元再计算几何响应，与对完整高斯积分计算该响应一致。

### 推论 ST2.3：移动探针的响应也要一起求导

若 $J$ 依赖 $u$，设 $\chi=JD^{-1}J^{\mathsf T}$，则

$$
\frac{d\chi}{du}
=\dot J D^{-1}J^{\mathsf T}
+JD^{-1}\dot J^{\mathsf T}
-JD^{-1}\dot D D^{-1}J^{\mathsf T}.
\tag{ST2.4}
$$

这是乘法法则及逆矩阵求导。改变钟尺、源归一化或探针轨迹时，前两项不能无条件略去。

分层消元的算子结合律已有仓内 Lean 锚点。式(ST2.1)至(ST2.4)增加了源与变分的实际义务。连续场论中，各块行列式必须来自同一受控积分与反项处方；独立定义的若干 zeta 行列式不自动满足同一乘法公式。一般时变背景下的延迟影响作用量，也不能直接用欧氏真空行列式替代。

## ST3．规范结构给 CUT 增加了实质条件

### 定理 ST3.1：线性规范恒等式在正确消元下下降

这一命题不要求完整矩阵正定。设实对称矩阵 $K$、可逆隐藏块 $C$ 以及规范生成矩阵 $R$ 满足

$$
K=\begin{pmatrix}A&B\\B^{\mathsf T}&C\end{pmatrix},
\quad R=\begin{pmatrix}R_V\\R_H\end{pmatrix},
\quad KR=0.
$$

则

$$
R_H=-C^{-1}B^{\mathsf T}R_V,
\qquad
\boxed{(A-BC^{-1}B^{\mathsf T})R_V=0.}
\tag{ST3.1}
$$

若完整线性读数还满足 $JR=0$，则 ST2 中的转移读数满足

$$
\boxed{J_{\mathrm{eff}}R_V=0.}
\tag{ST3.2}
$$

**证明。** $KR=0$ 的第二块给出 $R_H$；代回第一块得到(ST3.1)。再代入
$J_VR_V+J_HR_H=0$ 得到(ST3.2)。∎

这里只验证线性规范约束的下降。完整含规范零模的 $K$ 不被直接求逆；物理传播子需要适当规范固定或商空间构造。

### 定理 ST3.2：朴素投影的幂零缺陷

设分次空间上 $Q$ 的次数为 $+1$，$Q^2=0$；$P^2=P$ 且 $P$ 保持次数。则

$$
\boxed{(PQP)^2=-PQ(I-P)QP.}
\tag{ST3.3}
$$

**证明。** 在 $PQ^2P=0$ 中插入 $I=P+(I-P)$ 即得。∎

右边量化经过已删除部分再回到保留部分的贡献。如果它非零，压缩 $PQP$ 已经失去幂零性。若 $P$ 与 $Q$ 交换，右边为零，这是一个充分条件。

### 例 ST3.3：保持分次也不足以保证规范闭合

取次数为 $0,1,1,2$ 的基 $e_0,e_1,e_2,e_3$，定义

$$
Qe_0=e_1+e_2,\quad Qe_1=e_3,\quad Qe_2=-e_3,\quad Qe_3=0.
$$

则 $Q^2=0$。令 $P$ 保留 $e_0,e_1,e_3$，删除 $e_2$。这仍是保持次数的投影，但

$$
(PQP)^2e_0=e_3\ne0.
$$

因此，仅给变量标注“可见/隐藏”，不足以保证一个 BRST 型复形能够下降。物理态还需要在相应的 $\ker Q/\operatorname{im}Q$ 及适当内积上构造；链复形的线性恒等式不自动提供密度态正性。

### ST3.4 外部输入：弦场论中的规范相容积分

Sen 的超弦 Wilsonian 构造给出继承量子 BV 主方程的有效作用量。一个固定的形式约定为

$$
\frac12(S,S)-i\hbar\Delta_{\mathrm{BV}}S=0.
$$

其适用前提包括相应弦场空间、规范、顶点与积分处方。[ST-Sen]

树级同伦转移则将相互作用与规范恒等式一起转移到保留场上。Arvanitakis等给出一般场论构造；Singh对异质与II型超弦给出 twisted $L_\infty$ 表述。后者所讨论的同伦转移是经典/树级结果，不在本增订中被提升为其已经证明的任意圈阶定理。[ST-Arvanitakis] [ST-Singh]

这给本项目一个具体升级方向：将一般 CUT 限制为满足所需收缩、边界及规范条件的接口，并转移有效顶点和实际观察量。所转移的代数需要与本卷的因果响应和量子测量接口进一步匹配。

## ST4．从观察者完成接入全息恢复

### ST4.1 三类“相对熵”应保持各自对象类型

本卷可以同时研究：真实量子态的相对熵、ST7中辅助质量矩阵的相对熵、以及全息码子空间中的体内/边界相对熵。它们共享数学工具，比较的对象与物理含义不同。

JLMS在其全息条件和所述引力展开阶数下讨论体内与边界相对熵及模流。本文将其作为一种具体恢复实现的外部接口，不假定任意观察者窗口都已具有 AdS/CFT 对偶。[ST-JLMS]

### 命题 ST4.2：恢复误差控制全部约定的未来记录

固定有限维密度态 $\rho,\sigma$，其中 $\sigma$ 忠实；固定量子通道 $\mathcal N$，在有效支撑上定义

$$
\varepsilon_\rho
=D(\rho\|\sigma)-D(\mathcal N\rho\|\mathcal N\sigma).
$$

引用普适恢复定理：存在仅依赖 $\sigma,\mathcal N$ 的恢复通道 $\mathcal R$，在 $\operatorname{supp}\mathcal N\sigma$ 上采用该定理的恢复映射，并在正交补上作保迹扩展，使

$$
\varepsilon_\rho\ge-2\log F(\rho,\mathcal R\mathcal N\rho),
\quad F(\rho,\omega)=\|\sqrt\rho\sqrt\omega\|_1.
$$

这里 $F$ 为未平方保真度，自然对数用于相对熵。[ST-Recovery]

令 $\Lambda$ 为任意一个双方共用的后续 CPTP 实验过程，它可以包括有限次自适应测量及完整经典记录。对最终效果 $0\le E\le I$，有

$$
\boxed{
\left|\operatorname{tr}E\Lambda(\rho)
-\operatorname{tr}E\Lambda(\mathcal R\mathcal N\rho)\right|
\le\sqrt{1-e^{-\varepsilon_\rho}}
\le\sqrt{\varepsilon_\rho}.
}
\tag{ST4.1}
$$

整个经典记录分布的总变差距离满足同一界。

**证明。** 引用的恢复界给出 $F\ge e^{-\varepsilon_\rho/2}$。迹距离与保真度不等式给出

$$
\tfrac12\|\rho-\mathcal R\mathcal N\rho\|_1
\le\sqrt{1-F^2}\le\sqrt{1-e^{-\varepsilon_\rho}}.
$$

随后用 CPTP 的迹距离收缩性及效果统计界。最后用 $1-e^{-x}\le x$。∎

这是对一次初始恢复后整套共同实验的界，没有在每一步重复恢复。稀有结果条件化后的归一化概率需要另加成功概率下界；本命题控制的是未后选择的联合记录。它也不是自动的 diamond 范数界。

初始态必须包含能够影响这套未来实验的自由度。若只恢复一个纠缠楔代数，而未来 Heisenberg 观测量离开该可恢复代数，就不能直接应用(ST4.1)。这与仓内 `FutureStatisticsEquivalence` 的“先固定未来观测闭包”要求衔接。

## ST5．对偶要求连同观察协议一起运输

### 定理 ST5.1：完整线性响应的对偶协变

设两个正定有限高斯实现通过正交映射 $U$ 相关：

$$
\widetilde D=UDU^{\mathsf T},
\qquad \widetilde J=JU^{\mathsf T}.
$$

则

$$
\boxed{
\widetilde J\widetilde D^{-1}\widetilde J^{\mathsf T}
=JD^{-1}J^{\mathsf T}.
}
\tag{ST5.1}
$$

**证明。** $\widetilde D^{-1}=UD^{-1}U^{\mathsf T}$，代入后用 $U^{\mathsf T}U=I$。∎

如果 $P$ 是保留场投影，使用 $\widetilde P=UPU^{\mathsf T}$ 可以对应保留空间与隐藏空间。ST2的完整带源消元因此保持相同响应，即使两个坐标表示中的保留标签不同。

对一般实际对偶，需要运输态、所有允许仪器和协议，或给出相应代数同构；这个矩阵命题只验证其有限高斯部分。若对偶混合可见与隐藏变量，却仍强制沿用旧标签的截断与源，会比较不同实验。由此产生的差异不能据以宣称对偶失效。

### ST5.2 圆紧化的动量与绕数例子

取圆半径 $R>0$，弦参数 $\alpha'>0$。质量平方中的圆部分为

$$
\frac{n^2}{R^2}+\frac{w^2R^2}{\alpha'^2}.
$$

变换

$$
\widetilde R=\frac{\alpha'}R,\qquad (n,w)\mapsto(w,n)
$$

保持这部分谱。实际弦对偶还运输振子、物理态约束、简并度及必要的理论类型。圆对偶还要求

$$
\widetilde g_s=g_s\frac{\sqrt{\alpha'}}R,
\qquad
\widetilde\Phi=\Phi-\log\frac R{\sqrt{\alpha'}}.
$$

由此直接验证 $\widetilde R/\widetilde g_s^2=R/g_s^2$，这与对应低维引力作用量的归一化相容。相关圆紧化条件见[ST-Tong8]。这组公式没有把世界面模变换与目标空间 T 对偶视为同一个操作。

### 定理 ST5.3：只能恢复对偶轨道上的不变量

设完整观测数据 $\mathscr D(R)$ 使用相应运输后的实验满足

$$
\mathscr D(R)=\mathscr D(\alpha'/R).
$$

则由数据唯一恢复的任何标量 $\Theta$ 必须满足

$$
\Theta(R)=\Theta(\alpha'/R).
$$

特别地，任意输出裸半径实数的估计器 $\widehat R$，至少满足

$$
\boxed{
\max\left\{\left|\widehat R(\mathscr D)-R\right|,
\left|\widehat R(\mathscr D)-\alpha'/R\right|\right\}
\ge\frac12\left|R-\frac{\alpha'}R\right|.
}
\tag{ST5.2}
$$

**证明。** 相同输入数据必须有同一输出。用三角不等式
$|R-\alpha'/R|\le|R-\widehat R|+|\widehat R-\alpha'/R|$。∎

可恢复的候选量包括

$$
\left|\log\frac R{\sqrt{\alpha'}}\right|,
\qquad
\frac R{\sqrt{\alpha'}}+\frac{\sqrt{\alpha'}}R.
$$

因此本卷第30节的共同几何重建，在接入这种微观实现后，需要将“唯一”写成相对于规定规范和对偶关系的唯一。选择 $R\ge\sqrt{\alpha'}$ 可以选定代表元，但它是一项约定，不增加观测信息。

## ST6．黄金双更新进入弦世界面模群，钟尺进入物理读数

### 定理 ST6.1：同一个黄金矩阵给出两个不同归一化的参数

设

$$
F=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
A=F^2=\begin{pmatrix}2&1\\1&1\end{pmatrix},
\quad \varphi=(1+\sqrt5)/2.
$$

有 $A\in SL_2(\mathbb Z)$。它的特征值是 $\varphi^2,\varphi^{-2}$；仓内零坐标上的洛伦兹快速度增量是

$$
\eta_\varphi=2\log\varphi.
$$

环面世界面的复模 $\tau\in\mathbb H$ 在该模群元素下变换为

$$
\tau\mapsto\frac{2\tau+1}{\tau+1}.
$$

其固定点满足 $\tau^2-\tau-1=0$，所以是实轴上的 $\varphi$ 与 $\varphi'=-1/\varphi$，均不在 $\mathbb H$ 内。

用上半平面的标准双曲度量 $ds=|d\tau|/\operatorname{Im}\tau$，$A$ 的平移长度为

$$
\boxed{\ell(A)=4\log\varphi=2\eta_\varphi.}
\tag{ST6.1}
$$

**证明。** 行列式、特征值和固定点由二阶多项式计算。令

$$
w=\frac{\tau-\varphi}{\tau-\varphi'}.
$$

它是保持上半平面的实 Möbius 变换，且
$w(A\tau)=\varphi^{-4}w(\tau)$。连接两个固定点的测地线被送到虚轴；沿该轴的距离为
$|\log(\varphi^{-4})|=4\log\varphi$。∎

世界面环面基圈的模变换是标准弦微扰积分中的结构。[ST-Tong6] 本命题将仓内实际黄金矩阵放入这个群作用，给出可复核的表示接口。一个模群元素没有独自选定物理真空或物理时间；两个边界固定点也不构成位于物理模空间内部的固定点。

### 推论 ST6.2：常用的双曲模长度下界

对任意双曲 $A'\in SL_2(\mathbb Z)$，$|\operatorname{tr}A'|$ 是至少为3的整数。其伸缩因子（特征值模）$\lambda>1$ 满足
$\lambda+\lambda^{-1}=|\operatorname{tr}A'|$。因此

$$
\ell(A')=2\log\lambda\ge4\log\varphi,
$$

黄金双更新达到该界。这里固定了曲率为 $-1$ 的双曲度量规范；它是模群几何的经典极值，不能直接用来推导宇宙的最短时间或长度。

### 命题 ST6.3：弦框架与 Einstein 框架中的钟相位相容

在 $D>2$、允许该场重定义的区域，写

$$
G_E=\Omega^2G_s,
\qquad\Omega=e^{-2\Phi/(D-2)}.
$$

同一路径的固有时满足 $d\tau_E=\Omega\,d\tau_s$。对同一个两能级绝热探针，若完整钟作用量按该重定义运输，则其局部能隙满足
$\Delta E_E=\Omega^{-1}\Delta E_s$，因此

$$
\boxed{
\int\frac{\Delta E_E\,d\tau_E}{\hbar}
=\int\frac{\Delta E_s\,d\tau_s}{\hbar}.
}
\tag{ST6.2}
$$

**证明。** 第一式由度量重标定，第二式由同一相位作用量的场重定义。代入后 $\Omega$ 抵消。若背景变化过快，须保留探针跃迁、导数耦合和非绝热项；仅替换一个瞬时能隙不足以给出完整演化。∎

弦框架与 Einstein 框架的背景场重定义见[ST-Tong7]。这说明本卷的钟尺标定必须与完整物质作用量一同指定，不能只比较两个坐标表示中的度量分量。

## ST7．保留相对曲率结果，同时实行弦有效理论匹配

此前研究笔记对四维、有限个实标量场、共同曲率耦合 $\xi$、常数正定质量平方矩阵 $\mathsf M$ 及固定分块 $\mathcal P$ 给出

$$
\mathsf M_0=\mathcal P\mathsf M>0,
\qquad t=\operatorname{tr}\mathsf M,
\quad \rho_{\mathsf M}=\mathsf M/t.
$$

假定所选欧氏问题适用且算子正定，无边界或已单独处理边界项；曲率和背景变化相对最轻质量尺度足够小。所提取的是固定处方下的局域低导数项，不假定任意时变洛伦兹背景都允许 Wick 旋转。

同一热核处方下，比较打开与关闭跨块耦合的模型，局域欧氏曲率项
$\Gamma_{E,R}=-\kappa\int\sqrt g\,R$ 的高斯物质圈系数差为

$$
\Delta\kappa
=\frac{\hbar}{32\pi^2}\left(\frac16-\xi\right)
\left[\operatorname{tr}(\mathsf M\log\mathsf M)
-\operatorname{tr}(\mathsf M_0\log\mathsf M_0)\right].
\tag{ST7.1}
$$

对数使用同一质量平方参考尺度，它因迹相同而抵消。

**核对。** 标量热核中线性曲率系数是 $(1/6-\xi)R$。[ST-HeatKernel] 对两谱作相同 proper-time 积分，维数与迹相等使 $s^{-2}$ 曲率积分在 $s=0$ 有限。谱严格正定保证另一端收敛。两次分部积分给出括号中的差。由于 $\log\mathsf M_0$ 块对角，

$$
\operatorname{tr}(\mathsf M\log\mathsf M_0)
=\operatorname{tr}(\mathsf M_0\log\mathsf M_0),
$$

从而

$$
\boxed{
\Delta\kappa
=\frac{\hbar}{32\pi^2}\left(\frac16-\xi\right)
 tD(\rho_{\mathsf M}\|\mathcal P\rho_{\mathsf M}).
}
\tag{ST7.2}
$$

该相对熵编码质量谱及指定分块，实际量子场态另行给定。整个有效作用量差也不因此全部紫外有限。

### ST7.1 接入弦论时的三个匹配条件

**先识别实际子扇区。** 需要从选定弦紧化及其有效顶点中确定场分量、动能归一化、质量矩阵、曲率耦合和源。无法把任意正定矩阵直接认作一个已经构造出的弦真空。

**完整计入规范与统计。** 完整弦谱含不同自旋、费米子和规范约束，相关迹、行列式、热核系数与物理态投影各有结构。有限正定标量式(ST7.2)不能无条件求和成为整个无限弦谱的正熵公式。

**避免重复计数。** 若某组重场已经贡献到匹配后的引力 Wilson 系数，再把同一组场的行列式加一次会改变理论。应在统一的重整化方案与框架中写

$$
\kappa_{\mathrm{IR}}
=\kappa_{\mathrm{match}}(\mu)+\delta\kappa_{\mathrm{remaining}}(\mu),
$$

并检验达到所计算阶数的匹配尺度独立性；只有尚未计入的阈值或圈贡献才能增加。[ST-Sen] [ST-HeatKernel]

由弦论匹配可以约束本卷中原先自由的某些参数。它是否唯一确定现实的 $\xi$、模量或绝对 Newton 常数，取决于具体模型和独立数据，不能由通用桥式先行宣告。

## ST8．可执行的闭合顺序与验收对象

本增订的目标可以写成一张需要真正实现的相容关系：

$$
\begin{array}{ccc}
\text{固定弦模型、背景和完整源}
&\longrightarrow&\text{规范相容有效理论}\\
\downarrow\ \text{物理观察协议}&&\downarrow\ \text{转移后的相同协议}\\
\text{完整联合记录分布}
&=&\text{有效理论的联合记录分布}.
\end{array}
$$

精确等号要求保留全部必要项。采用截断后，右侧改为带已证明误差预算的近似。BV一致性、实际量子态正性、因果性和未来可恢复性是不同义务，任何一个不能自动替另一个作证。

第一步先在仓内现有真实载体上闭合带源 Schur 约化、方向变分及线性规范恒等式，并用ST3.3作为应被拒绝的截断实例。

第二步选择一个规范相容的弦有效子问题，明确保留场分量、消元传播子、顶点阶数、源/探针和边界条件。树级同伦转移与量子 BV 积分分别使用相应文献的假设，不将两种精度混记。

第三步在圆紧化中运输状态与协议，检查动量/绕数交换、dilaton归一化、截断窗口及完整响应相容。验收目标是具体量的相等和误差界，而非只出现 $R\leftrightarrow\alpha'/R$ 的符号。

第四步在明确有限码空间中构造 $\mathcal N,\mathcal R$ 及未来实验闭包，验证ST4.2。全息解释要另外给出实际编码、区域代数与适用的引力展开。

第五步在同一源、框架与反项方案中计算几何方向响应，检查ST2.3及匹配尺度依赖。最终引力动力学还需要背景变分方程、应力能守恒、状态条件和约束闭合。

**尚未承担的结论。** 本增订没有完成弦理论的 Lean 实现、连续因果场论的全部函数空间证明、真实紧化的模量选择、无限弦谱的阈值计算、非微扰AdS/CFT或现实宇宙的引力参数预测。上述普通证明给出的是可以复用且可以被反例约束的接口。

## ST9．文献与本增订的声明边界

外部理论归其原作者。本节列出主要读取位置；正文的有限矩阵证明和操作推论在本增订中给出，不据有限检索声称首次发现。

[ST-Tong6]: https://davidtong.org/pdfs/teaching/string-theory/string6.pdf "David Tong, String Theory, Chapter 6: String Interactions; Section 6.4.1 on torus moduli and modular transformations."
[ST-Tong7]: https://davidtong.org/pdfs/teaching/string-theory/string7.pdf "David Tong, String Theory, Chapter 7, Sections 7.2–7.3: background beta functions, low-energy action, string and Einstein frames."
[ST-Tong8]: https://davidtong.org/pdfs/teaching/string-theory/string8.pdf "David Tong, String Theory, Chapter 8, Sections 8.2–8.3: momentum, winding, T-duality and dilaton shift."
[ST-Sen]: https://arxiv.org/abs/1609.00459 "Ashoke Sen, Wilsonian Effective Action of Superstring Theory, JHEP 01 (2017) 108, DOI 10.1007/JHEP01(2017)108. Sections 2–4."
[ST-SenZwiebach]: https://arxiv.org/abs/2405.19421 "Ashoke Sen and Barton Zwiebach, String Field Theory: A Review (2024), DOI 10.1007/978-981-99-7681-2_62."
[ST-Arvanitakis]: https://arxiv.org/abs/2007.07942 "Alex S. Arvanitakis, Olaf Hohm, Chris Hull and Victor Lekeu, Homotopy Transfer and Effective Field Theory I: Tree-level, Fortschritte der Physik 70 (2022) 2200003, DOI 10.1002/prop.202200003. Sections 2–3 and 6."
[ST-Singh]: https://arxiv.org/abs/2405.08063 "Ranveer Kumar Singh, Algebraic structures in closed superstring field theory, homotopy transfer, and effective actions, Phys. Rev. D 110 (2024) 126007, DOI 10.1103/PhysRevD.110.126007. Sections 3–4 and the tree-level boundary in Section 1."
[ST-JLMS]: https://arxiv.org/abs/1512.06431 "Daniel L. Jafferis, Aitor Lewkowycz, Juan Maldacena and S. Josephine Suh, Relative entropy equals bulk relative entropy, JHEP 06 (2016) 004, DOI 10.1007/JHEP06(2016)004. Leading-order and nearby-state assumptions retained."
[ST-Recovery]: https://arxiv.org/abs/1509.07127 "Marius Junge, Renato Renner, David Sutter, Mark M. Wilde and Andreas Winter, Universal Recovery Maps and Approximate Sufficiency of Quantum Relative Entropy, Annales Henri Poincare 19 (2018) 2955–2978, DOI 10.1007/s00023-018-0716-0."
[ST-HeatKernel]: https://arxiv.org/abs/hep-th/0306138 "D. V. Vassilevich, Heat kernel expansion: user's manual, Physics Reports 388 (2003) 279–360, DOI 10.1016/j.physrep.2003.09.002."

---
