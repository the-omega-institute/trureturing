# 正交时间场论 OTF-005：轴面几何、相位纤维与内生闭合

> 理论参考输入：本稿为用户提供的研究正文，包含普通数学证明，未作本候选的 Lean/kernel 认证。原图以文内文字和公式呈现。

OTF RESEARCH SERIES / 005 / VERSION 1.0

正交时间场论

轴面几何、相位纤维与内生闭合

从单态对偶到扇形旋转、量子读出与全态反馈

Axis–Plane Geometry and Phase Fibres\
Endogenous Closure Beyond Scalar Fixed Points

**几何核心** 单态的正交对偶面生成稳定子转动；改变状态方向的面属于另一部分。 单位半径下，非反向两态的最短扇形有向面积精确生成最小旋转元。

$$
\begin{gathered}
 \Lambda^2V=\mathbb R(\star n)\oplus(n\wedge T_nS^2),\\
 R_{ab}=e^{-\Sigma_{ab}},\qquad
 \Sigma_{ab}=\frac{\theta}{2}\frac{a\wedge b}{\sin\theta},\quad 0<\theta<\pi.
 \end{gathered}
$$

**闭合核心** 余弦角度的吸引点可以伴随持续相位转动。 将相位和记录内生之后，标量不动点与整体不动点成为不同命题。

$$
T_s(x,z)=\bigl(s\cos x,e^{\mathrm i\omega(x)}z\bigr)
 \ \sim\
 F_s\times\bigl(z\mapsto e^{\mathrm i\omega(s\alpha)}z\bigr),
 \qquad \alpha=\cos\alpha.
$$

**范围** 提供完整候选约束及普通数学证明，条件性重建有限量子接口； 几何长度、曲率面积、钟时及相位分别标定。 不把结构对应直接升级为已验证的基础物理同一性。

2026 年 11 月 8 日 / Asia–Singapore

项目默认分支 dev，本轮固定提交：

`a5b3a5ef05eeeeba9338b2f682ae41c8b3f40822`

承接 OTF-001–004 与当前 AURIC 供应者；未运行新的 Lean 构建。

## 摘要

本文把线、面、方向、量子门、观察者与自反馈放在同一有限操作模型中， 并区分几何对偶、相干关系和实际动力学。首先证明三维完整线面对偶的条件性、 单态稳定子面与转向面的精确分解，以及最短平面扇形面积生成半角旋转元的公式。 以全方向线性锐比较、正性和混合仿射性为明确前提，重建 Clifford–Pauli 代数、 Bloch 状态球与 Born 半角概率；由此识别实轴投影实际对应非选择退相干。 随后证明方向变化的一形式、球面面积二形式与物理时长不能互换， 并以量子几何张量、Hopf 联络及细分投影极限连接局部转向与闭路相位。 本轮进一步构造余弦–相位斜积，给出一个一致收敛的相位校正级数， 把完整反馈精确共轭到收缩底流与恒速圆周转动的直积。 因此标量不动点可对应固定相位纤维、周期轨道或稠密相位运动； 自治幺正整体也不具有非平凡的强收敛吸引。 观察者的参考、相位访问和记录历史均列入模型。 标准结果保留来源归属；本轮新增综合及其限制逐项给出。

**关键词：** Hodge 对偶；Clifford 代数；量子几何；内部参考； 几何相位；扇形面积；关系时钟；余弦反馈；斜积。

## 目录

- [1　研究对象与完整候选约束](#section-1)
- [2　单态线面对偶：存在一个平面，不等于存在一个振荡](#section-2)
- [3　两态、派生投影与扇形面积生成的门](#section-3)
- [4　从锐比较与正性条件重建量子接口](#section-4)
- [5　观察轴、经典概率线与相干平面](#section-5)
- [6　单态面与转向面的统一：垂直、水平与钟](#section-6)
- [7　量子几何张量：同一结构中的长度、面积与相位](#section-7)
- [8　端点相同而历史不同：内部闭路与连续投影](#section-8)
- [9　观察者内生：注意力、仪器与可读关系](#section-9)
- [10　余弦自指的完整提升：压缩基底与转动纤维](#section-10)
- [11　理论所得、依赖关系与可区分的实验合同](#section-11)
- [A　来源输入、固定版本与证明归属](#section-A)

<a id="section-1"></a>

## 1　研究对象与完整候选约束

本轮用户提出一个贯穿几何、本体、观察与反馈的链条，并附有五项所谓证明。 本文完整读取附件后，保留其中成立的恒等式， 同时为其越过的类型边界补充定义、条件或反例。 特别需要区分：向量与标量投影、单态对偶与实际转向、 方向射线与旋量相位、几何长度与钟时、部分读出平衡与整体不动。

当前固定项目中的 OTF-001 已有半角旋转、端点稳定子、几何长度与 闭路相位；V53 已有线性锐比较及正性读出的 qubit 重建； V74、V78 已讨论相位纤维、兼容生成元与内部参考 [\[7\]](#ref-repo_otf1), [\[9\]](#ref-repo_v53), [\[8\]](#ref-repo_v74), [\[10\]](#ref-repo_v78)。 本文重证必要部分，使本稿可独立阅读；不把这些供应者重新宣称为首次发现。 本轮的主要综合推进是单态面与转向面的分解， 以及把余弦反馈提升到包含相位与记忆的整体后检验其真正闭合条件。

### 1.1　AX-005：七项候选结构约束

#### 结构约束 1.1：C1：有限关系接口与对偶要求

给定非零、有限维、正定实内积空间 $V$。 对一个基本接口，要求完整方向空间 $V$ 与完整反对称二次关系空间 $\Lambda^2V$ 之间有无冗余线性同构。 定向由内部参考承载；共同转动参考与所有状态只是坐标改写。 本约束是接口选择条件，不预先宣称物理时空维数。

#### 结构约束 1.2：C2：全方向线性锐比较

在非零含单位的实结合 $`*`$-代数中，有实线性映射 $A:V\to\mathfrak A_{\rm sa}$。 对每个单位 $n$，$A(n)^2=1$；所研究的局部代数由 $1,A(V)$ 生成。 本条件把不同方向的比较锁定在同一个代数，排除每个方向任意另设规则。

#### 结构约束 1.3：C3：正性、归一化与混合仿射性

操作态是在自伴部分上的实线性泛函 $L$， 这里正锥定义为有限和 $`\sum_jY_j^*Y_j`$； 后文同构把它识别为通常的半正定矩阵锥。 满足 $L(1)=1$ 及对正元素 $X$ 有 $L(X)\ge0$。 效应为 $0\le E\le1$，其概率为 $L(E)$。 对经典随机准备，响应按准备权重仿射组合。 这些条件是 Born 重建的明确输入，不由各向同性一项代替。

#### 结构约束 1.4：C4：可逆历史与内部参考

可逆比较由保持代数和 $`*`$ 结构的门实现； 连续连接到恒等的定向转向使用旋转元。 方向路径、完整门历史及相位参考分别保存。 对指定的光滑酉历史可引入生成元，但其速率尚须钟标定。

#### 结构约束 1.5：C5：复合、仪器与记录

多个量子接口采用已声明的复张量组合。 其共同复结构及相位比较的准备条件须先指定。 允许仪器由完全正、迹不增分支组成，全部分支之和保迹。 程序、参考、准备寄存器、记忆与未访问自由度均属于整体； 实际分支条件化只在其概率非零时定义。 该复合及更新规则不是单个三维接口的维数计数结论。

#### 结构约束 1.6：C6：内部钟与有限资源

物理时间使用内部钟读数、单位标定及适用区间。 几何弧长、扇形面积和闭路相位本身不指定秒。 有限协议使用有限准备、存储及精度； 连续控制和无限次细分另作有条件的数学极限。

#### 结构约束 1.7：C7：完整反馈合同

下一设置由内部程序、已存记录和参考状态更新。 若指定 $x_{n+1}=s\cos x_n$，需声明弧度编码、符号政策、增益和估计方式。 声称全态不动时，必须同时检查所有可访问的相位、控制与记忆； 忽略某些自由度得到的平衡只称相应商或读出的平衡。

这些约束规定一类模型的可兼容结构。 “没有外部物理观察者”不意味着没有形式前提； 后文用相同几何配上不同速率、相位和反馈，直接证明几何不足以唯一选定动力学。

<a id="section-2"></a>

## 2　单态线面对偶：存在一个平面，不等于存在一个振荡

#### 定理 2.1：完整一次–二次关系同构的维数条件

若 $\dim V=n\ge1$ 且 $V\cong\Lambda^2V$ 为完整线性空间同构， 则 $n=3$。反之，定向的三维 Euclidean 空间具有自然的 Hodge 同构 $\star:V\to\Lambda^2V$。

**证明。**

同构要求 $n=\binom n2=n(n-1)/2$，故 $n(n-3)=0$； 非零条件给出 $n=3$。 三维中 Hodge 算子由内积与单位定向体积元定义，直接把正交基 $e_1,e_2,e_3$ 映到 $e_2\wedge e_3,e_3\wedge e_1,e_1\wedge e_2$。

$\square$

这个定理证明的是 C1 的条件性维数选择。 各向同性的 Euclidean 空间存在于其他维数，因而“各向同性”自身不选三维； 局部 Bloch 接口的三维也不等于全部观察者或物理时空只有三维 [\[11\]](#ref-repo_axes)。

#### 定义 2.2：Clifford 乘积与定向体积元

在 $\operatorname{Cl}_{3,0}$ 中，$uv+vu=2u\cdot v$， 几何积为 $uv=u\cdot v+u\wedge v$。 取正定向正交单位基，令 $I=e_1e_2e_3$。 逆序运算 $\widetilde{\cdot}$ 反转乘积中因子的顺序。 标量单位写作 $1$，体积元写作 $I$，二者不混用。

#### 定理 2.3：Hodge 对偶的符号与等变性

$I$ 在 $\operatorname{Cl}_{3,0}$ 中居中，且 $I^2=-1$。 对向量 $v$、双向量 $B$，

$$
\star v=vI,\qquad \star B=-BI,\qquad \star^2=1.
$$

对单位 $n$，$\star n=nI$ 是 $n^\perp$ 的单位有向面积元。 它只依赖 $n$、度量及定向，不增加新的独立状态自由度。 该对应对 $\operatorname{SO}(3)$ 等变；若 $Q\in O(3)$，

$$
(\Lambda^2Q)(\star v)=\det(Q)\,\star(Qv).
$$

**证明。**

把 $e_j$ 与三个基因子交换，直接得到 $e_jI=Ie_j$， 以及 $I^2=(-1)^3=-1$。 在基上计算 $e_1I=e_2e_3$，而 $(e_2e_3)I=-e_1$， 给出各级 Hodge 符号及 $\star^2=1$。 正交变换把体积元变为 $\det(Q)I$，于是得到最后的等变公式。 推广到任意单位 $n$ 只需使用一个正定向正交变换。

$\square$

Hodge 星不是“对任意 grade 连续右乘同一个 $I$”。 后者平方为 $-1$，而三维正定 Hodge 星复合平方为 $+1$。 这一符号区别属于定义本身[\[5\]](#ref-hodge)。 另外，$n$ 和 $-n$ 的有向面积相反； 若只保留无定向直线 $\mathbb Rn$，还不能确定面积的定向。

#### 定理 2.4：单态给出切平面的复结构

对 $n\in S^2$ 及 $v\in T_nS^2=n^\perp$，定义

$$
J_n(v)=n\times v.
$$

则

$$
J_n^2=-\operatorname{id},\qquad
 \left\|J_nv\right\|=\left\|v\right\|,\qquad
 g(J_nu,v)=n\cdot(u\times v).
$$

在 Clifford 记法中，$J_n(v)=v(nI)$。

**证明。**

向量三重积给出 $n\times(n\times v)=n(n\cdot v)-v=-v$。 正交性给出范数等式；标量三重积给出最后的内积等式。 在 $n=e_3,v=e_1,e_2$ 的基上检验右乘公式， 再由旋转等变性推广。

$\square$

这是单态伴生面的一个精确意义：它使该方向的两维切平面具有 九十度转向与定向面积结构。它没有指定振幅、频率、能量、相位原点或传播方程。

#### 定理 2.5：无额外参考不能等变选择横向零相位

不存在 $\operatorname{SO}(3)$ 等变映射 $u:S^2\to\mathbb R^3$， 同时满足 $u(n)\perp n$、$\left\|u(n)\right\|=1$。 该结论甚至不需要假设连续性。

**证明。**

固定 $n=e_3$。绕 $e_3$ 的每个旋转都固定 $n$， 等变性要求它们全部固定 $u(e_3)$。 这些旋转的公共固定向量空间是 $\mathbb Re_3$， 与 $u(e_3)\perp e_3$ 及单位范数矛盾。

$\square$

因此单轴确定整个正交平面，却不确定平面中的一根首选半径。 完整内部参考或历史可以给出这根半径；它们是额外的内部信息。

<a id="section-3"></a>

## 3　两态、派生投影与扇形面积生成的门

#### 定义 3.1：非反向端点及其关系量

令 $a,b\in S^2$，$c=a\cdot b=\cos\theta$， $0<\theta<\pi$。定义

$$
C=ca,\qquad
 u=\frac{b-ca}{\sin\theta},\qquad
 B_{ab}=\frac{a\wedge b}{\sin\theta}=a\wedge u.
$$

则 $u\perp a$、$\left\|u\right\|=1$、$B_{ab}^2=-1$。

#### 定理 3.2：派生投影唯一，但不等于任意第三态

$C=(a\cdot b)a$ 是 $b$ 在 $\mathbb Ra$ 上的唯一正交投影， 不引入独立第三点自由度。 但当 $0<\theta<\pi$ 时，$C$ 一般不在纯方向球面上； 任意另给的路径中间态 $d\in S^2$ 也不由 $a,b,C$ 决定。

**证明。**

若 $b=\lambda a+w$ 且 $w\cdot a=0$，内积给出 $\lambda=a\cdot b$。 $\left\|C\right\|=|\cos\theta|<1$，说明它位于球内。 同一对端点之间存在不同中间点与不同曲线，投影公式对这些选择无约束。

$\square$

#### 定理 3.3：端点关系积与通用转向门的区别

端点关系积满足

$$
ab=\cos\theta+B_{ab}\sin\theta=e^{B_{ab}\theta},
 \qquad a(ab)=b.
$$

但一般三维旋转应使用

$$
\boxed{\quad
 R_{ab}
 =\frac{1+ba}{\sqrt{2(1+a\cdot b)}}
 =e^{-B_{ab}\theta/2},
 \qquad R_{ab}a\widetilde{R_{ab}}=b.\quad}
$$

对任意向量 $x$，$x\mapsto R_{ab}x\widetilde{R_{ab}}$ 保持向量 grade、内积和转动平面的正交补。

**证明。**

第一式由几何乘积与 $B_{ab}^2=-1$ 得出。 又 $ba=\cos\theta-B_{ab}\sin\theta$， 半角公式给出 $R_{ab}$ 的两种表达及 $R_{ab}\widetilde{R}_{ab}=1$。 在正交基 $a,u,k$ 中，直接计算

$$
R_{ab}a\widetilde{R}_{ab}=\cos\theta\,a+\sin\theta\,u=b,
$$

$$
R_{ab}u\widetilde{R}_{ab}=-\sin\theta\,a+\cos\theta\,u,
 \qquad R_{ab}k\widetilde{R}_{ab}=k,
$$

其中 $k\perp a,u$。 所以该作用是这个基中的标准正交旋转。 任意把 $a$ 送至 $b$ 的 $\operatorname{SO}(3)$ 旋转，设主旋角为 $\phi\in[0,\pi]$、单位轴为 $k$。Rodrigues 公式给出

$$
a\cdot b=\cos\phi+(1-\cos\phi)(k\cdot a)^2\ge\cos\phi,
$$

故 $\theta\le\phi$。上述旋转达到该下界。 在 $0<\theta<\pi$ 时，等号要求 $k\perp a$， 端点再唯一确定平面与转向。因此最小主旋角的 $\operatorname{SO}(3)$ 旋转唯一； 选择标量部分为正的 Spin 提升即得 $R_{ab}$。 此处最小性不涉及经过的物理时间或作用量。

$\square$

#### 反例 3.4：单输入等式不能替代全空间门

取 $a=e_1,b=e_2$。虽然 $e_1(e_1e_2)=e_2$，但

$$
e_3(e_1e_2)=I
$$

是三向量，不是空间向量。 所以 $x\mapsto x(ab)$ 不是整个 $\mathbb R^3$ 上的旋转。

单侧乘法在所选转动平面内有效， 通用三维作用需要双侧半角，这一范围在原作者几何代数教程中有明确区分 [\[4\]](#ref-gable), [\[6\]](#ref-lasenby)。

#### 定理 3.5：最短扇形面积精确生成最小旋转元

在 $a,u$ 平面中取最短单位扇形参数化

$$
X(r,t)=r(a\cos t+u\sin t),
 \quad0\le r\le1,\quad0\le t\le\theta .
$$

其有向面积双向量为

$$
\Sigma_{ab} =
 \int_0^\theta\int_0^1
 \partial_rX\wedge\partial_tX\,\mathrm dr\,\mathrm dt =
 \frac{\theta}{2}B_{ab}.
$$

因此

$$
\boxed{R_{ab}=e^{-\Sigma_{ab}}.}
$$

半径为 $R_0$ 时，$\Sigma^{(R_0)}_{ab}=R_0^2\Sigma_{ab}$， 相同旋转元为 $\exp[-\Sigma^{(R_0)}_{ab}/R_0^2]$。

**证明。**

直接求导得 $\partial_rX\wedge\partial_tX=r(a\wedge u)=rB_{ab}$。 积分给出 $\theta B_{ab}/2$，再应用定理 3.3。

$\square$

这保留了“夹角面积生成转向”的直观，并给出精确的归一化。 它使用已有度量、原点、单位半径和最短分支； 不需要任意添加第三个球面状态。

**图示（文字版）。** 左侧为单轴 $n$ 及其正交平面 $n^\perp$，平面内标出横向 $u,v$，其有向面积元为 $\star n$；该平面是稳定子面。右侧为单位圆内从 $a$ 向 $b$ 转过 $\theta$ 的最短平面扇形，$b$ 向 $a$ 轴的垂足为 $C=(a\cdot b)a$，有向扇形面积为 $\Sigma_{ab}=(\theta/2)B_{ab}$。

图示：左为单轴伴生平面的示意投影； 右为两态最短转向的单位平面扇形。二者承担不同作用。

#### 命题 3.6：相同端点仍有稳定子自由度

对 $a\ne-b$，所有满足 $R\in\operatorname{Spin}(3)$、$Ra\widetilde{R}=b$ 的旋转元可写为

$$
R=e^{-\varphi\,\star b/2}R_{ab},
 \qquad \varphi\in\mathbb R/(4\pi\mathbb Z).
$$

当 $a=b$，分式连续延拓为 $R_{aa}=1$，并定义 $\Sigma_{aa}=0$； 单位平面 $B_{ab}$ 本身不能唯一延拓，但稳定子仍存在。 $\varphi$ 的 $4\pi$ 周期属于 Spin 元素；在向量作用中相差 $2\pi$ 的参数诱导相同旋转。 当 $a=-b$，端点不指定转动平面，任取单位 $u\perp a$ 所得半圆旋转都可送达目标。

**证明。**

若 $Ra\widetilde{R}=b$，则 $S=R\widetilde{R_{ab}}$ 固定 $b$。 三维中固定轴 $b$ 的定向旋转恰为绕该轴的圆周群， 其旋转元为 $e^{-\varphi bI/2}$。 反向情形中，任意包含 $a$ 的平面内转过 $\pi$ 都将它送至 $-a$。

$\square$

#### 注 3.7：五种不同的面积量

单态单位对偶为 $\star a$； 两态平行四边形面积为 $\sin\theta$； 两态三角形面积为 $\sin\theta/2$； 最短单位扇形面积为 $\theta/2$； 球面闭路围成的立体角记为 $\Omega$。 前四项也不能互换。特别是 $\sin\theta=\sin(\pi-\theta)$， 故仅给外积面积模不能恢复转角。

#### 命题 3.8：两角参数化的正确范围

正交架 $e_1,e_2,e_3$ 给出满射

$$
n(\alpha,\beta)=
 \cos\alpha\,e_1+
 \sin\alpha\cos\beta\,e_2+
 \sin\alpha\sin\beta\,e_3,
$$

其中 $\alpha\in[0,\pi]$、$\beta\in[0,2\pi)$。 这是一种参数化，不是任意物理路径必须经过两次有限九十度转动的证明。

**证明。**

对单位 $n$，取 $\alpha=\arccos(n\cdot e_1)$； 非极点处取相应 $\operatorname{atan2}$，模 $2\pi$ 后得到 $\beta\in[0,2\pi)$。 在极点处 $\beta$ 任意，并非另一个确定读数。 任意光滑球面路径只要求 $n\cdot\dot n=0$； 其有限转角可以任意小，因而不被要求先经过指定的正交状态。

$\square$

<a id="section-4"></a>

## 4　从锐比较与正性条件重建量子接口

本节不把复矩阵作为未经解释的黑盒。 先由 C2 的跨方向约束得到 Clifford 代数，再给出显式矩阵表示。 这条条件性重建已由项目 V53 供应，本文保留其附加前提 [\[9\]](#ref-repo_v53)。

#### 定理 4.1：全方向线性锐性给出 Clifford 关系

在 C2 下，对任意 $u,v\in V$，

$$
A(u)A(v)+A(v)A(u)=2(u\cdot v)1.
$$

**证明。**

齐次性把单位方向条件推广为 $A(v)^2=\left\|v\right\|^2 1$，包括 $v=0$。 展开 $A(u+v)^2$，减去 $A(u)^2+A(v)^2$， 与 $\left\|u+v\right\|^2-\left\|u\right\|^2-\left\|v\right\|^2=2u\cdot v$ 比较即得。

$\square$

#### 定理 4.2：显式 Clifford–Pauli 对应

取

$$
\sigma_1=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
 \sigma_2=\begin{pmatrix}0&-\mathrm i\\\mathrm i&0\end{pmatrix},\quad
 \sigma_3=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
$$

映射 $e_j\mapsto\sigma_j$ 给出实 $`*`$-代数同构

$$
\operatorname{Cl}_{3,0}\cong M_2(\mathbb C),\qquad
 I\mapsto\mathrm i1_2,\qquad
 \widetilde{X}\mapsto X^\dagger.
$$

C2 所生成的非零代数也与此同构。

**证明。**

这些矩阵满足同样的反对易关系，因此给出代数同态。 任意 Clifford 字可重排到八个基字 $1,e_1,e_2,e_3,e_2e_3,e_3e_1,e_1e_2,I$。 其像为 $1_2,\sigma_1,\sigma_2,\sigma_3,\mathrm i\sigma_1,\mathrm i\sigma_2,\mathrm i\sigma_3,\mathrm i1_2$， 在实数上独立并张成全部 $M_2(\mathbb C)$，故同构。 矩阵共轭转置固定 $\sigma_j$ 并反转乘积，因而对应逆序。

由定理 4.1，C2 的生成代数是该代数的含单位商。 $M_2(\mathbb C)$ 作为实代数也是简单的： 任意非零双边理想经左右乘矩阵单位取得非零单项， 再乘其复系数的逆即可取得全部矩阵单位和单位元。 所以非零含单位商的核只能为零。

$\square$

取 $p=(1+e_3)/2$，左理想 $\operatorname{Cl}_{3,0}p$ 的矩阵像恰为 第二列为零的复矩阵。以 $p,e_1p$ 为复基，可把它识别为 $\mathbb C^2$。 因此复二维旋量可由所建代数的最小左理想实现； 该构造仍依赖 C1–C2，而非仅凭“存在”一词。

#### 定理 4.3：正归一读出恰为 Bloch 球

局部自伴部分为

$$
\mathfrak A_{\rm sa}=\{a1+v:a\in\mathbb R,\ v\in V\}.
$$

其正锥满足

$$
a1+v\ge0\iff a\ge\left\|v\right\|.
$$

每个 C3 泛函恰可唯一写成

$$
L_r(a1+v)=a+r\cdot v,\qquad \left\|r\right\|\le1.
$$

其极端点恰为 $\left\|r\right\|=1$。 对单位 $m$，事件投影 $p_m=(1+m)/2$ 的概率为

$$
\boxed{\quad
 L_r(p_m)=\frac{1+r\cdot m}{2}.\quad}
$$

纯态 $r=n$ 与方向 $m$ 夹角为 $\theta$ 时， $L_n(p_m)=\cos^2(\theta/2)$。

**证明。**

矩阵自伴部分由 $1_2,\sigma_j$ 实线性张成。 由于 $(v\cdot\boldsymbol{\sigma})^2=\left\|v\right\|^2 1_2$， $a1_2+v\cdot\boldsymbol{\sigma}$ 的特征值为 $a\pm\left\|v\right\|$， 给出正锥。 实线性及 $L(1)=1$ 给出 $L(a1+v)=a+r\cdot v$。 若 $\left\|r\right\|\le1$，则对正元素 $L(a1+v)\ge a-\left\|r\right\|\left\|v\right\|\ge0$。 若 $\left\|r\right\|>1$，取正元素 $1-r/\left\|r\right\|$，得到负读出，矛盾。 闭单位球的内部点能沿某条线作非平凡凸分解； 单位球面上的点由 Euclidean 范数的严格凸性不可如此分解。 最后直接代入 $p_m$ 并使用半角公式。

$\square$

定义 $\rho_r=(1_2+r\cdot\boldsymbol{\sigma})/2$ 后， $L_r(X)=\operatorname{tr}(\rho_rX)$ 对 $X=X^\dagger$ 成立； 如需作用于一般矩阵，再取此泛函的复线性延拓。 若 $\rho_n=|\psi_n\rangle\langle \psi_n|$， 则 $L_n(p_m)=|\langle\psi_m,\psi_n\rangle|^2$， 这给出通常的纯态平方概率形式。 本结论中的正性、实线性、锐比较与混合规则都属于证明依赖。

#### 反例 4.4：各向同性本身不选出平方律

设 $f:[-1,1]\to[-1,1]$ 连续、奇，且 $f(1)=1$。

$$
p_f(n,m)=\frac{1+f(n\cdot m)}2
$$

满足共同转动不变、互补读出归一化及端点确定性。 $f(t)=t^3$ 也满足这些条件，却不同于 Born 读出。 令 $0<t<1$。权重 $(1+t)/2,(1-t)/2$ 的 $\pm e_3$ 准备， 与等权准备 $n_\pm=\pm\sqrt{1-t^2}\,e_1+t e_3$， 有相同 Bloch 重心 $te_3$。 前者的 $e_3$ 结果概率为 $(1+t)/2$， 后者按 $f=t^3$ 为 $(1+t^3)/2$。 在本节重建的 Bloch 操作态中，两种准备均代表 $\rho_{te_3}$； 因此该替代规则不尊重该模型的混合等价。 只要求抽象的随机混合仿射性而不规定操作态空间，尚不能排除 保留额外准备信息的其他模型。

#### 命题 4.5：可逆转向与 Schrödinger 生成元

旋转元 $R=e^{-B\theta/2}$ 在矩阵表示中是行列式一的酉矩阵， 通过 $\rho\mapsto R\rho R^\dagger$ 实现相同 Bloch 转向。 任意满足 $U(0)=1_2$ 的可微酉历史 $U(t)$ 定义

$$
H(t)=\mathrm i\hbar\,\dot U(t)U(t)^\dagger,
$$

则 $H(t)=H(t)^\dagger$，且 $\mathrm i\hbar\,\dot\psi=H\psi$ 对 $\psi(t)=U(t)\psi(0)$ 成立。

**证明。**

双向量逆序变号，所以旋转元满足 $\widetilde{R}R=1$； 它在矩阵像中由无迹反自伴生成元指数得到，故行列式一且酉。 微分 $UU^\dagger=1$ 得 $\dot UU^\dagger$ 反自伴， 从而 $H$ 自伴；其余直接代入。

$\square$

这是指定酉历史的生成元表示，不从几何唯一确定 $H$ 或 $\hbar$ 的实验标定。 一般 $U(2)$ 门还允许中心相位 $e^{\mathrm i\chi}R$； 仅讨论 $\operatorname{Spin}(3)$ 的端点稳定子时，不应把这一额外中心因子漏入同一量词。

#### 定理 4.6：有条件的有限复合扩展

若 C5 选定共同复结构及复张量组合，$N$ 个基本接口的代数为 $M_{2^N}(\mathbb C)$。任一秩 $1\le d\le2^N$ 的投影角落 $PM_{2^N}(\mathbb C)P$ 与 $M_d(\mathbb C)$ 同构。 角落的单位为 $P$，归一化为 $L(P)=1$。 在识别为 $M_d(\mathbb C)$ 后，归一正实线性自伴读出唯一写为

$$
L(X)=\operatorname{tr}(\rho X),\qquad \rho\ge0,\quad\operatorname{tr}\rho=1.
$$

**证明。**

矩阵单位的张量积形成复合矩阵单位。 选择 $P$ 的像空间正交基，角落代数就是该像空间上的全部矩阵。 自伴矩阵上的实 Hilbert–Schmidt 配对非退化， 故存在唯一自伴 $\rho$ 代表 $L$。 对所有秩一正投影测试正性，得到 $\rho\ge0$； 以单位元测试得到 $\operatorname{tr}\rho=1$。

$\square$

从而标准有限维状态、效果概率和酉方程可在所列约束下重建。 复合规则及仪器规则仍为额外输入。 例如转置是单系统上的正保迹映射，却不是完全正： 对 Bell 态只在一侧转置会产生特征值 $-1/2$。 具体地，$|\Phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2$ 的密度矩阵 经一侧转置为交换算子的二分之一； 反对称向量 $(|01\rangle-|10\rangle)/\sqrt2$ 对应特征值 $-1/2$。 所以“局部正性”不能替代 C5 的完整复合兼容性。

<a id="section-5"></a>

## 5　观察轴、经典概率线与相干平面

#### 定义 5.1：两种不能混同的投影

实方向空间中的正交投影为

$$
Q_n(r)=(r\cdot n)n,\qquad Q_n^2=Q_n.
$$

量子事件投影为

$$
p_n=\frac{1+n\cdot\boldsymbol{\sigma}}{2},\qquad p_n^2=p_n.
$$

前者作用于三维 Bloch 坐标，后者作用于复二维旋量。 $Q_n=Q_{-n}$，而 $p_{-n}=1_2-p_n$。

#### 定理 5.2：实轴投影恰为非选择锐测量

对 $\rho_r=(1_2+r\cdot\boldsymbol{\sigma})/2$，

$$
\mathcal D_n(\rho_r)
 =p_n\rho_rp_n+p_{-n}\rho_rp_{-n}
 =\rho_{Q_n(r)}.
$$

两个选择性结果的概率为 $(1\pm r\cdot n)/2$； 正概率分支的归一态分别为 $p_{\pm n}$。

**证明。**

在 $n=e_3$ 的基中，$p_n,p_{-n}$ 是两个对角矩阵单位； 双侧夹乘后求和保留对角元并消去交叉元， 恰把 $(r_1,r_2,r_3)$ 变为 $(0,0,r_3)$。 旋转协变性推广到任意 $n$。 每个秩一分支满足 $p_{\pm n}\rho_rp_{\pm n} =\operatorname{tr}(\rho_rp_{\pm n})p_{\pm n}$。

$\square$

因此附件中的 $X\mapsto(X\cdot n)n$ 有明确的量子解释： 它对应忽略结果的测量通道。 该通道把 Bloch 球送到一条 *经典二元概率线段* ， 不必选出某个唯一极点。 若纯方向 $b\perp n$，派生投影 $C=0$ 对应 $1_2/2$， 而不是“对象不存在”。

#### 定理 5.3：内部参考架下的线–相干分解

设 $(u,v,n)$ 为内部正定向正交架。令

$$
z=r\cdot n,\qquad
 c=\frac{r\cdot u-\mathrm ir\cdot v}{2}.
$$

在对应测量基中，

$$
\rho_r=
 \begin{pmatrix}(1+z)/2&c\\\overline c&(1-z)/2\end{pmatrix},
 \qquad
 z^2+4|c|^2=\left\|r\right\|^2\le1.
$$

绕 $n$ 转动参考架会改变 $c$ 的相位坐标，而不改变 $|c|$。 非选择通道 $\mathcal D_n$ 固定 $z$ 并令 $c=0$。

**证明。**

将 $r=(r\cdot u)u+(r\cdot v)v+zn$ 代入 Pauli 表示， 得到矩阵形式及勾股恒等式。 横向架旋转对两个实坐标作平面旋转，等价于给 $c$ 乘单位相位。 最后应用定理 5.2。

$\square$

这给“线与面是同一态的相对表现”一个操作版本： 在指定参考下，轴向坐标给出两结果的概率偏置， 横向平面承载相干的两个实坐标。 单态 $r=n$ 仍具有几何对偶面，但在自身基中 $c=0$； 几何上存在一个相干坐标空间，并不保证该态在该空间有非零分量。 单次点击记录与重复试验的干涉分布也不互斥。

#### 命题 5.4：面积控制比较的非对易性

对单位 $a,b$，

$$
[p_a,p_b]=\frac{\mathrm i}{2}(a\times b)\cdot\boldsymbol{\sigma},
 \qquad
 \left\|[p_a,p_b]\right\|_{\rm op}=\frac{|\sin\theta|}{2}.
$$

**证明。**

由 $(a\cdot\boldsymbol{\sigma})(b\cdot\boldsymbol{\sigma}) =(a\cdot b)1_2+\mathrm i(a\times b)\cdot\boldsymbol{\sigma}$， 减去逆序乘积并除以四即可。 向量 Pauli 算子的算子范数为对应向量长度。

$\square$

这里外积确实刻画两种锐比较的不相容程度。 它不把全部物理波动都归约为某个外积。

#### 反例 5.5：线性投影本身不删除干涉交叉项

令 $Q_o$ 为实线投影。若 $Q_o(B_j)=a_jo$，则

$$
\left\|Q_o(B_1+B_2)\right\|^2
 =(a_1+a_2)^2=a_1^2+a_2^2+2a_1a_2.
$$

取 $B_1=B_2=o$，两个外积 $o\wedge B_j$ 均为零， 交叉项却为二。 先将每一路变为模方再相加，已经另外引入非相干求和规则。

量子情形同样有

$$
|\langle o|\psi_1+\psi_2\rangle|^2 =
 |\langle o|\psi_1\rangle|^2+
 |\langle o|\psi_2\rangle|^2+
 2\operatorname{Re}\!\left(
 \langle o|\psi_1\rangle
 \overline{\langle o|\psi_2\rangle}\right).
$$

是否保留交叉项取决于相干准备和记录处理。 若两条路径有归一化标记 $m_1,m_2$，令 $a_j=\langle o|\psi_j\rangle$，忽略标记后交叉项为 $2\operatorname{Re}(a_1\overline{a_2}\langle m_2|m_1\rangle)$。 标记正交是该项对所有振幅普遍消失的充分条件； 某一读数也可因特定相位偶然为零。 这取决于准备和记录，不能归因于“输出只有一条线”。

#### 反例 5.6：Bloch 方向不能直接按振幅相加

$|0\rangle$ 与 $e^{\mathrm i\phi}|1\rangle$ 的 Bloch 方向始终是 $e_3,-e_3$， 两方向之和恒为零。 但

$$
\frac{|0\rangle+e^{\mathrm i\phi}|1\rangle}{\sqrt2}
$$

的 Bloch 方向为 $(\cos\phi,\sin\phi,0)$， 随相对相位遍历整个赤道。 因此两条输入射线的端点不包含相干叠加所需的全部相位信息。

#### 命题 5.7：幂等性不强迫一维存在

投影可以具有任意允许的秩。 对密度态 $\rho$ 与正交投影 $P=P^\dagger=P^2$，

$$
\operatorname{tr}(\rho P)=1
 \iff \operatorname{supp}\rho\subseteq\operatorname{ran}P.
$$

当 $\operatorname{rank}P>1$ 时，判断保持确定并不排除其内部相位及动力学。

**证明。**

$\operatorname{diag}(1,1,0)$ 已是秩二幂等反例。 一般地，令 $Q=1-P$， $\operatorname{tr}(\rho Q)=\left\|Q\rho^{1/2}\right\|_{\rm HS}^2$， 所以概率一恰对应支撑包含。

$\square$

因此可以把“概念粒子性”约定为稳定可重复的标签， 但不能从 $P^2=P$ 推出所有概念或所有存在必为秩一物理粒子。 一个明确的逻辑语义还需要说明判断对象、允许效果及更新规则； 不同非对易投影也不自动组成同一 Boolean 代数。

<a id="section-6"></a>

## 6　单态面与转向面的统一：垂直、水平与钟

#### 定义 6.1：方向作用与两个面积分量

对 $n\in S^2$，定义

$$
\pi_n:\Lambda^2V\longrightarrow T_nS^2,
 \qquad \pi_n(B)=-\frac12[B,n],
$$

其中 $[B,n]=Bn-nB$。 固定该方向的生成元称垂直分量；改变方向的分量称水平分量。 这两个术语指作用的核与补空间，不是另加的空间上下方向。

#### 定理 6.2：轴面生成元的正交分解

每个 $B\in\Lambda^2V$ 唯一分解为

$$
\boxed{\quad B=\lambda\,\star n+n\wedge u,\qquad
 u\perp n,\quad \lambda\in\mathbb R.\quad}
$$

而且

$$
\pi_n(B)=u,\qquad
 \ker\pi_n=\mathbb R(\star n),\qquad
 \left\|B\right\|^2=\lambda^2+\left\|u\right\|^2.
$$

因此

$$
0\longrightarrow\mathbb R(\star n)\longrightarrow\Lambda^2V
 \xrightarrow{\ \pi_n\ }T_nS^2\longrightarrow0
$$

是一个正合序列。

**证明。**

在定向正交架 $(n,u_1,u_2)$ 中， $\Lambda^2V$ 的正交基为 $u_1\wedge u_2,n\wedge u_1,n\wedge u_2$。 第一项即 $\star n$，它与 $n$ 对易。 对 $u\perp n$， $(nu)n=-u$、$n(nu)=u$，故 $-\tfrac12[nu,n]=u$。 分解、核、满射性及范数等式随即成立。

$\square$

#### 定理 6.3：同一方向路径的全部面积生成元

给定 $C^1$ 路径 $n(t)\in S^2$，其全部二向量生成元为

$$
B(t)=n(t)\wedge\dot n(t)+\lambda(t)\star n(t).
$$

若

$$
\dot R=-\frac12BR,\qquad R(0)\in\operatorname{Spin}(3),
$$

且初始方向相符，则 $n(t)=R(t)n(0)\widetilde{R(t)}$。 其中 $\lambda(t)$ 可任取连续实函数；取 $\lambda=0$ 定义水平提升。

**证明。**

旋量微分给出 $\frac{d}{dt}(Rn_0\widetilde{R})=-[B,n]/2$。 定理 6.2 把此方程化为 $u=\dot n$，并保留核方向 $\lambda\star n$。 反过来，构造的路径满足同一线性方向演化及相同初值， 由常微分方程唯一性得到结论。

$\square$

写 $B=I\omega$，则

$$
\omega=n\times\dot n+\lambda n,\qquad
 \dot n=\omega\times n.
$$

这使“单态必伴一个面”获得准确的动力学意义： $\star n$ 是绕该态方向的稳定子生成元； $n\wedge\dot n$ 才生成它离开当前位置的变化。 二者属于同一个面积空间，但不是同一个作用。

#### 推论 6.4：兼容一个纯态路径的全部 Hamiltonian

采用 Pauli 表示后，给定 Bloch 路径 $n(t)$ 的全部自伴生成元为

$$
H(t)=\frac{\hbar}{2}
 \bigl(n\times\dot n+\lambda n\bigr)\cdot\boldsymbol{\sigma}+h_0(t)1_2,
$$

其中 $\lambda,h_0$ 为任意连续实函数。 方向路径不能唯一指定这两个相位相关自由度。

**证明。**

任意二阶 Hermitian 矩阵可写为 $h_01_2+\hbar\omega\cdot\boldsymbol{\sigma}/2$。 Pauli 对易关系将 $\dot\rho=-\mathrm i[H,\rho]/\hbar$ 化为 $\dot n=\omega\times n$，再用上式求解。

$\square$

给定路径的生成元不唯一及内部参考的移动项， 在项目 V74 中已有一般投影版本 [\[8\]](#ref-repo_v74)。 本节把它与用户的单态 Hodge 面明确接起来。

#### 定义 6.5：变化的面积表示与射影长度

定义二向量值一形式

$$
\beta_n(v)=n\wedge v,\qquad v\in T_nS^2.
$$

本文的 Fubini–Study 规范为

$$
d_{\rm FS}([\psi],[\phi])=\arccos|\langle\psi|\phi\rangle|.
$$

因此 qubit 的 Bloch 球距离 $\theta$ 对应射影距离 $\theta/2$。 $\beta$ 是对切向量取值的一形式，不是球面上的标量面积二形式。

#### 定理 6.6：面积表示给出长度，钟速率仍须动力学

对球面切向量 $v$ 有 $\left\|\beta_n(v)\right\|=\left\|v\right\|$。 若 $n(t)$ 为 $C^2$，则

$$
\begin{split}
 n(t)\cdot n(t+\delta)&=
 1-\frac12\left\|\dot n(t)\right\|^2\delta^2+o(\delta^2),\\
 n(t)\wedge n(t+\delta)&=
 \delta\,n(t)\wedge\dot n(t)+O(\delta^2).
 \end{split}
$$

沿纯态 Schrödinger 历史，

$$
\frac{ds_{\rm FS}}{dt}
 =\frac12\left\|\dot n\right\|
 =\frac{\Delta H}{\hbar}.
$$

**证明。**

外积范数公式给 $\left\|n\wedge v\right\|^2=\left\|n\right\|^2\left\|v\right\|^2-(n\cdot v)^2=\left\|v\right\|^2$。 对 $\left\|n\right\|^2=1$ 微分两次得 $n\cdot\dot n=0$、$n\cdot\ddot n=-\left\|\dot n\right\|^2$； Taylor 展开即给前两式。 再由 $H=h_01_2+\hbar\omega\cdot\boldsymbol{\sigma}/2$，

$$
(\Delta H)^2=\frac{\hbar^2}{4}
 \bigl(\left\|\omega\right\|^2-(\omega\cdot n)^2\bigr)
 =\frac{\hbar^2}{4}\left\|\dot n\right\|^2.
$$

结合 $ds_{\rm FS}=\left\|\mathrm dn\right\|/2$ 完成证明。

$\square$

此速度关系与 Anandan–Aharonov 原文一致； 其射影直线采用单位球半径规范，长度为本文的两倍 [\[3\]](#ref-anandan)。明确规范才能避免把因子二当成物理差异。

#### 命题 6.7：几何形状不选定秒，也不给全局单调钟

同一非恒定几何路径可由任意正的光滑速度重参数化。 不存在一个实函数 $T:S^2\to\mathbb R$， 能对所有允许的可逆非平凡路径始终严格增加。

**证明。**

把 $n(t)$ 改为 $n(f(s))$，其中 $f$ 严格递增， 其像及几何长度不变，经过的参数时长却可任意缩放。 对第二项，取允许闭路，从同一态出发并返回； 严格增加将推出 $T(n_0)<T(n_0)$，矛盾。

$\square$

#### 反例 6.8：细分后的余弦乘积不是经过时间

把总转角为 $\Theta$ 的最短大圆弧等分为 $N$ 段。 线投影乘积为

$$
\tau_N=\cos^N(\Theta/N)\longrightarrow1,
$$

而总球面长度恒为 $\Theta$。 因为 $N\log\cos(\Theta/N)=-\Theta^2/(2N)+O(N^{-3})$。 量子连续成功概率则使用 $\cos^{2N}(\Theta/(2N))$，也趋于一。 两种极限都不表示这段变化没有发生。

故可以把 $\int\left\|\beta_n(\dot n)\right\|\,dt$ 定义为一种内禀变化量， 再用已声明的钟进行标定；不能仅改名就证明“面积等于物理时间”。 对有符号投影连乘，还不能在任意夹角下声称其数值单调： 乘上负的余弦会改变符号。其绝对值虽不增，仍不是可加的通用钟。

<a id="section-7"></a>

## 7　量子几何张量：同一结构中的长度、面积与相位

#### 定义 7.1：方向的量子几何张量

对 $P_n=(1_2+n\cdot\boldsymbol{\sigma})/2$ 及 $u,v\in T_nS^2$，令

$$
\mathcal Q_n(u,v)=
 \operatorname{tr}\!\bigl(P_n\,\mathrm dP_n(u)\,\mathrm dP_n(v)\bigr).
$$

#### 定理 7.2：度量与有向面积统一于同一张量

$$
\boxed{\quad
 \mathcal Q_n(u,v)=\frac14
 \bigl[u\cdot v+\mathrm in\cdot(u\times v)\bigr].\quad}
$$

其对称实部是本文的 Fubini–Study 度量； 两倍反对称虚部为

$$
F_n(u,v)=\frac12n\cdot(u\times v).
$$

**证明。**

$\mathrm dP_n(u)=u\cdot\boldsymbol{\sigma}/2$，且 $(u\cdot\boldsymbol{\sigma})(v\cdot\boldsymbol{\sigma}) =(u\cdot v)1_2+\mathrm i(u\times v)\cdot\boldsymbol{\sigma}$。 再用 $\operatorname{tr}P_n=1$、$\operatorname{tr}(P_n w\cdot\boldsymbol{\sigma})=n\cdot w$ 即得公式。取 $u=v$ 得长度平方 $\left\|u\right\|^2/4$。

$\square$

这一统一比“波必等于任意面积”更具体： 同一张量的实部控制邻近可区分性，虚部控制有向相位运输。 由单态得到的切平面复结构 $J_nu=n\times u$，满足 $F_n(u,v)=2g_{\rm FS}(J_nu,v)$。

#### 定义 7.3：旋量提升与相位纤维

归一化旋量构成 $S^3\subset\mathbb C^2$， 映射

$$
\psi\longmapsto n,\qquad n_j=\psi^\dagger\sigma_j\psi
$$

把相差共同相位的旋量送到同一方向。 其纤维为 $\{e^{\mathrm i\chi}\psi:\chi\in\mathbb R/(2\pi\mathbb Z)\}$， 故 $S^3/U(1)\simeq\mathbb{CP}^1\simeq S^2$。 这是一套状态表示；是否可读相位差取决于内部参考与允许的操作。

#### 定理 7.4：相位曲率及闭路半立体角

取局部代表

$$
\psi_N(\theta,\varphi)=
 \begin{pmatrix}
 \cos(\theta/2)\\ e^{\mathrm i\varphi}\sin(\theta/2)
 \end{pmatrix},
 \qquad
 a=-\mathrm i\psi_N^\dagger\mathrm d\psi_N
 =\frac{1-\cos\theta}{2}\,\mathrm d\varphi.
$$

则

$$
F=\mathrm da=\frac12\sin\theta\,\mathrm d\theta\wedge\mathrm d\varphi.
$$

规范变换 $\psi_N\mapsto e^{\mathrm i\chi}\psi_N$ 使 $a\mapsto a+\mathrm d\chi$。 对定向闭路的水平提升，回返相位为

$$
\gamma=-\oint a=-\frac{\Omega}{2}\pmod{2\pi},
$$

其中 $\Omega$ 是所围有向球面积，按 $4\pi$ 取模。

**证明。**

直接微分归一化旋量得到 $a,F$ 与规范公式。 写水平旋量 $\psi_h=e^{\mathrm i\chi}\psi_N$， 条件 $\psi_h^\dagger\mathrm d\psi_h=0$ 给 $\mathrm d\chi=-a$。 沿闭路积分并使用 Stokes 定理得到相位。 若路径跨越坐标片，加入重叠处的规范变换； 换用球面另一补片改变 $\Omega$ 一个 $4\pi$ 整数倍， 因此不改变 $e^{\mathrm i\gamma}$。

$\square$

Berry 原文以绝热量子历史导出几何相位，并给出自旋情形的立体角公式 [\[2\]](#ref-berry)。上面证明的是所声明连接的水平运输； 它本身不把任意实际驱动自动认定为绝热驱动。

#### 命题 7.5：不能从每个方向全局选出光滑归一化相位代表

不存在光滑截面 $S^2\to S^3$，使每个 $n$ 都得到一个唯一归一化旋量。

**证明。**

若有全局代表，$a=-\mathrm i\psi^\dagger\mathrm d\psi$ 将为全局一形式， 其曲率仍为上式。闭球面上 Stokes 定理给 $\int_{S^2}\mathrm da=0$，但实际 $\int_{S^2}F=2\pi$，矛盾。

$\square$

这不是要求放进一个外部观察者。 它要求内部参考使用局部约定，并保留不同约定之间的相位关系； 单个方向不能承担全部相位历史。 单态的对偶平面存在，不等于该平面已带有一个特定相位指针或转速。

#### 注 7.6：若把接口扩展为一个场

对一个已声明的参数流形 $M$ 及映射 $n:M\to S^2$， 可拉回上述度量与曲率：

$$
g_{\mu\nu}=\frac14\,\partial_\mu n\cdot\partial_\nu n,\qquad
 F_{\mu\nu}=\frac12\,n\cdot
 (\partial_\mu n\times\partial_\nu n).
$$

这确实定义了方向场的几何结构。 但 $M$ 的物理含义、作用量、传播方程、局域性与钟还需另外指定。 这些公式不直接推出电磁场、真空能或基本粒子的质量与自旋谱。

<a id="section-8"></a>

## 8　端点相同而历史不同：内部闭路与连续投影

#### 定理 8.1：三次最短转向留下可比较的相位

沿内部方向历史

$$
e_3\longrightarrow e_1\longrightarrow e_2\longrightarrow e_3
$$

使用最短水平门

$$
U_1=\frac{1_2-\mathrm i\sigma_y}{\sqrt2},\quad
 U_2=\frac{1_2-\mathrm i\sigma_z}{\sqrt2},\quad
 U_3=\frac{1_2-\mathrm i\sigma_x}{\sqrt2},
$$

则

$$
U_3U_2U_1
 =\frac{1_2-\mathrm i\sigma_z}{\sqrt2}
 =e^{-\mathrm i\pi\sigma_z/4}.
$$

初态 $|0\rangle$ 的 Bloch 方向返回原处，旋量积累相位 $-\pi/4$。

**证明。**

由 $\sigma_i\sigma_j=\delta_{ij}1_2+\mathrm i\epsilon_{ijk}\sigma_k$，

$$
(1_2-\mathrm i\sigma_z)(1_2-\mathrm i\sigma_y)
 =1_2+\mathrm i\sigma_x-\mathrm i\sigma_y-\mathrm i\sigma_z.
$$

再左乘 $1_2-\mathrm i\sigma_x$ 得 $2(1_2-\mathrm i\sigma_z)$， 除以 $(\sqrt2)^3$ 即得结论。 $\sigma_z|0\rangle=|0\rangle$ 给出该相位。 三个大圆短弧围成正八分球，$\Omega=\pi/2$， 与定理 7.4 一致。

$\square$

#### 命题 8.2：一般三角闭路的无坐标相位

若 $a,b,c$ 两两非反向，令

$$
S=1+a\cdot b+b\cdot c+c\cdot a,\qquad
 D=a\cdot(b\times c).
$$

沿 $a\to b\to c\to a$ 的最短水平门回返相位因子为

$$
h(a,b,c)=\frac{S-\mathrm iD}{\sqrt{S^2+D^2}}.
$$

**证明。**

直接展开 Pauli 乘积得

$$
\operatorname{tr}(P_aP_cP_b)=\frac{S-\mathrm iD}{4}.
$$

最短门在每一步的当前输入上满足

$$
U(b\leftarrow a)\psi_a
 =\frac{P_b\psi_a}{\sqrt{\langle\psi_a|P_b|\psi_a\rangle}}.
$$

这是逐步选择正实相邻重叠，不是让闭路全部预选代表同时具有正实重叠； 逐段复合故给出上式复数的单位相位。 Gram 行列式恒等式 $D^2=1+2(a\cdot b)(b\cdot c)(c\cdot a) -(a\cdot b)^2-(b\cdot c)^2-(c\cdot a)^2$ 进一步给

$$
S^2+D^2=2(1+a\cdot b)(1+b\cdot c)(1+c\cdot a)>0.
$$

因此分母非零，公式处处有定义。

$\square$

这里第三个方向若是 *实际经历的内部控制步骤* ，就是真实历史信息。 它与 §3 的派生点 $C=(a\cdot b)a$ 不同。 消去一个不独立的投影变量，并不允许消去一个已经发生的门。 端点关系积沿闭路会望远镜消去：

$$
(e_3e_1)(e_1e_2)(e_2e_3)=1.
$$

而半角旋量门的复合仍有上述余相位。 这说明端点代数摘要与完整运输不是同一对象。

#### 定理 8.3：密集正投影可保留有限几何相位

设 $\psi(t)$ 为 $C^2$ 归一化闭合代表，$\psi(T)=\psi(0)$， $P(t)=\psi(t)\psi(t)^\dagger$。 令 $t_k=kT/N$，并选定各步成功分支的 Kraus 算子恰为 $P(t_k)$。 则

$$
P(t_N)\cdots P(t_0)\psi(0) =
 \psi(0)\prod_{k=0}^{N-1}
 \langle\psi(t_{k+1})|\psi(t_k)\rangle
 \ \longrightarrow\
 e^{-\int_0^T\langle\psi|\dot\psi\rangle\,dt}\psi(0).
$$

成功概率趋于一；相位可为 $e^{-\mathrm i\Omega/2}\ne1$。

**证明。**

秩一乘积逐项收缩得到乘积式。 令 $\delta=T/N$，每项展开为

$$
\langle\psi(t+\delta)|\psi(t)\rangle
 =1-\delta\langle\psi(t)|\dot\psi(t)\rangle+O(\delta^2).
$$

取连续对数，求和余项为 $O(N\delta^2)=O(1/N)$； Riemann 和给指数极限。 归一化使 $\langle\psi|\dot\psi\rangle$ 纯虚， 而每项模方为 $1-O(\delta^2)$，故总成功概率趋一。 再由连接定义得到闭路相位。

$\square$

该命题涉及已指定的成功分支实现及其相干运输。 若仅保存归一化分支密度矩阵，共同相位不可见； 要比较这条相位，须保持内部相干参考。 任意实现同一密度矩阵通道的装置也不自动给出相同的受控相位。 所以“密集测量”既可抑制离开某固定子空间， 也可在移动的子空间中运输状态，不能一概解释为抽走全部时间。

<a id="section-9"></a>

## 9　观察者内生：注意力、仪器与可读关系

#### 定义 9.1：内部观察者模型

声明一个有限协议整体

$$
\mathcal H_{\rm all}=
 \mathcal H_S\otimes\mathcal H_C\otimes\mathcal H_R\otimes\mathcal H_M\otimes\mathcal H_E.
$$

其中 $S$ 是当前目标，$C$ 是控制程序， $R$ 是方向与相位参考，$M$ 是记录，$E$ 是未访问自由度。 这些名称是功能划分；整体态记为 $\varrho$。 注意力设置 $a$ 是 $C,R,M$ 中的物理编码，选择一个仪器 $\{\mathcal I_{y|a}\}_y$、访问菜单及后续更新。 它不能仅由目标的一条方向替代。

#### 定理 9.2：有限仪器可以放入整体内部

设 $\mathcal H_S$ 有限维，一个有限仪器具有有限组 Kraus 算子 $K_{y\mu}$， $\sum_{y,\mu}K_{y\mu}^\dagger K_{y\mu}=1$，则

$$
V\psi=\sum_{y,\mu}K_{y\mu}\psi\otimes|y,\mu\rangle
$$

是等距映射。选辅助准备态 $|0\rangle_A$ 后，存在酉作用使 $U(\psi\otimes|0\rangle_A)=V\psi$。 从内部记录读出 $y$ 并忽略 $\mu$， 得到 $\mathcal I_y(\rho)=\sum_\mu K_{y\mu}\rho K_{y\mu}^\dagger$。

**证明。**

$V^\dagger V=\sum K_{y\mu}^\dagger K_{y\mu}=1$。 取输入子空间的正交基，把其像补成整体正交基， 便得到一个酉延拓。 记录投影与偏迹直接给分支公式。

$\square$

因此有限次自适应观察可使用历史 $h_k=(y_1,\ldots,y_k)$ 及内部政策 $a_{k+1}=\pi(h_k,C,R)$。 非归一分支态满足

$$
\widetilde\rho_{h_k}
 =\mathcal I_{y_k|a_k}\cdots
  \mathcal I_{y_1|a_1}(\rho_0),\qquad
 p(h_k)=\operatorname{tr}\widetilde\rho_{h_k}.
$$

这使状态、设置与记录在同一模型中传播。 酉扩张给出操作自洽性，不额外解决某一种本体解释中的唯一结果问题。

#### 定理 9.3：有限历史中的内部钟构造

设完整数据寄存器的有限历史由酉门 $U_1,\ldots,U_N$ 给出，令 $|\Phi_k\rangle=U_k\cdots U_1|\Phi_0\rangle$。 引入正交钟态 $|0\rangle_T,\ldots,|N\rangle_T$，构造

$$
|\Omega_N\rangle
 =\frac1{\sqrt{N+1}}\sum_{k=0}^N
 |k\rangle_T\otimes|\Phi_k\rangle.
$$

定义

$$
L_k=\frac1{\sqrt2}
 \bigl(\langle k|_T\otimes1-\langle k-1|_T\otimes U_k\bigr),
 \qquad
 G_{\rm hist}=\sum_{k=1}^N L_k^\dagger L_k.
$$

则 $G_{\rm hist}\ge0$，$G_{\rm hist}|\Omega_N\rangle=0$； 条件于内部钟读数 $k$，数据态为 $|\Phi_k\rangle$。

**证明。**

正性由平方和给出。 每项 $L_k$ 对历史态的作用正比于 $\Phi_k-U_k\Phi_{k-1}=0$，故满足传播约束。 钟读数概率为 $1/(N+1)$， 对 $\langle k|_T$ 收缩并归一即得到 $\Phi_k$。

$\square$

这个构造把有序演化编码为一个整体中的相关关系， 是“时间也在整体内部”的一个可审查模型 [\[7\]](#ref-repo_otf1), [\[12\]](#ref-repo_v21)。 $G_{\rm hist}$ 是传播约束，不自动是实际推动钟运行的 Hamiltonian。 钟标签的顺序、允许门及初始条件仍为明示结构； 有限时刻标签也不自行给出秒、连续时间或唯一的宇宙状态。

#### 命题 9.4：共同参考变换与主动操作不同

若所有态、效果、门共同作酉坐标变换，全部概率不变。 若内部移动参考为 $W(t)$，则

$$
\psi_{\rm rel}=W^\dagger\psi,\qquad
 H_{\rm rel}=W^\dagger HW-\mathrm i\hbar W^\dagger\dot W.
$$

**证明。**

概率由迹的循环性保持。 微分 $W^\dagger\psi$ 并用 $\dot W^\dagger W=-W^\dagger\dot W$ 即得生成元式。

$\square$

该项是相对运动的必要部分，不需要场外参考 [\[8\]](#ref-repo_v74), [\[12\]](#ref-repo_v21)。 同时改变坐标描述，并不等于实际改变目标与装置的相对耦合。

#### 定理 9.5：未耦合的注意力改动不改变目标边缘态

对任意联合态 $\varrho_{SR}$ 和 $R$ 上保迹完全正映射 $\Phi_R$，

$$
\operatorname{tr}_R[(\operatorname{id}_S\otimes\Phi_R)(\varrho_{SR})]=\operatorname{tr}_R\varrho_{SR}.
$$

**证明。**

对 $S$ 上任意效果 $E$，

$$
\operatorname{tr}[(E\otimes1)(\operatorname{id}\otimes\Phi_R)(\varrho)]
 =\operatorname{tr}[(E\otimes\Phi_R^*(1))\varrho]
 =\operatorname{tr}[(E\otimes1)\varrho].
$$

效果区分有限维态，故两个边缘态相同。

$\square$

因此把“注意力”作为理论变量，需要明确它改变的是 物理测量设置、耦合、可访问的参考或条件化记录。 仅改变一个未与目标耦合的内部标签，不会使目标无条件地坍缩。 选择性记录可以改变条件态，但不能与上述无条件边缘态混同。

#### 定理 9.6：两路径中的可读区分度与条纹可见度

设

$$
|\Psi\rangle=\sqrt p\,|0\rangle|m_0\rangle
 +e^{\mathrm i\phi}\sqrt{1-p}\,|1\rangle|m_1\rangle,
 \qquad 0\le p\le1,
$$

标记态归一，$\gamma=\langle m_1|m_0\rangle$。 对相位扫描后的平衡合束读出，条纹可见度为

$$
\mathcal V=2\sqrt{p(1-p)}\,|\gamma|.
$$

允许对标记作最优二元判别时，令

$$
\mathcal D=\left\|
 p|m_0\rangle\langle m_0|-(1-p)|m_1\rangle\langle m_1|
 \right\|_1,
$$

则最优正确率为 $(1+\mathcal D)/2$，并且

$$
\mathcal D^2+\mathcal V^2=1.
$$

**证明。**

目标约化态的非对角元模为 $\sqrt{p(1-p)}|\gamma|$。 平衡合束输出随扫描相位 $\delta$ 为 $\frac12[1+2\sqrt{p(1-p)}|\gamma|\cos(\delta+\delta_0)]$， 故得到可见度。 令 $\Delta=p|m_0\rangle\langle m_0|-(1-p)|m_1\rangle\langle m_1|$。 任意二元效果 $0\le E\le1$ 的正确率为 $(1-p)+\operatorname{tr}(E\Delta)$；选择 $\Delta$ 的正谱投影达到最大值， 即 $(1+\left\|\Delta\right\|_1)/2$。 在两标记张成的空间， $\operatorname{tr}\Delta=2p-1$、$\det\Delta=-p(1-p)(1-|\gamma|^2)$。 其迹范数为 $\sqrt{1-4p(1-p)|\gamma|^2}$。 退化情形由连续性成立，代入完成证明。

$\square$

路径区分度与可见度的量化关系属于既有波粒互补性研究[\[1\]](#ref-englert)； 上面针对所声明的纯标记模型给出直接证明。 这条等式仅针对上述纯联合态和完整标记判别菜单。 若菜单受限，实际可得区分度可降低；混合与噪声也可降低可见度。 它把“何时粒子、何时波”落实为路径信息与干涉统计的实验关系， 不把粒子点击和波状分布当作互相排斥的两种实体。

#### 例 9.7：每轮端点方向相同而内部参考变化

取内部参考位 $R$ 与目标 $|0\rangle_S$， 初态为

$$
|\Xi_\phi\rangle
 =\frac{|0\rangle_R+e^{\mathrm i\phi}|1\rangle_R}{\sqrt2}
   \otimes|0\rangle_S.
$$

只在参考支路 $|1\rangle_R$ 控制执行定理 8.1 的闭路， 则 $\phi\mapsto\phi-\pi/4$， 目标在每轮闭路结束时返回 $e_3$。 回路中目标可改变并与参考纠缠，逐轮端点相同不表示全过程恒定。 参考上的 $\sigma_x$ 正结果概率为 $(1+\cos\phi)/2$， $\sigma_y$ 读出再分辨正弦分量。 相位差与其读出全部在整体内部。

这也说明单态的 $\star n$ 可以成为相对相位变化的生成元， 而无须把一个不可读的孤立共同相位误称为可观测波。

<a id="section-10"></a>

## 10　余弦自指的完整提升：压缩基底与转动纤维

#### 定义 10.1：带相位的内部反馈合同

令 $J=[-1,1]$、$s\in\{+1,-1\}$， 指定反馈政策

$$
F_s(x)=s\cos x.
$$

$x$ 是以弧度编码的有符号设置；负号选择的是反馈政策。 在包含一个可访问内部相对相位的模型 $X=J\times U(1)$ 上，进一步指定

$$
T_s(x,z)=\bigl(F_s(x),e^{\mathrm i\omega(x)}z\bigr),
$$

其中 $\omega:J\to\mathbb R$ 为 Lipschitz 函数，常数记为 $K$。 这里只把 $X$ 称为已声明的提升状态空间， 不把它等同于包含所有钟与记忆的宇宙全态。

#### 定理 10.2：正负余弦政策各有唯一吸引实不动点

存在唯一 $\alpha\in(0,1)$ 满足 $\cos\alpha=\alpha$， 其近似值为 $0.7390851332$。 $F_s$ 的唯一实不动点为 $`x_*=s\alpha`$。 对 $x_0\in J$，

$$
|F_s^n(x_0)-x_*|\le L^n|x_0-x_*|,
 \qquad L=\sin1<1.
$$

任意实初值经一步即进入 $J$，故实迭代也收敛。

**证明。**

$F_s(J)\subseteq J$，且 $|F_s'(x)|=|\sin x|\le\sin1<1$。 压缩映射定理给唯一不动点与估计。 任意实不动点必须满足 $|x|\le1$； $\cos x$ 的偶性给正负两政策的不动点互为相反数。 对 $s=+1$，不动点显然在 $(0,1)$。

$\square$

这个数由所选函数与单位增益决定。 例如反馈 $x_{n+1}=g\cos x_n$，$0<g<1$， 同样是压缩，但其正不动点随 $g$ 改变。 对方程 $x_g=g\cos x_g$ 微分得

$$
\frac{\mathrm dx_g}{\mathrm dg}
 =\frac{\cos x_g}{1+g\sin x_g}>0.
$$

所以没有经过独立物理选律，$\alpha$ 不是由各向同性强制给出的自然常数。 两个政策满足 $F_-(-x)=-F_+(x)$， 但这不定义电荷共轭、反粒子或热力学时间箭头。

若 $|x|$ 被实际编码为 Bloch 夹角，正结果概率是 $p_+=(1+\cos x)/2$，在不动点处为 $(1+\alpha)/2\approx0.86954$。 $\alpha^2$ 与 $1-\alpha^2$ 可分别是纯态的概率偏置平方与 归一相干模平方；它们不是系统以某概率变成粒子、以另一概率变成波。 同样，复方程 $\cos z=\pm z$ 的根若没有指定谱问题，不能直接称为能级。 自伴能量算子的本征值为实数，因为 $H\psi=E\psi$ 蕴涵 $E=\langle\psi|H|\psi\rangle/\left\|\psi\right\|^2\in\mathbb R$。

#### 定理 10.3：余弦–相位反馈的精确共轭

令 $`\omega_*=\omega(x_*)`$，定义

$$
A(x)=\sum_{j=0}^{\infty}
 \bigl[\omega(F_s^j x)-\omega_*\bigr].
$$

则该级数在 $J$ 上一致绝对收敛，且

$$
|A(x)|\le\frac{K}{1-L}|x-x_*|,
 \qquad \operatorname{Lip}(A)\le\frac{K}{1-L}.
$$

映射

$$
\mathcal H(x,z)=\bigl(x,e^{\mathrm iA(x)}z\bigr)
$$

是 $X$ 上的同胚，并满足

$$
\boxed{\quad
 \mathcal H\circ T_s
 =(F_s\times R_{\omega_*})\circ\mathcal H,\qquad
 R_{\omega_*}(z)=e^{\mathrm i\omega_*}z.\quad}
$$

**证明。**

每项满足

$$
|\omega(F_s^j x)-\omega_*|
 \le K L^j|x-x_*|\le2KL^j,
$$

故几何级数控制给出一致收敛及第一项界。 对 $x,y\in J$，

$$
|A(x)-A(y)|
 \le\sum_{j\ge0}K|F_s^j x-F_s^j y|
 \le\frac{K}{1-L}|x-y|.
$$

去掉首项得到余边界方程

$$
A(x)-A(F_sx)=\omega(x)-\omega_*.
$$

$\mathcal H^{-1}(x,z)=(x,e^{-\mathrm iA(x)}z)$ 连续， 故为同胚。最后

$$
\begin{split}
 \mathcal H(T_s(x,z))
 &=\bigl(F_sx,e^{\mathrm i[\omega(x)+A(F_sx)]}z\bigr)\\
 &=\bigl(F_sx,e^{\mathrm i[\omega_*+A(x)]}z\bigr),
 \end{split}
$$

即为所求共轭关系。

$\square$

这把模型精确分解成角度压缩与恒定相位旋转。 相位的 $x$ 依赖部分是可求和的瞬态，其累计相位有限； 固定基底处仍留下不能由这个瞬态抹去的转角。

#### 推论 10.4：相位补偿后的指数收敛

选实数提升 $\phi_{n+1}=\phi_n+\omega(x_n)$， $x_{n+1}=F_s(x_n)$。令 $\Phi_\infty=\phi_0+A(x_0)$，则

$$
\phi_n=\phi_0+n\omega_*+A(x_0)-A(x_n),
$$

从而

$$
|\phi_n-n\omega_*-\Phi_\infty|
 \le\frac{K}{1-L}L^n|x_0-x_*|.
$$

**证明。**

逐次求和余边界方程使 $A$ 项望远镜消去， 再用定理 10.3 的估计。

$\square$

#### 定理 10.5：提升模型的闭合分类

圆 $`\mathcal C=\{x_*\}\times U(1)`$ 不变且横向吸引。 在 $X$ 中：

- \(i\) 存在不动点，当且仅当 $`\omega_*\in2\pi\mathbb Z`$。 此时整条 $\mathcal C$ 都是不动点，仍无唯一相位选择。

- \(ii\) 若 $`\omega_*/(2\pi)=p/q`$ 为非整数既约有理数，$q\ge2$， 则 $\mathcal C$ 上最小周期为 $q$， 每条轨道指数逼近一条 $q$ 周期轨道。

- \(iii\) 若 $`\omega_*/(2\pi)`$ 为无理数， 则没有周期点，每条轨道的极限点集合为整个 $\mathcal C$。

**证明。**

若 $F_s^q(x)=x$，压缩估计给 $`|x-x_*|\le L^q|x-x_*|`$，故 $`x=x_*`$。 在该圆上只剩固定角的圆周旋转，给出不动点及有理周期条件。 一般轨道与 $`(x_*,e^{\mathrm i(\Phi_\infty+n\omega_*)})`$ 的距离指数趋零，故保留其极限点集合。 无理旋转生成无限圆周子群；其闭包含任意小的非零角， 这些角的整数倍逼近任意圆周角，故闭包为全圆。 同样的论证适用于任意尾轨道，因此每点都是极限点。

$\square$

#### 命题 10.6：剩余相位不能被单值基底规范消去

若改变相位坐标为 $z'=e^{\mathrm iB(x)}z$， 其中 $B$ 为连续实函数，则新增量为

$$
\omega_B(x)=\omega(x)+B(F_sx)-B(x)\pmod{2\pi}.
$$

在 $`x_*`$ 处必有 $`\omega_B(x_*)=\omega_*\pmod{2\pi}`$。

**证明。**

代入坐标变换；不动点使两个 $B$ 项相消。

$\square$

若扩大规范允许显含轮数的共同旋转参考， 可把恒定转角写入参考本身； 但完整参考关系并未因此停止变化。 这不能被用来证明整个内部观察者已固定。

#### 反例 10.7：余弦已固定，内部相位仍为八周期

取 $\omega(x)\equiv-\pi/4$。 由 §9 的内部受控三角回路可实现这项相对相位更新。 若 $`x_0=x_*`$，则

$$
T_s^n(x_*,z_0)
 =\bigl(x_*,e^{-\mathrm in\pi/4}z_0\bigr).
$$

角度从始至终固定，但联合状态最小周期为八， 且内部 $\sigma_x,\sigma_y$ 参考读出可以分辨这些相位。

#### 命题 10.8：严格追加记忆阻止完整不动点

若完整反馈还含计数记录 $m\in\mathbb N$， 每轮更新 $m\mapsto m+1$， 则无论 $x$ 与相位是否固定，完整模型都没有不动点。

**证明。**

不动点将要求 $m=m+1$。 有限循环存储则改为周期条件，并非自动不动； 无限追加需要无限资源，不能冒充有限装置的永久协议。

$\square$

#### 定理 10.9：自主酉整体没有非平凡吸引收敛

设完整有限量子态按 $\varrho_n=U^n\varrho_0(U^\dagger)^n$ 演化。 若其在迹范数下收敛到 $`\varrho_*`$， 则 $`\varrho_0=\varrho_*`$，且该态原本就被 $U$ 固定。

**证明。**

连续性使 $`U\varrho_*U^\dagger=\varrho_*`$。 酉不变性给

$$
\left\|\varrho_n-\varrho_*\right\|_1
 =\left\|\varrho_0-\varrho_*\right\|_1
$$

对每个 $n$ 成立。左边趋零，故右边为零。

$\square$

因此 $F_s$ 的压缩可作为约化、估计或有记录反馈的有效律， 但不能直接代表有限封闭量子整体的非平凡吸引流。 若把所有资源加入，必须重新检查它们的演化； 所谓“内部动力学已经规定完整”，也不等于“每个变量最终静止”。

#### 注 10.10：从期望反馈到一次实验的额外步骤

在量子读出中，$\cos x$ 可以是某二值结果 $Y\in\{-1,1\}$ 的期望，但 $Y$ 本身一般不等于该期望。 如果政策使用 $x_{n+1}=sY_n$，状态下一步便落在 $\{\pm1\}$， 不会遵循确定性余弦迭代趋于 $\pm\alpha$。 要实现近似期望反馈，必须指定相同准备的重复采样、估计误差、 内部控制精度及记录资源。

<a id="section-11"></a>

## 11　理论所得、依赖关系与可区分的实验合同

### 11.1　一条可以审查的条件重建链

#### 定理 11.1：OTF-005 条件综合

在 C1–C7 的适用范围内，得到以下兼容结构：

$$
\begin{gathered}
 V\simeq\Lambda^2V,\ \dim V>0
 \ \Longrightarrow\ \dim V=3,\\
 \text{线性锐比较}
 \ \Longrightarrow\ \operatorname{Cl}_{3,0}\simeq M_2(\mathbb C),\\
 \text{归一正读出}
 \ \Longrightarrow\
 \rho_r=(1_2+r\cdot\boldsymbol{\sigma})/2,\quad
 p(+|r,n)=\tfrac12(1+r\cdot n),\\
 \text{指定路径与参考；闭路取水平提升}
 \ \Longrightarrow\
 B=n\wedge\dot n+\lambda\star n,\quad
 \gamma_{\rm horiz}=-\Omega/2,\\
 \text{指定余弦--相位政策及 Lipschitz 增量}
 \ \Longrightarrow\
 T_s\sim F_s\times R_{\omega_*}.
 \end{gathered}
$$

各箭头是有条件的数学推论；最后一项仅覆盖所声明的 $X$。 若纳入其他参考、记录和钟，仍须检验它们各自的更新。

**证明。**

依次应用 §2 的维数定理、§4 的代数及正锥重建、 定理 6.3、7.4 和 10.3。 每一步的输入均已在相应定义、约束或定理中列出。

$\square$

| 结果 | 足够输入 | 删除输入后的具体缺口 |
|:---|:---|:---|
| 三维方向–面积对偶 | 完整线性同构、正定度量、定向 | 仅各向同性允许不同维数；任意给定同构不必已是归一 Hodge 星 |
| 扇形生成最短门 | 非反向端点、最短平面选择、Spin 半角作用 | 反向端点不定平面；一般门还含稳定子及中心相位 |
| Born 读出 | 线性全方向锐比较、正性与归一化 | $f(n\cdot m)=(n\cdot m)^3$ 仍保留单纯旋转对称 |
| 时间速度 | 路径、Hamiltonian、内部钟与单位 | 重参数化保留路径却改变经过时长 |
| 注意力影响读出 | 设置编码、耦合、访问菜单及记录 | 未耦合参考上的保迹操作不改变目标边缘态 |
| 余弦整体固定 | 基底固定、$`\omega_*\equiv0`$ 及所有其余已声明变量固定 | 三角回路给八周期；追加记录使整体无不动点 |

C1 中若还要求所选同构 $T:V\to\Lambda^2V$ 旋转等变， 则它必为 $\lambda\star$： 固定 $n$ 的稳定子迫使 $\star^{-1}T(n)$ 平行 $n$； 旋转传递性及线性使比例处处相同。 再以等距和定向选取正号，才固定为本文 $\star$。 这明确了“存在某个同构”与“唯一自然对应”的区别。

### 11.2　对原始五组论断的逐项修订

1.  **单态、线与伴生面。** 有向单位状态确实唯一确定 $\star n$，但二者是同一几何数据。 该面给稳定子与切平面复结构；振幅、频率和相干准备并未由它额外生成。 无向直线还会把 $n,-n$ 混同，故“粒子线”必须注明取向或事件标签。

2.  **双态、转向与无须第三点。** 派生 $C=(a\cdot b)a$ 不增加自由度，正确。 最短平面扇形给 $R_{ab}=e^{-\Sigma_{ab}}$，正确且需要半角。 但实际中间门与球面闭路信息不能从最终两个端点恢复， 因此第三个真实历史点不能当作派生投影删除。

3.  **线性时间与面积时间。** 长度、扇形生成元和闭路曲率提供不同的变化度量。 它们能够参与关系时钟模型，但还需速率及单位。 正交一阶条件给切向变化，不要求每次演化进行一次或两次有限直角跳转。

4.  **粒子、波、概念与存在。** 在声明的操作语义中，稳定可重复事件可称“粒子式标签”， 参考相干与相位历史可称“波式关系”。 不过事件可为高秩、混态也可确定某个判断， 语言中的定义更不等同质量、自旋和局域场的物理粒子。 这是一种可用的结构类比，不能靠同名完成本体证明。

5.  **内生观察者与自指闭环。** 观察者包含参考、控制与记忆，而不只是一根可转向的轴。 $\cos x=\pm x$ 给指定标量政策的平衡； 完整提升还须检查相位、程序及记录。 闭合的演化规则、闭合的轨道、全态不动与唯一吸引态是四个不同命题。

### 11.3　哪些结果可以直接设计成判别协议

| 协议 | 明确可比较的读数 | 可以排除的过强解释 |
|:---|:---|:---|
| 保持目标终点，改变内部闭路 | 参考支路的相位条纹随 $\Omega$ 改变；水平相位 $-\Omega/2$ | 两个端点决定全部门历史 |
| 固定准备，改变路径标记重叠 | $\mathcal V=2\sqrt{p(1-p)}\vert \gamma\vert$ 及可读路径信息 | 只凭观察者主轴夹角就决定全部波粒现象 |
| 保持几何路径，改变驱动速率 | 路径长度相同，内部钟差不同 | 几何面积或长度本身就是秒 |
| 固定余弦政策，加入内部三角控制 | $x$ 已稳定而相位参考呈八周期 | 标量不动点自动是完整观察者不动点 |
| 加入记录计数再检查状态 | 目标、相位与记录分别比较 | 返回目标态便意味着历史已被删除 |

这些是把不同论断区分开的操作合同； 其中若干数值关系属于既有量子几何的重建， 不能据此宣称已经产生超出标准量子理论的新实验预言。 若要把“所有对象都是时间场”升级为独立物理理论， 仍须给出整体状态空间及相互作用、空间与局域性的恢复、 单位和常数的标定，以及至少一个能够区分竞争模型的结果。 本文已把这些任务的接口写清，没有以命名替代它们。

### 11.4　整体图景的直接表述

可以把每个基本接口想成一个方向，以及它能如何变化的完整规则。 这个方向天然带着一个正交面； 面内的相位指针若要变得可读，需要同一整体里的参考。 当状态开始转向，变化由另一组含该方向的平面生成。 转向串成路径，路径闭合后，方向可以回来而参考相位仍留下历史。

观察者就是这个整体中负责选择设置、保存结果、再据此行动的一部分。 在某一参考下，状态分成概率偏置与相干分量； 改变耦合或读取、丢弃记录，会改变后续能看到的统计。 所有这些过程都可以内生描述，但它们的存在不要求主观意识创造结果。

最终，余弦自指可以让一个设置稳定下来。 稳定下来的设置仍可能承载旋转相位、走动的钟与不断增加的记录。 因此理论的闭合标准应是： *所有声称相关的内部变量都有明确更新律， 所有声称静止的变量都通过自己的固定条件。* 这保留了用户关于统一与内生性的方向， 并把“完全闭环”变成可以证明、也可以由具体反例否证的数学命题。

<a id="section-A"></a>

## A　来源输入、固定版本与证明归属

**本轮理论输入。**

本稿接续用户提供的完整附件《粘贴的文本 (1)(1).txt》，共 241 行、 21 345 字节；该附件已全文读取。其 SHA–256 为 `1694ec6384883614258f8e81cc3c8ea1b8adc80b7ae485c08ac9f6f22c0db83a`。 附件关于单态方向、伴生面、二态转向、内生观察者及余弦闭环的主张， 是本稿待形式化和检验的理论输入；原文中的物理等同不自动作为已证前提。

**本轮项目快照。**

对 [trureturing 仓库](https://github.com/the-omega-institute/trureturing) 重新查询得到默认分支 `dev`，随后固定提交：

`a5b3a5ef05eeeeba9338b2f682ae41c8b3f40822`。

提交时间为 2026 年 11 月 7 日 20:44:52 UTC， 即 11 月 8 日 04:44:52 Asia/Singapore；查询时间为 11 月 7 日 20:48:09.412909 UTC，即 11 月 8 日 04:48:09.412909 Singapore。 本附录全部项目链接均固定于该提交；前轮来源仅用于导航。 理论目录接口返回 1000 条，已达到接口上限，不构成完整全库清单。 本轮有界核读 8 份相关理论文稿及 3 个 Lean 文件；未执行全库审计或 Lean 构建。

**已有项目供应者。**

OTF-001 的 §§3、9–12 已包含半角旋转元与稳定子、Fubini–Study 长度、 余弦非全局时钟、三角闭路相位、内生仪器及静态历史时钟 [\[7\]](#ref-repo_otf1)。 V74 的 §§4、8、10 已包含给定射线轨迹的全部生成元、Hopf 水平分布、 水平闭路的相位余量及移动内部参考生成元[\[8\]](#ref-repo_v74)。 V78 的 §§2、6 区分全门、旋量、射线和完整框架联络； 完整框架平坦不排除射线曲率[\[10\]](#ref-repo_v78)。 三轴观察者卷、V21 及相位运输卷分别供应任务相对的读出商、 共同参考变换与关系时钟、受声明控制及相干菜单约束的历史相位 [\[11\]](#ref-repo_axes), [\[12\]](#ref-repo_v21), [\[13\]](#ref-repo_holonomy), [\[14\]](#ref-repo_continuation)。

**Clifford–正性重建的准确归属。**

V53 的 §4 已完整核读[\[9\]](#ref-repo_v53)。 其上游条件是全方向线性锐读出，极化后给出 Clifford 关系及中心复结构。 Pauli 表示给所生成实代数 $M_2(\mathbb C)$；自伴元素为 $a\mathbf1+v\cdot\sigma$，谱为 $a\pm|v|$，故正锥恰由 $a\geq|v|$ 给出。 再 *明确加入* 正性、实线性和归一的状态泛函，得到

$$
L(a\mathbf1+v\cdot\sigma)=a+r\cdot v,\qquad |r|\leq1,
 \qquad L\!\left(\frac{\mathbf1\pm n\cdot\sigma}{2}\right)
 =\frac{1\pm r\cdot n}{2}.
$$

这条条件重建及纯态 Born 规则已有来源；它没有从三个几何轴的正交性单独推出。 同卷 §5 还说明，共同 $U(1)$ 是相容全效果下的响应纤维， 内部相干支路可以读取相对相位。本稿的表述不把上述标准重建列为本轮首创。

**外部原文的核读范围。**

Hodge 星的度量、定向和逐阶符号依 Conrad 讲义的定义及证明； 旋量的双侧半角作用依 GABLE §§3.4.1–3.4.3（正文 pp.24–27） 和 Lasenby 作者讲义的 pp.26–29[\[5\]](#ref-hodge), [\[4\]](#ref-gable), [\[6\]](#ref-lasenby)。 Berry 原文实际核读 pp.45–48、50–52，并以原页图像复核 p.51 的式(27) [\[2\]](#ref-berry)；Anandan–Aharonov 原文四页均核读， 并以原页图像复核 pp.1697、1699 的速度公式[\[3\]](#ref-anandan)。 该文采用单位半径射影直线，$ds/dt=2\Delta H/\hbar$； 若本稿采用 $d_{\rm FS}=\arccos|\langle\psi|\phi\rangle|$， 相应长度为其一半，速度为 $\Delta H/\hbar$。 这些来源供应几何约定和标准定理，不供应“任意面积即物理时间”或意识导致坍缩的结论。

**形式化与本轮增量的范围。**

三个 Lean 文件已全文读过，导入依赖未逐一核读，亦未运行构建或轴公理打印。 它们分别支持单测量上下文的可见维数、有限未来读出核的反单调性及时间投影限制律 [\[15\]](#ref-repo_lean)；qubit 的 $1{:}2$ 在这里是维数比例，不是粒子与波的概率比例。 在上述八份已选文稿中，对余弦反馈、相位及斜积关键词的有限检索未命中 本稿的余弦–相位联合收敛表述；这不构成全仓库或全部文献的新颖性证明。 本稿新增的条件命题以正文证明为依据，已有三角 Berry 历史与标准几何结果按上述来源消费。

## 参考来源

<a id="ref-englert"></a>

\[1\] B.-G. Englert. *Fringe Visibility and Which-Way Information: An Inequality*. Phys. Rev. Lett. **77**, 2154–2157 (1996). [出版社页面](https://doi.org/10.1103/PhysRevLett.77.2154)。 本轮核对出版社摘要及元数据；正文的纯标记等式另给自足证明。

<a id="ref-berry"></a>

\[2\] M. V. Berry. *Quantal phase factors accompanying adiabatic changes*. Proc. R. Soc. Lond. A **392**, 45–57 (1984). [DOI](https://doi.org/10.1098/rspa.1984.0023) ；[作者原文](https://michaelberryphysics.wordpress.com/wp-content/uploads/2013/07/berry120.pdf)。 本轮核读范围见附录正文。

<a id="ref-anandan"></a>

\[3\] J. Anandan and Y. Aharonov. *Geometry of quantum evolution*. Phys. Rev. Lett. **65**, 1697–1700 (1990). [DOI](https://doi.org/10.1103/PhysRevLett.65.1697) ；[作者大学原文](https://www.tau.ac.il/~yakir/yahp/yh64)。 原 PDF 四页已核读；具体范围见来源附录。

<a id="ref-gable"></a>

\[4\] L. Dorst, S. Mann and T. Bouma. *GABLE: A Matlab Tutorial for Geometric Algebra*, 2002-12-03. [作者 Waterloo 教程](https://cs.uwaterloo.ca/~smann/GABLE/tutorial.pdf)， §§3.4.1–3.4.3，正文 pp.24–27。

<a id="ref-hodge"></a>

\[5\] B. Conrad. *Math 396: Hodge-star operator*. [Stanford 作者讲义](https://math.stanford.edu/~conrad/diffgeomPage/handouts/star.pdf)， 5 页；核对定义、逐阶平方符号及三维叉积段落。

<a id="ref-lasenby"></a>

\[6\] J. Lasenby. *Lecture 1: Basics of Geometric Algebra*, July 2018. [UPC 托管作者讲义](https://web.mat.upc.edu/sebastia.xambo/A18/JoanLasenby-0723.pdf)， 其中 pp.26–29 给一般三维旋转的双侧半角作用。

<a id="ref-repo_otf1"></a>

\[7\] trureturing 项目文稿： [《正交时间场论 OTF-001》](https://github.com/the-omega-institute/trureturing/blob/a5b3a5ef05eeeeba9338b2f682ae41c8b3f40822/docs/develop/theory/OTF_001_ORTHOGONAL_TIME_FIELD_THEORY.md)。 固定提交同附录；实际核读 L24–247、656–841、855–1042。

<a id="ref-repo_v74"></a>

\[8\] trureturing 项目文稿： [《平滑量子历史、余切与内生运动 V74》](https://github.com/the-omega-institute/trureturing/blob/a5b3a5ef05eeeeba9338b2f682ae41c8b3f40822/docs/develop/theory/AURIC_SMOOTH_QUANTUM_HISTORIES_COTANGENT_DYNAMICS_AND_ENDOGENOUS_MOTION_V74.md)。 实际核读 L326–433、760–909、1013–1100。

<a id="ref-repo_v53"></a>

\[9\] trureturing 项目文稿： [《三轴锐读出、内生复结构与共同相位相容 V53》](https://github.com/the-omega-institute/trureturing/blob/a5b3a5ef05eeeeba9338b2f682ae41c8b3f40822/docs/develop/theory/AURIC_SHARP_THREE_AXIS_READOUTS_ENDOGENOUS_COMPLEX_STRUCTURE_AND_COMMON_PHASE_COMPATIBILITY_V53.md)。 实际核读 L398–735，即 §§4–5 的 Clifford、正性与共同相位论证。

<a id="ref-repo_v78"></a>

\[10\] trureturing 项目文稿： [《门流形与可积关系 V78》](https://github.com/the-omega-institute/trureturing/blob/a5b3a5ef05eeeeba9338b2f682ae41c8b3f40822/docs/develop/theory/AURIC_GATE_MANIFOLDS_INTEGRABLE_RELATIONS_TANGENT_KERNELS_AND_RECURSIVE_ERROR_V78.md)。 实际核读 L165–241、748–893。

<a id="ref-repo_axes"></a>

\[11\] trureturing 项目文稿： [《观察者内生的三轴几何与预测接口》](https://github.com/the-omega-institute/trureturing/blob/a5b3a5ef05eeeeba9338b2f682ae41c8b3f40822/docs/develop/theory/AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md)。 实际核读 L1–82、375–508。

<a id="ref-repo_v21"></a>

\[12\] trureturing 项目文稿： [《静态量子历史与内生观察者 V21》](https://github.com/the-omega-institute/trureturing/blob/a5b3a5ef05eeeeba9338b2f682ae41c8b3f40822/docs/develop/theory/AURIC_STATIC_QUANTUM_HISTORIES_ENDOGENOUS_OBSERVERS_AND_RELATIONAL_CLOCKS_V21.md)。 实际核读 L754–840、968–990。

<a id="ref-repo_holonomy"></a>

\[13\] trureturing 项目文稿： [《FIB-ATOM: Probability, Phase Transport and Holonomy》](https://github.com/the-omega-institute/trureturing/blob/a5b3a5ef05eeeeba9338b2f682ae41c8b3f40822/docs/develop/theory/AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md)。 实际核读 L1–38、129–233、746–795、1428–1484。

<a id="ref-repo_continuation"></a>

\[14\] trureturing 项目文稿： [《FIB-ATOM 相位运输与 holonomy 续篇》](https://github.com/the-omega-institute/trureturing/blob/a5b3a5ef05eeeeba9338b2f682ae41c8b3f40822/docs/develop/theory/AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY_CONTINUATION.md)。 实际核读 L513–595，即参考分量、PSD 余量与纯度判据。

<a id="ref-repo_lean"></a>

\[15\] trureturing 固定提交中的三个 Lean 源文件： [SingleContextVisibleRemainderDimension](https://github.com/the-omega-institute/trureturing/blob/a5b3a5ef05eeeeba9338b2f682ae41c8b3f40822/D5/S3/Quantum/MeasurementGeometry/SingleContextVisibleRemainderDimension.lean) （315 行）； [FiniteTimeProjectionKernelAntitone](https://github.com/the-omega-institute/trureturing/blob/a5b3a5ef05eeeeba9338b2f682ae41c8b3f40822/D5/S3/ConceptDynamics/TimeProjection/FiniteTimeProjectionKernelAntitone.lean) （58 行）； [FiniteTimeProjectionRestrictionLaws](https://github.com/the-omega-institute/trureturing/blob/a5b3a5ef05eeeeba9338b2f682ae41c8b3f40822/D5/S3/ConceptDynamics/TimeProjection/FiniteTimeProjectionRestrictionLaws.lean) （86 行）。全文只读，未执行构建。
