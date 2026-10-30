数学研究稿 / 版本 1.0

# AURIC–E8 相容扩张与观察理论

**积分扩张、中心相位、全局提升、控制生成与黄金读出**

从两个五模式局部接口出发，给出一个条件明确的数学理论：
严格积分扩张选择 E8；同一模 5 关系控制中心相位与全局提升；
实际观察决定相位能否被区分；来源域与读出合同决定黄金投影是否可稳定恢复。

**依据项目** [the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing)

**固定快照** `66259f03d60716f143cd59c7644dadcb67cc1b73`

**编写日期** 2026 年 10 月 30 日

本文给出普通数学意义下的定义与证明，并标明所调用的经典结构定理。
它是可供进一步形式化的研究稿；没有声称完成 Lean 核验、仓库入链或物理实现。
经典格论、Lie 理论、量子判别和紧群控制结果均按其来源使用，不主张新的优先权。

<a id="abstract"></a>

## 摘要

设两个局部五模式接口分别对应 $A_4$ 根格，并在固定正定内积下正交直和。
本文首先证明：任何严格包含 $A_4\oplus A_4$ 且保持整数配对的加法扩张，
自动是偶幺模 E8 根格；带标记的扩张恰有两种，对应
$b=\pm2a$ 的模 5 胶合线。偶性、幺模性与最短新关系无需另加为假设。

选定正号胶合后，E8 的五分级给出
$H=(\operatorname{SU}(5)\times\operatorname{SU}(5))/\langle(\zeta I,\zeta^2I)\rangle$。
本文证明实际效果族的中心相位观察核，并计算带权分级纯态探针的最优成功率
$\frac15(\sum_j\sqrt{w_j})^2$。在有限二维复形上，全局提升存在恰当且仅当一个
$H^2(-;\mathbb F_5)$ 障碍消失；两个局部障碍的相容式为 $o_2=2o_1$，
与根格胶合由同一个中心商联系。恢复正负两种标记后，非零的相容全局障碍
恰能选定其中一个胶合符号。均匀分级探针可以精确读出给定边提升的面缺陷。

控制方面，完整局部 $\mathfrak{su}(5)\oplus\mathfrak{su}(5)$ 加任意一个非局部连续方向生成紧
$\mathfrak e_8$。有限的一参数生成菜单有统一有限词长上界，但本文不计算该上界；
Haar 几乎处处的目标至少需要 248 个可调单参数脉冲，若任意局部门免费，
至少需要五次关系脉冲。

读出方面，黄金投影 $a+\varphi b$ 在整数格上精确单射而逆处处不连续。
高度 $H$ 的来源域有最小间隔 $\Theta(H^{-1})$；
共轭双读出的全格最坏误差阈值恰为 $1/2$；
有界内部窗口使单读出具有统一分离及 Lipschitz 逆，并产生非周期 Delone 集。
黄金细化满足改变窗口后的精确尺度协变，保存的是一个不定配对。
这些结果共同区分了结构存在、全局相容、可观察性与有限精度可恢复性。

<a id="contents"></a>
## 目录

- [摘要](#abstract)
- [1. 项目接口、逻辑范围与理论对象](#section-1)
  - [1.1 从项目中保留的具体结构](#subsection-1-1)
  - [1.2 四种对象不能混同](#subsection-1-2)
  - [1.3 共同的恢复语言](#subsection-1-3)
- [2. 严格积分扩张的 E8 选择定理](#section-2)
  - [2.1 局部根格及其判别配对](#subsection-2-1)
  - [2.2 假设不可省略及一个量子反模型](#subsection-2-2)
- [3. 五分级、局部子群与中心相位](#section-3)
  - [3.1 从根格到标准 Lie 代数](#subsection-3-1)
- [4. 实际观察、相干资源与相位辨别](#section-4)
  - [4.1 不扩大权限的效果族](#subsection-4-1)
  - [4.2 最优单份概率的完整公式](#subsection-4-2)
- [5. 全局相容的中心提升障碍](#section-5)
  - [5.1 固定射影表示的提升](#subsection-5-1)
  - [5.2 有限二维复形上的可计算形式](#subsection-5-2)
- [6. 控制闭包、精确有限字与成本下界](#section-6)
  - [6.1 一个关系方向的 Lie 生成](#subsection-6-1)
  - [6.2 统一有限词长的存在定理](#subsection-6-2)
  - [6.3 两种资源合同下的必要成本](#subsection-6-3)
- [7. 黄金读出与有限精度恢复](#section-7)
  - [7.1 额外选定的几何读出](#subsection-7-1)
  - [7.2 有限高度下的匹配精度界](#subsection-7-2)
  - [7.3 共轭双读出的全域鲁棒性](#subsection-7-3)
- [8. 有界内部窗口、非周期性与尺度协变](#section-8)
  - [8.1 来源限制恢复稳定性](#subsection-8-1)
  - [8.2 Delone 集与有限局部复杂性](#subsection-8-2)
  - [8.3 黄金细化保持的准确结构](#subsection-8-3)
- [9. 综合定理：全局相容可以选择胶合标记](#section-9)
  - [9.1 从局部积分选择到全局标记选择](#subsection-9-1)
  - [9.2 一个同时满足各层条件的模型](#subsection-9-2)
  - [9.3 依赖、反例与尚未被证明的部分](#subsection-9-3)
- [10. 进一步形式化的精确目标](#section-10)
- [参考文献与项目定位](#references)

<a id="section-1"></a>

## 1. 项目接口、逻辑范围与理论对象

<a id="sec-interface"></a>

<a id="subsection-1-1"></a>

### 1.1 从项目中保留的具体结构

本文使用固定快照 `66259f03d60716f143cd59c7644dadcb67cc1b73`，不把它表述为持续更新的最新状态。
主要项目依据为 [[1](#ref-repoOmega), [2](#ref-repoFib)]。其中五模式 FIB 合法空间是

<a id="eq-fib"></a>

$$
\mathcal H_F=\operatorname{span}_{\mathbb C}\{\lvert 000\rangle,\lvert 100\rangle,\lvert 010\rangle,\lvert 001\rangle,\lvert 101\rangle\}
\simeq\mathbb C^5.
\tag{1}
$$

依次记这些模式为 $(N,2,3,5,25)$。对对角态，若概率向量依此排序为
$p=(p_0,p_1,p_2,p_3,p_{13})$，则三个占据均值为

$$
X=p_1+p_{13},\qquad Y=p_3+p_{13},\qquad Z=p_2.
$$

所有给出相同均值的概率向量恰为

<a id="eq-fiber"></a>

$$
p=(1-X-Y-Z+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa),
\quad
\max(0,X+Y+Z-1)\le\kappa\le\min(X,Y).
\tag{2}
$$

这是沿 $(1,-1,0,-1,1)$ 的区间纤维。对一般五维密度态，三个均值不会把纤维
缩成一维：在正定态处，迹一 Hermitian 空间实维数为 $24$，这三个独立线性
约束留下维数 $21$。因此必须声明来源域是对角概率还是全部量子态。

项目原始菜单包括同一固定总和 $K$ 的非负时间演化、指定完全测量和停止；
它没有自动提供任意相位门或独立控制。项目后来另立假设 45.1、55.2，
逐项增加独立翻转、实参数时间、零漂移与指定相位复用。
其定理 64.1 在该理想菜单中给出精确有限字结论，并明确区分脉冲数、持续时间、
参数精度与硬件成本。本文沿用这一习惯：**每一项操作资源都必须单独写入假设**。
这些定位都是项目理论文本的陈述，不代替本文定理的证明，也不声称已经核验对应
Lean 声明。[[1](#ref-repoOmega)]

<a id="subsection-1-2"></a>

### 1.2 四种对象不能混同

| 层次 | 数学对象 | 本文赋予的用途 |
| --- | --- | --- |
| 局部态 | $\mathbb C^5,\ \mathbb C^5\otimes\mathbb C^5$ | 原始五模式接口及普通复合态；维数为 5 或 25 |
| 关系格 | $A_4\oplus A_4\subset\Gamma\subset\mathbb R^8$ | 整数电荷、允许关系和积分扩张 |
| 全局对称 | 紧 $E_8$，$\mathcal K=\mathfrak e_{8,\mathbb C}$ | Lie 闭包、248 维伴随载体及五分级 |
| 读出记录 | 效果概率，$a+\varphi b$ | 实际观察等价和误差下的来源恢复 |

这些对象之间的映射是理论的一部分，不能仅凭相同数字或名称识别。
例如，后文从五个 E8 分级各取一个向量得到的五维探针，
并不是自动等同于式 [(1)](#eq-fib) 的原始五维空间。

<a id="statement-1-1"></a>

**定义 1.1（分层理论的数据）。**

本理论的一份实例由以下数据组成，所用结论只依赖其列出的部分：

1. 两个带标记的五维局部接口 $V,W$，其电荷空间均取标准 $A_4$；

2. 固定正交、等尺度的正定内积，以及严格积分关系扩张 $\Gamma$；

3. 从该根格得到的标准复 E8 Lie 代数、其紧实型及伴随载体 $\mathcal K$；

4. 指定的可制备态、允许门、实际效果集合与所计算的资源；

5. 需要全局拼接时，有限二维复形上的投影平坦边数据；

6. 需要黄金读出时，额外选定的整数基、黄金投影和来源域。

<a id="subsection-1-3"></a>

### 1.3 共同的恢复语言

<a id="statement-1-2"></a>

**命题 1.2（观察纤维判据）。**

设 $q:S\to Y$ 是记录映射，$f:S\to T$ 是目标，且 $S\ne\varnothing$。
存在 $d:q(S)\to T$ 满足 $f=d\circ q$，当且仅当

$$
q(s)=q(s')\Longrightarrow f(s)=f(s').
$$

**证明。**

若 $f=d\circ q$，结论直接成立。反之，对 $y\in q(S)$，
把 $d(y)$ 定义为任意 $s\in q^{-1}(y)$ 的 $f(s)$；
纤维上常值保证存在且唯一，因而无需为每个纤维保留额外选择。证毕。
 □

该命题只说解码映射存在，不给计算时间、连续性或误差保证。
后文的相位观察核与黄金稳定性分别补上这些不同义务。

<a id="section-2"></a>

## 2. 严格积分扩张的 E8 选择定理

<a id="sec-selection"></a>

<a id="subsection-2-1"></a>

### 2.1 局部根格及其判别配对

令

$$
V_0=\{x\in\mathbb R^5:\sum_i x_i=0\},\qquad
Q=V_0\cap\mathbb Z^5,\qquad
L_0=Q\oplus Q\subset E=V_0\oplus V_0.
$$

内积为两份标准欧氏内积的正交直和。$Q$ 是根长平方为 $2$ 的 $A_4$ 根格。
记

$$
\omega_k=e_1+\cdots+e_k-\frac{k}{5}\mathbf1,\qquad 1\le k\le4.
$$

<a id="statement-2-1"></a>

**引理 2.1（判别群和最短代表）。**

<a id="lem-discriminant"></a>

有 $Q^*/Q\simeq\mathbb F_5$，以 $[\omega_1]$ 为生成元，且
$[\omega_k]=k[\omega_1]$。在此标记下，

$$
\overline B(a,a')=\frac{4aa'}5\pmod{\mathbb Z}.
$$

类 $k\in\{1,2,3,4\}$ 的最小平方范数为 $k(5-k)/5$，
达到最小值的向量恰有 $\binom5k$ 个。$Q$ 中平方范数为 $2$ 的向量有 $20$ 个。

**证明。**

$Q$ 由 $e_i-e_{i+1}$ 生成，故 $x\in Q^*$ 当且仅当 $x_i-x_j\in\mathbb Z$。
结合 $\sum_i x_i=0$，所有坐标具有共同的五分之一小数部分，商群阶为 $5$。
$\omega_k-k\omega_1$ 是坐标和为零的整数向量，故有相应类等式。
又 $\omega_1^2=4/5$，得到判别配对。

类 $k$ 的向量可且只能写成
$m-(k/5)\mathbf1$，其中 $m\in\mathbb Z^5$、$\sum_i m_i=k$。于是

$$
\left\lVert m-(k/5)\mathbf1\right\rVert^2=\sum_i m_i^2-\frac{k^2}{5}
\ge k-\frac{k^2}{5},
$$

因为任意整数 $m_i$ 都满足 $m_i^2\ge m_i$。
等号恰在每个 $m_i\in\{0,1\}$ 时成立，即恰选 $k$ 个位置。
在零类中，平方范数为 $2$ 且坐标和为零只可能是 $e_i-e_j$，$i\ne j$，
共有 $5\cdot4=20$ 个。
最后，以 $e_i-e_{i+1}$ 为基，Gram 矩阵的主对角元为 $2$、相邻元为 $-1$；
其 $n$ 阶行列式满足 $D_n=2D_{n-1}-D_{n-2}$、$D_0=1,D_1=2$，
故 $D_n=n+1$，特别地 $\det Q=5$。证毕。
 □

<a id="statement-2-2"></a>

**定义 2.2（积分关系扩张）。**

加法子群 $L\subset E$ 称为 $L_0$ 的积分关系扩张，当

$$
L_0\subset L,\qquad \left\langle L,L\right\rangle\subset\mathbb Z.
$$

若 $L\ne L_0$，称为严格扩张。该定义不预设偶性、幺模性或新的最短根。

<a id="statement-2-3"></a>

**定理 2.3（严格积分扩张选择 E8）。**

<a id="thm-selection"></a>

固定上述标记和内积，严格积分关系扩张恰有两个：

$$
\begin{aligned}
\Gamma_+&=L_0+\mathbb Z(\omega_1,\omega_2),&
C_+&=\{(a,2a):a\in\mathbb F_5\},
\end{aligned}
\tag{3}
$$

$$
\begin{aligned}
\Gamma_-&=L_0+\mathbb Z(\omega_1,\omega_3),&
C_-&=\{(a,-2a):a\in\mathbb F_5\}.
\end{aligned}
\tag{4}
$$

二者自动为偶幺模格，指数 $[\Gamma_\pm:L_0]=5$，
均与 E8 根格等距。带标记时有两种扩张；忘掉该标记后只有一个等距类型。

**证明。**

**第一步：把所有扩张限制到有限商。**
若 $x\in L$，则 $\left\langle x,L_0\right\rangle\subset\mathbb Z$，所以 $x\in L_0^*$。
因此 $L_0\subset L\subset L_0^*$，格的离散性自动成立，
而 $C=L/L_0$ 是 $(Q^*/Q)^2\simeq\mathbb F_5^2$ 的子空间。
积分性等价于 $C$ 对判别配对

$$
\overline B((a,b),(a',b'))=\frac{4(aa'+bb')}{5}\pmod{\mathbb Z}
$$

全迷向。

**第二步：分类非零全迷向子空间。**
任何非零 $(a,b)\in C$ 满足 $a^2+b^2=0$ 于 $\mathbb F_5$。
若 $a=0$，则 $b=0$，矛盾。因此 $a\ne0$，
而 $(b/a)^2=-1=4$，即 $b/a=2$ 或 $-2$。
对应两条直线均全迷向；任何二维子空间都是全空间，显然不全迷向。
故非零 $C$ 恰为 $C_+$ 或 $C_-$，其逆像正是所列两格。

**第三步：偶性与幺模性自动出现。**
对 $x\in\Gamma_\pm$，有 $5x\in L_0$。
$L_0$ 是偶格，所以 $25x^2\in2\mathbb Z$；积分性又使 $x^2\in\mathbb Z$。
因 $25$ 是奇数，$x^2\in2\mathbb Z$。
$A_4$ 的 Gram 行列式为 $5$，故

$$
\det\Gamma_\pm=\frac{\det L_0}{[\Gamma_\pm:L_0]^2}
=\frac{25}{25}=1.
$$

这里格行列式指 Gram 行列式。

**第四步：直接识别根系。**
零胶合类中有 $40$ 个平方范数 $2$ 的根。
每个非零类 $(j,\pm2j)$ 的两份最小范数之和为 $2$；
由引理 [2.1](#lem-discriminant)，各有 $50$ 个最短向量。
所以整格恰有 $40+4\cdot50=240$ 个平方范数 $2$ 的向量。
若 $r^2=2$，则反射
$s_r(x)=x-\left\langle x,r\right\rangle r$ 保持该积分格，故这些向量形成有限约化根系。
它包含两个 $A_4$ 根系，且胶合根 $(\omega_1,\omega_2)$
或 $(\omega_1,\omega_3)$ 分别与两个因子的根非正交，
因此该秩八根系不可约。按有限不可约单根长根系的 ADE 分类，
秩八的 $A_8,D_8,E_8$ 根数分别为 $72,112,240$，故这里是 E8。
原来两个 $A_4$ 的根连同胶合根生成整格，因此它确为 E8 根格。
此处明确调用经典 ADE 分类，而非仅由维数猜测 Lie 类型。

**第五步：两个标记的关系。**
等距映射 $(x,y)\mapsto(x,-y)$ 将 $C_+$ 变为 $C_-$，
因此两格等距。这一映射不属于保持各局部标记的
$W(A_4)\times W(A_4)$；局部 Weyl 群在判别群上作用平凡。
故不能把带标记的两种选择默认为同一个选择。证毕。
 □

<a id="statement-2-4"></a>

**推论 2.4（一条新关系已经足够）。**

若 $x\in E\setminus L_0$ 满足
$\left\langle x,L_0\right\rangle\subset\mathbb Z$ 且 $x^2\in\mathbb Z$，则 $L_0+\mathbb Z x$ 已是 E8 根格。

**证明。**

任意两元素 $l+mx,l'+nx$ 的内积都是整数，故构成严格积分扩张。
应用定理 [2.3](#thm-selection)。不需要再要求 $x^2=2$。证毕。
 □

<a id="statement-2-5"></a>

**命题 2.5（一类最短胶合配方中的五的唯一性）。**

对两个等尺度 $A_{m-1}$，若要求新向量为
$(\omega_1,\omega_k)$、$1\le k\le m-1$ 且平方范数等于 $2$，
则只能有 $(m,k)=(5,2)$ 或 $(5,3)$。

**证明。**

范数条件为

$$
\frac{m-1+k(m-k)}m=2,
\quad\text{即}\quad (k-1)m=k^2+1.
$$

$k=1$ 不可能；$k\ge2$ 时，
$m=k+1+2/(k-1)$。整数性迫使 $k-1$ 为 $2$ 的正因子，
得 $k=2,3$，且均有 $m=5$。证毕。
 □

这个命题只覆盖明示的胶合配方，不能推出所有可能物理模型都必须有五个模式。
经典 $A_4^2$ 胶合的具体实现亦可参看 [[4](#ref-sage)]；
本文的选择证明则展示了各额外假设的作用。

<a id="subsection-2-2"></a>

### 2.2 假设不可省略及一个量子反模型

不要求严格扩张时，$L=L_0$ 就是反例；不要求整数配对时，
$L=L_0^*$ 就不满足结论。等尺度、正交和“在同一八维电荷空间内扩张”
也是实质条件，不能由 $\dim V=\dim W=5$ 单独推出。

<a id="statement-2-6"></a>

**命题 2.6（普通张量积给出不同闭包）。**

<a id="prop-su25"></a>

在 $\mathcal H=V\otimes W\simeq\mathbb C^{25}$ 上，令
$\mathfrak h_{\rm loc}=\mathfrak{su}(V)\otimes I+I\otimes\mathfrak{su}(W)$。
对任意 $X\in\mathfrak{su}(25)\setminus\mathfrak h_{\rm loc}$，

$$
\operatorname{Lie}_{\mathbb R}(\mathfrak h_{\rm loc},X)=\mathfrak{su}(25).
$$

**证明。**

复化后有 $\mathfrak h_{\rm loc,\mathbb C}$-模分解

$$
\mathfrak{sl}(V\otimes W)
=(\mathfrak{sl} V\otimes I)\oplus(I\otimes\mathfrak{sl} W)
\oplus(\mathfrak{sl} V\otimes\mathfrak{sl} W).
$$

最后一项是直和 Lie 代数的不可约模，维数为 $24\cdot24=576$。
把 $X$ 的局部部分减去后，生成子代数在此不可约模中包含非零向量。
由于对子代数中的局部方向取括号保持生成子代数，不可约性使整个非局部模
都包含在内。因此其复化为 $\mathfrak{sl}(25)$，实维数同为 $624$，得到结论。证毕。
 □

这说明双五模式的普通复合和双 $A_4$ 的积分关系扩张回答不同问题。
E8 的选择来源于定理 [2.3](#thm-selection) 的条件。

<a id="section-3"></a>

## 3. 五分级、局部子群与中心相位

<a id="sec-grading"></a>

<a id="subsection-3-1"></a>

### 3.1 从根格到标准 Lie 代数

以下选 $\Gamma=\Gamma_+$。按经典 Chevalley–Serre 根系构造，
得到复单 Lie 代数 $\mathfrak g=\mathfrak e_{8,\mathbb C}$ 及其紧实型 $\mathfrak k$。
这里采用标准构造连同 Jacobi 恒等式和根串括号定理；
没有把任意 $248$ 维向量空间直接称为 E8。
与本节对应的显式五分级及子群见 Yokota [[3](#ref-yokota)]，
尤其其定理 5.12.1、5.12.5。

<a id="statement-3-1"></a>

**命题 3.1（由胶合类诱导的五分级）。**

<a id="prop-grading"></a>

以 $\Gamma/L_0\simeq\mathbb F_5$ 标记根空间，有

$$
\mathfrak g=\bigoplus_{j\in\mathbb F_5}\mathfrak g_j,\qquad
[\mathfrak g_j,\mathfrak g_k]\subset\mathfrak g_{j+k}.
$$

令 $V,W\simeq\mathbb C^5$ 为两份标准模，则

$$
\begin{aligned}
\mathfrak g_0&=\mathfrak{sl}(V)\oplus\mathfrak{sl}(W),\\
\mathfrak g_1&=V\otimes\Lambda^2W,\\
\mathfrak g_2&=\Lambda^2V\otimes W^*,\\
\mathfrak g_3&=(\Lambda^2V)^*\otimes W,\\
\mathfrak g_4&=V^*\otimes(\Lambda^2W)^*.
\end{aligned}
$$

其维数依次为 $48,50,50,50,50$。

**证明。**

零类含两个 $A_4$ 的 $40$ 个根空间及八维 Cartan 空间，所以得到 $\mathfrak g_0$。
类 $j$ 的最短权由引理 [2.1](#lem-discriminant) 给出，正是
$\Lambda^jV\otimes\Lambda^{2j\bmod5}W$ 的权。
在 $j=1,2,3,4$ 时化简外幂对偶即为所列模块。
根空间括号在根之和为根时落入该和根空间，否则为零或 Cartan 元，
故胶合类相加给出分级性质。证毕。
 □

设 $G$ 为紧连通 E8 群，取其标准紧实型；
它的中心平凡。令 $\mathfrak h=\mathfrak{su}(5)\oplus\mathfrak{su}(5)\subset\mathfrak k$。
记 $\zeta=e^{2\pi i/5}$。

<a id="statement-3-2"></a>

**定理 3.2（准确的局部群与五重提升）。**

<a id="thm-center"></a>

$\mathfrak h$ 对应的连通子群为

$$
H=\frac{\operatorname{SU}(5)\times\operatorname{SU}(5)}{C},
\qquad
C=\{(\zeta^aI,\zeta^{2a}I):a\in\mathbb F_5\}.
$$

它忠实嵌入 $G$，并有中心扩张

<a id="eq-centralextension"></a>

$$
1\longrightarrow\mu_5\longrightarrow H
\xrightarrow{p}\operatorname{PU}(5)\times\operatorname{PU}(5)\longrightarrow1.
\tag{5}
$$

取 $z=[(\zeta I,I)]$，在伴随复空间 $\mathcal K=\mathfrak g$ 上记其表示为 $Z$，
则

$$
Z|_{\mathfrak g_j}=\zeta^j I.
$$

因此一个已指定的局部射影对恰有五个 $H$ 提升。

**证明。**

紧单连通群 $\operatorname{SU}(5)^2$ 的 Lie 代数嵌入积分为到 $G$ 的群同态。
核离散且正规，故包含在中心 $\mu_5^2$。
由命题 [3.1](#prop-grading)，中心元素 $(\zeta^aI,\zeta^bI)$
在 $\mathfrak g_j$ 上乘以 $\zeta^{j(a+2b)}$。
它在整个伴随空间上平凡，恰当且仅当 $a+2b=0$，
亦即 $b=2a$ 于 $\mathbb F_5$。因 $G$ 中心平凡，伴随表示忠实，
故该同态的核正是 $C$。

到两个射影群的映射核是 $\mu_5^2/C$。
同态 $(a,b)\mapsto a+2b$ 具有核 $C$，并将商识别为 $\mathbb F_5$，
从而得到式 [(5)](#eq-centralextension)。
取 $(a,b)=(1,0)$ 即得 $Z$ 的分级作用及五重纤维。证毕。
 □

<a id="statement-3-3"></a>

**说明 3.3（相位属于哪一个群）。**

这份 $\mu_5$ 是 $H\to\operatorname{PU}(5)^2$ 的核，也是 $H$ 的中心；
它不是 E8 的中心。原始单个五维接口上的整体相位，
与伴随载体不同分级之间的相对相位，也不是同一个观察对象。

<a id="statement-3-4"></a>

**命题 3.4（E8 不能忠实作用在原始五维空间上）。**

任意连续群同态 $G\to U(5)$ 都是平凡的。

**证明。**

导数 $\mathfrak k\to\mathfrak u(5)$ 的核是理想。
因 $\mathfrak k$ 为实单 Lie 代数，导数要么单射，要么为零。
单射被 $248>25$ 排除，所以导数为零。
$G$ 连通，像因此只有单位元。证毕。
 □

后文以负 Killing 形式在紧实型上的复化构造正定 Hermitian 内积，
使 $\mathcal K$ 成为 $248$ 维酉载体。E8 控制群的实维数为 $248$，
任一态轨道维数至多为 $248$；
它不等于维数为 $248^2-1=61503$ 的 $\operatorname{SU}(248)$。

<a id="section-4"></a>

## 4. 实际观察、相干资源与相位辨别

<a id="sec-observation"></a>

<a id="subsection-4-1"></a>

### 4.1 不扩大权限的效果族

令 $P_j$ 为 $\mathfrak g_j$ 的正交投影。指定实际允许的效果族
$\mathscr E\subset\{E:0\le E\le I\}$，并定义

$$
\mathcal O=\operatorname{span}_{\mathbb C}(\{I\}\cup\mathscr E).
$$

这里只取线性张成，不自动关闭到乘法代数，也不自动提供谱测量。
定义 $a\sim_{\mathscr E}b$，当

$$
\operatorname{tr}(EZ^a\rho Z^{-a})=\operatorname{tr}(EZ^b\rho Z^{-b})
$$

对所有密度态 $\rho$ 和所有 $E\in\mathscr E$ 成立。
“所有密度态”是此结构性等价定义的量词；
若实验只允许部分态，必须另按该来源域计算观察核。

<a id="statement-4-1"></a>

**定理 4.1（相位观察核）。**

<a id="thm-obskernel"></a>

令

$$
D(\mathcal O)=\{j-k\in\mathbb F_5:
P_jAP_k\ne0\text{ 对某个 }A\in\mathcal O\}.
$$

则

$$
a\sim_{\mathscr E}b
\quad\Longleftrightarrow\quad
(a-b)d=0\quad\text{对所有 }d\in D(\mathcal O).
$$

特别地，全为分级块对角效果时五种相位都不可见；
有任一跨分级块时，全输入实验族区分所有不同相位。

**证明。**

密度态分离 Hermitian 算子，故响应对所有态相等恰等价于
$Z^{-a}EZ^a=Z^{-b}EZ^b$。
这一等式对效果成立当且仅当对其线性张成成立。
而其 $(j,k)$ 块是

$$
P_jZ^{-a}AZ^aP_k=\zeta^{a(k-j)}P_jAP_k.
$$

故每个非零块都要求 $(a-b)(j-k)=0$ 于 $\mathbb F_5$。
$5$ 是素数，任一非零 $j-k$ 已迫使 $a=b$。证毕。
 □

<a id="statement-4-2"></a>

**推论 4.2（固定状态与中心平均）。**

若允许全部效果，固定 $\rho$ 的五个状态
$\rho_a=Z^a\rho Z^{-a}$ 要么全相同，要么两两不同。
前者恰在 $\rho$ 分级块对角时成立。此外

$$
\frac15\sum_{a=0}^4Z^a\rho Z^{-a}=\sum_{j=0}^4P_j\rho P_j.
$$

**证明。**

取每一块并使用
$P_j\rho_aP_k=\zeta^{a(j-k)}P_j\rho P_k$；
对非零跨块，素数性再次排除两个不同相位给出同一状态。
平均式由 $\sum_a\zeta^{a(j-k)}=5\delta_{jk}$ 得到。证毕。
 □

两两不同不等于一份样本可以完美辨别，也不等于一个固定效果就区分五值。
例如 $\psi=(e_0+e_1)/\sqrt2$、$E=\lvert \psi\rangle\langle \psi\rvert$ 给出的概率是
$(1+\cos(2\pi a/5))/2$，相位 $a$ 和 $-a$ 在这个实验中相同。

<a id="subsection-4-2"></a>

### 4.2 最优单份概率的完整公式

从每个 $\mathfrak g_j$ 选单位向量 $e_j$，令

$$
w_j\ge0,\quad \sum_jw_j=1,\qquad
\psi=\sum_j\sqrt{w_j}e_j,\qquad
\psi_a=Z^a\psi.
$$

假定这些探针可制备，未知 $a$ 均匀分布，并允许所需的五结果 POVM。
这些是本节的新增操作条件，不能由局部五模式或 E8 控制自动推出。

<a id="statement-4-3"></a>

**定理 4.3（带权五分级探针的最优辨别）。**

<a id="thm-phaseopt"></a>

$$
P_{\rm opt}(w)=
\sup_{\substack{M_a\ge0\\\sum_aM_a=I}}
\frac15\sum_a\left\langle \psi_a,M_a\psi_a\right\rangle
=\frac15\left(\sum_{j=0}^4\sqrt{w_j}\right)^2.
$$

完美单份辨别恰在所有 $w_j=1/5$ 时成立。
若仅 $r$ 个权重非零，则 $P_{\rm opt}\le r/5$，
等号恰在这些非零权重均为 $1/r$ 时成立。

**证明。**

记 $m^{(a)}_{jk}=\left\langle e_j,M_ae_k\right\rangle$。
正半定性给
$|m^{(a)}_{jk}|\le\sqrt{m^{(a)}_{jj}m^{(a)}_{kk}}$。
因此

$$
\begin{aligned}
P_{\rm succ}
&\le\frac15\sum_{j,k}\sqrt{w_jw_k}
\sum_a\sqrt{m^{(a)}_{jj}m^{(a)}_{kk}}\\
&\le\frac15\sum_{j,k}\sqrt{w_jw_k}
\sqrt{\left(\sum_am^{(a)}_{jj}\right)
\left(\sum_am^{(a)}_{kk}\right)}
=\frac15\left(\sum_j\sqrt{w_j}\right)^2.
\end{aligned}
$$

第二个不等式为 Cauchy–Schwarz；最后使用 $\sum_aM_a=I$。

为达到上界，令 $S=\operatorname{span}\{e_0,\ldots,e_4\}$，
取 Fourier 正交基及全空间 POVM

$$
f_a=\frac1{\sqrt5}\sum_j\zeta^{aj}e_j,\qquad
M_a=\lvert f_a\rangle\langle f_a\rvert+\frac15(I-P_S).
$$

于是 $\left\langle f_a,\psi_a\right\rangle=5^{-1/2}\sum_j\sqrt{w_j}$，
恰达到上界。最后两项结论分别由
$(\sum_j\sqrt{w_j})^2\le5$ 和在 $r$ 项上的 Cauchy–Schwarz
及其等号条件得到。证毕。
 □

该公式是几何均匀纯态最优判别在此五分级中的专门化；
一般平方根测量背景见 Eldar–Forney [[5](#ref-eldar)]。
本节给出直接证明，以免把“可区分”替换成未经量化的成功保证。

<a id="statement-4-4"></a>

**推论 4.4（混合态的权重上界）。**

任意密度态 $\rho$，令 $w_j=\operatorname{tr}(P_j\rho)$，则其均匀中心轨道满足

$$
P_{\rm opt}(\rho)\le\frac15\left(\sum_j\sqrt{w_j}\right)^2.
$$

混合态等权重不是完美辨别的充分条件。

**证明。**

纯化 $\rho$，将投影改为 $P_j\otimes I$。
纯化态各分级范数仍为 $\sqrt{w_j}$，故可用定理 [4.3](#thm-phaseopt)。
允许访问纯化环境只会扩大测量集合，给出上界。
反例 $\rho=\frac15\sum_j\lvert e_j\rangle\langle e_j\rvert$ 在中心作用下不变，
最优成功率仅为 $1/5$。证毕。
 □

<a id="statement-4-5"></a>

**命题 4.5（额外提供多份来源时的成功率）。**

<a id="prop-copies"></a>

若可取得同一未知相位的 $n$ 份 $\psi_a$ 并允许联合测量，记
$w^{*n}$ 为 $\mathbb F_5$ 上的循环卷积，则

$$
P_{\rm opt}^{(n)}=\frac15\left(\sum_r\sqrt{w^{*n}_r}\right)^2.
$$

若 $w$ 支持至少两个分级，令
$r_*=\max_{d\ne0}|\sum_jw_j\zeta^{dj}|<1$，则

$$
1-P_{\rm opt}^{(n)}\le4r_*^{\,2n}.
$$

有限 $n$ 的完美辨别仍当且仅当最初 $w$ 均匀。

**证明。**

按总分级 $j_1+\cdots+j_n$ 分解 $\psi^{\otimes n}$，
所得正交分量的平方范数为 $w^{*n}_r$，故第一式由
定理 [4.3](#thm-phaseopt) 得到。
非零 $d$ 时，素数性使两个不同支持点的 $\zeta^{dj}$ 不同，
严格三角不等式给出 $r_*<1$。
设 $p=w^{*n}$、$u_j=1/5$、$B=\sum_j\sqrt{p_ju_j}$。则

$$
1-B^2
\le\sum_j(\sqrt{p_j}-\sqrt{u_j})^2
\le5\sum_j(p_j-u_j)^2
=\sum_{d\ne0}|\widehat w(d)|^{2n}.
$$

这里第一式来自 $1-B^2\le2(1-B)$，第二式来自分母
$(\sqrt{p_j}+\sqrt{u_j})^2\ge u_j$，最后为有限 Fourier 的 Parseval 等式。
这给出误差界。有限次卷积均匀恰等价于所有非平凡
$\widehat w(d)^n=0$，也即最初 $\widehat w(d)=0$，等价于 $w$ 均匀。证毕。
 □

<a id="section-5"></a>

## 5. 全局相容的中心提升障碍

<a id="sec-obstruction"></a>

<a id="subsection-5-1"></a>

### 5.1 固定射影表示的提升

设 $\Pi$ 为离散群，固定
$\rho:\Pi\to G_0=\operatorname{PU}(5)\times\operatorname{PU}(5)$。
提升是同态 $\widetilde\rho:\Pi\to H$ 满足 $p\widetilde\rho=\rho$。
本节固定这份投影识别，不额外按任意 $H$ 共轭取商。

任取集合意义的规范化提升 $s(\gamma)\in H$，
满足 $p(s(\gamma))=\rho(\gamma)$、$s(1)=1$。唯一的
$c(\gamma,\delta)\in\mathbb F_5$ 由

$$
s(\gamma)s(\delta)=z^{c(\gamma,\delta)}s(\gamma\delta)
$$

定义。这里 $z\in H$ 是群元素，$Z=\operatorname{Ad}(z)$ 才是作用于 $\mathcal K$ 的矩阵。
这种中心扩张提升障碍的通用背景见 [[6](#ref-neeb)]；
以下只证明所需的平坦表示版本。

<a id="statement-5-1"></a>

**定理 5.1（提升障碍与自由参数）。**

<a id="thm-grouplift"></a>

上述 $c$ 满足二余循环恒等式

$$
c(\gamma,\delta)+c(\gamma\delta,\epsilon)
=c(\delta,\epsilon)+c(\gamma,\delta\epsilon).
$$

换选提升只改变一个二余边界，因此定义
$o_H(\rho)=[c]\in H^2(\Pi;\mathbb F_5)$，系数作用平凡。存在同态提升当且仅当
$o_H(\rho)=0$。一旦存在，固定 $\rho$ 的实际同态提升集合是
$H^1(\Pi;\mathbb F_5)=\operatorname{Hom}(\Pi,\mathbb F_5)$ 的挠集。

**证明。**

比较 $(s(\gamma)s(\delta))s(\epsilon)$ 与
$s(\gamma)(s(\delta)s(\epsilon))$，使用 $z$ 中心性即得余循环恒等式。
换为 $s'(\gamma)=z^{b(\gamma)}s(\gamma)$ 时，

$$
c'(\gamma,\delta)=c(\gamma,\delta)
+b(\gamma)+b(\delta)-b(\gamma\delta)=c+\delta b.
$$

所以能把乘法缺陷全部消去，恰当且仅当 $[c]=0$。
两同态提升之差唯一写为
$\widetilde\rho_1(\gamma)=z^{\chi(\gamma)}\widetilde\rho_0(\gamma)$；
同态性与中心性说明 $\chi$ 必且只须是加法同态。
因此 $\operatorname{Hom}(\Pi,\mathbb F_5)$ 的作用自由且传递，
即所称挠集：选一个基准提升后才得到与该群的具体识别。证毕。
 □

<a id="statement-5-2"></a>

**定理 5.2（与根格同源的障碍相消式）。**

<a id="thm-cancel"></a>

写 $\rho=(\rho_1,\rho_2)$，令两因子各自提升到 $\operatorname{SU}(5)$ 的障碍为
$o_1,o_2\in H^2(\Pi;\mathbb F_5)$。则

$$
\boxed{\ o_H(\rho)=o_1+2o_2,\qquad
\rho\text{ 可提升到 }H\ \Longleftrightarrow\ o_2=2o_1.\ }
$$

**证明。**

选两因子的集合提升，其乘法缺陷分别为
$\zeta^{c_1(\gamma,\delta)}I$ 和 $\zeta^{c_2(\gamma,\delta)}I$。
定理 [3.2](#thm-center) 的商映射满足

$$
[(\zeta^aI,\zeta^bI)]=[(\zeta^{a+2b}I,I)]=z^{a+2b}.
$$

因此联合缺陷就是 $c_1+2c_2$，取上同调类得第一式。
于 $\mathbb F_5$ 中，$o_1+2o_2=0$ 等价于 $o_2=2o_1$。证毕。
 □

根格胶合线与障碍相消式中的同一个斜率来自同一个中心商 $C$。
这是一条具体构造链：格判别类给出分级权，分级权给出中心核，
中心核再给出提升缺陷的线性组合。

<a id="statement-5-3"></a>

**例 5.3（各自不可提升而联合可提升的环面数据）。**

在 $\mathbb C^5$ 的基 $e_0,\ldots,e_4$ 上令
$De_j=\zeta^je_j$、$Se_j=e_{j+1\bmod5}$。
两者行列式为 $1$，且 $DS=\zeta SD$。
对 $\Pi=\mathbb Z^2=\langle u,v:[u,v]=1\rangle$，定义

$$
\rho_1(u)=[D],\quad\rho_1(v)=[S],\qquad
\rho_2(u)=[D^2],\quad\rho_2(v)=[S].
$$

两份射影数据都满足交换关系，但任何 $\operatorname{SU}(5)$ 生成元提升仅相差中心标量，
不能改变交换子 $\zeta I$ 或 $\zeta^2 I$，所以各自都不能提升。
在 $H$ 中却有

$$
\widetilde\rho(u)=[(D,D^2)],\qquad
\widetilde\rho(v)=[(S,S)],
$$

因为其交换子 $[(\zeta I,\zeta^2I)]=1$。
若第二因子改成平凡表示，联合交换子为 $z\ne1$，提升便不存在。
此结论只针对通过指定 $H$ 归约实现该份投影数据。

<a id="subsection-5-2"></a>

### 5.2 有限二维复形上的可计算形式

设 $B$ 是有限连通二维胞腔复形，选定各胞腔方向，
并把每个二胞腔的附着映射固定为有限有向边词。
给每条有向边指定 $g_e\in G_0$，满足
$g_{\bar e}=g_e^{-1}$，以及每个面的**有序**边界乘积为 $1$。
这是平坦路径输运数据，不是任意非平坦主丛的全部数据。

任取边提升 $h_e\in H$，$p(h_e)=g_e$，
$h_{\bar e}=h_e^{-1}$。面乘积落入中心，定义

$$
\prod_{e\in\partial f}^{\rm ordered}h_e=z^{\eta_f},
\qquad \eta_f\in\mathbb F_5.
$$

故 $\eta\in C^2(B;\mathbb F_5)$。换面起点只共轭该乘积，
而中心元素不变；反转面方向使 $\eta_f$ 取负。
这些行为恰与胞腔余链的方向约定一致。

<a id="statement-5-4"></a>

**定理 5.4（面缺陷、中心校准与提升分类）。**

<a id="thm-celllift"></a>

对边相位余链 $b\in C^1(B;\mathbb F_5)$，换
$h_e$ 为 $h'_e=z^{b_e}h_e$ 时，

$$
\eta'=\eta+\delta b.
$$

因此

<a id="eq-cellcriterion"></a>

$$
\boxed{\ \text{存在全部面闭合的 }H\text{ 边提升}
\quad\Longleftrightarrow\quad
[\eta]=0\in H^2(B;\mathbb F_5).\ }
\tag{6}
$$

存在时，固定全部 $G_0$ 边标签，并只商去每个顶点投影为单位元的
中心顶点规范变换，所得提升类是 $H^1(B;\mathbb F_5)$ 的挠集。
对连通一维图总可提升，提升类共有 $5^{b_1(B)}$ 个。

**证明。**

不能重排一般边算子，但新增的 $z^{b_e}$ 全是中心元素，
可以移到乘积前。每条边在面边界中带符号的出现次数，
恰给 $(\delta b)_f$，所以 $\eta'=\eta+\delta b$。
因 $B$ 二维，$C^3=0$，$\eta$ 自动为二余循环。
消除全部面缺陷恰等价于解线性方程 $\delta b=-\eta$，
也即式 [(6)](#eq-cellcriterion)。

两套平坦提升之差满足 $\delta b=0$。
中心顶点规范 $u\in C^0$ 改变边相位一个 $\delta u$，
故差的等价类为 $Z^1/B^1=H^1$，作用自由且传递。
图没有二胞腔，故不存在面约束；有限连通图的
$H^1(B;\mathbb F_5)\simeq\mathbb F_5^{b_1(B)}$，得到计数。证毕。
 □

<a id="statement-5-5"></a>

**说明 5.5（两种二阶上同调不能直接识别）。**

选基点后，边数据给出 $\rho:\pi_1(B)\to G_0$。
上述类是群提升障碍沿分类映射 $B\to B\pi_1(B)$ 的拉回，
而不是无条件把 $H^2(B;\mathbb F_5)$ 与 $H^2(\pi_1(B);\mathbb F_5)$ 认同。
例如 $B=S^2$ 的 $H^2$ 非零，但平坦表示平凡，
本模型产生的障碍类只能为零。二维关系允许障碍出现，
不保证每份二维数据都有非零障碍。

<a id="statement-5-6"></a>

**定理 5.6（相位读出与全局相容的组合）。**

<a id="thm-operationalobstruction"></a>

在上述边数据上，额外供应：
所选 $h_e$ 在 $\mathcal K$ 上的实际执行、均匀分级探针
$\psi=5^{-1/2}\sum_je_j$，以及定理 [4.3](#thm-phaseopt) 的 Fourier 测量。
则一次完整面边界作用后，可以概率 $1$ 读出当前 $\eta_f$。
读得所有面缺陷后，能否通过中心边相位校准使全部面闭合，
恰由有限线性系统 $\delta b=-\eta$ 决定。

**证明。**

有序边界作用等于 $Z^{\eta_f}$。
五种 $Z^a\psi$ 正是 Fourier 正交基，所以该次测量确定 $\eta_f$。
校准判据由定理 [5.4](#thm-celllift)。
若也允许实际执行所求的中心校准，就可把代数解落实到新边提升。证毕。
 □

单面 $\eta_f$ 依赖当前边提升，$[\eta]$ 才不依赖该选择。
测量完毕后的有限域线性求解，并不消除制备、执行、误差和取得记录的成本。
若全部效果块对角，定理 [4.1](#thm-obskernel) 说明这些中心面缺陷在该读出下不可见。

<a id="section-6"></a>

## 6. 控制闭包、精确有限字与成本下界

<a id="sec-control"></a>

<a id="subsection-6-1"></a>

### 6.1 一个关系方向的 Lie 生成

本节规定局部控制为 $\mathfrak h=\mathfrak{su}(5)\oplus\mathfrak{su}(5)$，
关系方向为 $X\in\mathfrak k\setminus\mathfrak h$，并允许 $e^{tX}$ 的所有实参数 $t$。
这里 $X$ 已属于紧 E8 代数，不是任意 $248\times248$ 反 Hermitian 矩阵。
若项目提供的是 $U(5)$ 菜单，可以取其可实现的 $\operatorname{SU}(5)$ 子菜单；
不能用一个未定义的全局行列式五次根，把 $U(5)$ 单值地投到 $\operatorname{SU}(5)$。

<a id="statement-6-1"></a>

**定理 6.1（任一非局部连续方向生成整个 E8）。**

<a id="thm-controlclosure"></a>

对每个 $X\in\mathfrak k\setminus\mathfrak h$，

$$
\boxed{\ \operatorname{Lie}_{\mathbb R}(\mathfrak h,X)=\mathfrak k.\ }
$$

**证明。**

令 $\mathfrak l=\operatorname{Lie}_{\mathbb R}(\mathfrak h,X)$。
其复化 $\mathfrak l_{\mathbb C}$ 是 $\mathfrak h_{\mathbb C}$-子模并包含 $\mathfrak g_0$。
命题 [3.1](#prop-grading) 的四个非零分级是两两不等价的不可约
$\mathfrak h_{\mathbb C}$-模。由半单模的完全可约性及该分解的无重数性，
$X$ 的任一非零非局部分量迫使 $\mathfrak l_{\mathbb C}$ 包含某个完整 $\mathfrak g_j$。

以下证明任一非零分级都经括号生成其余分级。
写 $u_i=e_i-\mathbf1/5$、$v_i=e_i-\mathbf1/5$ 为两因子的五个标准权。
以下两组均为“两个根的和仍是根”：

$$
(u_1,v_1+v_2)+(u_2,v_3+v_4)=(u_1+u_2,-v_5),
$$

$$
(u_1+u_2,-v_1)+(u_3+u_4,-v_2)=(-u_5,-v_1-v_2).
$$

标准根空间括号定理保证对应括号非零，
故 $[\mathfrak g_1,\mathfrak g_1]\ne0$ 于 $\mathfrak g_2$，
$[\mathfrak g_2,\mathfrak g_2]\ne0$ 于 $\mathfrak g_4$。
取负根又得到 $[\mathfrak g_4,\mathfrak g_4]\ne0$ 于 $\mathfrak g_3$，
$[\mathfrak g_3,\mathfrak g_3]\ne0$ 于 $\mathfrak g_1$。
括号像是 $\mathfrak h_{\mathbb C}$-子模，目标不可约，故这些非零像都是整个目标。
循环 $1\to2\to4\to3\to1$ 从任一非零分级到达所有分级。
因此 $\mathfrak l_{\mathbb C}=\mathfrak g$，从而
$\dim_{\mathbb R}\mathfrak l=248=\dim_{\mathbb R}\mathfrak k$，得到结论。证毕。
 □

这里的分级是复分级；紧实共轭交换 $\mathfrak g_1,\mathfrak g_4$ 以及 $\mathfrak g_2,\mathfrak g_3$。
定理没有把每个复 $50$ 维分级视为一个实 $50$ 维控制空间。
如果只给某个固定角度的门 $e^{t_0X}$，结论不自动成立；
例如该门可能就是单位元。

<a id="subsection-6-2"></a>

### 6.2 统一有限词长的存在定理

<a id="statement-6-2"></a>

**定义 6.2（有限连续菜单与词长）。**

固定有限集合 $\mathcal S=\{Y_1,\ldots,Y_m\}\subset\mathfrak k$。
合法字是 $\prod_{\ell=1}^r e^{t_\ell Y_{i_\ell}}$，
$t_\ell\in\mathbb R$。词长计实际调用数 $r$。

<a id="statement-6-3"></a>

**定理 6.3（固定菜单的统一有限生成）。**

<a id="thm-uniform"></a>

若 $\operatorname{Lie}_{\mathbb R}(\mathcal S)=\mathfrak k$，则存在有限整数 $N(\mathcal S)$，
使每个 $g\in G$ 都有长度不超过 $N(\mathcal S)$ 的精确合法字。

**证明。**

令 $R$ 为所有合法字组成的子群，定义

$$
L=\operatorname{span}_{\mathbb R}\{\operatorname{Ad}_rY:r\in R,\ Y\in\mathcal S\}.
$$

$L$ 对 $\operatorname{Ad}_R$ 不变。对其中生成向量 $Z=\operatorname{Ad}_rY$，
$e^{tZ}=r e^{tY}r^{-1}\in R$。对 $\operatorname{Ad}_{e^{tZ}}L\subset L$ 求导，
得到 $[Z,L]\subset L$，再线性扩张知 $L$ 为 Lie 子代数。
它包含 $\mathcal S$，所以 $L=\mathfrak k$。

从这些实际共轭方向中选基 $Z_1,\ldots,Z_{248}$。
映射

$$
F(t_1,\ldots,t_{248})=\prod_{\ell=1}^{248}e^{t_\ell Z_\ell}
$$

在原点的导数为同构。由逆函数定理，其像包含单位元邻域 $U$。
每个 $Z_\ell=\operatorname{Ad}_{r_\ell}Y_{i_\ell}$，
其指数可由固定共轭字实现，故整个 $U$ 内的目标都可用某个共同有限长度
$M$ 表示。缩小 $U$ 使它对称且包含单位元。

$\bigcup_{n\ge1}U^n$ 是 $G$ 的开子群；
$G$ 连通，故它等于 $G$。这些 $U^n$ 递增并覆盖紧群 $G$，
紧性给出某个 $n_0$ 满足 $G=U^{n_0}$。
于是 $N(\mathcal S)=n_0M$ 即可。证毕。
 □

这是紧群统一有限生成的经典结论在本菜单中的应用，
一般结果见 D'Alessandro [[7](#ref-dalessandro)]。
本证明给出**统一有限上界存在**，不能误写为“没有统一上界”。
它没有给出 $N(\mathcal S)$ 的已评价数值、可执行综合算法、
实参数的有限位精度或随系统尺寸变化的多项式界。

<a id="subsection-6-3"></a>

### 6.3 两种资源合同下的必要成本

<a id="statement-6-4"></a>

**引理 6.4（低维光滑像零测）。**

若 $M$ 是维数小于 $d$ 的第二可数光滑流形，
$F:M\to G$ 光滑，而 $G$ 是 $d$ 维 Lie 群，
则 $F(M)$ 的 Haar 测度为零。

**证明。**

以可数个相对紧坐标块覆盖 $M$ 和目标图。
在每个紧块上 $F$ 为 Lipschitz。若源维数为 $m<d$，
以边长 $\delta$ 的小立方体覆盖源，所需数为 $O(\delta^{-m})$；
每个像包含于半径 $O(\delta)$ 的目标球，总体积为
$O(\delta^{d-m})\to0$。Haar 测度在图中有光滑正密度，
故结论不变。可数并仍为零测。证毕。
 □

<a id="statement-6-5"></a>

**定理 6.5（有限单参数菜单的 248 下界）。**

<a id="thm-248"></a>

对固定有限单参数菜单，Haar 几乎处处的 $g\in G$，
任何精确合法字至少有 $248$ 次可调脉冲调用。
允许额外穿插可数个选项的固定离散门，不改变该下界。
若菜单 Lie 生成 E8，则几乎处处有
$248\le\ell(g)\le N(\mathcal S)$。

**证明。**

每个固定离散字型、含 $r$ 个可调调用的词，给出光滑映射
$\mathbb R^r\to G$。当 $r<248$ 时，其像由上引理为零测。
所有有限字型可数，故长度小于 $248$ 的全部可达目标仍为零测。
上界来自定理 [6.3](#thm-uniform)。证毕。
 □

<a id="statement-6-6"></a>

**定理 6.6（局部操作免费时的五次关系下界）。**

<a id="thm-fivecost"></a>

另换成本模型：任意 $h\in H$ 都免费，仅计算关系脉冲 $e^{tX}$。
若 $X\in\mathfrak k\setminus\mathfrak h$，Haar 几乎处处的 E8 目标至少需要五次关系脉冲；
同时存在依赖 $X$ 的统一有限调用上界。五次不在此被证明为充分或最优。

**证明。**

使用至多 $r$ 次关系脉冲的目标包含在下列光滑映射的像中：

$$
H^{r+1}\times\mathbb R^r\longrightarrow G,\qquad
(h_0,\ldots,h_r,t_1,\ldots,t_r)
\longmapsto h_0e^{t_1X}h_1\cdots e^{t_rX}h_r.
$$

其源维数为 $48(r+1)+r=49r+48$。
当 $r\le4$ 时至多为 $244<248$，像为零测；
取有限并得下界。取 $\mathfrak h$ 的有限基加 $X$，
由定理 [6.1](#thm-controlclosure) 和 [6.3](#thm-uniform)
得到有限全词长上界，也就得到关系调用的统一上界。证毕。
 □

定理 [6.1](#thm-controlclosure) 计算新增**方向数**，
定理 [6.6](#thm-fivecost) 计算实际**调用数**，
定理 [6.5](#thm-248) 又在另一个计费模型中计算全部可调调用。
这些数量没有可互换的含义。若进一步要求数字参数、误差容限与有界时间，
必须另立计算模型。

<a id="section-7"></a>

## 7. 黄金读出与有限精度恢复

<a id="sec-golden"></a>

<a id="subsection-7-1"></a>

### 7.1 额外选定的几何读出

本节先对任意 $d\ge1$ 建立一般整数系数理论，最后取 $d=4$。
令

$$
\varphi=\frac{1+\sqrt5}{2},\qquad
\sigma=1-\varphi=-\varphi^{-1},\qquad
\Gamma_d=\mathbb Z^d\oplus\mathbb Z^d,
$$

$$
P_+(a,b)=a+\varphi b,\qquad P_-(a,b)=a+\sigma b,\qquad
S(a,b)=(P_+(a,b),P_-(a,b)).
$$

所有 $\ell^\infty$ 范数均是这些**系数坐标**中的最大范数。
应用于 E8 时，额外选定简单根基、$H_4$ 投影及共轭坐标的标号识别。
在 Dechant 等 [[8](#ref-dechant)] 式 (3) 的约定下，可以取

$$
a=(n_1,n_2,n_3,n_8),\qquad b=(n_7,n_6,n_5,n_4).
$$

于是一个读口具有 $a+\varphi b$ 形式，其代数共轭为 $a+\sigma b$。
这些结构不由前面的 $A_4^2$ 胶合自动指定。
若改用实际 E8 或 $H_4$ 欧氏范数，应加入由固定基决定的范数等价常数。

<a id="statement-7-1"></a>

**引理 7.1（代数范数）。**

<a id="lem-algnorm"></a>

对 $(p,q)\in\mathbb Z^2\setminus\{(0,0)\}$，

$$
(p+\varphi q)(p+\sigma q)=p^2+pq-q^2\in\mathbb Z\setminus\{0\}.
$$

**证明。**

由 $\varphi+\sigma=1$、$\varphi\sigma=-1$ 得乘积式。
若乘积为零，某个因子为零；$\varphi,\sigma$ 的无理性迫使 $p=q=0$，
与假设矛盾。证毕。
 □

<a id="statement-7-2"></a>

**定理 7.2（精确单射与处处失稳）。**

<a id="thm-unstable"></a>

$P_+$ 在 $\Gamma_d$ 上单射，但其逆
$P_+(\Gamma_d)\to\Gamma_d$ 在继承的欧氏拓扑下处处不连续。
其连续实扩张 $\mathbb R^{2d}\to\mathbb R^d$ 的核维数则为 $d$。

**证明。**

若 $a+\varphi b=0$，每个整数坐标对由无理性知 $a_i=b_i=0$。
这给整数域单射。令 $F_0=0,F_1=1$ 为 Fibonacci 数，

$$
v_n=(F_{n+1},-F_n)e_1.
$$

由递推或 Binet 公式，

$$
P_+v_n=\sigma^ne_1\to0,\qquad
P_-v_n=\varphi^ne_1,\qquad
\left\lVert v_n\right\rVert_\infty\to\infty.
$$

故逆在 $0$ 不连续；平移序列 $v+v_n$ 给出任意像点处的不连续性。
连续实扩张的核为 $\{(-\varphi b,b):b\in\mathbb R^d\}$，维数为 $d$。证毕。
 □

<a id="subsection-7-2"></a>

### 7.2 有限高度下的匹配精度界

对整数 $H\ge1$，定义

$$
D_H=\{(a,b)\in\Gamma_d:\left\lVert a\right\rVert_\infty,\left\lVert b\right\rVert_\infty\le H\},
\quad
\delta_H=\min_{\substack{u,v\in D_H\\u\ne v}}
\left\lVert P_+u-P_+v\right\rVert_\infty.
$$

<a id="statement-7-3"></a>

**定理 7.3（高度与最小间隔）。**

<a id="thm-height"></a>

$$
\boxed{\ \frac1{2\varphi H}\le\delta_H<\frac{\varphi}{2H}.\ }
$$

因此 $\delta_H=\Theta(H^{-1})$，常数与 $d$ 无关。

**证明。**

不同 $u,v\in D_H$ 的差在某个坐标有非零整数对 $(p,q)$，
且 $|p|,|q|\le2H$。由引理 [7.1](#lem-algnorm)，

$$
|p+\varphi q|\ge\frac1{|p+\sigma q|}
\ge\frac1{2H(1+|\sigma|)}=\frac1{2\varphi H}.
$$

向量最大范数至少为这个坐标绝对值，得到下界。

取最大的 $n\ge1$ 使 $F_{n+1}\le2H$，于是 $F_{n+2}>2H$。
因 $D_H-D_H=D_{2H}$，向量 $v_n$ 是两个允许来源之差。
所以 $\delta_H\le|\sigma|^n=\varphi^{-n}$。
由递推归纳 $F_k\le\varphi^{k-1}$，故
$2H<F_{n+2}\le\varphi^{n+1}$，即
$\varphi^{-n}<\varphi/(2H)$，得到上界。证毕。
 □

<a id="statement-7-4"></a>

**定理 7.4（闭噪声与开噪声的尖锐端点）。**

<a id="thm-noise"></a>

在 $D_H$ 上，若观测为 $P_+v+\eta$、$\left\lVert \eta\right\rVert_\infty\le\varepsilon$，
则存在对所有允许来源和噪声均正确的解码器，当且仅当

$$
2\varepsilon<\delta_H.
$$

若噪声合同改为 $\left\lVert \eta\right\rVert_\infty<\varepsilon$，则充要条件为
$2\varepsilon\le\delta_H$。

**证明。**

来源可完全恢复恰当且仅当不同来源的允许记录集互不相交。
这些记录集为相应的闭球或开球。
两个闭最大范数球在中心距离等于 $2\varepsilon$ 时共享中点，
所以必须严格大于；开球允许等号。
$D_H$ 有限，最小间隔实际达到，故必要性没有下确界不取到的问题。证毕。
 □

特别地，

$$
\varepsilon<\frac1{4\varphi H}\ \Longrightarrow\ \text{保证可恢复},
\qquad
\varepsilon\ge\frac{\varphi}{4H}\ \Longrightarrow\ \text{不可能统一恢复}.
$$

这说明绝对精度需为 $H^{-1}$ 阶；
以单位尺度的小数位计，需要 $\log_2H+O(1)$ 位。
若计算包括整数部分在内的总位数，读出范围也随 $H$ 增长，仍需另行计入。
该信息论阈值不提供数据获取或解码搜索的时间上界。

<a id="subsection-7-3"></a>

### 7.3 共轭双读出的全域鲁棒性

<a id="statement-7-5"></a>

**定理 7.5（联合读出的稳定逆与精确阈值）。**

<a id="thm-joint"></a>

对连续实扩张，若 $x=P_+(a,b)$、$y=P_-(a,b)$，则

$$
b=\frac{x-y}{\sqrt5},\qquad
a=\frac{\varphi y-\sigma x}{\sqrt5}.
$$

并有

$$
\left\lVert (a,b)\right\rVert_\infty
\le\left\lVert S(a,b)\right\rVert_\infty
\le\varphi^2\left\lVert (a,b)\right\rVert_\infty.
$$

联合格 $S(\Gamma_d)$ 的最小最大范数间隔恰为 $1$。
若两个读口各有闭噪声不超过 $\varepsilon$，
整个无限整数来源域可统一恢复，当且仅当 $\varepsilon<1/2$。

**证明。**

相减得 $b$ 的逆公式，回代得 $a$ 的公式。
因 $\varphi+|\sigma|=\sqrt5$，

$$
\left\lVert a\right\rVert_\infty\le\left\lVert (x,y)\right\rVert_\infty,\qquad
\left\lVert b\right\rVert_\infty\le\frac2{\sqrt5}\left\lVert (x,y)\right\rVert_\infty
\le\left\lVert (x,y)\right\rVert_\infty.
$$

正向上界分别来自 $1+\varphi=\varphi^2$ 与 $1+|\sigma|=\varphi$。
非零整数差的系数范数至少为 $1$，故联合像间隔至少为 $1$；
差 $(e_1,0)$ 达到 $1$。

对带噪读数代入逆公式，误差满足
$\left\lVert \Delta a\right\rVert_\infty\le\varepsilon$、
$\left\lVert \Delta b\right\rVert_\infty\le2\varepsilon/\sqrt5$。
当 $\varepsilon<1/2$，逐坐标取最近整数精确恢复来源。
若 $\varepsilon\ge1/2$，来源 $0$ 和 $(e_1,0)$ 的联合输出中点
$(e_1/2,e_1/2)$ 同时允许，统一解码不可能。证毕。
 □

<a id="section-8"></a>

## 8. 有界内部窗口、非周期性与尺度协变

<a id="sec-window"></a>

<a id="subsection-8-1"></a>

### 8.1 来源限制恢复稳定性

对任意 $W\subset\mathbb R^d$，定义

$$
\Gamma(W)=\{v\in\Gamma_d:P_-v\in W\},\qquad
\Lambda(W)=P_+\Gamma(W).
$$

这个窗口是来源合同：它限制允许的内部值，并不声称观察者已取得 $P_-$ 读数。
令 $D=\operatorname{diam}_\infty W$。

<a id="statement-8-1"></a>

**定理 8.1（窗口分离与 Lipschitz 恢复）。**

<a id="thm-window"></a>

若 $0<D<\infty$，则任意不同 $v,w\in\Gamma(W)$ 满足

$$
\left\lVert P_+v-P_+w\right\rVert_\infty\ge\frac1D.
$$

并且

$$
\left\lVert v-w\right\rVert_\infty
\le C_D\left\lVert P_+v-P_+w\right\rVert_\infty,\qquad
C_D=\frac1{\sqrt5}\max\{|\sigma|+\varphi D^2,\ 1+D^2\}.
$$

因此闭噪声 $\left\lVert \eta\right\rVert_\infty\le\varepsilon<1/(2D)$
足以在整个窗口来源域上保证唯一恢复。若 $D=0$，来源域至多含一个元素。

**证明。**

对非零差选一个非零整数坐标对 $(p,q)$。
内部差满足 $|p+\sigma q|\le D$，而引理 [7.1](#lem-algnorm) 给出
$|(p+\varphi q)(p+\sigma q)|\ge1$，因此可见差至少为 $1/D$。

记可见差为 $x$、内部差为 $y$。由联合逆公式，

$$
\left\lVert \Delta a\right\rVert_\infty
\le\frac{|\sigma|\left\lVert x\right\rVert_\infty+\varphi D}{\sqrt5},\qquad
\left\lVert \Delta b\right\rVert_\infty
\le\frac{\left\lVert x\right\rVert_\infty+D}{\sqrt5}.
$$

非零差时 $\left\lVert x\right\rVert_\infty\ge1/D$，故
$D\le D^2\left\lVert x\right\rVert_\infty$。代入即得 Lipschitz 常数。
不同来源的噪声球在 $2\varepsilon<1/D$ 时不交，给出恢复保证。
若 $D=0$，所有来源有同一个 $P_-$ 值；
$P_-$ 的整数域单射性由 $\sigma$ 的无理性证明，故至多一个来源。证毕。
 □

箱窗 $W_R=[-R,R]^d$ 的 $D=2R$，所以间隔至少为 $1/(2R)$，
闭噪声小于 $1/(4R)$ 即充分。这个保证不依赖整数高度。
Fibonacci 失稳方向被排除的原因很明确：其内部读出为 $\varphi^ne_1$，无界。

<a id="subsection-8-2"></a>

### 8.2 Delone 集与有限局部复杂性

<a id="statement-8-2"></a>

**定义 8.2。**

点集称为均匀离散，若不同点之间存在统一正的距离下界；
称为相对稠密，若某个有限半径的每个球都包含一个点。
同时满足二者称为 Delone 集。
按平移计算、以点为中心的固定半径图样只有有限多种，
称为有限局部复杂性。

<a id="statement-8-3"></a>

**引理 8.3（两个单投影稠密）。**

$P_+(\Gamma_d)$ 与 $P_-(\Gamma_d)$ 都在 $\mathbb R^d$ 中稠密。

**证明。**

对任意无理数 $\theta$，将 $0,\theta,\ldots,N\theta$ 的小数部分
放入 $N$ 个等分区间，鸽巢原理给出任意小的非零
$m+n\theta$。改变符号使其为正，再用整数倍逼近任意实数，
可知 $\mathbb Z+\theta\mathbb Z$ 稠密。取 $\theta=\varphi,\sigma$，逐坐标作积即可。证毕。
 □

<a id="statement-8-4"></a>

**定理 8.4（窗口产生非周期 Delone 集）。**

<a id="thm-delone"></a>

若 $W$ 有界且内部非空，则 $\Lambda(W)$ 均匀离散、相对稠密、
具有有限局部复杂性，且没有非零平移周期。
这些结论不要求窗口闭性或边界测度为零。
其中非周期性只需 $W$ 有界且 $\Lambda(W)\ne\varnothing$。

**证明。**

**均匀离散。**
由定理 [8.1](#thm-window)，内部非空也保证 $D>0$。

**相对稠密。**
联合像 $L=S(\Gamma_d)$ 是 $\mathbb R^{2d}$ 中的满秩格。
取其紧基本平行多面体 $F$，并取非空开集 $U\subset W$。
紧集 $K=-\pi_-(F)$ 被开集族
$U-P_-\gamma$、$\gamma\in\Gamma_d$ 覆盖；
这是因为内部投影稠密。选有限子覆盖对应 $\gamma_1,\ldots,\gamma_m$。
对任意 $t\in\mathbb R^d$，写 $(t,0)=\ell+f$，$\ell\in L,f\in F$。
则 $\ell_-\in K$，故可选 $i$ 使 $\ell_-+P_-\gamma_i\in U$。
所以 $\lambda=\ell_++P_+\gamma_i\in\Lambda(W)$，并有

$$
\left\lVert \lambda-t\right\rVert_\infty
\le\sup_{f\in F}\left\lVert \pi_+f\right\rVert_\infty+
\max_i\left\lVert P_+\gamma_i\right\rVert_\infty.
$$

这是与 $t$ 无关的有限常数。此处紧性来自基本域，而不是未经假设的窗口紧性。

**非周期。**
设 $\Lambda(W)+t=\Lambda(W)$，取 $P_+v\in\Lambda(W)$。
存在唯一 $u\in\Gamma_d$ 使 $t=P_+u$。
周期性和 $P_+$ 单射性迫使 $v+nu\in\Gamma(W)$，对所有 $n\in\mathbb Z$ 成立。
于是 $P_-v+nP_-u$ 全在有界 $W$ 中，故 $P_-u=0$。
$P_-$ 在整数域单射，给出 $u=0$、$t=0$。
非空性必要：空点集的每个向量都是周期。

**有限局部复杂性。**
若一个差向量的可见部分位于有界集 $B_0$，
内部部分必在有界集 $W-W$ 中。联合格与有界集
$B_0\times(W-W)$ 的交只有有限点，故有界可见范围内只有有限种差向量。
每个以点为中心的固定半径图样都是这一有限集合的子集，
从而图样种类有限。证毕。
 □

<a id="statement-8-5"></a>

**推论 8.5（有限等差链的长度界）。**

若 $x,x+t,\ldots,x+Nt\in\Lambda(W)$，$t\ne0$，且 $W$ 直径为 $D<\infty$，
则

$$
N\le D\left\lVert t\right\rVert_\infty.
$$

**证明。**

写 $t=P_+u$。两个端点给出
$N\left\lVert P_-u\right\rVert_\infty\le D$，而某个非零坐标的代数范数保证
$\left\lVert P_+u\right\rVert_\infty\left\lVert P_-u\right\rVert_\infty\ge1$。
合并即得。证毕。
 □

<a id="subsection-8-3"></a>

### 8.3 黄金细化保持的准确结构

定义整数变换

$$
T(a,b)=(b,a+b).
$$

它满足 $T^2=T+I$、$T^{-1}=T-I$，故为 $\Gamma_d$ 的整数模自同构。

<a id="statement-8-6"></a>

**定理 8.6（改变窗口后的精确尺度协变）。**

<a id="thm-scaling"></a>

$$
P_+T=\varphi P_+,\qquad P_-T=\sigma P_-.
$$

对任意窗口及任意整数 $n$，

$$
\boxed{\ \Lambda(\sigma^nW)=\varphi^n\Lambda(W).\ }
$$

特别地 $\Lambda(\sigma^2W)=\varphi^2\Lambda(W)$。
若 $W$ 关于原点星形，则 $\varphi^2\Lambda(W)\subseteq\Lambda(W)$；
若 $W$ 还有界且内部非空，该包含不能成为固定窗口的等号。

**证明。**

由 $\varphi^2=\varphi+1$、$\sigma^2=\sigma+1$ 直接计算得两个读出恒等式。
$T^n$ 在整数格上双射，所以
$P_-v\in W$ 当且仅当 $P_-T^nv\in\sigma^nW$，
同时 $P_+T^nv=\varphi^nP_+v$。这给出集合恒等式。
原点星形使 $\sigma^2W\subseteq W$，故得到包含。
若固定窗口下有等号，相对稠密保证存在非零点 $x\in\Lambda(W)$；
反复应用反向尺度得 $\varphi^{-2n}x\in\Lambda(W)$。
这些不同点趋向零，违反均匀离散性。证毕。
 □

<a id="statement-8-7"></a>

**命题 8.7（不定范数的守恒）。**

<a id="prop-indefinite"></a>

令

$$
\mathcal N(a,b)=\sum_{i=1}^d(a_i^2+a_ib_i-b_i^2)
=P_+(a,b)\cdot P_-(a,b).
$$

则其签名为 $(d,d)$，且
$\mathcal N(Tv)=-\mathcal N(v)$、
$\mathcal N(T^2v)=\mathcal N(v)$。
$T^2$ 不可能保持任何正定实内积。

**证明。**

因 $\varphi\sigma=-1$，第一个变换式来自两个读出的尺度乘积，
再作用一次得第二式。
每对坐标的二次型矩阵为
$\left(\begin{smallmatrix}1&1/2\\1/2&-1\end{smallmatrix}\right)$，
行列式为 $-5/4$，有一正一负特征值，所以总签名为 $(d,d)$。
$T^2$ 有实特征值 $\varphi^2>1$；若保持正定内积，
其非零特征向量的长度将既不变又乘以 $\varphi^2$，矛盾。证毕。
 □

当 $d=4$ 时，该不定结构为 $(4,4)$ 型，区别于 E8 的正定度量。
这给出明确的代数守恒式，没有把黄金细化当作酉门。
固定窗口的替换铺砌还需要分窗、平移及拼接规则；
上述点集结论本身不指定某一具体铺砌。

<a id="section-9"></a>

## 9. 综合定理：全局相容可以选择胶合标记

<a id="sec-synthesis"></a>

<a id="subsection-9-1"></a>

### 9.1 从局部积分选择到全局标记选择

此前选了正号胶合。现在恢复两个带标记候选，
令 $s\in\{+1,-1\}$，并定义

$$
C_s=\{(\zeta^aI,\zeta^{2sa}I):a\in\mathbb F_5\},\qquad
H_s=(\operatorname{SU}(5)\times\operatorname{SU}(5))/C_s.
$$

它们分别由定理 [2.3](#thm-selection) 的 $\Gamma_+,\Gamma_-$ 给出；
两个 $\operatorname{SU}(5)$ 因子的标记始终固定。

<a id="statement-9-1"></a>

**定理 9.1（积分扩张与全局障碍的联合选择）。**

<a id="thm-jointselection"></a>

固定两份局部射影表示 $\rho_1,\rho_2$，其 $\operatorname{SU}(5)$ 提升障碍为
$o_1,o_2\in H^2(\Pi;\mathbb F_5)$。
在定理 [2.3](#thm-selection) 允许的两个带标记 E8 扩张中，
存在与该数据相容的平坦 $H_s$ 提升，当且仅当

$$
\boxed{\ o_2=2o_1\quad\text{或}\quad o_2=-2o_1.\ }
$$

更精确地：

1. 若 $o_1=o_2=0$，两种标记都允许；

2. 若至少一项非零且满足上述条件，恰有一种标记允许；

3. 其他情形，两种标记都不能实现该份固定投影数据。

**证明。**

在 $\Gamma_s$ 中，分级权的判别类为 $(j,2sj)$，
故中心 $(\zeta^a,\zeta^b)$ 的角色是 $\zeta^{j(a+2sb)}$。
其核为 $C_s$，联合提升障碍因而是
$o_s=o_1+2s\,o_2$。
它为零恰当且仅当 $o_2=2s\,o_1$。
若正负两种同时成立，则 $4o_1=0$。
$4$ 在 $\mathbb F_5$ 中可逆，故 $o_1=0$，继而 $o_2=0$。
其余各项直接由此得出。证毕。
 □

这一结果给出理论中真正的反馈关系：
局部积分性把选择压缩为两个标记，非零全局障碍可以进一步选定其中一个。
虽然两个根格等距，反转第二因子会改变其标记及相应射影数据；
在固定数据的任务中，不能免费用这一步抹去差别。
符号唯一不等于提升唯一：对可行符号，具体提升仍构成
$H^1(\Pi;\mathbb F_5)$ 挠集。沿选定嵌入得到的是带指定 $H_s$ 归约的
E8 平坦表示，实际操作实现还须满足前文的资源条件。

<a id="subsection-9-2"></a>

### 9.2 一个同时满足各层条件的模型

<a id="statement-9-2"></a>

**命题 9.2（理论实例非空）。**

存在同时具有严格积分扩张、非平凡局部提升相消、E8 Lie 生成、
相位探针读出和稳定黄金窗口来源的实例。

**证明。**

取 $\Gamma_+$ 及其标准紧 E8 构造。
全局数据用第 [5](#sec-obstruction) 节的环面例子，
其局部障碍分别为 $1,2$，联合提升已显式给出。
在伴随空间各分级取一个单位向量，明确把均匀探针制备和 Fourier 测量
列入允许操作，则定理 [4.3](#thm-phaseopt) 适用。
取 $\mathfrak h$ 的有限基和任意 $X\in\mathfrak k\setminus\mathfrak h$ 为连续菜单，
定理 [6.1](#thm-controlclosure)、[6.3](#thm-uniform) 给出 E8 的精确有限生成。
最后选择第 [7](#sec-golden) 节的 $d=4$ 坐标读出，
并取任意 $R>0$ 的箱窗，定理 [8.1](#thm-window)、[8.4](#thm-delone)
给出稳定恢复及非周期 Delone 集。
各结构按同一已识别的 E8 格和伴随对象连接，没有要求互相矛盾的维数或权限。证毕。
 □

该命题证明这套分层条件有数学模型，不声称某个现有物理装置已经实现它。
跨层映射仍需在具体应用中给出：例如电荷如何编码为可制备态，
黄金读数由什么仪器取得，以及源域窗口如何保证。

<a id="subsection-9-3"></a>

### 9.3 依赖、反例与尚未被证明的部分

| 目标结论 | 关键条件 | 去掉条件后的具体情况 |
| --- | --- | --- |
| E8 选择 | 固定正交等尺度 $A_4^2$、严格整数配对扩张 | 无严格性时为 $A_4^2$；普通张量积控制闭包可为 $\mathfrak{su}(25)$ |
| 全局平坦提升 | $o_1+2s\,o_2=0$ | 环面 $(D,S)$ 配平凡第二因子给不可消去缺陷 |
| 相位全输入可见 | 实际效果含跨分级块 | 块对角效果对五种相位完全相同 |
| 单份完美判别 | 均匀纯探针及 Fourier 测量权限 | 两分级探针最优成功率至多 $2/5$；均匀混合态仍可完全盲 |
| 完整 E8 可达 | 完整局部代数及非局部连续方向 | 单个固定角度可能是单位门；E8 控制不等于 $\operatorname{SU}(248)$ 控制 |
| 统一单口精度 | 有界内部窗口或有界整数高度 | 全格 Fibonacci 序列造成处处不连续的逆 |
| 固定窗口替换 | 另有分窗、平移和拼接规则 | 黄金尺度协变只保证窗口也相应改变 |

本文最强的结论是条件式的相容与恢复定理。
它没有从五模式计数单独推出 E8，没有把 E8 识别为整个物理宇宙，
也没有把理想实参数的精确字存在性提升为数字算法复杂度结论。
这些限制来自所证明命题的量词与对象，而非额外的修辞保留。

<a id="section-10"></a>

## 10. 进一步形式化的精确目标

<a id="sec-formalization"></a>

本文没有交付或执行 Lean 代码。若按项目的形式化路线继续，
可以把已经证明的数学命题拆为以下独立模块，而不先承诺整套 E8 库的可用性。

1. **有限判别计算。** 在 $\mathbb F_5^2$ 中分类全迷向子空间，证明只有零空间与两条斜率 $\pm2$ 的直线。 这是选择定理最小而有限的核心。

2. **整数配对扩张。** 形式化 $L_0\subset L\subset L_0^*$、指数公式和“奇指数积分扩张保持偶性”； 根数与 ADE 识别分别列出依赖。

3. **中心核和角色。** 对模 5 的五分级证明角色 $a+2b$、观察核、 中心平均等于分级去相干。这些可先于完整 E8 构造验证。

4. **量子判别。** 在有限维复内积空间中证明正半定矩阵元素界， 构造 Fourier POVM，并证明精确最优概率及等号条件。

5. **有限复形相容。** 先用有限矩阵实现 $\delta:C^1\to C^2$， 证明边相位修正和 $\delta b=-\eta$ 判据，再接抽象上同调。

6. **黄金稳定性。** 在二次数域中证明整数范数非零、Fibonacci 恒等式、 $\delta_H$ 双边界、闭噪声端点和窗口分离。

7. **Lie 控制与全局综合。** 把完全可约性、根空间非零括号、逆函数定理、紧性分别作为已核验依赖接入， 避免把一个“控制生成”标签当成所有代数与分析义务已经完成。

优先关系可以简写为：有限模 5 核心支持格选择及中心相位；
中心相位支持全局障碍和操作读出；Lie 结构支持控制；
二次数域算术独立支持精度定理，再经选定 E8 基与几何读口连接。
每个模块都有明确来源域、权限、结论与反例，可分别进入项目的证明依赖图。

<a id="references"></a>

## 参考文献与项目定位

<a id="ref-repoOmega"></a>

**[1]**
The Omega Institute.
*AURIC $\Omega$ 静态相融纤维理论*.
固定提交 `66259f03d60716f143cd59c7644dadcb67cc1b73`，
文件 `AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md`。
本文重点使用 §1 的原菜单与五模式、假设 45.1、55.2，
定理 64.1 及 §80.2 的成本区分。
[固定快照原文](https://github.com/the-omega-institute/trureturing/blob/66259f03d60716f143cd59c7644dadcb67cc1b73/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)。

> **编者定位注（仅校正文献定位）。** 本条保留原稿“§80.2”的写法；在所引固定快照中，对应条目是第 61 节“FIB 实际菜单的精确脉冲维数界”下的**定理 80.2（精确可达与几乎处处的长字）**，见[第 61 节](https://github.com/the-omega-institute/trureturing/blob/66259f03d60716f143cd59c7644dadcb67cc1b73/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md#61-fib-实际菜单的精确脉冲维数界)。该固定文件第 4624 行为节标题，第 4635 行为定理标题。

<a id="ref-repoFib"></a>

**[2]**
The Omega Institute.
*FIB-ATOM 金字塔：基础公式、原子关系与同源接续总表*.
同一固定提交，文件
`AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md`。
[固定快照原文](https://github.com/the-omega-institute/trureturing/blob/66259f03d60716f143cd59c7644dadcb67cc1b73/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)。
项目文献中的既有内部引用保持各自原有归属。

<a id="ref-yokota"></a>

**[3]**
Ichiro Yokota.
*Exceptional Lie groups*. 2009.
[arXiv:0902.0431](https://arxiv.org/abs/0902.0431)。
尤其 §5.12、定理 5.12.1 与 5.12.5，给出 E8 的五分级及
$(\operatorname{SU}(5)\times\operatorname{SU}(5))/\mathbb Z_5$ 子群的具体构造。

<a id="ref-sage"></a>

**[4]**
SageMath 官方文档.
*Integral lattices*.
[参考页面](https://doc.sagemath.org/html/en/reference/modules/sage/modules/free_quadratic_module_integer_symmetric.html)。
包含从 $A_4^2$ 用 $(1,2)$ 胶合得到 E8 的例子；
本文定理 [2.3](#thm-selection) 另给直接证明和全部带标记扩张的分类。

<a id="ref-eldar"></a>

**[5]**
Yonina C. Eldar and G. David Forney Jr.
*On Quantum Detection and the Square-Root Measurement*.
IEEE Transactions on Information Theory 47 (2001), 858–872.
[arXiv:quant-ph/0005132](https://arxiv.org/abs/quant-ph/0005132)。
本文的五重相位公式是几何均匀纯态最优判别的专门化。

<a id="ref-neeb"></a>

**[6]**
Karl-Hermann Neeb, Friedrich Wagemann and Christoph Wockel.
*Making Lifting Obstructions Explicit*.
Proceedings of the London Mathematical Society (3) 106 (2013), 589–620.
[arXiv:1108.5853](https://arxiv.org/abs/1108.5853)。
用于说明中心扩张提升障碍的经典背景；
本文自行证明的是固定平坦表示与有限二维边数据版本。

<a id="ref-dalessandro"></a>

**[7]**
Domenico D'Alessandro.
*Uniform Finite Generation of Compact Lie Groups and universal quantum gates*.
2001.
[arXiv:quant-ph/0111133](https://arxiv.org/abs/quant-ph/0111133)。
本文给出该经典统一有限生成结论适用于当前菜单的完整存在性证明。

<a id="ref-dechant"></a>

**[8]**
Pierre-Philippe Dechant, Celine Boehm and Reidun Twarock.
*Affine extensions of non-crystallographic Coxeter groups induced by projection*.
Journal of Mathematical Physics 54 (2013), 093508.
[arXiv:1110.5228](https://arxiv.org/abs/1110.5228)。
§II.2、式 (3) 提供 E8 到 $H_4$ 的投影约定。
本文的稳定性常数针对该约定下的系数坐标，
而非未经转换的欧氏长度。
