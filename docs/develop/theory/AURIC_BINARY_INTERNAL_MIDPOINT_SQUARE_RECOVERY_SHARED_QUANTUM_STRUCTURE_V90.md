# 二元内生中点、平方可恢复性与共享量子结构

从一个二态平方条件到共同恢复、全部后续读出与酉性

**AURIC v90：一个完整候选的定义、定理与反向审计**

项目连续研究稿

2026 年 11 月 3 日（新加坡）

## 摘要

v89 用两个可观测关系元的操作平方缺额，认证全部生成关系词的乘法闭合。
v90 转向状态端：给定两个内部准备，能否仅由转换后的内容，通过同一量子操作恢复两者，
从而回答两者的全部后续完整读出？

本轮只提出一个新候选 $C_{90}$。取二态自身的中点
$\sigma=(\rho_0+\rho_1)/2$ 为内部校准，在共同支撑上定义对称加权平方区别。
要求这个量在指定通道下不减少。证明这一标量等式当且仅当存在同一 CPTP 恢复，
且可取由通道及中点确定的 Petz 映射。
证明包含有限矩阵端点收缩、完整三线插值、Petz 的完全正保迹性，
以及平方损失对恢复残差和全部后续读出总变差的控制。

在明示的谱比二次比较类中，正反次序相容与完整独立组合相容唯一固定对称权。
该唯一性有明确模型范围，不冒充无前提的量子公理重构。
二元区别与一次恢复残差组成有限 Gram 块，归一后可提升到三维球；
精确恢复、零区别、归一尺度和读出不确定性分别处理。
更换二态内部的非退化混合锚，不改变零损失成员资格。

通过 v88–v89 的保态条件期望和固定点代数，进一步得到所有可恢复态的共同右因子分块结构；
证明恢复映射反序组合，平方损失沿门序列精确相加。
两个不对易 qubit 态的共同可恢复性迫使整个 qubit 通道可逆，同维时为酉；
更高维的明确反例阻止这一结论无条件外推。
最后接回既有 Hilbert、Born、仪器、张量积、不确定性及动力学重构链。
核心恢复数学已有一手文献，本稿提供项目接续与自足解析证明，不作优先权主张。
未运行数学程序、CAS、数值实验或候选枚举。

## 目录

- [1. 本轮推进：由关系词闭合到二态统计充分](#section-1)
- [2. 由两个态自身生成锚与唯一候选](#section-2)
- [3. 为何采用这个平方：正反比较与独立组合的有限刻画](#section-3)
- [4. 加权平方为什么收缩：两个端点与完整插值证明](#section-4)
- [5. 平方饱和为何产生同一个完全正恢复](#section-5)
- [6. 由平方误差控制所有完整后续读出](#section-6)
- [7. 回到真正二元中点：一端恢复等价于两端共同恢复](#section-7)
- [8. 二元区别的尺度、纯态圆弧与有限三维证书](#section-8)
- [9. 内部换锚不改变零损失资格，稳定读出仍可不确定](#section-9)
- [10. 删去条件会发生什么：纯度、区分度与另一种平方](#section-10)
- [11. 由一对态锁住整体：qubit 的精确刚性](#section-11)
- [12. 二维之外与旁参考：恢复的对象必须说清楚](#section-12)
- [13. 成功分支并不等于完整回返](#section-13)
- [14. 从二态恢复到稳定关系代数：接回 v88 与 v89](#section-14)
- [15. 共有量子子态的精确形式](#section-15)
- [16. 多段压缩的逆序恢复与平方预算](#section-16)
- [17. 多个态共用一张恢复关系表](#section-17)
- [18. 把候选写成定义间约束：有限关系理论的完整接口](#section-18)
- [19. 如何接回现有量子力学公理：依赖与有限证明](#section-19)
- [20. 统一关系场的有限推进与本轮总图景](#section-20)
- [来源、版本与核读范围](#references)

<a id="section-1"></a>

## 1. 本轮推进：由关系词闭合到二态统计充分

<a id="sec-c90-scope"></a>

本轮承接 v89，版本递增为 v90。对当前 GitHub HEAD 作了一次有界公开读取，未成功；
仓库核读因此仍限定于固定提交

`c63ab162315fddd0801cbe9f47dbf3eda6e13360`

下已取得的16份理论 Markdown，以及本对话已经交付的 v88、v89。
这里不认证尚未读取的仓库更新。

项目已经分别处理过：共同复关系核和平方读出，完整记录产生的完全正操作，
共享相干子空间的最小补足，全部逻辑输入的纠错条件，
以及可见代数、相对锚和双向比较相容 [1](#ref-v67)、[2](#ref-v79)、[3](#ref-v80)、[4](#ref-n2)、[5](#ref-omega)、[8](#ref-v88)、[9](#ref-v89)。
这些前件继续使用。新问题是：**对指定的两个态，一次内部转换何时保留了共同恢复它们所需的全部信息？**

这个问题与 v89 有三个具体区别。
v89 检查操作对关系元的乘法是否相容；本轮检查转换后的状态是否统计充分。
v89 的近似定理控制有限长度关系词；本轮从态的恢复误差控制任意相同的完整后续实验。
此外，本轮用二态本身的中点作参照，明确把参照的来源放进二元定义。

核心等价属于已有量子充分性和恢复理论。
Gao–Li–Marvian–Rouzé 给出了本轮所需对称 $\chi^2$ 的恢复界；
Cao–Lu 给出相关权算子张量相容的唯一性 [10](#ref-gaorecovery)、[11](#ref-caolu)。
本稿将所需有限证明展开，并将它们接到项目的内容、地址、补结构与执行范围。

**白话图景。**两份内容经过一次转换后，表面读数还相近，并不能说明区别仍然完整。
本轮要检查的是：能否用同一套内部规则，把这两份内容都接回来。
如果能够，那么原来关于它们的后续问题，都可以经由这套共同恢复继续回答。
这使“已经足够”成为一个具体的关系性质。

<a id="section-2"></a>

## 2. 由两个态自身生成锚与唯一候选

<a id="sec-c90-definition"></a>

### 定义 2.1（二元内容、内生中点与共同支撑）

给定同一有限载体上的两个密度矩阵
$\rho_0,\rho_1\ge0$、$\operatorname{Tr}\rho_0=\operatorname{Tr}\rho_1=1$，定义

$$
\sigma=\frac{\rho_0+\rho_1}{2},\qquad
 \delta=\frac{\rho_0-\rho_1}{2}=\rho_0-\sigma,
 \qquad S=\operatorname{supp}\sigma.
$$

所有输入算符先限制在 $S$ 上。给定 CPTP 内部转换 $\mathcal N$，
令 $\tau=\mathcal N(\sigma)$，输出限制在 $\operatorname{supp}\tau$ 上。

### 引理 2.2（支撑限制不删去这一对内容）

上述两个态均支撑在 $S$，且 $\sigma$ 在 $S$ 上忠实。
通道在 $S$ 上的全部矩阵输出均支撑于 $\operatorname{supp}\tau$，限制后的通道仍 CPTP。

**证明。**
若 $v\in\ker\sigma$，则两个非负数
$\langle v,\rho_i v\rangle$ 之和为零，故每个都为零。
正算子的平方根给 $\rho_i v=0$。
在 $S$ 上，任意正算符 $X$ 都满足某个有限 $c$ 下的 $X\le c\sigma$，
故 $0\le\mathcal N(X)\le c\tau$。
其输出支撑于 $\operatorname{supp}\tau$；正算符的复线性张成是全部矩阵空间，故一般矩阵也成立。
输入嵌入与输出压缩保持完全正，输出支撑又保证迹不变。

此后所有逆及分数幂均在上述正支撑上取。
这样允许原始两态为纯态，也允许它们的中点在原大载体上不满秩，
不需要向不参与比较的方向注入任意小权重。
中点是既有混合接口上的数学定义；实际制备它仍需对应的原生混合操作。

### 定义 2.3（对称加权平方比较）

对归一忠实参照 $\sigma$，定义

$$
\|X\|_{2,\sigma^{-1}}
 :=\left\lVert \sigma^{-1/4}X\sigma^{-1/4}\right\rVert_2,
 \qquad
 Q_\sigma(\rho):=\|\rho-\sigma\|_{2,\sigma^{-1}}^2.
$$

二态自身的平方区别为

<a id="eq-c90-binary-information"></a>

$$
\mathcal I(\rho_0,\rho_1)
 :=\|\delta\|_{2,\sigma^{-1}}^2
 =Q_\sigma(\rho_0)=Q_\sigma(\rho_1).
\tag{2.1}
$$

这是由态的区别与内部校准形成的二次关系量，不将它误写成另一条 Born 概率规则。
后文证明 $0\le\mathcal I\le1$，并说明对称权的精确选择范围。

### 定义 2.4（本轮唯一候选 C90：二元内生平方可恢复相容）

<a id="def-c90"></a>

定义指定通道的二元平方损失

<a id="eq-c90-loss"></a>

$$
\ell_{\mathcal N}(\rho_0,\rho_1)
 :=\mathcal I(\rho_0,\rho_1)
   -\mathcal I(\mathcal N\rho_0,\mathcal N\rho_1).
\tag{2.2}
$$

被称为这对内容的*完整二元代表*的转换，采用唯一有限条件

<a id="eq-c90"></a>

$$
\boxed{\quad \ell_{\mathcal N}(\rho_0,\rho_1)=0.\quad}
 \tag{C90}
$$

这是一项带作用范围的成员资格，不要求每种测量或噪声都对全部态对无损。
它要等价的完整定义是：存在同一个 CPTP 映射 $\mathcal R$，使

$$
\mathcal R\mathcal N(\rho_0)=\rho_0,
 \qquad
 \mathcal R\mathcal N(\rho_1)=\rho_1.
$$

若每个态分别允许一台依赖未知标签的制备器，问题会变得空洞；
因此这里必须是**同一个**恢复操作。

**白话图景。**先把两份内容放在同一把内部尺子上；这把尺子就是它们自己的中点。
再比较转换前后，经过校准的平方区别是否减少。
后面的定理将证明：完全没有减少，恰好意味着同一条恢复规则能接回两者。
参照、转换和恢复都由当前关系数据确定，无需再指定一个外部观察位置。

<a id="section-3"></a>

## 3. 为何采用这个平方：正反比较与独立组合的有限刻画

<a id="sec-c90-metric"></a>

归一化和“看起来像平方”不足以选定一个量子区别量。
本节把所用比较类及其相容条件全部写出，说明两侧各放一个四分之一次幂的来源。
这是比较定义的结构选择，不另外添加一条要求所有物理通道无损的公理。

### 定义 3.1（局部谱比二次比较类）

设 $\sigma=\sum_i s_i\lvert i\rangle\langle i\rvert>0$，$\operatorname{Tr}\sigma=1$。
对同一个正函数 $\kappa:(0,\infty)\to(0,\infty)$，$\kappa(1)=1$，定义

$$
\Omega_\sigma^\kappa(E_{ij})
 =\frac1{s_j}\kappa\!\left(\frac{s_i}{s_j}\right)E_{ij},
 \qquad
 g_\sigma^\kappa(X,Y)=\operatorname{Tr}(X^\dagger\Omega_\sigma^\kappa(Y)).
$$

这个谱比形式要求一个矩阵方向的权只取决于其两端谱值；
它等价于左右乘法算符的函数，故不依赖简并谱空间中任选的基。
其对角部分是经典二次校准 $\sum_i|X_{ii}|^2/s_i$。

这里 $\Omega_\sigma^\kappa$ 在 Hilbert–Schmidt 空间上给出正内积。
尚未把它假定为一个作用于状态的量子通道，也未预先假定数据处理单调性。
所选择的是如下两个完整比较接口：

<a id="eq-c90-star-weight"></a>

$$
\Omega_\sigma^\kappa(X^\dagger)
 =\Omega_\sigma^\kappa(X)^\dagger,
\tag{3.1}
$$

<a id="eq-c90-tensor-weight"></a>

$$
\Omega_{\sigma\otimes\tau}^\kappa
 =\Omega_\sigma^\kappa\otimes\Omega_\tau^\kappa.
\tag{3.2}
$$

第二式要求全部复极化比较随独立组合相容，包含交叉项与次序，
不能弱化成只检查若干 Hermitian 自平方或概率。

### 定理 3.2（所声明比较类中的唯一对称权）

在上述谱比类中，两式对全部忠实参照成立，当且仅当

<a id="eq-c90-weight-selection"></a>

$$
\boxed{\quad \kappa(x)=x^{-1/2},\qquad
 \Omega_\sigma(X)=\sigma^{-1/2}X\sigma^{-1/2}.\quad}
\tag{3.3}
$$

因此

$$
g_\sigma(X,X)
 =\operatorname{Tr}(X^\dagger\sigma^{-1/2}X\sigma^{-1/2})
 =\left\lVert \sigma^{-1/4}X\sigma^{-1/4}\right\rVert_2^2.
$$

**证明。**
将伴随相容用于 $E_{ij}$，得到

$$
\kappa(x^{-1})=x\kappa(x).
$$

任意正数 $x$ 均可用一个忠实 qubit 参照的两谱值之比实现。
将张量相容用于 $E_{ij}\otimes E_{kl}$，两端公共分母相同，故

$$
\kappa(xy)=\kappa(x)\kappa(y)\qquad(x,y>0).
$$

取 $y=x^{-1}$ 并利用 $\kappa(1)=1$，得到
$1=x\kappa(x)^2$。正性唯一给出 $\kappa(x)=x^{-1/2}$。
反向代入即可核对归一、伴随与张量相容。
最后以迹的循环性得到四分之一次幂的平方范数表示。

这是标准量子 $\chi^2$ 权算子张量刻画的有限证明；相关结果见 Cao–Lu 的 Lemma7(ii) [11](#ref-caolu)。
这里甚至不需要先在整个候选类上使用算符单调性；
选出的比较在全部 CPTP 通道下收缩，将由下一节独立证明。

### 说明 3.3（唯一性的准确范围）

结论限定于已声明的谱比二次比较类和完整接口。
本稿没有证明“内容即地址”单独迫使所有可能度量都属于这个类，
也没有把其他量子信息度量称为非法。
本轮选择的是能与正反次序、完整独立组合及随后恢复构造同时相容的一套规范。

### 命题 3.4（只保简单张量自平方不能代替完整组合）

取 $\kappa_R(x)=(1+x)/(2x)$。
它正、满足 $\kappa_R(1)=1$ 与伴随相容；
在 Hermitian $X$ 上给出 $\operatorname{Tr}(X^2\sigma^{-1})$。
对 Hermitian 简单张量 $X\otimes Y$，其自平方比较满足乘性，
但不满足完整权算子的张量相容。

**证明。**
该权算子为
$\Omega_\sigma^R(X)=(\sigma^{-1}X+X\sigma^{-1})/2$。
对 Hermitian $X$，迹循环性给出所述平方。
对简单张量，这个量为
$\operatorname{Tr}((X^2\otimes Y^2)(\sigma^{-1}\otimes\tau^{-1}))$，
自然分解为两个单端自平方的乘积。
然而

$$
\kappa_R(4)=\frac58\ne\frac9{16}=\kappa_R(2)^2,
$$

所以张量相容失败。

若在整个复合空间上，对每个 Hermitian 元都已保证两权算子的自平方相同，
则保持伴随与实极化足以推出完整算符相等；上面反例只否定更弱的简单张量检验。
在经典对角方向上，这些权甚至完全一致。
真正区别它们的是非交换交叉比较。
后文还会给出该 RLD 平方零损失而共同恢复不存在的显式二态反例。

**白话图景。**平方不能只看总数，还要看比较的两个方向和组合方式。
在本节写明的比较类中，左右不能偏向一端，独立内容接在一起后也不能换一套交叉规则。
这两项配套条件把权重固定成两侧对称的形式。
四分之一次幂来自把这个完整二次比较写成普通长度平方，而非另加一个神秘尺度。

<a id="section-4"></a>

## 4. 加权平方为什么收缩：两个端点与完整插值证明

<a id="sec-c90-interpolation"></a>

先证明一个一般工具，再把参考态限定为定义 [2.4](#def-c90) 中由两端自身决定的中点。
固定 CPTP 映射 $\mathcal N:M_d\to M_k$，以及

$$
\sigma>0,\qquad \operatorname{Tr}\sigma=1,\qquad
 \tau=\mathcal N(\sigma)>0.
$$

待比较的 $\rho$ 只需是密度矩阵，不要求严格正。
采用前文的对称加权平方，并明确记号

$$
W_\sigma(Z)=\sigma^{-1/4}Z\sigma^{-1/4},\qquad
 \left\lVert Z\right\rVert_{2,\sigma^{-1}}=\left\lVert W_\sigma(Z)\right\rVert_2,
 \qquad Q_\sigma(\rho)=\left\lVert \rho-\sigma\right\rVert_{2,\sigma^{-1}}^2.
$$

这个范数一般不同于 $\sqrt{\operatorname{Tr}(Z^\dagger\sigma^{-1}Z)}$。
以下沿复插值与恢复映射的标准思路展开 [12](#ref-beigi)、[10](#ref-gaorecovery)，
将本轮需要的有限维证明列全，不把数据处理不等式作为黑箱。

### 引理 4.1（两个端点的范数收缩）

<a id="lem-c90-endpoints"></a>

UCP 映射在算符范数下收缩，CPTP 映射在迹范数下收缩；
两者都对任意复矩阵成立。

**证明。**
若 $\Psi(X)=\sum_jL_j^\dagger XL_j$ 且 $\sum_jL_j^\dagger L_j=I$，
令 $V\xi=\sum_jL_j\xi\otimes\lvert j\rangle$。于是 $V^\dagger V=I$，
且 $\Psi(X)=V^\dagger(X\otimes I)V$，故
$\left\lVert \Psi(X)\right\rVert_\infty\le\left\lVert X\right\rVert_\infty$。
对 CPTP 的 $\mathcal N$，其普通迹伴随 $\mathcal N^*$ 为 UCP。
奇异值分解给出迹范数对偶性，因此

$$
\begin{aligned}
 \left\lVert \mathcal N(X)\right\rVert_1
 &=\sup_{\left\lVert Y\right\rVert_\infty\le1}
     |\operatorname{Tr}(Y^\dagger\mathcal N(X))|\\
 &=\sup_{\left\lVert Y\right\rVert_\infty\le1}
     |\operatorname{Tr}((\mathcal N^*Y)^\dagger X)|
 \le\left\lVert X\right\rVert_1.
 \end{aligned}
$$

这里没有将输入限于 Hermitian 矩阵。

### 定理 4.2（对称加权 Hilbert–Schmidt 收缩）

<a id="thm-c90-contraction"></a>

定义

$$
T(X)=\tau^{-1/4}\mathcal N(\sigma^{1/4}X\sigma^{1/4})\tau^{-1/4}.
$$

则对全部复矩阵 $X$，$\left\lVert T(X)\right\rVert_2\le\left\lVert X\right\rVert_2$。

**证明。**
在闭条带 $0\le\operatorname{Re}z\le1$ 上定义解析族

<a id="eq-c90-analytic-family"></a>

$$
T_z(X)=\tau^{-z/2}
       \mathcal N(\sigma^{z/2}X\sigma^{z/2})\tau^{-z/2}.
\tag{4.1}
$$

矩阵幂用严格正矩阵的实对数定义，故每个矩阵元解析。
在 $z=it$ 时，左右的虚幂都是酉矩阵；分别从两侧乘酉矩阵保持 Schatten 范数，
不要求它们互为伴随。由引理 [4.1](#lem-c90-endpoints)，

<a id="eq-c90-left-endpoint"></a>

$$
\left\lVert T_{it}(X)\right\rVert_1\le\left\lVert X\right\rVert_1.
\tag{4.2}
$$

再令

$$
\Psi(X)=\tau^{-1/2}
       \mathcal N(\sigma^{1/2}X\sigma^{1/2})\tau^{-1/2}.
$$

它完全正，且 $\Psi(I)=\tau^{-1/2}\mathcal N(\sigma)\tau^{-1/2}=I$。
因而

$$
T_{1+it}(X)=\tau^{-it/2}
       \Psi(\sigma^{it/2}X\sigma^{it/2})\tau^{-it/2},
 \qquad
 \left\lVert T_{1+it}(X)\right\rVert_\infty\le\left\lVert X\right\rVert_\infty.
$$

先取可逆的 $X,Y$，满足 $\left\lVert X\right\rVert_2=\left\lVert Y\right\rVert_2=1$。
写极分解 $X=UD$、$Y=VE$，其中 $U,V$ 酉，$D,E>0$，且
$\operatorname{Tr} D^2=\operatorname{Tr} E^2=1$。构造解析测试函数

<a id="eq-c90-test-function"></a>

$$
f(z)=\operatorname{Tr}\!\left[
 E^{2z}V^\dagger\,
 T_z\!\left(UD^{2(1-z)}\right)\right].
\tag{4.3}
$$

在左边界，$\left\lVert UD^{2(1-it)}\right\rVert_1=1$、
$\left\lVert E^{2it}V^\dagger\right\rVert_\infty=1$，故 $|f(it)|\le1$。
在右边界，$\left\lVert UD^{-2it}\right\rVert_\infty=1$、
$\left\lVert E^{2+2it}V^\dagger\right\rVert_1=1$，故 $|f(1+it)|\le1$。
这里分别使用迹配对的 $S_1$–$S_\infty$ 对偶性。

固定上述正矩阵后，虚幂酉、实幂在闭条带内有界，所以 $f$ 在整个条带有界。
三线引理给出 $|f(1/2)|\le1$。
也可直接将最大模原理应用于
$f(z)e^{\delta z^2}$ 与高度为 $2R$ 的矩形：两个竖边的界不超过
$e^\delta$，横边随 $R\to\infty$ 被 $e^{-\delta R^2}$ 压住；
先令 $R\to\infty$，再令 $\delta\downarrow0$，得到相同结论。
在中点，式 [(4.3)](#eq-c90-test-function) 正是

$$
f(1/2)=\operatorname{Tr}(Y^\dagger T(X)).
$$

对全部 Hilbert–Schmidt 单位测试矩阵 $Y$ 取上确界，便得到所需收缩。

最后处理奇异矩阵。将极分解中的部分等距映射延拓为酉矩阵，
对 $D\ge0$ 取

$$
D_\varepsilon=
 \frac{D+\varepsilon I}{\left\lVert D+\varepsilon I\right\rVert_2},
 \qquad X_\varepsilon=UD_\varepsilon,
$$

对 $Y$ 同样处理。正则化后的矩阵可逆、HS 范数为一，且收敛于原矩阵。
上述界对每个 $\varepsilon>0$ 成立，有限维连续性允许令
$\varepsilon\downarrow0$。一般范数由缩放恢复，零矩阵情形直接成立。

**白话图景。**这一步把两种已经可靠的比较接起来：完整状态转换不会放大迹范数，
归一后的读口转换不会放大算符范数。
在两端之间做严格的解析插值，就得到当前需要的平方收缩。
所以平方差不会增加有一个完整证明，不需要先把数据处理结论当成新公理。

<a id="section-5"></a>

## 5. 平方饱和为何产生同一个完全正恢复

<a id="sec-c90-recovery"></a>

定义恢复映射

<a id="eq-c90-petz"></a>

$$
\mathcal R_\sigma(Y)
 =\sigma^{1/2}\mathcal N^*(\tau^{-1/2}Y\tau^{-1/2})\sigma^{1/2}.
\tag{5.1}
$$

它只依赖当前接口 $\mathcal N$ 与参考态 $\sigma$，不依赖待检查的 $\rho$。

### 引理 5.1（恢复映射的归一性与加权伴随）

<a id="lem-c90-petz"></a>

$\mathcal R_\sigma$ 为 CPTP，且 $\mathcal R_\sigma(\tau)=\sigma$。
定理 [4.2](#thm-c90-contraction) 中 $T$ 的 HS 伴随满足

$$
T^\dagger(Y)=\sigma^{1/4}
       \mathcal N^*(\tau^{-1/4}Y\tau^{-1/4})\sigma^{1/4},
$$

并有

<a id="eq-c90-weighted-adjoint"></a>

$$
W_\sigma^{-1}T^\dagger T W_\sigma
 =\mathcal R_\sigma\mathcal N.
\tag{5.2}
$$

**证明。**
式 [(5.1)](#eq-c90-petz) 是三个完全正映射的组合。普通迹配对给出

$$
\begin{aligned}
 \operatorname{Tr}\mathcal R_\sigma(Y)
 &=\operatorname{Tr}\!\left(\sigma\mathcal N^*(\tau^{-1/2}Y\tau^{-1/2})\right)\\
 &=\operatorname{Tr}\!\left(\tau\tau^{-1/2}Y\tau^{-1/2}\right)=\operatorname{Tr} Y.
 \end{aligned}
$$

又因 $\mathcal N^*(I)=I$，
$\mathcal R_\sigma(\tau)=\sigma^{1/2}\mathcal N^*(I)\sigma^{1/2}=\sigma$。
将 $T$ 的三个因子按 HS 内积取伴随，便得所示 $T^\dagger$。
再代入 $W_\sigma^{-1}(X)=\sigma^{1/4}X\sigma^{1/4}$，直接合并相邻幂次，
得到式 [(5.2)](#eq-c90-weighted-adjoint)。

### 定理 5.2（一般参考态下的饱和、恢复及残差）

<a id="thm-c90-general-recovery"></a>

令

$$
\ell_\sigma(\rho)=Q_\sigma(\rho)-Q_\tau(\mathcal N\rho).
$$

则 $\ell_\sigma(\rho)\ge0$，且下列三项等价：

1. $\ell_\sigma(\rho)=0$；

2. $\mathcal R_\sigma\mathcal N(\rho)=\rho$；

3. 存在同一个 CPTP 映射 $\mathcal S$，使
          $\mathcal S\mathcal N(\rho)=\rho$ 且 $\mathcal S(\tau)=\sigma$。

此外，

<a id="eq-c90-weighted-residual"></a>

$$
\boxed{\quad
 \ell_\sigma(\rho)
 \ge\left\lVert \rho-\mathcal R_\sigma\mathcal N\rho\right\rVert_{2,\sigma^{-1}}^2.
 \quad}
\tag{5.3}
$$

**证明。**
令 $X=W_\sigma(\rho-\sigma)$，则
$TX=W_\tau(\mathcal N\rho-\tau)$。
在 HS Hilbert 空间上记 $C=T^\dagger T$。
定理 [4.2](#thm-c90-contraction) 给出 $0\le C\le I$，因此

<a id="eq-c90-positive-defect"></a>

$$
\ell_\sigma(\rho)
 =\left\lVert X\right\rVert_2^2-\left\lVert TX\right\rVert_2^2
 =\langle X,(I-C)X\rangle_{\mathrm{HS}}\ge0.
\tag{5.4}
$$

利用式 [(5.2)](#eq-c90-weighted-adjoint) 和
$\mathcal R_\sigma\mathcal N(\sigma)=\sigma$，得到

<a id="eq-c90-residual-coordinate"></a>

$$
(I-C)X=W_\sigma(\rho-\mathcal R_\sigma\mathcal N\rho).
\tag{5.5}
$$

由于 $I-C\ge0$，式 [(5.4)](#eq-c90-positive-defect) 为零恰好意味着
$(I-C)X=0$，所以前两项等价。取 $\mathcal S=\mathcal R_\sigma$ 得第三项。
反之，若第三项成立，分别对 $\mathcal N$ 和 $\mathcal S$ 使用已经证明的加权收缩，
得到

$$
Q_\sigma(\rho)
 =Q_{\mathcal S\tau}(\mathcal S\mathcal N\rho)
 \le Q_\tau(\mathcal N\rho)
 \le Q_\sigma(\rho).
$$

两个不等式必须同时饱和。

最后，$0\le I-C\le I$ 给出 $(I-C)^2\le I-C$，故

$$
\left\lVert (I-C)X\right\rVert_2^2
 \le\langle X,(I-C)X\rangle_{\mathrm{HS}}=\ell_\sigma(\rho).
$$

代入式 [(5.5)](#eq-c90-residual-coordinate) 即得残差界。

这里 $I-C$ 的正性指它作为 HS Hilbert 空间上的算符为正，
并非声称它是矩阵正锥上的完全正映射，也并非声称
$\rho-\mathcal R_\sigma\mathcal N\rho\ge0$。
一般恢复映射的存在并没有被提前假定；它由明确的加权伴随构造给出。

**白话图景。**平方长度没有减少，意味着加权转换在这一份差别上没有压掉任何方向。
它的伴随经过同样的内部尺度换回去，恰好成为一条合法恢复通道。
这条通道同时接回待比较内容与参考态；有少量损失时，同一个计算还给出接回误差。

<a id="section-6"></a>

## 6. 由平方误差控制所有完整后续读出

<a id="sec-c90-readout-bound"></a>

### 引理 6.1（归一校准给出的迹范数界）

<a id="lem-c90-trace-norm"></a>

对任意矩阵 $Z$，

$$
\left\lVert \sigma^{1/4}Z\sigma^{1/4}\right\rVert_1
 \le\sqrt{\operatorname{Tr}\sigma}\,\left\lVert Z\right\rVert_2=\left\lVert Z\right\rVert_2.
$$

**证明。**
迹范数可用酉测试矩阵取得对偶上确界。
对任意酉 $U$，迹循环与 HS Cauchy–Schwarz 给出

$$
|\operatorname{Tr}(U\sigma^{1/4}Z\sigma^{1/4})|
 \le\left\lVert \sigma^{1/4}U\sigma^{1/4}\right\rVert_2\left\lVert Z\right\rVert_2.
$$

再计算

$$
\begin{aligned}
 \left\lVert \sigma^{1/4}U\sigma^{1/4}\right\rVert_2^2
 &=\operatorname{Tr}(U^\dagger\sigma^{1/2}U\sigma^{1/2})\\
 &\le\left\lVert U^\dagger\sigma^{1/2}U\right\rVert_2
       \left\lVert \sigma^{1/2}\right\rVert_2
 =\operatorname{Tr}\sigma=1.
 \end{aligned}
$$

取上确界即得结论。最后的常数一使用了校准态的归一化。

### 推论 6.2（迹距离与完整读出分布）

<a id="cor-c90-operational-bound"></a>

记 $\widehat\rho=\mathcal R_\sigma\mathcal N\rho$。
则

<a id="eq-c90-trace-distance"></a>

$$
\boxed{\quad
 \frac12\left\lVert \rho-\widehat\rho\right\rVert_1
 \le\frac12\sqrt{\ell_\sigma(\rho)}.
 \quad}
\tag{6.1}
$$

对同一个完整后续 CPTP 协议 $\Lambda$ 及任意有限 POVM $\{M_y\}$，令

$$
p_y=\operatorname{Tr}(M_y\Lambda(\rho)),\qquad
 \widehat p_y=\operatorname{Tr}(M_y\Lambda(\widehat\rho)).
$$

则

<a id="eq-c90-tv-bound"></a>

$$
\frac12\sum_y|p_y-\widehat p_y|
 \le\frac12\left\lVert \rho-\widehat\rho\right\rVert_1
 \le\frac12\sqrt{\ell_\sigma(\rho)}.
\tag{6.2}
$$

**证明。**
在引理 [6.1](#lem-c90-trace-norm) 中取
$Z=W_\sigma(\rho-\widehat\rho)$，再使用
式 [(5.3)](#eq-c90-weighted-residual)，即得迹距离界。
测量与 $\Lambda$ 合成仍是 CPTP 映射，其输出为对角概率矩阵。
引理 [4.1](#lem-c90-endpoints) 的迹范数收缩遂给出总变差界。
等价地，对任一最终事件，其效果经 $\Lambda^*$ 拉回后仍位于 $[0,I]$。
对 Hermitian、无迹的 $Z$，正负谱分解给出

$$
\sup_{0\le F\le I}|\operatorname{Tr}(FZ)|=\frac12\left\lVert Z\right\rVert_1.
$$

因此一般结果空间也能用事件概率差的上确界表述同一结论。

完整协议可以包含由该接口准备的辅助系统、反馈及全部分支记录，只要对两种输入使用同一个
确定的 CPTP 接口。任意已有的未知纠缠扩张，则须另行把联合态纳入声明。
若仅保留某个分支再除以其成功概率，条件化可能放大差别，
不能不加条件地继续使用式 [(6.2)](#eq-c90-tv-bound)。
这一界也没有自动供应恢复映射所需的实际装置；原生菜单、校准与执行资源
仍由项目已经声明的操作接口负责。

**白话图景。**平方损失不只告诉我们“有多少东西没接回来”。
它还能限制以后任何完整读出的差别：不论接下来怎样加入辅助系统、记录或反馈，
两份内容产生的完整结果分布都不会超过同一个误差界。
若只挑一个罕见分支重新归一，就改变了问题，不能把完整分布的界直接照搬。

<a id="section-7"></a>

## 7. 回到真正二元中点：一端恢复等价于两端共同恢复

<a id="sec-c90-midpoint-recovery"></a>

现在令 $\rho_0,\rho_1$ 为定义 [2.4](#def-c90) 中的两态，取

$$
\sigma=\frac{\rho_0+\rho_1}{2},\qquad
 d=\frac{\rho_0-\rho_1}{2},\qquad
 \tau=\mathcal N(\sigma).
$$

这是两端自身确定的中点，不再增加第三个独立参考态。
先令 $p=\operatorname{supp}\sigma$、$q=\operatorname{supp}\tau$ 为支撑投影，
并将矩阵接口限制到相应支撑空间。
由于 $\rho_i\le2\sigma$，两端均支撑在 $p$ 中；其输出均支撑在 $q$ 中。
对任意 $p$ 上的正矩阵 $X$，存在有限常数 $c$ 使 $X\le c\sigma$，故
$\mathcal N(X)\le c\tau$。因此 $\mathcal N$ 确实限制为这两个支撑空间之间的
CPTP 映射，$\sigma,\tau$ 在各自空间中严格正，前述逆幂均合法。

若需要在原输出空间定义全通道，可将支撑内恢复扩为

$$
\widetilde{\mathcal R}_\sigma(Y)
 =\mathcal R_\sigma(qYq)+\operatorname{Tr}((I-q)Y)\sigma.
$$

这个扩展完全正且迹保持，并与所有实际 $\mathcal N(\rho_i)$ 上的恢复一致。
下文仍使用支撑内的简洁记号。

### 定理 7.1（C90 的二态恢复形式）

<a id="thm-c90-midpoint-main"></a>

对上述中点与式 [(2.2)](#eq-c90-loss) 的平方损失 $\ell$，下列条件等价：

1. C90 成立，即 $\ell=0$；

2. $\mathcal R_\sigma\mathcal N(\rho_0)=\rho_0$；

3. $\mathcal R_\sigma\mathcal N(\rho_1)=\rho_1$；

4. 存在同一个 CPTP 映射 $\mathcal S$ 同时恢复两态：
          $\mathcal S\mathcal N(\rho_i)=\rho_i$，$i=0,1$。

对两个端点还同时有

<a id="eq-c90-pair-errors"></a>

$$
\left\lVert \rho_i-\mathcal R_\sigma\mathcal N\rho_i\right\rVert_{2,\sigma^{-1}}^2
 \le\ell,
 \qquad
 \frac12\left\lVert \rho_i-\mathcal R_\sigma\mathcal N\rho_i\right\rVert_1
 \le\frac12\sqrt\ell.
\tag{7.1}
$$

同一个上界适用于每个端点的全部完整后续读出。

**证明。**
由 $\rho_0-\sigma=d$、$\rho_1-\sigma=-d$，

$$
\mathcal I(\rho_0,\rho_1)=Q_\sigma(\rho_0)=Q_\sigma(\rho_1).
$$

输出的中点为 $\tau$，差为 $\mathcal N(d)$，所以
$\ell=\ell_\sigma(\rho_0)=\ell_\sigma(\rho_1)$。
定理 [5.2](#thm-c90-general-recovery) 随即给出前三项等价和两个误差界。
也可直接由线性性看出

$$
\rho_1-\mathcal R_\sigma\mathcal N\rho_1
 =-(\rho_0-\mathcal R_\sigma\mathcal N\rho_0),
$$

所以恢复一端必然恢复另一端。

前三项成立时，$\mathcal R_\sigma$ 就是第四项所需的共同映射。
反之，任何共同恢复两端的 $\mathcal S$ 都自动满足

$$
\mathcal S(\tau)
 =\frac{\mathcal S\mathcal N(\rho_0)+\mathcal S\mathcal N(\rho_1)}2
 =\sigma.
$$

因此可应用一般恢复定理。若原先在更大空间给出 $\mathcal S$，
由 $\mathcal S(\tau)=\sigma$ 及正性，它也可限制到同一支撑接口。
最后使用推论 [6.2](#cor-c90-operational-bound)，便得全部后续读出结论。

### 命题 7.2（二元例子达到误差常数）

<a id="prop-c90-sharp"></a>

取擦除通道 $\mathcal N(X)=\operatorname{Tr} X\in\mathbb C$，并令

$$
\rho_0=\operatorname{diag}(1/2+t,1/2-t),\qquad
 \rho_1=\operatorname{diag}(1/2-t,1/2+t),\qquad |t|\le1/2.
$$

则 $\sigma=I_2/2$、$\tau=1$、$\mathcal R_\sigma(y)=y\sigma$，且

$$
\ell=4t^2,
 \qquad
 \frac12\left\lVert \rho_i-\sigma\right\rVert_1=|t|=\frac12\sqrt\ell.
$$

加权残差界也取等号。

**证明。**
两输出都为 $1$，所以输出二元平方为零。
输入差为 $d=\operatorname{diag}(t,-t)$，对中点白化后平方范数为 $4t^2$。
恢复将两端都送回 $\sigma$；残差的两个特征值为 $t,-t$ 或其相反数，
故迹距离为 $|t|$，加权平方残差等于 $\ell$。

本定理恢复的是声明的这一对态及其概率混合，并不要求
$\mathcal R_\sigma\mathcal N$ 在整个矩阵空间上等于恒等映射。
它也不抹去已经发生的记录历史。这样的限定与内生中点并不冲突：
中点只固定当前这对关系的比较尺度，恢复结论仍须准确指向所声明的内容范围。

**白话图景。**两份内容自己就确定了中间的参考，不必从整体外面再放一把尺子。
如果转换没有减少它们相对中点的平方差，同一条恢复规则就能把两端一起接回来。
因为中点已经固定，接回一端就自动接回另一端。
有少量损失时，两端以及各自未来的完整读出，都共享同一个明确的误差账。

<a id="section-8"></a>

## 8. 二元区别的尺度、纯态圆弧与有限三维证书

<a id="sec-c90-geometry"></a>

### 命题 8.1（内生中点平方的完整零边界与满边界）

对全部二态，

$$
0\le\mathcal I(\rho_0,\rho_1)\le1.
$$

零值当且仅当 $\rho_0=\rho_1$；值为一当且仅当两态支撑正交。
若两态对易，谱概率分别为 $p_i,q_i$，则

$$
\mathcal I(\rho_0,\rho_1)
 =\frac12\sum_{i:p_i+q_i>0}\frac{(p_i-q_i)^2}{p_i+q_i}.
$$

**证明。**
在中点支撑上令 $A=\sigma^{-1/2}\delta\sigma^{-1/2}$。
由 $\sigma\pm\delta=\rho_{0,1}\ge0$，得到 $-I\le A\le I$。
因此

$$
\mathcal I=\operatorname{Tr}(\sigma^{1/2}A\sigma^{1/2}A)
 \le \operatorname{Tr}(\sigma A^2)\le1.
$$

第一不等式是对 $A\sigma^{1/2}$ 与 $\sigma^{1/2}A$ 使用
Hilbert–Schmidt Cauchy–Schwarz；两者的平方范数同为 $\operatorname{Tr}(\sigma A^2)$。
非负性来自原定义；零范数恰好等价于 $\delta=0$。

若 $\mathcal I=1$，上面两个不等式都取等号。
忠实性给 $A^2=I$，两个 HS 向量相等给 $[A,\sigma]=0$。
令 $P_\pm=(I\pm A)/2$，便有
$\rho_0=2\sigma P_+$、$\rho_1=2\sigma P_-$，所以支撑正交。
反过来，支撑正交时 $A$ 就是这两个支撑上的正负单位元，代入得一。
对易公式由共同对角基中 $\sigma_i=(p_i+q_i)/2$、$\delta_i=(p_i-q_i)/2$ 得到。

### 命题 8.2（两个纯态的圆弧读出）

对归一纯态 $\rho_i=\lvert \psi_i\rangle\langle \psi_i\rvert$，定义标准纯态角

$$
\theta=\arccos|\langle\psi_0,\psi_1\rangle|\in[0,\pi/2].
$$

则

<a id="eq-c90-pure-angle"></a>

$$
\boxed{\quad\mathcal I(\rho_0,\rho_1)=\sin\theta
 =\sqrt{1-|\langle\psi_0,\psi_1\rangle|^2}.\quad}
\tag{8.1}
$$

**证明。**
对 $0<\theta\le\pi/2$，选择共同相位与二维正交基，使

$$
\psi_0=c e_0+s e_1,\qquad \psi_1=c e_0-s e_1,
 \qquad c=\cos(\theta/2),\ s=\sin(\theta/2).
$$

于是 $\sigma=\operatorname{diag}(c^2,s^2)$、$\delta=cs\,\sigma_x$。
经两侧 $\sigma^{-1/4}$ 后，非对角元为 $\sqrt{cs}$，
所以平方范数为 $2cs=\sin\theta$。
$\theta=0$ 时两态相同，直接使用零边界。

这把二态的内生比较与纯态圆弧角接起来。
该角采用 $\arccos|\langle\psi_0,\psi_1\rangle|$ 的约定；
qubit Bloch 球上对应的夹角是 $2\theta$。
公式是二态区别的读出，并未规定任意实际动力学轨迹都是圆弧。

**白话图景。**两个纯态之间的相干重叠，可以读成一段角度；本轮的中点平方区别就是这个角度的正弦。
两态重合时区别为零，彼此正交时区别达到一。
这样圆弧直觉有了明确的二态量，但时间怎样走、轨迹怎样弯仍由实际操作决定。

### 原区别与恢复残差的 Gram 块

沿用核心证明的 $W_\sigma(X)=\sigma^{-1/4}X\sigma^{-1/4}$、HS 收缩 $T$。
本段固定 $\mathcal R:=\mathcal R_\sigma$ 为式 [(5.1)](#eq-c90-petz) 的规范 Petz 恢复，
以下残差恒等式不指任意另选的恢复映射。
令

$$
u=W_\sigma(\delta),\qquad
 C=T^\dagger T,\qquad B=I-C,\qquad r=Bu.
$$

则 $0\le B\le I$，并且

$$
r=W_\sigma(\rho_0-\mathcal R\mathcal N\rho_0)
 =-W_\sigma(\rho_1-\mathcal R\mathcal N\rho_1).
$$

这里 $B$ 的正性是 HS Hilbert 空间上的正性，$r$ 是差向量；
二者不被误当成量子效果或密度态。

### 定理 8.3（有限三维恢复证书及尺度条件）

定义

$$
a=\left\lVert u\right\rVert_2^2,\qquad b=\left\lVert r\right\rVert_2^2,\qquad c=\langle u,r\rangle_{\rm HS}.
$$

则 $a=\mathcal I$、$c=\ell_{\mathcal N}$ 为实数，且

<a id="eq-c90-gram-region"></a>

$$
\boxed{\quad0\le b\le c\le a\le1,
 \qquad c^2\le ab.\quad}
\tag{8.2}
$$

二态精确恢复当且仅当 $b=c=0$。
当 $a,b>0$ 时，

$$
\mathbf q=\frac{(c,0,\sqrt{ab-c^2})}{\sqrt{ab}}\in S^2_+.
$$

其第二坐标固定为零，故只占据一条子午线的四分之一圆弧。
当 $a+b>0$ 时，也可采用 Bloch 球内坐标

$$
\frac1{a+b}\begin{pmatrix}a&c\\c&b\end{pmatrix}
 =\frac12(I+\mathbf z\cdot\boldsymbol\sigma),
 \qquad
 \mathbf z=\left(\frac{2c}{a+b},0,\frac{a-b}{a+b}\right).
$$

保留 $a,b$ 与 $\mathbf q$，或保留 $a+b$ 与 $\mathbf z$，才能重构整个 Gram 块。

**证明。**
$b=\langle u,B^2u\rangle\le\langle u,Bu\rangle=c\le a$，
而 Cauchy–Schwarz 给 $c^2\le ab$。
若 $c=0$，正性使 $B^{1/2}u=0$，故 $r=0$；反向由 $c=\langle u,r\rangle$。
球坐标由 $ab-c^2\ge0$ 直接归一；Bloch 球内条件等价于
$4c^2+(a-b)^2\le(a+b)^2$。

在后一图形中还满足 $z_x,z_z\ge0$、$z_x+z_z\ge1$。
若原区别 $a>0$，精确恢复对应北极 $(0,0,1)$。
在前一上半球图形中，精确恢复时 $b=0$，归一式反而没有定义。
若 $a=0$，两态本来相同，全部 Gram 数据为零，不能由此认证通道在其他态上的作用。

### 命题 8.4（归一图形相同，绝对损失仍可不同）

固定原二态中点，令

$$
\rho_{0,t}=\sigma+t\delta,
 \qquad\rho_{1,t}=\sigma-t\delta,
 \qquad0<t\le1.
$$

则 $(a_t,b_t,c_t)=t^2(a,b,c)$。
两种归一图形在各自有定义时均不变，但平方损失及恢复误差的绝对尺度改变。

**证明。**
二态均为原态与中点的凸组合，仍合法；中点以及由它定义的 $T,B$ 不变。
区别与残差均乘 $t$，故全部二次量乘 $t^2$。

本节的三维图表示一个二元 Gram 证书，未把原密度矩阵或整个通道的所有参数编码成单个球点。
由于 $c$ 为非负实数，这里也没有凭空引入一个自由相位或手性坐标。

**白话图景。**把“原来的区别”和“回接后剩下的区别”放在一起，就得到一张有限三维关系图。
缺额为零时，回接已经完整；两态原来就相同时，图根本没有可比较的长度。
图形还必须带着尺度：把两态都向中点收近，归一图形可以完全不变，实际损失却会缩小。

<a id="section-9"></a>

## 9. 内部换锚不改变零损失资格，稳定读出仍可不确定

<a id="sec-c90-anchor"></a>

### 定理 9.1（二态内部混合锚的零判定一致）

对 $0<p<1$，令
$\sigma_p=(1-p)\rho_0+p\rho_1$，并定义

$$
\ell_p=Q_{\sigma_p}(\rho_0)
       -Q_{\mathcal N\sigma_p}(\mathcal N\rho_0).
$$

则下列条件等价：某一个 $p$ 有 $\ell_p=0$；每一个 $p$ 都有 $\ell_p=0$；
存在同一 CPTP 操作恢复原二态；中点候选 C90 成立。

**证明。**
任意 $0<p<1$ 的混合具有同一共同支撑。
若 $\ell_p=0$，核心定理给一个共同恢复 $\rho_0,\sigma_p$ 的操作。
由 $\rho_1=(\sigma_p-(1-p)\rho_0)/p$ 及线性性，它也恢复 $\rho_1$。
反之，恢复原二态的同一个操作必恢复每个 $\sigma_p$，
对正反两个通道使用平方收缩，将不等式夹成等号。

各锚下的非零数值、恢复公式在未声明态上的行为，可以不同；
定理固定的是同一二态模型的*精确零损失资格*。
这不是说增加任意第三个参照态以后，仍不需要检查新的恢复范围。
中点的优点是交换两态不改变定义，且两端恢复误差具有相同范数。

### 命题 9.2（可恢复性与单次结果不确定性相容）

取 $\rho_0=\lvert 0\rangle\langle 0\rvert$、$\rho_1=\lvert +\rangle\langle +\rvert$，以及任意酉通道
$\mathcal N(X)=UXU^\dagger$。则 C90 成立。
然而在态 $\rho_1$ 上读出 $P_0=\lvert 0\rangle\langle 0\rvert$，有
$p(0)=1/2$、$\operatorname{Var}_{\rho_1}(P_0)=1/4$。

**证明。**
酉逆共同恢复两个态，故由主定理得到 C90。
投影概率及方差由 Born 规则直接计算。

平方区别没有损失，保证两态的全部统计能够被共同接续；
它没有把统计中的随机结果变成确定值。
恢复是一个新追加的内部操作，对被声明的状态接口起作用，
不会自动抹除已经保留在其他记录中的历史。

**白话图景。**这把尺子不需要一个绝对的外部位置。
在同一对内容之间，换一种两端都保留权重的内部混合，数值刻度会变，完整可恢复与否不会变。
而且完整找回一个量子态，只是找回它原有的概率规则；那个规则本身仍然可以给一半对一半的结果。

<a id="section-10"></a>

## 10. 删去条件会发生什么：纯度、区分度与另一种平方

<a id="sec-c90-counterexamples"></a>

以下例子采用本轮的内生中点
$\sigma=(\rho_0+\rho_1)/2$、半差 $d=(\rho_0-\rho_1)/2$。
记 $\mathsf X=\begin{pmatrix}0&1\\1&0\end{pmatrix}$、
$\mathsf Z=\operatorname{diag}(1,-1)$ 为自伴 Pauli 统计算符；
它们不是密度态。记 $P_0=\lvert 0\rangle\langle 0\rvert$、$P_1=\lvert 1\rangle\langle 1\rvert$、
$P_+=\lvert +\rangle\langle +\rvert$，其中 $\lvert +\rangle=(\lvert 0\rangle+\lvert 1\rangle)/\sqrt2$。

### 命题 10.1（普通纯度既不单调，也不认证共同恢复）

取 $0<a<1$，令

$$
\rho_0=\frac{I+a\mathsf Z}{2},\qquad
 \rho_1=\frac{I+a\mathsf X}{2},\qquad
 N(X)=\operatorname{Tr}(X)\rho_0.
$$

这是 CPTP 通道，两态及其中点均忠实，而且

$$
\operatorname{Tr}(\rho_i^2)=\operatorname{Tr}\bigl(N(\rho_i)^2\bigr)
 =\frac{1+a^2}{2}\quad(i=0,1).
$$

尽管两个普通平方都保持，仍不存在共同恢复通道。
同一通道还将 $I/2$ 的纯度由 $1/2$ 提高到 $(1+a^2)/2$。

**证明。**
Pauli 算符平方为 $I$、迹为零，直接展开得到上述纯度。
两个不同输入被送到同一个 $\rho_0$，任何单值恢复映射都无法从
这一个输出同时返回两个不同输入。纯度增加的断言也由
$N(I/2)=\rho_0$ 直接得到。

### 命题 10.2（保持最优二元区分度仍可丢失共同量子内容）

令 $a,b>0$ 且 $a^2+b^2<1$，取

$$
\rho_0=\frac{I+a\mathsf X+b\mathsf Z}{2},\qquad
 \rho_1=\frac{I+a\mathsf X-b\mathsf Z}{2},\qquad
 N=E_z,
$$

其中 $E_z(X)=P_0XP_0+P_1XP_1$ 为去相干通道。
则 $N$ 完整保持两态的迹距离，却不存在共同的正保迹恢复映射。

**证明。**
两态之差为 $b\mathsf Z$，被 $E_z$ 原样保留，故迹距离不变。
若 $S$ 同时恢复两态，由和与差得到

$$
S(I/2)=\frac{I+a\mathsf X}{2},\qquad S(\mathsf Z)=\mathsf Z.
$$

于是

$$
S(P_0)=\frac{I+a\mathsf X+\mathsf Z}{2}.
$$

右侧的较小本征值为 $(1-\sqrt{1+a^2})/2<0$，与正性矛盾。
因此普通二元区分度保持不能替代 C90。

**白话图景。**两种东西可以一样纯，也可以仍然同样容易区分，
却已经失去了共同的相干内容。
“这个数字没变”必须先说明保住了哪一种关系。
C90 检查的是两端能否由同一个合法过程共同找回来。

### 定义 10.3（用于反例的 RLD 平方）

在同一个中点与半差上，另定义

$$
J_{\mathrm{RLD}}(\rho_0,\rho_1)
 =\operatorname{Tr}(d\sigma^{-1}d).
$$

本节简记 $J:=\mathcal I(\rho_0,\rho_1)=\operatorname{Tr}(d\sigma^{-1/2}d\sigma^{-1/2})$。二者满足

<a id="eq-c90-rld-difference"></a>

$$
J_{\mathrm{RLD}}-J
 =\frac12\left\lVert [\sigma^{-1/2},d]\right\rVert_2^2\ge0.
\tag{10.1}
$$

这由展开交换子的 Hilbert–Schmidt 平方并使用迹的循环性得到。
两种加权平方不能在恢复定理中直接互换。

量子 $\chi^2$ 的恢复性质确实依赖所选权重；
对称 $1/2$ 权重与 RLD 的区别已有明确研究 [10](#ref-gaorecovery)。
下面给出本轮中点约定下可逐项核算的例子。

### 命题 10.4（RLD 零损失但没有共同 CPTP 恢复）

取

$$
\rho_0=\operatorname{diag}(3/4,1/4),\qquad
 \rho_1=\operatorname{diag}(1/4,3/4),\qquad
 N(X)=x_{00}P_0+x_{11}P_+.
$$

此通道的输入、输出中点均忠实，并且

<a id="eq-c90-rld-example"></a>

$$
\begin{aligned}
 J_{\mathrm{RLD,in}}&=J_{\mathrm{RLD,out}}=\frac14,\\
 J_{\mathrm{in}}&=\frac14,\qquad
 J_{\mathrm{out}}=\frac{\sqrt2}{8}<\frac14.
 \end{aligned}
\tag{10.2}
$$

不存在同时恢复 $\rho_0,\rho_1$ 的 CPTP 映射。

**证明。**
输入端 $\sigma=I/2$、$d=\mathsf Z/4$。
输出中点与半差分别为

$$
\tau=\begin{pmatrix}3/4&1/4\\1/4&1/4\end{pmatrix},
 \qquad
 e=N(d)=\frac{\mathsf Z-\mathsf X}{8}.
$$

因此 $\det\tau=1/8$、$e^2=I/32$、$\operatorname{Tr}(\tau^{-1})=8$，
给出 $J_{\mathrm{RLD,out}}=1/4$。
又因 $e$ 与 $\tau-I/2=(\mathsf X+\mathsf Z)/4$ 反对易，
$e$ 在 $\tau$ 的本征基中只有非对角项。若本征值为 $t_+,t_-$，则

$$
J_{\mathrm{out}}
 =\frac{\operatorname{Tr}(e^2)}{\sqrt{t_+t_-}}
 =\frac{1/16}{\sqrt{1/8}}=\frac{\sqrt2}{8}.
$$

输入两个平方均为 $1/4$，从而得到式 [(10.2)](#eq-c90-rld-example)。

若共同恢复 $S$ 存在，令 $A=S(P_0)$、$B=S(P_+)$。
两条恢复等式给出

$$
\frac{3A+B}{4}=\rho_0,\qquad
 \frac{A+3B}{4}=\rho_1,
$$

解得 $A=P_0$、$B=P_1$。
令 $F=S^*(P_0)$，则 $0\le F\le I$，且
$\langle 0\rvert F\lvert 0\rangle=1$、$\langle +\rvert F\lvert +\rangle=0$。
正性分别迫使 $F\lvert 0\rangle=\lvert 0\rangle$、$F\lvert +\rangle=0$，与
$\langle0|+\rangle=1/\sqrt2$ 及 $F=F^\dagger$ 矛盾。

**白话图景。**这个通道把两个可分开的标签，换成两个互相重叠的量子态。
RLD 的平方恰好不变，却不能把标签共同找回来。
本轮的对称平方严格下降，准确记下这次遗漏。
权重放在关系的哪一侧，是恢复条件的一部分。

<a id="section-11"></a>

## 11. 由一对态锁住整体：qubit 的精确刚性

<a id="sec-c90-qubit-rigidity"></a>

一般而言，共同恢复只认证声明的态族。
但在二维里，不对易的二态没有足够空间隐藏另一个未认证的量子方向。
以下证明把 v88 的保忠实态结构与 v89 的乘法域直接连接起来
 [8](#ref-v88)、[9](#ref-v89)。

### 定理 11.1（qubit 不对易二态的恢复刚性）

设 $N:M_2(\mathbb C)\to M_k(\mathbb C)$ 为 CPTP，
二态中点 $\sigma>0$、$N(\sigma)>0$，并满足 C90。
若 $[\rho_0,\rho_1]\ne0$，则 Petz 恢复满足

$$
R_{\sigma,N}N=\operatorname{id}_{M_2}.
$$

即同一个恢复通道恢复整个输入矩阵代数。

**证明。**
令 $E=R_{\sigma,N}N$。
前述恢复定理给出 $E(\rho_i)=\rho_i$，因而 $E(\sigma)=\sigma$。
定义

$$
\Phi(X)=\sigma^{-1/2}
 E(\sigma^{1/2}X\sigma^{1/2})\sigma^{-1/2}.
$$

则 $\Phi$ 为 UCP，保持忠实泛函
$\phi_\sigma(X)=\operatorname{Tr}(\sigma X)$，并固定
$A=\sigma^{-1/2}\rho_0\sigma^{-1/2}$。
因为 $[\rho_0,\sigma]=[\rho_0,\rho_1]/2\ne0$，
$A$ 不是标量。在二维中写
$A=\alpha P+\beta(I-P)$，其中 $\alpha\ne\beta$，$P$ 为秩一投影。
由 $\Phi(A)=A$、$\Phi(I)=I$ 得 $\Phi(P)=P$。

固定投影的两个 Schwarz 缺额为零，所以 $P$ 属于乘法域。
在 $A$ 的本征基中，左右乘法相容迫使

$$
\begin{aligned}
 \Phi(E_{00})&=E_{00},&\Phi(E_{11})&=E_{11},\\
 \Phi(E_{01})&=\lambda E_{01},&
 \Phi(E_{10})&=\bar\lambda E_{10}.
 \end{aligned}
$$

保 $\phi_\sigma$ 给出 $(\lambda-1)\sigma_{10}=0$。
若 $\sigma_{10}=0$，则 $\sigma$ 与 $A$ 同为对角，
$\rho_0=\sigma^{1/2}A\sigma^{1/2}$ 也与 $\sigma$ 对易，矛盾。
故 $\lambda=1$、$\Phi=\operatorname{id}$，最后由可逆的夹乘变换得到
$E=\operatorname{id}$。

### 推论 11.2（同维时通道必为酉共轭）

在上述定理中若 $k=2$，则存在酉 $U$ 使 $N(X)=UXU^\dagger$。
更一般地，任意同维 CPTP 通道有 CPTP 左逆时都为酉共轭。

**证明。**
设 $A_i,B_j$ 分别为 $N,R$ 的 Kraus 算子。
恒等通道的 Choi 矩阵秩为一；其正秩一分解中的向量必须共线，
故复合通道的每个 Kraus 算子满足
$B_jA_i=c_{ji}I$。由 $R$ 保迹，

$$
A_i^\dagger A_l
 =\sum_j A_i^\dagger B_j^\dagger B_jA_l
 =\left(\sum_j\bar c_{ji}c_{jl}\right)I.
$$

这个必要条件尚未使用输入输出同维。
对正系数矩阵作酉对角化，等价地混合 Kraus 指标，可使
$A_i^\dagger A_l=p_i\delta_{il}I$。
同维时，每个 $p_i>0$ 的 $A_i$ 都可逆；
两个非零者不可能满足 $A_i^\dagger A_l=0$。
故仅剩一个非零 Kraus 算子，保迹条件使它为酉。

**白话图景。**真正的两能级系统里，两种不共用同一经典方向的状态，
已经约束了全部量子方向。
若同一过程能把这两种状态完整找回来，它就不能另藏一个被删掉的方向。
只有输入、输出空间同维时，这才进一步化为单个酉门。

### 说明 11.3（很小的二态损失不自动使整个通道接近酉）

固定 $N=E_z$、$0<z<1$，令

$$
\rho_0=\frac{I+z\mathsf Z}{2},\qquad
 \rho_1^\epsilon=\frac{I+z\mathsf Z+\epsilon\mathsf X}{2}.
$$

对充分小的 $\epsilon>0$，两态忠实且不对易；
由它们和 $I$ 可线性解出 $\mathsf X,\mathsf Z$，故生成 $M_2$。
它们的输出相同，故 $J_{\mathrm{out}}=0$。
选定 $\epsilon_0<\sqrt{1-z^2}$，则对 $0<\epsilon\le\epsilon_0$，
中点的最小本征值一致满足

$$
\lambda_{\min}(\sigma_\epsilon)\ge
 m:=\frac{1-\sqrt{z^2+\epsilon_0^2/4}}2>0.
$$

因为 $d_\epsilon=-\epsilon\mathsf X/4$，

$$
0\le\ell=J_{\mathrm{in}}
 \le\frac{\left\lVert d_\epsilon\right\rVert_2^2}{m}
 =\frac{\epsilon^2}{8m}\longrightarrow0.
$$

但对任意酉 $U$，$N(P_+)=I/2$ 与 $UP_+U^\dagger$ 的迹范数距离恒为 $1$。
所以 $N$ 始终远离每个酉通道。
问题在于两输入趋于重合，不能从小误差推出全代数的统一稳定性；
这与 v89 中近重合生成元的边界一致 [9](#ref-v89)。

<a id="section-12"></a>

## 12. 二维之外与旁参考：恢复的对象必须说清楚

<a id="sec-c90-reference-scope"></a>

### 命题 12.1（三维中不对易二态仍不足以认证全部输入）

在 $\mathbb C^3$ 中取

$$
\begin{gathered}
 P=\operatorname{diag}(1,1,0),\quad Q=I-P,
 \qquad N(X)=PXP+QXQ,\\
 \sigma=\operatorname{diag}(1/2,1/3,1/6),\qquad
 d=\frac{E_{12}+E_{21}}6,\\
 \rho_0=\sigma+d,\quad\rho_1=\sigma-d.
 \end{gathered}
$$

两态均忠实且不对易，C90 成立，但 $N$ 不存在全态恢复通道。

**证明。**
两态左上 $2\times2$ 块的行列式为 $5/36>0$，
第三个对角元为 $1/6$，故均正定。
而 $[\rho_0,\rho_1]=-(E_{12}-E_{21})/18\ne0$。
通道固定 $\rho_0,\rho_1,\sigma$，所以输入输出的 $J$ 相同。
由于 $P,Q$ 与 $\sigma$ 对易，直接代入 Petz 公式还得到 $R_{\sigma,N}=N$。
然而 $\lvert \psi_\pm\rangle=(\lvert 1\rangle\pm\lvert 3\rangle)/\sqrt2$ 的两个纯态
经 $N$ 得到同一输出，故无法共同恢复全部态。

**白话图景。**二维里没有藏身处的遗漏，到三维就能躲在另一个块之间。
眼前两态及其不对易关系可以都保住，第一维与第三维之间的相干却被删去。
二态关系能够画进有限三维图，不代表整个高维输入都已通过检查。

旁参考也必须明确包含在哪个声明里。
若 $E(\rho_i)=\rho_i$，则 $E\otimes\operatorname{id}_R$ 自动恢复

$$
\sum_i p_i\rho_i\otimes\lvert i\rangle\langle i\rvert,
$$

但不自动恢复所有与旁端口 $R$ 纠缠的状态。
例如 $E_z$ 固定 $P_0,P_1$，中点为 $I/2$，这对态满足 C90；
记 $\lvert \Phi^+\rangle=(\lvert 00\rangle+\lvert 11\rangle)/\sqrt2$，它对 Bell 态却给出

$$
(E_z\otimes\operatorname{id})(\lvert \Phi^+\rangle\langle \Phi^+\rvert)
 =\frac{P_0\otimes P_0+P_1\otimes P_1}{2}.
$$

任何恢复该二态的 $S$ 都必须固定 $P_0,P_1$，
因此 $S\otimes\operatorname{id}$ 仍固定右侧的混合态，不能还原 Bell 态。
只有已经证明 $RN=\operatorname{id}_{M_d}$ 时，
才由线性自动得到对任意旁参考的完整恢复。

**白话图景。**旁参考可以是 $\Omega$ 内另一个保留端口。
“这两个内容能回来”与“它们和整个旁端口之间的一切联系都能回来”
是两种范围不同的声明。完全正性保证把旁端口接上后操作仍合法；
它本身不保证被删掉的关联已经恢复。

<a id="section-13"></a>

## 13. 成功分支并不等于完整回返

<a id="sec-c90-postselection"></a>

本轮 $N$ 是确定性的 CPTP 接口。
单次测量的成功分支通常只是完全正且迹不增；
成功后再除以成功概率，所得条件态映射一般非线性。
因此不能把这种归一条件映射直接代入 C90 的线性 DPI 证明。

### 命题 13.1（后选择可逆不蕴含确定性全态可逆）

取 $0<p<q<1$，定义两个成功滤波算子

$$
F=\operatorname{diag}(\sqrt p,\sqrt q),\qquad
 G=\sqrt p\,F^{-1}=\operatorname{diag}(1,\sqrt{p/q}).
$$

二者均为收缩，且对任意态 $\omega$，

$$
GF\omega F^\dagger G^\dagger=p\omega.
$$

故两次都成功时，归一后的内容完全返回，联合成功概率为 $p$。
但第一个滤波包含成功与失败的带标记通道并无全态 CPTP 左逆。

**证明。**
前半由 $GF=\sqrt pI$ 直接得到。
令 $F_f=(I-F^\dagger F)^{1/2}$，把失败也保留，确定性通道为

$$
\widehat N(\omega)=
 \lvert s\rangle\langle s\rvert\otimes F\omega F^\dagger
 +\lvert f\rangle\langle f\rvert\otimes F_f\omega F_f^\dagger.
$$

若它有全态 CPTP 左逆，前述复合 Kraus 论证的必要条件要求
每个 Kraus 算子的 $K_i^\dagger K_i$ 都为标量倍 $I$。
成功 Kraus 算子却满足
$K_s^\dagger K_s=F^\dagger F=\operatorname{diag}(p,q)$，矛盾。

成功后的条件输出为
$F\omega F^\dagger/\operatorname{Tr}(F\omega F^\dagger)$，
其分母随输入改变；对两个态分别归一后再取平均，
通常不等于先取中点再通过同一个线性通道。
若要沿用 C90，就应声明检查的是哪个确定性接口、哪些成功与失败记录，
并在该完整接口上重新核验候选。
这与项目把分支记录和保留端口纳入共同内容的约定相接
 [5](#ref-omega)、[6](#ref-record)。
这里的标记按经典记录保留；若改为保留仪器的全部相干环境，
讨论对象就是另一个更大的通道。

**白话图景。**一次回溯可以在成功分支中完整返回，同时仍有失败分支和成功概率。
返回内容、执行概率、保留记录都属于这次关系。
把成功的那条路单独归一，并不会自动把整个过程变成确定性的逆门。

<a id="section-14"></a>

## 14. 从二态恢复到稳定关系代数：接回 v88 与 v89

先固定归一忠实态 $\sigma>0$、有限维 CPTP 映射 $\mathcal N$，并设
$\tau=\mathcal N(\sigma)>0$。本节使用前文已经定义的 Petz 恢复
$\mathcal R=\mathcal R_{\sigma,\mathcal N}\equiv\mathcal R_\sigma$，
下标完整写出时同时强调所依赖的通道，不增加新的恢复公理。
记

$$
\Gamma_\sigma(X)=\sigma^{1/2}X\sigma^{1/2},\qquad
\mathcal T=\mathcal R\mathcal N,\qquad
\Phi_\sigma=\Gamma_\sigma^{-1}\mathcal T\Gamma_\sigma.
$$

$\mathcal T$ 作用于状态，$\Phi_\sigma$ 作用于加权关系坐标。
它们的固定对象不同，不能把这两个映射混为同一个状态更新。

### 命题 14.1（往返过程供应一个保态的关系接口）

$\Phi_\sigma$ 含单位、完全正，并保持
$\phi_\sigma(X)=\operatorname{Tr}(\sigma X)$。在本轮 Petz 往返情形，还有
$\Phi_\sigma=\mathcal T^*$。其不动空间
$\mathcal F=\operatorname{Fix}\Phi_\sigma$ 是含单位 $*$-子代数，且

$$
E_n=\frac1n\sum_{r=0}^{n-1}\Phi_\sigma^r
\longrightarrow E
$$

收敛到保持 $\phi_\sigma$ 的完全正条件期望，值域为 $\mathcal F$。

**证明。**
共轭映射 $\Gamma_\sigma$ 及其逆都完全正，故 $\Phi_\sigma$ 完全正。
$\mathcal T(\sigma)=\sigma$ 给 $\Phi_\sigma(I)=I$，保迹性给

$$
\operatorname{Tr}(\sigma\Phi_\sigma(X))
=\operatorname{Tr}(\mathcal T(\Gamma_\sigma(X)))=\operatorname{Tr}(\sigma X).
$$

又由 $\mathcal R=\Gamma_\sigma\mathcal N^*\Gamma_\tau^{-1}$，

$$
\Phi_\sigma=\mathcal N^*\Gamma_\tau^{-1}\mathcal N\Gamma_\sigma
=\mathcal T^*.
$$

现可应用 v89 的保忠实态固定点定理。其关键一步是：若 $X$ 不动，
正平方缺额的 $\sigma$ 期望为零；忠实性使它及 $X^\dagger$ 的缺额都为零。
故不动元位于乘法域，乘积仍不动。GNS 收缩使幂一致有界，
有限维 Cesàro 平均留下特征值一的空间；乘法域同时给极限的双模性。
这正是 v89 已证的机制，不把其一般结构重新认领为本轮发现 [9](#ref-v89)。

由 $\mathcal T^r=\Gamma_\sigma\Phi_\sigma^r\Gamma_\sigma^{-1}$，
状态端平均也收敛，极限为

$$
E_*=\Gamma_\sigma E\Gamma_\sigma^{-1}.
$$

这里 $E_*$ 是普通迹对偶；$E$ 是含单位的关系粗化，$E_*$ 是保迹的状态粗化。
本节只需这一平均结论，不把它当作免费可执行的无限重复协议。

**白话图景。**把内容送出去，再用同一内部参照接回来，会形成一个往返过程。
能够原样返回的内容，对应一套稳定关系；这些关系继续组合也仍然稳定。
于是本轮的恢复接口接到了 v89 的不动代数，再接到 v88 的相容分辨率。
三轮讨论的是同一条链上的不同问题。

<a id="section-15"></a>

## 15. 共有量子子态的精确形式

### 定理 15.1（稳定代数、参照分块与全部可恢复态）

在上述条件下，可选择同一有限载体的分解

$$
\mathcal H=\bigoplus_j(\mathcal H_{L_j}\otimes\mathcal H_{R_j}),
\qquad
\mathcal F=\bigoplus_j\bigl(B(\mathcal H_{L_j})\otimes I_{R_j}\bigr),
$$

使忠实参照具有形式

<a id="eq-v90-shared-reference"></a>

$$
\sigma=\bigoplus_j p_j\,\sigma_{L_j}\otimes\omega_{R_j},
\qquad p_j>0,\quad\sum_jp_j=1,
\tag{15.1}
$$

其中各因子均为归一忠实态。往返过程固定的*全部*密度矩阵恰好是

<a id="eq-v90-shared-family"></a>

$$
\boxed{\quad
\rho=\bigoplus_j q_j\,\rho_{L_j}\otimes\omega_{R_j},
\qquad q_j\ge0,\quad\sum_jq_j=1.
\quad}
\tag{15.2}
$$

这里 $\rho_{L_j}$ 可为任意密度矩阵；$q_j=0$ 时该因子的选取不影响状态。

**证明。**
第一步是有限矩阵子代数的标准表示。下面重述 v88 的分块论证，
以核定哪些因子真的由同一个保态粗化锁住 [8](#ref-v88)。
令 $P_j$ 为 $\mathcal F$ 的中心块投影。双模性给
$E(P_jXP_k)=P_jE(X)P_k=0$ 当 $j\ne k$。
保态性随即使 $\sigma$ 的跨块矩阵元为零。

在第 $j$ 块，$E(I_{L_j}\otimes Y)$ 既属于该块的可见代数，
又与全部 $X\otimes I$ 对易，故只能为 $f_j(Y)I$。
$f_j$ 为归一正泛函，可写作 $f_j(Y)=\operatorname{Tr}(\omega_{R_j}Y)$。
再用双模性得到

$$
E(X\otimes Y)=\operatorname{Tr}(\omega_{R_j}Y)\,X\otimes I.
$$

对所有 $X,Y$ 使用 $\phi_\sigma E=\phi_\sigma$，便知该块参照的所有乘积读数
都等于 $p_j\operatorname{Tr}(\sigma_{L_j}X)\operatorname{Tr}(\omega_{R_j}Y)$，从而得到
式 [(15.1)](#eq-v90-shared-reference)。整体忠实性迫使块权及两因子均忠实。

最后，$\mathcal T(\rho)=\rho$ 当且仅当
$X=\Gamma_\sigma^{-1}(\rho)\in\mathcal F$。正性使
$X=\bigoplus_j X_j\otimes I$ 且 $X_j\ge0$，故

$$
\rho=\bigoplus_j p_j\,
\sigma_{L_j}^{1/2}X_j\sigma_{L_j}^{1/2}\otimes\omega_{R_j}.
$$

把左因子的迹吸收到 $q_j$ 得式 [(15.2)](#eq-v90-shared-family)。
反向，对该式取
$X_j=(q_j/p_j)\sigma_{L_j}^{-1/2}\rho_{L_j}\sigma_{L_j}^{-1/2}$，
即可得到一个正的不动关系元，故列出的每个态都固定。

### 推论 15.2（生成全矩阵关系的二态锁住全部输入）

取 $\sigma=(\rho_0+\rho_1)/2$。若 C90 恢复 $\rho_0,\rho_1$，且
$C^*(\rho_0,\rho_1)=M_d$，则 $\mathcal R\mathcal N=\mathrm{id}_{M_d}$。

**证明。**
两态都具有式 [(15.2)](#eq-v90-shared-family) 的共同分块。
若有多个非零块，任一非平凡中心块投影都与两态对易，
这与其生成代数的交换子仅含标量矛盾。
若只有一块而 $\dim\mathcal H_R>1$，当 $\omega_R$ 非标量时，
$I_L\otimes\omega_R$ 是非标量共同对易元；
当 $\omega_R$ 为标量时，任取非标量 $I_L\otimes Y$ 仍给矛盾。
故只能有一块且右因子一维，于是 $\mathcal F=M_d$、$\Phi_\sigma=\mathrm{id}$，
经 $\Gamma_\sigma$ 还原即得结论。

该推论额外使用全矩阵生成条件；一般可恢复二态不满足它。
它推出全部输入有共同 CPTP 左逆，不把不同维数载体间的可逆编码一概称为同维酉门。

由前文恢复等价定理，固定态也恰是相对于同一 $\sigma$ 的平方损失为零的态。
因此上述结构把“多个态共享一段子态”落实为：在同一个块内，右因子
$\omega_{R_j}$ 相同，变化发生在左因子及块权上。
一般存在多个直和块，不能把它擅自改成整个载体上的一个共同张量因子。
这也不同于 N2 的“跨翼幅度残差正交”：后者是相干关系的共享充分性，
这里是指定通道和参照下的统计可恢复性 [4](#ref-n2)、[5](#ref-omega)。

### 命题 15.3（丢弃一个共同因子后的精确重建）

若 $\mathcal N=\operatorname{Tr}_R$、$\sigma=\sigma_L\otimes\omega_R>0$，则

$$
\mathcal R_{\sigma,\mathcal N}(Y)=Y\otimes\omega_R.
$$

所以所有 $\rho_L\otimes\omega_R$ 都由同一恢复保留，
而一般相关态的固定条件仍是 $\rho=(\operatorname{Tr}_R\rho)\otimes\omega_R$。

**证明。**
此时 $\tau=\sigma_L$、$\mathcal N^*(Z)=Z\otimes I_R$。
代入 Petz 公式，左右两个 $\sigma_L^{1/2}$ 分别抵消 $\sigma_L^{-1/2}$，
留下 $Y\otimes\omega_R$。固定条件由复合映射直接得到。

**白话图景。**两个内容可以各自有不同的左半部，却共同使用同一份右半部的状态规则。
如果一次压缩只丢掉这份共同部分，输出足以把它接回来。
“接回”需要实际准备这份已校准的共同子态；它没有复制任意未知内容。
若不同块共用的子态不同，地址还必须保留块的区别。

<a id="section-16"></a>

## 16. 多段压缩的逆序恢复与平方预算

### 定理 16.1（Petz 恢复按处理路径的相反次序组合）

设 $\mathcal N$ 后接 $\mathcal M$，并令
$\tau=\mathcal N\sigma$、$\upsilon=\mathcal M\tau$。
在这三个参照均忠实的声明载体上，有

<a id="eq-v90-petz-chain"></a>

$$
\boxed{\quad
\mathcal R_{\sigma,\mathcal M\mathcal N}
=\mathcal R_{\sigma,\mathcal N}\,
 \mathcal R_{\tau,\mathcal M}.
\quad}
\tag{16.1}
$$

**证明。**
用加权共轭表示，右侧等于

$$
\Gamma_\sigma\mathcal N^*\Gamma_\tau^{-1}
\Gamma_\tau\mathcal M^*\Gamma_\upsilon^{-1}
=\Gamma_\sigma(\mathcal M\mathcal N)^*\Gamma_\upsilon^{-1},
$$

恰为左侧。这个等式对全部输出算子成立；不要求各段先已无损。

现在回到本轮实际采用的内生二元问题。给两个态 $\rho_0,\rho_1$，令

$$
\sigma_0=\frac{\rho_0+\rho_1}{2},\qquad
d_0=\frac{\rho_0-\rho_1}{2}.
$$

依次施加声明的 CPTP 映射 $\mathcal N_1,\ldots,\mathcal N_m$，
定义 $\sigma_i=\mathcal N_i(\sigma_{i-1})$、$d_i=\mathcal N_i(d_{i-1})$，
并在各忠实参照载体上记

$$
J_i=\operatorname{Tr}\!\left[(\sigma_i^{-1/4}d_i\sigma_i^{-1/4})^2\right],
\qquad \ell_i=J_{i-1}-J_i\ge0.
$$

这里 $J_i$ 就是第 $i$ 段后实际二态的 $\mathcal I$。
中点随过程共同传递，因此两端相对于中点的平方距离始终同为 $J_i$。

### 定理 16.2（二元沿途损失的精确相加）

令 $\mathcal N_{[m]}=\mathcal N_m\cdots\mathcal N_1$，则

$$
J_0-J_m=\sum_{i=1}^m\ell_i.
$$

复合过程满足 C90，当且仅当每一段对其*实际到达的二元态*满足 C90。
令 $\mathcal R_i=\mathcal R_{\sigma_{i-1},\mathcal N_i}$，则对 $b=0,1$，

<a id="eq-v90-total-loss"></a>

$$
\frac12\left\|\rho_b-
(\mathcal R_1\cdots\mathcal R_m)\mathcal N_{[m]}(\rho_b)\right\|_1
\le\frac12\sqrt{\sum_{i=1}^m\ell_i}.
\tag{16.2}
$$

**证明。**
第一式逐项相消；各项非负，所以总和为零等价于每项为零。
由式 [(16.1)](#eq-v90-petz-chain) 归纳，逆序恢复的复合就是整个通道的
中点 Petz 恢复。对该复合通道套用前文主定理，其损失正是 $J_0-J_m$，
便得所列界 [10](#ref-gaorecovery)。

本轮没有要求任意通道对任意二元组都无损。
C90只认证当前声明的二元内容及过程；换一对输入，须核验相应条件。
多个阶段各自重选而不随过程传递的参照，也不能直接套用上述望远镜相消。
任何相同的后续完整实验再作用于原态与恢复态，读出差仍受迹距离界控制；
实际逆操作、记录访问及校准权限继续按项目原合同供应 [6](#ref-record)、[7](#ref-atlas)。

**白话图景。**一段地址经过几次压缩，每次损失都记在同一份中点比较账上。
这些损失正好相加；后面的合法处理不能把已经损失的区分能力凭空补回来。
返回时先接回最后一段，再接回前一段。
因此整条路径的误差可以用一笔总预算控制，而不是为每一步重新猜一个恢复规则。

<a id="section-17"></a>

## 17. 多个态共用一张恢复关系表

### 命题 17.1（固定参照下的有限态族证书）

固定同一个 $\sigma>0$、$\mathcal N$ 及 $\tau=\mathcal N\sigma>0$，
取有限态族 $\rho_1,\ldots,\rho_s$ 和严格正权重 $w_j$，$\sum_jw_j=1$。
定义

$$
\ell_j=Q_\sigma(\rho_j)-Q_\tau(\mathcal N\rho_j),\qquad
L=\sum_jw_j\ell_j.
$$

则 $L=0$ 当且仅当同一个 $\mathcal R_{\sigma,\mathcal N}$
恢复整个族 $\{\sigma,\rho_1,\ldots,\rho_s\}$。
并且

$$
\sum_jw_j\left[
\frac12\|\rho_j-\mathcal R_{\sigma,\mathcal N}\mathcal N\rho_j\|_1
\right]^2\le\frac14 L.
$$

**证明。**
每项损失非负且权重严格为正，故 $L=0$ 恰好等价于所有 $\ell_j=0$。
逐态应用同一参照的主定理；Petz 映射只依赖 $\sigma,\mathcal N$，
所以得到的是同一个恢复。反向由数据处理两次夹逼给每项零损失。
最后逐态平方误差界乘 $w_j$ 后相加即可。

这把单一二元证书推广成同一通道下的有限统计模型，既不更换 Born 规则，
也不增设另一个公理。它承接量子充分性的标准恢复结构 [10](#ref-gaorecovery)、[11](#ref-caolu)。
若不同局部问题各自更换参照、通道或恢复许可，逐个得到的
$\forall j\,\exists\mathcal R_j$ 不能直接写成已供应
$\exists\mathcal R\,\forall j$ 的共同装置；本命题正是利用同一
$\sigma$ 和同一 $\mathcal N$ 明确完成这一步。

**白话图景。**要让许多内容共享一个地址体系，不能为每个内容临时换一套解码器后就说它们已经统一。
固定共同参照和同一处理过程，再检验每个内容的平方损失，才会得到同一张恢复关系表。
表里允许内容不同，也允许结果仍有不确定性；它要求保留的是这些内容原有的全部统计区别。

<a id="section-18"></a>

## 18. 把候选写成定义间约束：有限关系理论的完整接口

<a id="sec-c90-theory"></a>

前面的证明使“完整二元代表”有了两个等价定义：
一个是单个平方等式，另一个是同一通道恢复两个态。
它们通过明示的 Petz 公式连接，而恢复又连接全部后续读出与固定关系代数。
因此本轮内生化的具体对象是*统计充分性*：不必在给出关系比较之后，
再独立输入一条“这对内容可恢复”的判断。

### 定义 18.1（有限二元可恢复关系模型）

一个本轮讨论的有限模型包含：

1. 既有内部历史标签、共同复关系核及其有限 Hilbert 载体；
         状态为该载体上的归一正算符，效果与完整读出采用已有读出接口。

2. 已声明的原生准备、混合、组合与记录过程，及其 CPTP 表示；
         对分支则保留相应完全正迹不增映射及其概率。

3. 当前指定的二元内容 $\rho_0,\rho_1$、自身中点 $\sigma$，
         以及实际要检查的转换 $\mathcal N$。

4. 用式 [(2.2)](#eq-c90-loss) 定义损失；
         以 C90 作为“该转换是这对内容的完整代表”的成员资格。
         若需要实际执行恢复，须同时给出恢复接口的原生实现。

这是一个可计算定义、推论与范围都已明确的有限理论片段。
“内部”表示准备、参照、读口、记录和恢复均在同一个声明模型内；
它不表示仅写出一个公式就已经制备了所需状态、获得未知参数，或完成任意算法。
中点与恢复依赖当前二态统计模型；它们没有依赖一个偷偷读取未知端点标签的外部操作。

### 定理 18.2（共同恢复等价于同一完整效果翻译）

若 C90 成立，则存在同一个 UCP 映射
$\mathcal R^*$，把输入端的全部效果翻译为输出端效果，并对 $b=0,1$ 满足

<a id="eq-c90-effect-translation"></a>

$$
\operatorname{Tr}(\rho_bF)
 =\operatorname{Tr}\bigl(\mathcal N(\rho_b)\mathcal R^*(F)\bigr),
 \qquad 0\le F\le I.
\tag{18.1}
$$

完整 POVM 的归一以及所有辅助矩阵级的正性都被保持。
反之，若同一个 UCP 效果翻译满足上述等式，则其迹对偶为两态的共同 CPTP 恢复，
故 C90 成立。

**证明。**
C90 给出 CPTP 的 $\mathcal R$。
其对偶 UCP，故 $0\le\mathcal R^*(F)\le I$，
且 $\sum_y\mathcal R^*(F_y)=I$ 当 $\sum_yF_y=I$。
迹对偶与 $\mathcal R\mathcal N(\rho_b)=\rho_b$ 给出等式。
反之，全部效果的实线性张成是 Hermitian 矩阵空间；
与它们的迹配对相等就迫使两个状态相等。
UCP 的迹对偶是 CPTP，故得到所需共同恢复。

这使“关系的关系”有一个具体数学对象：
$\mathcal R^*$ 本身就是把一整套读出关系连到另一套读出关系的同一个映射。
其复合与保单位条件正是读出之间必须相容的约束。
仅对每一个效果分别寻找一个无共同正性保证的替代效果，不能代替此定理。

**白话图景。**内容在一次转换后还能代表原来的内容，意思是以后关于它的整套问题仍能共同接续。
本轮证明，一个特定的平方等式恰好保证存在这张共同的翻译表。
表的来源是两份内容和当前转换自身；表与表可以组合，形成更大一层关系。
这样“恢复”“充分”“共享”成为同一内部结构的不同定义，而不是互不相关的外部口号。

<a id="section-19"></a>

## 19. 如何接回现有量子力学公理：依赖与有限证明

<a id="sec-c90-reconstruction"></a>

本轮的逻辑顺序保持明确：共同复载体、Born 读出和 CPTP 过程由项目以前各轮的
比较与组合条件建立；本轮在这些前件上证明新的恢复约束。
不能先用 CPTP 来证明 C90 的等价，再倒称 C90 单独推出 CPTP。
下表把继承部分、本轮新增部分与动力学仍需的前件分开列出。

| 标准表述 | 内部关系的前件 | 得到的结果与本轮位置 |
|---|---|---|
| 复 Hilbert 态空间 | 共同复核、全部有限 Gram 正性、零比较等价与声明张成 | 商空间及完备化；共同复结构由前序合同继承，V79 校准效果与共同 $J$ 相容 |
| 纯态与混合态 | 射线等价、归一正泛函及内部概率混合 | $\lvert \psi\rangle\langle \psi\rvert$ 与 $\rho\ge0$、$\operatorname{Tr}\rho=1$；中点是二态内部混合 |
| Born 平方与效果 | V67 细分标定，或 V79 二元反向相容及共同相位锚 | $p_e=\operatorname{Tr}(\rho E_e)$、$E_e\ge0$、$\sum_eE_e=I$；本轮不改动概率规则 |
| 组合与纠缠 | 两端复关系核的独立组合、产品准备张成声明载体、共同记录及可用准备 | $\mathcal H_A\otimes\mathcal H_B$；非乘积态的关联，继承原组合合同 |
| 完整量子操作 | 仿射混合、全部辅助系统正性、全结果归一与记录表示 | CPTP 通道及 Kraus 表示；本轮用它证明平方收缩和恢复 |
| 测量后的状态 | 已指定的完全正仪器及全部分支 | 分支概率与归一条件态；POVM 本身不唯一决定扰动 |
| 可逆门 | C90 对生成全部矩阵关系的二态成立；输入输出同维 | 同一个 CPTP 左逆，继而 $\mathcal N(\rho)=U\rho U^\dagger$，这是本轮新增入口 |
| Schrödinger 动力学 | 上述酉过程、可微内部时钟及相位提升；自治还需平移组合 | $H=i\hbar\dot U U^\dagger$、$i\hbar\dot\psi=H\psi$；自治给单参数酉群 |
| 不确定性 | 正内积、自伴关系读口及 Born 期望 | Robertson 界；二态恢复完整不使单次结果确定 |
| 粗化及共有子态 | C90 恢复映射、v89 固定代数、v88 保态相容分块 | $\bigoplus_jq_j\rho_{L_j}\otimes\omega_{R_j}$；同一规范恢复全部该族 |

相关旧版前件按固定仓库文本核读 [1](#ref-v67)、[2](#ref-v79)、[3](#ref-v80)、[4](#ref-n2)、[5](#ref-omega)、[6](#ref-record)、[7](#ref-atlas)。
下面把这条链所需的有限线性代数步骤再列一次，使本稿可独立阅读。

### 命题 19.1（由共同正关系核到 Hilbert 载体）

设内部标签集为 $S$，共同复核 $K$ 满足
$K(t,s)=\overline{K(s,t)}$，且每个有限组合都有
$\sum_{s,t}\overline{c_s}K(s,t)c_t\ge0$。
则有限形式和的空间，按零范数方向取商，具有内积

$$
\left\langle\sum_sc_se_s,\sum_td_te_t\right\rangle
 =\sum_{s,t}\overline{c_s}K(s,t)d_t.
$$

若核秩有限，该商就是有限维复 Hilbert 空间。

**证明。**
正二次式通过考察 $\|x+zy\|^2\ge0$ 得到 Cauchy–Schwarz。
因而零范数元与全部向量内积为零，商上的内积与代表选取无关且正定。
有限维空间已经完备；一般情形可另作完备化。

### 命题 19.2（继承的细分标定给 Born 平方）

在已经构造的 Hilbert 载体上，设分支权 $w(r)\ge0$ 只依赖分支范数 $0\le r\le1$，
$w(1)=1$，并与任意正交细分相容：

$$
w(\sqrt{a^2+b^2})=w(a)+w(b),\quad a,b\ge0,\ a^2+b^2\le1.
$$

则在归一分支范围内 $w(r)=r^2$。

**证明。**
令 $f(x)=w(\sqrt x)$，则在 $x,y\ge0$、$x+y\le1$ 内
$f(x+y)=f(x)+f(y)$、$f(1)=1$。
非负性使 $f$ 单调；先对非负有理数得到 $f(q)=q$，
再用有理数上下夹逼得到所有 $x\in[0,1]$ 上 $f(x)=x$。
故 $w(r)=r^2$。正交细分相容是已声明的比较条件，并非由一句“归一”替代。

对完整线性分支 $M_e$，若 $\sum_eM_e^\dagger M_e=I$，便得到

$$
p_e=\|M_e\psi\|^2
 =\langle\psi,E_e\psi\rangle,\qquad E_e=M_e^\dagger M_e.
$$

再按内部混合线性延拓，得到 $p_e=\operatorname{Tr}(\rho E_e)$。
更一般的有限维归一正泛函 $f$ 可用迹配对唯一写为 $f(X)=\operatorname{Tr}(\rho X)$；
对秩一投影的正性给 $\rho\ge0$，$f(I)=1$ 给 $\operatorname{Tr}\rho=1$。
极端归一正态恰是秩一投影：秩大于一时谱分解给非平凡混合，
秩一时任何正混合的支撑均必须在同一条射线上。

独立组合核 $K_{AB}((a,b),(a',b'))=K_A(a,a')K_B(b,b')$
的商空间由乘积标签张成，并以保持内积的对应
$e_{(a,b)}\mapsto e_a\otimes e_b$ 给出张量积载体。
哪些非乘积态能被实际准备，继续由原生操作菜单规定。

**白话图景。**Hilbert 空间把所有相容的内部比较放进同一张线性表；
Born 平方让一次正交细分前后仍然使用同一份概率账；
张量积让两个独立端口的比较能够一起表达。
本轮继续问的是：这张表经过某个操作后，有哪些内容还能完整接回来。

### 命题 19.3（完全正过程、仪器与测量更新）

有限维完全正映射有表示
$\mathcal N(X)=\sum_rK_rXK_r^\dagger$；
保迹当且仅当 $\sum_rK_r^\dagger K_r=I$。
对给定仪器 $\mathcal J_e$，$\sum_e\mathcal J_e$ 保迹，
测量概率与条件态为

$$
p_e=\operatorname{Tr}\mathcal J_e(\rho),\qquad
 \rho\mid e=\frac{\mathcal J_e(\rho)}{p_e}\quad(p_e>0).
$$

效果 $E_e=\mathcal J_e^*(I)$ 满足 $\sum_eE_e=I$。

**证明。**
完全正性使 Choi 矩阵
$C_{\mathcal N}=\sum_{i,j}E_{ij}\otimes\mathcal N(E_{ij})$
为正。将其分解成有限个正秩一项，把每个向量重排成矩阵 $K_r$，
比较矩阵单位系数，即得到 Kraus 表示。
对全部 $X$ 比较迹，得到保迹充要条件。
仪器的分支迹给出非负且总和为一的概率，除以非零概率即得归一条件态。

同一组效果可以对应不同的 $\mathcal J_e$；
因此 Born 概率不会独自选定唯一测量扰动。
Lüders 更新 $P_e\rho P_e/\operatorname{Tr}(\rho P_e)$ 对应特定投影仪器，
必须保留这个仪器条件。v90 的全结果读出与恢复定理适用于相应完整通道，
不会将归一后的非线性条件态映射当作 CPTP。

### 命题 19.4（由可恢复生成关系到酉运动方程）

设同维 CPTP 过程 $\mathcal N_t$ 对某个生成 $M_d$ 的二态保持 C90。
则每个 $t$ 有酉表示 $\mathcal N_t(\rho)=U(t)\rho U(t)^\dagger$。
若已给定可微的内部时间及可微酉相位提升，令

$$
H(t)=i\hbar\dot U(t)U(t)^\dagger.
$$

则 $H(t)=H(t)^\dagger$，且

$$
i\hbar\dot\psi(t)=H(t)\psi(t),\qquad
 i\hbar\dot\rho(t)=[H(t),\rho(t)].
$$

**证明。**
前文生成代数推论给同一个全输入 CPTP 左逆；同维 Kraus 证明给酉性。
对 $UU^\dagger=I$ 微分，得到
$\dot U U^\dagger+U\dot U^\dagger=0$，故 $H$ 自伴。
对 $\psi(t)=U(t)\psi(0)$ 及 $\rho(t)=U(t)\rho(0)U(t)^\dagger$ 微分即得两式。

若另有自治的时间平移组合，并选择相容的单参数酉提升，有限维群结构给
$U(t)=e^{-itH/\hbar}$，$H$ 不随 $t$ 变。
改变相位 $U\mapsto e^{i\alpha(t)}U$ 会把
$H$ 改为 $H-\hbar\dot\alpha I$；密度态运动不受这一标量平移影响。
时间参数、作用量单位 $\hbar$ 及具体 $H$ 的谱，不由 C90 的零损失资格确定。

### 命题 19.5（不确定性保留为内部比较的约束）

对自伴 $A,B$ 与态 $\rho$，令
$\widetilde A=A-\operatorname{Tr}(\rho A)I$、$\widetilde B=B-\operatorname{Tr}(\rho B)I$。
则

$$
\Delta_\rho A\,\Delta_\rho B
 \ge\frac12|\operatorname{Tr}(\rho[A,B])|.
$$

**证明。**
取 HS 向量 $X=\widetilde A\sqrt\rho$、$Y=\widetilde B\sqrt\rho$。
其范数分别为两个标准差，内积为 $\operatorname{Tr}(\rho\widetilde A\widetilde B)$。
Cauchy–Schwarz 说明标准差乘积不小于该内积的绝对值，再取虚部，即得所示界。

**白话图景。**现有量子力学的各条标准规则，可以沿明确的依赖一条条接起来。
本轮新增加的是可逆性的一个入口：若两个态已经生成全部关系，而且共同平方区别没有损失，
操作就必须保留全部输入；同维时它就是酉门。
再给可微的内部时钟，切向变化才写成 Schrödinger 方程。
完整可逆仍允许读出结果不确定，因为保住的是整套概率关系。

<a id="section-20"></a>

## 20. 统一关系场的有限推进与本轮总图景

对每个声明的局部切口，都可以取两个内部准备、它们的中点、
一个局部转换及其平方损失。不同切口间的转换若有共同物理接口，
则本轮的复合定理使比较和恢复沿路径接续。
这提供了关系场的一个有限层接口：场中的关系变化可以用相同格式的
状态、效果、转换、恢复与损失继续描述。

在这一接口中，内容与地址的相容要求是可检验的：
把某个输出称为原二态的完整地址，就应通过 C90 或等价的共同恢复检验；
零缺额时，恢复后的全部未来完整读数一致。
有限三维证书表达当前二元 Gram 关系，但保留载体、尺度、
状态族和通道的完整数据仍然必要。

这一推进没有选择一个具体时空、局部作用量或场的谱。
若要得到连续统一场，还需证明不同分辨率下的共同极限、局部性、
相容的动力学及所需统一估计。
v89 已将平方归一、比较谱隙与物理质量隙的量词分别说明 [9](#ref-v89)。
本轮不重新展开相关新闻，而是给出这些有限接口之间可以严格组合的一步。

**白话图景。**整体里有不同的内容；每两份内容自己就能定出一个比较中点。
一次门操作可能改变内容的外观，也可能删掉区别。
若经过中点校准后的对称平方区别一分不少，同一条内部恢复规则就能把两份内容都接回来，
原来的全部后续问题也都能接续。它们共有的部分，可以在分块后写成共同子态；
几段操作的损失沿路相加，恢复按相反次序组合。
如果这两份内容已经生成整个载体的关系，完整恢复便锁住全部量子方向，同维时就是酉运动。
这就是本轮把“二元关系、关系的关系、内部锚、共享内容和可逆轨迹”接成一套有限理论的方式。

<a id="references"></a>

## 来源、版本与核读范围

<a id="ref-v67"></a>

### [1]

trureturing 项目，V67：历史脚本、内容寻址与同一整体中的量子纠缠。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_HISTORY_SCRIPTS_CONTENT_ADDRESSING_AND_QUANTUM_ENTANGLEMENT_IN_ONE_ONTIC_STATE_V67.md)。
沿用 §9.3、定理9.5的全实正交细化与平方读出证明；核读来自已经取得的固定版本文本。

<a id="ref-v79"></a>

### [2]

trureturing 项目，V79：二元反向相容、有限相位证书与量子读出重构。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_BINARY_REVERSAL_COMPATIBILITY_FINITE_PHASE_CERTIFICATES_AND_QUANTUM_READOUT_RECONSTRUCTION_V79.md)。
共同相位锚、二次效果表示及归一/二次齐次不足以独自决定效果的范围，沿用原稿明示前件。

<a id="ref-v80"></a>

### [3]

trureturing 项目，V80：全结果二元差异不扩张、有限有向锚与内生量子过程。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_ALL_OUTCOME_BINARY_DIFFERENCE_NONEXPANSION_FINITE_ORIENTED_ANCHORS_AND_ENDOGENOUS_QUANTUM_PROCESSES_V80.md)。
沿用全结果、辅助系统相容与完全正过程的既有重构接口。

<a id="ref-n2"></a>

### [4]

trureturing 项目，V78 continuation N2：共享历史充分性、最小内部补足与维数预算。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_SHARED_HISTORY_SUFFICIENCY_MINIMAL_INTERNAL_COMPLETION_AND_DIMENSION_BUDGET_N2_V78_CONTINUATION.md)。
核读 §§2.1–2.2、§7 的幅度投影、残差正交及最小补足；本轮区分相干充分性与二态统计充分性。

<a id="ref-omega"></a>

### [5]

trureturing 项目，*AURIC Omega Static Compatibility Fiber Theory*。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)。
核读 §8 的全逻辑输入纠错与互补通道恒定条件；本轮的二态恢复不无条件替代该全输入声明。

<a id="ref-record"></a>

### [6]

trureturing 项目，*Recursive Relational Observation: Minimal Record Dilations*。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MINIMAL_RECORD_DILATIONS.md)。
沿用 Theorem2.2、Assumption2.3 中实际环境记录、受控逆操作及资源访问条件。

<a id="ref-atlas"></a>

### [7]

trureturing 项目，*Quantum Origin: Endogenous Cut Atlas and Discrete Reconstruction Boundaries III*。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_III.md)。
沿用 §§12–13 的全未来菜单与逐分支自治；§21 关于无相关精确回返的范围不被本轮恢复公式绕过。

<a id="ref-v88"></a>

### [8]

本对话研究稿，*AURIC v88: Recursive Spheres and Relative Resolution Fields*，2026。
[已交付 v88 PDF](https://chatgpt.com/library?file_id=libfile_abe42acba7fc8191bad08d801bf443f2&account_id=personal)。
本轮核读双向有序比较、保忠实态条件期望、模不变性与块乘积参照的等价证明。

<a id="ref-v89"></a>

### [9]

本对话研究稿，*AURIC v89: Quadratic Closure, Recursive Stability and Quantum Field Boundaries*，2026。
沿用已交付稿的 C89 乘法域、保忠实态固定点代数与 Cesàro 条件期望；
保留比较谱隙、物理质量隙及连续场极限的区分。

<a id="ref-gaorecovery"></a>

### [10]

Li Gao, Haojian Li, Iman Marvian and Cambyse Rouzé,
*Sufficient Statistic and Recoverability via Quantum Fisher Information Metrics*,
arXiv:2302.02341 (2023).
[论文与版本记录](https://arxiv.org/abs/2302.02341)；
[全文](https://arxiv.org/pdf/2302.02341)。
核读 Lemma4.9、Theorem4.10 及 Remark4.8：对称 $1/2$ 比较的
Petz 恢复残差界，以及其他量子 Fisher 权重不能一概替换的边界。
本稿核心平方恢复界属于该已知数学结果；中点组织和项目接续不构成其优先权主张。

<a id="ref-caolu"></a>

### [11]

Yu Cao and Jianfeng Lu,
*Tensorization of the Strong Data Processing Inequality for Quantum Chi-Square Divergences*,
*Quantum* 3, 199 (2019), arXiv:1904.06562.
[论文与版本记录](https://arxiv.org/abs/1904.06562)；
[全文](https://arxiv.org/pdf/1904.06562)。
核读谱权定义与 Lemma7(ii) 的完整权算子张量相容唯一性。
本稿引用的是该有限权刻画，不把它与论文主旨的强数据处理常数张量化混为一谈。

<a id="ref-beigi"></a>

### [12]

Salman Beigi,
*Sandwiched Rényi Divergence Satisfies Data Processing Inequality*,
*Journal of Mathematical Physics* 54, 122202 (2013), arXiv:1306.5920.
[论文与版本记录](https://arxiv.org/abs/1306.5920)；
[全文](https://arxiv.org/pdf/1306.5920)。
作为复插值证明数据处理的主要方法来源；本稿对所需 $1$–$\infty$ 端点及 $2$ 范数收缩另给自足有限证明。
