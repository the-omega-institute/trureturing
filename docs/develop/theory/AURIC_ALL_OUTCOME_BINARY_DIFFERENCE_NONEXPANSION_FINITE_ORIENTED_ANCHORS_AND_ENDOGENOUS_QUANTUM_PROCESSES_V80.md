# 全结果二元差分不增公理

从有限定向锚统一重建量子读出与实际过程

AURIC v80：完整候选、解析证明及理论闭合

项目连续研究稿

2026 年 11 月 2 日

## 摘要

v79 从二元反向相容重建事件的二次读出。v80 在已经声明实际后继的接口上再推进一步：
保留全部结果，使用同一个内部强度与相位参考，
只要求任意输入相对有限四周锚的总相干差分不增加。
本稿不预设实际后继线性，也不预设各事件权重为二次形式。

主定理证明：完整强度守恒、有限方向校准和上述单边不等式，
迫使完整输出成为复线性等距。正反锚夹定交叉实部，四分之一周锚夹定虚部，
总范数排除未记录的正交余量。各结果投影随即给线性分支、
正效果、Born 形式及 v79 反向相容。
在同一已定向实际幅度接口上，这把 v78 的读出与实际后继两组约束合并为一个候选。

二元归一三维提升与主证明使用同一组比较：
每个不等式切出球内半空间，相反方向将同一关系点锁定。
完整圆形输入在各事件分支中成为椭圆，其形状矩阵之和为单位阵。
本稿接回已有的密度态、量子仪器、张量复合、锐测量与光滑动力学，
并给单位输入稳定界及平方根误差阶的解析反例。

强度的概率意义、共同复参考、实际后继与合法复合的供应继续保留既有前件。
有限锚约束比较的一端；另一端仍覆盖整个声明输入域。
全部数学结论均由文内解析证明支持，文献读取与排版不承担数学验证。

## 目录

- [1. 本轮的版本位置与完整目标](#section-1)
- [2. 基本对象：完整实际后继与同一标尺](#section-2)
- [3. 一个完整的新候选：全结果二元差分不增](#section-3)
- [4. 反着推：删去条件以后发生什么](#section-4)
- [5. 主定理：单边不等式迫使复线性等距](#section-5)
- [6. 读出与后继两组约束在这里合并](#section-6)
- [7. 二元三维提升：四个半空间锁住同一个关系点](#section-7)
- [8. 整体圆、分支椭圆与周期：一个可严格证明的图景](#section-8)
- [9. 状态、概率与观测公理怎样接入](#section-9)
- [10. 完整过程、量子仪器与标准 CP 闭包](#section-10)
- [11. 关系的关系：序贯、复合与内部参考](#section-11)
- [12. 锐测量、自伴可观测量与理想投影更新](#section-12)
- [13. 可逆历史、薛定谔形式与参数周期](#section-13)
- [14. 近似比较：单位输入的稳定性与误差阶](#section-14)
- [15. 量词与对象边界：哪些看似反例其实换了比较](#section-15)
- [16. 用新候选组成完整的有限量子理论](#section-16)
- [17. 来源位置、相邻文献与本轮新增范围](#section-17)

<a id="section-1"></a>

## 1. 本轮的版本位置与完整目标

本轮递增为 v80。核心候选可以用一句话说：

> **同一过程保留全部结果以后，相对同一组内部定向参考，
> 不能凭空放大两条历史的相干差分。**

这里的差分是同一相干参考下的向量差，含相对相位信息。
它不同于只由纯态射线决定的统计距离。
输入、结果、参考与记录都属于同一个整体 $\Omega$。

### 1.1 最新项目状态与继承范围

本轮固定公开快照为

`9bf2db5e96b1e6b9c96fdf9665ff9ec3ae0cf252`

提交时间为 2026 年 11 月 2 日 07:21:43 UTC。
此次公开 v78 综合稿已更新为 24 节扩充稿：
其第 8 节给实际后继的核下降，第 10 节已经给出有限 CP/Kraus 的反向闭包，
第 13 节处理锐测量与理想更新[1](#ref-synthesis)。
本轮继续消费这些既有成果。

与上轮固定快照相比，项目还新增了单一纯整体的设置--源关系稿，
以及可见代数、未来闭合等邻近结果[3](#ref-whole)、[4](#ref-atlas3)。
它们再次明确：整体内部的设置、记忆和来源关系必须随同协议保留；
把它们都放在 $\Omega$ 内，并不会自动给出独立性或一个只依赖被缩减状态的操作。
这正是本稿要求“同一实际过程、同一完整输入接口”的原因。

| 既有层次 | v80 的处理 |
| --- | --- |
| Q1：共同正比较、$J$、根与标尺 | 继承已经证明的供应及其明确前件 |
| v79：反向相容给二次读出 | 在本轮完整后继接口中成为推论 |
| Q3：实际输出的完整复核匹配 | 由有限定向锚与差分不增推出 |
| CP、Kraus 与记录表示 | 继续消费既有闭包；展示新入口怎样接入 |
| Q4：声明独立复合的积核 | 保留，以取得张量表示 |
| 平滑时间及具体动力学 | 由实际历史与时钟供应；不由不等式独自产生 |

Closure 已从实际输出的完整复 Gram 匹配推出线性分支[2](#ref-closure)。
本轮的增量是给出供应该匹配的更直接二元条件，并在完整输出层同时推出事件二次性。
“从关系得到线性后继”和 CP 表示本身不重新认领为首次结果。

**白话图景。**上一轮把结果概率的形状锁定了。这一轮把结果以后去了哪里也纳入同一个比较。
只要全部结果合起来没有丢失总强度，又不把相对于内部参考的差分放大，
正反参考就会把每一项交叉关系锁住。概率形式和线性过程因此一同出现。

<a id="section-2"></a>

## 2. 基本对象：完整实际后继与同一标尺

<a id="statement-2-1"></a>

#### 定义 2.1（继承的共同相干接口）

$H$ 为复维数 $d\ge1$ 的有限 Hilbert 空间，内积对第二变量线性。
它来自项目已有的正实历史核、零关系商和实际共同参考 $J$，
其中 $Jx=ix$、$J^2=-I$。
总强度为 $N(x)=\left\lVert x\right\rVert ^2$。
$\Omega$ 是包含对象、关系及合法操作的整体结构，$\Omega_0$ 是校准的单位根向量，
两者类型不同。

这项表示的实起点与有限根证书见综合稿第 3--4 节[1](#ref-synthesis)。
本稿对整个 $\Omega$ 不作有限维断言；有限维限制作用在当前声明的相干截口。

<a id="statement-2-2"></a>

#### 定义 2.2（已指定的实际结果族）

对有限结果集 $\mathcal E$，给已有共同复参考与内积的有限维复 Hilbert 输出空间 $W_e$，
以及实际幅度映射

$$
F_e:H\longrightarrow W_e.
$$

同一个 $F_e$ 用于本协议的全部输入；当前不假定它可加、齐次、连续或线性。
不同输入的输出幅度在该结果通道内具有同一个相干参考。
它们不是可逐输入任意重选相位的射线代表。

若某项记忆会返回并改变输出，它须包含在输入接口中；
若设置改变了实际过程，就要相应改变协议标识，不能在同一个 $F_e$ 中暗换设置。
实际后继与参考的供应仍是模型的明确前件。

<a id="statement-2-3"></a>

#### 定义 2.3（完整强度标定）

用同一内部标尺读取结果强度，定义

$$
w_e(x)=\left\lVert F_e(x)\right\rVert ^2.
$$

要求包含全部成功、失败、停止及声明结果的菜单满足

<a id="eq-mass"></a>

$$
\boxed{\sum_{e\in\mathcal E}\left\lVert F_e(x)\right\rVert ^2=\left\lVert x\right\rVert ^2.}\tag{2.1}
$$

因此 $F_e(0)=0$。
此时尚未要求 $w_e$ 关于输入 $x$ 为二次函数。

平方范数的概率意义使用已有的同根标定：
全部效果上的非负、归一、合法细分可加读出，纯根校准及声明准备协变[2](#ref-closure)。
本轮要推出的是事件对输入的二次依赖，而不是重新把未标定范数称为实验频率。

为记账，令

$$
W=\bigoplus_eW_e,\qquad F(x)=\bigoplus_eF_e(x).
$$

于是式[(2.1)](#eq-mass)写成 $\left\lVert F(x)\right\rVert =\left\lVert x\right\rVert$。
后文的差分比较实际为

$$
\left\lVert F(x)-F(a)\right\rVert ^2
=\sum_e\left\lVert F_e(x)-F_e(a)\right\rVert ^2.
$$

它不比较不同结果标签之间的交叉相位。
这个直和作为数学表示，不自动授予跨标签相干重合的实际控制。

**白话图景。**每个结果都有自己的后继记录，但同一结果里，不同输入留下的记录必须能用同一参考比较。
先把所有结果的强度都保留下来，再谈差分是否增加。
如果把失败记录丢掉，或者暗中换了设置，就已经换了要证明的对象。

<a id="section-3"></a>

## 3. 一个完整的新候选：全结果二元差分不增

选择声明域中可用的复正交单位框 $a_1,\ldots,a_d$。
每个种子锚有四个定向位置：

<a id="eq-anchors"></a>

$$
\mathcal A=\{a_j,ia_j,-a_j,-ia_j:1\le j\le d\}.\tag{3.1}
$$

这些方向由同一内部参考给出。

<a id="statement-3-1"></a>

#### 定义 3.1（有限四周定向校准）

要求每个结果通道在这些锚上满足

<a id="eq-orientation"></a>

$$
\boxed{F_e(i^ka_j)=i^kF_e(a_j),\qquad k=1,2,3.}\tag{3.2}
$$

等价地，每个被比较的差向量
$F_e(i^ka_j)-i^kF_e(a_j)$ 具有零强度。

它只校准有限锚，不预设所有 $x$ 的 $F_e(ix)=iF_e(x)$。
在实表示中，输出的 $i$ 是相应的已给定共同 $J_e$。

<a id="statement-3-2"></a>

#### 定义 3.2（v80 完整候选）

在上述实际输出接口中，要求完整强度标定[(2.1)](#eq-mass)、
有限四周校准[(3.2)](#eq-orientation)，以及

<a id="eq-nonexpansion"></a>

$$
\boxed{
\sum_e\left\lVert F_e(x)-F_e(a)\right\rVert ^2
\le\left\lVert x-a\right\rVert ^2,
\qquad x\in H,\ a\in\mathcal A.
}\tag{3.3}
$$

真正新增的关系条件为式[(3.3)](#eq-nonexpansion)：
同一完整过程相对于有限定向锚不增加相干差分。

两边比较的两个元是输入 $x$ 与锚历史 $a$；
每一结果中比较的是它们的两个实际后继。
该条件目前只有单边不等式，没有预先要求完整交叉核相等。

### 3.1 有限性的准确含义

第二个比较槽只取 $4d$ 个锚；第一个槽仍覆盖整个声明输入域。
因此它不是“只做有限次输入采样，就认证任意未知函数”的断言。
$4d$ 是当前四周布局的数量，不宣称绝对最小。
它也不能与 v79 的 $d(d+1)$ 个单标量效果相位探针直接比较：
本轮使用实际输出向量和全输入比较，检验的信息类型不同。

### 3.2 相位规范与实际幅度的边界

固定地将某一结果通道整体乘以一个相位，不改变候选及事件核。
逐输入任意重选相位则会改变跨输入的相干比较。
例如

$$
F(x)=e^{i\theta(x)}x,\qquad
\theta(x)=\frac{|x_1|^2}{\left\lVert x\right\rVert ^2}\quad(x\ne0)
$$

在单输入密度矩阵上总给 $F(x)F(x)^*=xx^*$，却一般不是线性幅度映射。
这说明抽象恒等密度通道，和一个已指定相干幅度提升的相容性，是不同类型的问题。
本稿的等价定理针对后者；若只给粗通道，须先声明相应细记录或幅度实现。

**白话图景。**同一把尺有正、反和两个四分之一周方向。
拿任意历史与这些参考比较，过程以后不能把差分放大。
这不是先规定门的公式，而是要求所有内部比较能沿同一过程接续。

<a id="section-4"></a>

## 4. 反着推：删去条件以后发生什么

### 4.1 强度、光滑与全部相位协变仍允许错误后继

取一个结果，$H=W=\mathbb C ^2$，定义

<a id="eq-nonlinear"></a>

$$
F(z_1,z_2)=\bigl(z_1,e^{i\pi|z_1|^2}z_2\bigr).\tag{4.1}
$$

它光滑、保范数，且对全部共同相位满足
$F(e^{i\theta}x)=e^{i\theta}F(x)$。
对标准基 $a_1=e_1,a_2=e_2$，全部四周锚都被逐点固定。

但令 $a=e_2,x=(e_1+e_2)/\sqrt2$，就有

$$
F(a)=e_2,\qquad F(x)=\frac{e_1+ie_2}{\sqrt2},
$$

<a id="eq-nonlinear-fail"></a>

$$
\left\lVert x-a\right\rVert ^2=2-\sqrt2,\qquad
\left\lVert F(x)-F(a)\right\rVert ^2=2.\tag{4.2}
$$

失败精确落在这一对输入上。
它还显示：即使一个过程在所有基锚与相位方向上正常，
对合成输入的差分约束仍不可省略。

### 4.2 只有不增，整圆仍可被折叠

在 $\mathbb C \cong\mathbb R ^2$ 上定义

<a id="eq-fold"></a>

$$
F(x+iy)=|x|+i|y|.\tag{4.3}
$$

它保范数，而且对任意两点都有

$$
|F(z)-F(w)|^2
=(|x|-|x'|)^2+(|y|-|y'|)^2
\le|z-w|^2.
$$

但 $F(-1)=F(1)$、$F(-i)=F(i)$。
它甚至通过 $F(i)=iF(1)$，所以只检查一个四分之一周等式不够。
相对于参考 $1$，输入圆被变成

$$
(\cos\theta,\sin\theta)\longmapsto
(|\cos\theta|,|\sin\theta|).
$$

四周定向校准禁止这种把相反方向叠在一起的行为。

复共轭 $F(z)=\overline z$ 则保持所有实距离，却反转复方向：
$F(iz)=-iF(z)$。它说明精确实等距也需要共同方向约束。

### 4.3 完整性承担什么

若不保留全部强度，零映射满足四周方向和所有差分不增，却把全部输入送为零。
更一般地，$F(x)=cx$、$0<c<1$ 也通过不增条件。
因此完整强度守恒的作用是排除未记入的损失；一个实际损失结果应作为菜单中的结果保留。

**白话图景。**光滑、不丢总强度，仍能在合成输入处悄悄转歪关系。
只要求差分不增加，又允许把整圆折起来。
把完整强度和四个方向一起保留后，放大、折叠与漏记三种自由度才同时被约束住。

<a id="section-5"></a>

## 5. 主定理：单边不等式迫使复线性等距

<a id="statement-5-1"></a>

#### 定理 5.1（有限定向锚的完整记录刚性）

设 $F:H\to W$ 满足定义[3.2](#statement-3-2)，$\dim_{\mathbb C }H=d$。
则存在唯一复线性等距 $V:H\to W$，使

<a id="eq-isometry"></a>

$$
\boxed{F(x)=Vx\quad(x\in H),\qquad V^*V=I.}\tag{5.1}
$$

特别地，完整二元距离、复内积、可加性、齐次性与连续性全部成为结论。

**证明。**

令 $b_j=F(a_j)$。由完整强度，$\left\lVert b_j\right\rVert =1$。
将不增式展开，并使用两边已经相同的对角范数，得到

$$
\operatorname{Re} \langle b_j,F(x)\rangle \ge\operatorname{Re} \langle a_j,x\rangle .
$$

再用反向锚 $-a_j$；定向校准给 $F(-a_j)=-b_j$，
故相同展开给反向不等式。因此

$$
\operatorname{Re} \langle b_j,F(x)\rangle =\operatorname{Re} \langle a_j,x\rangle .
$$

用 $ia_j,-ia_j$，并注意
$\operatorname{Re} \langle ib_j,F(x)\rangle =\operatorname{Im} \langle b_j,F(x)\rangle$，同样得到虚部相等。
所以

<a id="eq-coordinate"></a>

$$
\boxed{\langle b_j,F(x)\rangle =\langle a_j,x\rangle \quad(1\le j\le d,\ x\in H).}\tag{5.2}
$$

取 $x=a_k$，即得 $\langle b_j,b_k\rangle =\delta_{jk}$：
输出种子框自动复正交。
按基定义复线性等距

$$
Vx=\sum_{j=1}^d\langle a_j,x\rangle \,b_j.
$$

式[(5.2)](#eq-coordinate)表明，$F(x)$ 在
$L=\operatorname{span} _{\mathbb C }\{b_1,\ldots,b_d\}$ 上的正交投影恰为 $Vx$。
但是

$$
\left\lVert F(x)\right\rVert ^2=\left\lVert x\right\rVert ^2
=\sum_j|\langle a_j,x\rangle |^2=\left\lVert Vx\right\rVert ^2.
$$

正交余量范数因此为零，得到 $F(x)=Vx$。
种子框张成输入，故该线性映射唯一。

□

<a id="statement-5-2"></a>

#### 推论 5.2（全部二元关系成为等号）

对任意 $u,v\in H$，

$$
\langle F(u),F(v)\rangle =\langle u,v\rangle ,\qquad
\left\lVert F(u)-F(v)\right\rVert ^2=\left\lVert u-v\right\rVert ^2.
$$

所有原来的锚不等式均取等号。
并且 $\dim_{\mathbb C }W\ge d$，完整输出的张成空间恰有维数 $d$。

输出的整个载体可以更大；后一个维数说的是当前输入像的张成空间，
不是所有记录寄存器的最小维数。

<a id="statement-5-3"></a>

#### 命题 5.3（单位输入版本）

若实际 $F$ 仅定义在单位球面上，完整范数、四周校准及锚不等式也只对单位输入成立，
同一证明给唯一复线性等距 $V$，使 $F(x)=Vx$ 对全部单位 $x$ 成立。

**证明。**

主证明只需把输入取为种子框，以及当前被认证的 $x$。
二者均在单位球面，坐标与范数论证保持不变。

□

此时 $V$ 给出唯一数学线性延拓；未经比较的未归一装置输出不因此自动获证。

**白话图景。**正方向要求交叉读数不能偏小，反方向又要求它不能偏大，
所以它只好相等。两个四分之一周方向再锁住另一项交叉读数。
所有坐标锁定以后，总强度不允许另藏一份正交残余。
于是后继只能沿同一个复线性等距接续。

<a id="section-6"></a>

## 6. 读出与后继两组约束在这里合并

令 $P_e$ 是直和空间 $W$ 的第 $e$ 个坐标投影。
注意它首先是记录表示中的坐标投影，不表示每个抽象投影都已成为实际控制。

<a id="statement-6-1"></a>

#### 定理 6.1（分支、效果与 Born 形式同时出现）

在 v80 条件下，定义

$$
M_e=P_eV,\qquad E_e=M_e^*M_e.
$$

则实际后继满足

<a id="eq-branches"></a>

$$
\boxed{
F_e(x)=M_ex,\qquad
0\le E_e\le I,\qquad
\sum_eE_e=I,\qquad
w_e(x)=\langle x,E_ex\rangle .
}\tag{6.1}
$$

各事件核为

$$
k_e(u,v)=\langle M_eu,M_ev\rangle =\langle u,E_ev\rangle ,
\qquad \sum_ek_e(u,v)=\langle u,v\rangle .
$$

**证明。**

$F=V$ 后取各坐标即得线性后继。
$M_e^*M_e$ 为正，且
$\sum_eM_e^*M_e=V^*V=I$，故每项不超过 $I$。
范数平方及内积展开给其余各式。

□

对非零输入，并在已有同根概率标定与声明准备范围内，

$$
p_e(x)=\frac{\langle x,E_ex\rangle }{\left\lVert x\right\rVert ^2}.
$$

这没有在证明前预置单事件的二次依赖。

<a id="statement-6-2"></a>

#### 推论 6.2（v79 及完整相干闭合成为推论）

令 $C_e(u,v)=w_e(u+v)-w_e(u)-w_e(v)$。
则

$$
C_e(u,v)=2\operatorname{Re} \langle u,E_ev\rangle ,\qquad
C_e(u,-v)=-C_e(u,v).
$$

此外

$$
C_e(u+v,z)=C_e(u,z)+C_e(v,z),
$$

$$
w_e\!\left(\sum_jx_j\right)
=\sum_jw_e(x_j)+\sum_{j<k}C_e(x_j,x_k).
$$

所有全相干三阶及更高阶差分为零。

**证明。**

由式[(6.1)](#eq-branches)作二次展开。
每个有限合成只有单项与二元交叉项，因此三阶以上包含--排除差分逐项抵消。

□

<a id="statement-6-3"></a>

#### 定理 6.3（同一实际接口上的精确等价）

在共同输入输出比较、同一幅度相位约定及完整强度等式[(2.1)](#eq-mass)下，以下三项等价：

1. v80 的有限定向锚与全输入差分不增；

2. 完整实际输出 $F$ 是复线性等距；

3. 每个实际后继 $F_e=M_e$ 复线性，且 $\sum_eM_e^*M_e=I$。

这也等价于旧 Q2/Q3 在*这些同一实际幅度输出*上给出的完备权重及完整复核匹配：
存在正效果 $E_e$，$\sum_e E_e=I$，且

$$
\langle F_e(u),F_e(v)\rangle =\langle u,E_ev\rangle
\qquad\text{对全部 }u,v\in H.
$$

**证明。**

$1\Rightarrow2$ 是主定理；$2\Rightarrow3$ 是坐标投影。
反向，将分支合成直和给 $F^*F=I$，因此全部距离取等号、全部共同相位协变，
从而 $3\Rightarrow1$。
旧完整核匹配按已有零关系下降定理给同一实际线性分支；
反向由 $\langle M_eu,M_ev\rangle =\langle u,E_ev\rangle$ 直接恢复[2](#ref-closure)、[1](#ref-synthesis)。

□

若只给抽象 POVM 或密度矩阵 CP 映射的存在，尚未指定相干幅度实现，
就不能直接使用最后一句等价。
只在一组张成历史上匹配，也只供应该组输出的唯一线性延拓；
若一个任意函数在其他输入上的实际值已经指定，
必须把那些值纳入匹配，才能证明该实际函数等于延拓。
相对于 v79 的纯数值读出接口，本轮使用了更丰富的实际后继数据；
因此这里的合并不宣称在任何接口上都逻辑更弱。

**白话图景。**同一条总关系先决定完整过程，再投影到每个结果，
就同时得到“这个结果发生多少”和“发生以后到哪里”。
所以反向相容、二次概率和线性后继可以放在同一个内部约束下推导，
而实际装置的后继方向仍由它自己的历史指定。

<a id="section-7"></a>

## 7. 二元三维提升：四个半空间锁住同一个关系点

对两个非同时为零的输入 $u,v$，记

$$
a=\left\lVert u\right\rVert ^2,\quad b=\left\lVert v\right\rVert ^2,\quad z=\langle u,v\rangle ,\quad s=a+b>0.
$$

将二元关系写成

<a id="eq-bloch"></a>

$$
R=\frac1s
\begin{pmatrix}a&\overline z\\z&b\end{pmatrix}
=\frac12(I+\mathbf r\cdot\boldsymbol\sigma),
\qquad
\mathbf r=\left(\frac{2\operatorname{Re}  z}{s},\frac{2\operatorname{Im}  z}{s},\frac{a-b}{s}\right).\tag{7.1}
$$

该矩阵是 Gram 矩阵的转置，仍然为正，且

$$
1-\left\lVert \mathbf r\right\rVert ^2=\frac{4(ab-|z|^2)}{s^2}\ge0.
$$

完整二元数据是 $(s,\mathbf r)$。球是每个二元截面的表示，不限制全局 $H$ 只有三维。

<a id="statement-7-1"></a>

#### 命题 7.1（差分不等式是球内半空间约束）

在主定理证明之前，完整强度已使输入二元关系和完整输出二元关系具有相同的 $a,b,s$。
写其横坐标为 $X_{\rm in},X_{\rm out}$，则

$$
\left\lVert F(u)-F(v)\right\rVert ^2=s(1-X_{\rm out}),\qquad
\left\lVert u-v\right\rVert ^2=s(1-X_{\rm in}).
$$

所以差分不增等价于 $X_{\rm out}\ge X_{\rm in}$。
当 $v$ 是已定向锚时，反向锚又给 $X_{\rm out}\le X_{\rm in}$。
两个四分之一周锚相同地锁定 $Y$，而 $Z$ 已由对角强度固定。

**证明。**

展开两项平方范数即可。
反向与四分之一周校准，使相应输出交叉项分别乘以 $-1$ 或 $\pm i$；
将这些比较拉回同一 $(X,Y,Z)$ 坐标，正好得到相反的两组半空间。

□

因此“三维关系点被锁定”与主证明中的实、虚坐标夹逼，是同一项数学约束。

<a id="figure-1"></a>

**图 1。**

```latex
\begin{figure}[htbp]
\centering
\begin{tikzpicture}[>=Latex,font=\small]
\begin{scope}[xshift=-3.55cm]
\fill[accent!7] (0,0) circle (1.35);
\draw[ink,thick] (0,0) circle (1.35);
\draw[->,ink!65] (-1.6,0)--(1.65,0) node[right] {$X$};
\draw[->,ink!65] (0,-1.55)--(0,1.65) node[above] {$Y$};
\draw[accent,dashed] (.405,-1.28)--(.405,1.28);
\draw[accent,dashed] (-1.25,.54)--(1.25,.54);
\draw[->,warm,thick] (-.9,.54)--(.29,.54);
\draw[->,warm,thick] (1.2,.54)--(.52,.54);
\draw[->,warm,thick] (.405,-.8)--(.405,.42);
\draw[->,warm,thick] (.405,1.2)--(.405,.66);
\fill[ink] (.405,.54) circle (2.4pt);
\node[anchor=north west] at (.47,.45) {$\mathbf r_0$};
\node[align=center,text width=5.4cm] at (0,-2.02)
{正反参考锁定 $X$\\四分之一周参考锁定 $Y$};
\end{scope}
\begin{scope}[xshift=3.55cm]
\fill[accent!7] (0,0) circle (1.35);
\draw[ink,thick] (0,0) circle (1.35);
\draw[->,ink!65] (-1.6,0)--(1.65,0) node[right] {$X$};
\draw[->,ink!65] (0,-1.55)--(0,1.65) node[above] {$Y$};
\fill[accent] (.955,0) circle (2.5pt);
\fill[warm] (0,.955) circle (2.5pt);
\draw[->,warm,thick] (.92,.15) to[bend right=20] (.15,.92);
\node[anchor=north] at (.92,-.13) {输入};
\node[anchor=east] at (-.12,.95) {失败输出};
\node[align=center,text width=5.4cm] at (0,-2.02)
{两个点都在球内\\同一关系仍可能没有匹配};
\end{scope}
\end{tikzpicture}
\caption{$Z=0$ 截面的示意。左侧把四个比较拉回同一坐标后，交点被锁定；
右侧对应式\eqref{eq:nonlinear}，关系点从 $(1/\sqrt2,0,0)$ 转到 $(0,1/\sqrt2,0)$。
失败不必表现为球外点，也可能是两个合法关系之间缺少同一性。}
\end{figure}
```

<a id="statement-7-2"></a>

#### 定理 7.2（完整菜单的带尺度重心守恒）

在 v80 结论下，对各事件定义

$$
a_e=\left\lVert M_eu\right\rVert ^2,\quad b_e=\left\lVert M_ev\right\rVert ^2,\quad
z_e=\langle M_eu,M_ev\rangle ,\quad s_e=a_e+b_e.
$$

当 $s_e>0$ 时由式[(7.1)](#eq-bloch)定义 $R_e,\mathbf r_e$，令 $\tau_e=s_e/s$。
忽略零 $s_e$ 的项，则

<a id="eq-bary"></a>

$$
\boxed{
\sum_e\tau_e=1,\qquad
R=\sum_e\tau_eR_e,\qquad
\mathbf r=\sum_e\tau_e\mathbf r_e.
}\tag{7.2}
$$

**证明。**

$V^*V=I$ 给各事件未归一 Gram 矩阵之和为输入 Gram 矩阵。
除以共同的 $s$，得到矩阵重心式；Pauli 坐标为线性的，给向量式。
若 $s_e=0$，两输出均为零，交叉项也为零，不定义其归一方向。

□

这个较大结构正是

$$
0\preceq k_e\preceq K,\qquad
\sum_ek_e=K,\qquad K(u,v)=\langle u,v\rangle ,
$$

即已有正核序区间 $[0,K]$ 的完备分解[2](#ref-closure)。
核正性涉及全部有限相干系数，不是逐条目大小。

**白话图景。**一条不等式只把关系限制在球的一侧，反向参考把它限制在另一侧；
两个方向合起来，就锁住一个坐标。另一对相位参考锁住第二个坐标，
总强度锁住第三个坐标。每个结果仍可拿走不同份额，但这些份额按强度合起来，
必须恢复同一个父关系。

<a id="section-8"></a>

## 8. 整体圆、分支椭圆与周期：一个可严格证明的图景

这一节把“圆与椭圆”放入明确的输入历程，而不将任意历史假定为闭轨。
设 $u,v$ 为实正交单位向量，即

$$
\left\lVert u\right\rVert =\left\lVert v\right\rVert =1,\qquad \operatorname{Re} \langle u,v\rangle =0.
$$

考虑已经声明的圆形幅度族

$$
x(t)=u\cos t+v\sin t.
$$

<a id="statement-8-1"></a>

#### 定理 8.1（圆在完整输出中保形，在事件分支中成为椭圆）

完整输出 $Vx(t)$ 仍为单位正圆。
每个未归一事件轨迹

$$
y_e(t)=M_eu\cos t+M_ev\sin t
$$

位于一个实维数至多为 $2$ 的子空间；非退化时为椭圆，
允许退化为线段或点。
令

$$
G_e=
\begin{pmatrix}
a_e&c_e\\c_e&b_e
\end{pmatrix},
\quad
a_e=\langle u,E_eu\rangle ,\quad b_e=\langle v,E_ev\rangle ,
\quad c_e=\operatorname{Re} \langle u,E_ev\rangle .
$$

则

<a id="eq-ellipsebudget"></a>

$$
\boxed{0\le G_e\le I_2,\qquad \sum_eG_e=I_2.}\tag{8.1}
$$

椭圆半轴长度的平方为

<a id="eq-axes"></a>

$$
\lambda_{e,\pm}=
\frac{a_e+b_e\pm\sqrt{(a_e-b_e)^2+4c_e^2}}2.\tag{8.2}
$$

**证明。**

$V$ 保持实内积，所以 $Vu,Vv$ 仍实正交单位。
将事件映射限制到 $\operatorname{span} _{\mathbb R }\{u,v\}$，得实线性映射
$T_e:\mathbb R ^2\to W_e$，
$T_e(\alpha,\beta)=\alpha M_eu+\beta M_ev$。
它的实 Gram 矩阵为 $T_e^*T_e=G_e$。
对 $G_e$ 作实正交对角化后，两个输出轴正交，长度分别为
$\sqrt{\lambda_{e,+}},\sqrt{\lambda_{e,-}}$，故单位圆的像为所述椭圆。
$0\le E_e\le I$ 给 $0\le G_e\le I_2$，
完备性给 $\sum_eG_e=I_2$。二阶特征方程直接给式[(8.2)](#eq-axes)。

□

<a id="statement-8-2"></a>

#### 推论 8.2（二次读出的双角周期）

同一圆形输入上的事件强度为

<a id="eq-doubleangle"></a>

$$
w_e(t)=
\frac{a_e+b_e}{2}
\,+\,\frac{a_e-b_e}{2}\cos2t
\,+\,c_e\sin2t.\tag{8.3}
$$

因此 $\pi$ 是强度的周期；非常数时其基本参数周期为 $\pi$。
完整非退化幅度圆的参数周期为 $2\pi$。

**证明。**

展开 $\left\lVert y_e(t)\right\rVert ^2$，再使用二倍角恒等式。
非常数的一阶 $\cos2t,\sin2t$ 组合的基本周期为 $\pi$。

□

正负幅度在普通纯态射线中已经识别，因此不能把幅度周期、
纯态射线周期和实际记录返回周期混成一个数。
如果 $u,v$ 在同一复直线上，射线轨迹甚至可能不动。
时间周期还需要实际时钟如何推进参数 $t$。

一个具体例子是两结果滤波：

$$
M_0=\begin{pmatrix}\sqrt3/2&0\\0&1/2\end{pmatrix},
\qquad
M_1=\begin{pmatrix}1/2&0\\0&\sqrt3/2\end{pmatrix}.
$$

输入 $x(t)=(\cos t,\sin t)$ 的两条分支分别为横长、纵长椭圆，
而

$$
w_0(t)=\frac34\cos^2t+\frac14\sin^2t,\qquad
w_1(t)=\frac14\cos^2t+\frac34\sin^2t,\qquad
w_0+w_1=1.
$$

<a id="figure-2"></a>

**图 2。**

```latex
\begin{figure}[htbp]
\centering
\begin{tikzpicture}[>=Latex,font=\small]
\begin{scope}[xshift=-4.8cm]
\draw[->,ink!45] (-1.45,0)--(1.45,0);
\draw[->,ink!45] (0,-1.45)--(0,1.45);
\draw[ink,thick] (0,0) circle (1.2);
\node[align=center,text width=4cm] at (0,-1.95)
{输入圆\\$\norm{x(t)}=1$};
\end{scope}
\begin{scope}
\draw[->,ink!45] (-1.45,0)--(1.45,0);
\draw[->,ink!45] (0,-1.45)--(0,1.45);
\draw[accent,thick] (0,0) ellipse [x radius=1.03923,y radius=.6];
\node[align=center,text width=4cm] at (0,-1.95)
{结果 $0$ 的幅度平面\\半轴 $\sqrt3/2,\ 1/2$};
\end{scope}
\begin{scope}[xshift=4.8cm]
\draw[->,ink!45] (-1.45,0)--(1.45,0);
\draw[->,ink!45] (0,-1.45)--(0,1.45);
\draw[warm,thick] (0,0) ellipse [x radius=.6,y radius=1.03923];
\node[align=center,text width=4cm] at (0,-1.95)
{结果 $1$ 的幅度平面\\半轴 $1/2,\ \sqrt3/2$};
\end{scope}
\end{tikzpicture}
\caption{两个分支图画在各自的输出幅度平面中。
形状矩阵相加为 $I_2$，所以各方向被分走的平方强度互补。
这里画的是未归一事件幅度；条件归一后的曲线需另外分析。}
\end{figure}
```

上述椭圆结论是固定线性映射对已给圆形输入的结果。
它没有把“目标偏离历史切线”单独作为椭圆判据，
也没有将条件归一后的轨迹自动称为欧氏椭圆。
历史切向、测地线与椭圆读出的既有分类继续按 v78 的前件使用[5](#ref-arcs)、[6](#ref-periods)。

**白话图景。**完整过程保住整圈；某个结果只接收这圈的一部分，于是这一份可以被压成椭圆。
一个方向被这个结果多拿走，其他结果就必须少拿走，所有形状矩阵合起来仍是原圆。
幅度转一整圈，平方读数在相反位置已经重复，所以自然出现双角周期。
这给“圆、椭圆、周期”一个有明确前提的统一解释。

<a id="section-9"></a>

## 9. 状态、概率与观测公理怎样接入

### 9.1 完整效果接口上的状态表示

<a id="statement-9-1"></a>

#### 定理 9.1（有限状态读出为密度算符；继承结构的展开）

在完整效果区间上，设同一个响应 $p$ 非负，$p(I)=1$，
并对 $E,F\ge0$、$E+F\le I$ 满足 $p(E+F)=p(E)+p(F)$。
则存在唯一密度算符 $\rho\ge0,\operatorname{Tr} \rho=1$，使

$$
p(E)=\operatorname{Tr} (\rho E).
$$

该状态空间的极端点恰为秩一投影。

**证明。**

非负与可加性先给单调性。
整数细分给有理齐次；有理数上下夹逼给效果缩放上的实齐次。
对任意 $A\ge0$，取 $t>0$ 且 $t\ge\left\lVert A\right\rVert$，定义 $\varphi(A)=t\,p(A/t)$，
齐次性使其与 $t$ 无关，并得到正锥上的可加齐次函数。
按自伴差分再作复线性延拓，得到矩阵空间的正归一线性泛函。
有限维迹配对的非退化性给唯一 Hermitian $\rho$；
在秩一投影上为非负使 $\rho\ge0$，而 $\varphi(I)=1$ 给 $\operatorname{Tr} \rho=1$。

秩大于一时，谱分解给非平凡密度凸组合。
若秩一投影是两个密度矩阵的非平凡凸组合，
在其正交补上非负性迫使两者都为零；两者支撑均在同一一维空间且迹一，
故都等于原投影。这证明极端点刻画。

□

这是综合稿已有的状态分类接口[1](#ref-synthesis)。
受限实际菜单只识别此状态空间的相应商；
最新可见代数稿专门保留了这一层区别[4](#ref-atlas3)。
这里没有把全部数学效果都当成实际可执行实验。

单位纯态 $\psi$ 的密度矩阵是 $|\psi\rangle \langle \psi|$。
两单位向量对全部效果响应相同，当且仅当它们的秩一投影相同，
也即只差整体相位。相干历史的比较仍可保留相对于别的历史的相位，
所以“同一纯态”与“同一带参考历史”也须分清。

### 9.2 同一根锁定概率的来源

已有读出合同还给

$$
p_0(P_{\Omega_0})=1,\qquad
p_h(E)=p_0(U_h^*EU_h).
$$

由状态表示，$p_0(P_{\Omega_0})=1$ 迫使根密度矩阵支撑在
$\operatorname{span} \{\Omega_0\}$，故 $p_0(E)=\langle \Omega_0,E\Omega_0\rangle$。
沿声明准备 $U_h$ 运输，得到

$$
p_h(E)=\langle U_h\Omega_0,EU_h\Omega_0\rangle .
$$

将本轮推出的 $E_e=M_e^*M_e$ 代入，
就把实际事件权重与同根 Born 概率绑定。
更一般维数下的纯根版本已由 Closure 给出，本轮只消费其有限截口[2](#ref-closure)。

**白话图景。**状态是一份足够回答后续读口的关系说明。
完整效果菜单使这份说明恰好成为密度矩阵；最纯的说明是一条复射线。
同一根的标定再把数学强度绑定到这个实际来源。
于是本轮的事件二次形式成为该来源上的概率，而不是一条悬空的数值公式。

<a id="section-10"></a>

## 10. 完整过程、量子仪器与标准 CP 闭包

<a id="statement-10-1"></a>

#### 定理 10.1（实际分支唯一决定仪器响应）

给输入密度算符 $\rho$、结果 $e$ 后的效果 $B$。
对应未归一响应为

$$
\operatorname{Tr} (\rho M_e^*BM_e)
=\operatorname{Tr} (M_e\rho M_e^*B).
$$

因此实际分支在密度算符上的表示唯一为

$$
\mathcal I_e(\rho)=M_e\rho M_e^*.
$$

它完全正；完整带标签输出保持总迹。

**证明。**

迹的循环性给响应等式，全部效果分离 Hermitian 算符，故表示唯一。
对任意有限参考空间 $R$ 和正 $X$，

$$
(\mathcal I_e\otimes\operatorname{id}_R)(X)
=(M_e\otimes I_R)X(M_e^*\otimes I_R)\ge0.
$$

所以完全正。又
$\sum_e\operatorname{Tr} (M_e\rho M_e^*)=\operatorname{Tr} (\rho\sum_eM_e^*M_e)=\operatorname{Tr} \rho$。
若输出空间各异，完整输出写作
$\bigoplus_eM_e\rho M_e^*$；
在声明的共同输出空间中实现后，才可直接对支路求和。

□

若结果 $e$ 的实际输出中还包含内部记录因子 $R_e$，
选择其正交记录框 $\{|\alpha\rangle \}$，写

$$
M_ex=\sum_\alpha M_{e\alpha}x\otimes|\alpha\rangle .
$$

忽略这份记录后，

<a id="eq-kraus"></a>

$$
\mathcal I_e(\rho)=\sum_\alpha M_{e\alpha}\rho M_{e\alpha}^*,
\qquad E_e=\sum_\alpha M_{e\alpha}^*M_{e\alpha}.\tag{10.1}
$$

每个求和内的输出空间须相同或已有指定嵌入。
若某份记忆还会返回影响后续过程，就不能在描述该未来问题时提前忽略它。
最新设置--源稿和可见代数稿都保留了这项输入充分性要求[3](#ref-whole)、[4](#ref-atlas3)。

结果概率为 $p_e=\operatorname{Tr} (\rho E_e)$；
仅在 $p_e>0$ 时定义条件后态
$\rho_e=\mathcal I_e(\rho)/p_e$。
归一化条件映射一般非线性，不与未归一 CP 映射混淆。

### 10.1 反向闭包：每个有限量子仪器都有这种数学表示

<a id="statement-10-2"></a>

#### 定理 10.2（标准有限 CP/Kraus 闭包；继承定理）

设 $\Phi$ 是有限矩阵空间间的复线性映射。
则它完全正，当且仅当存在有限算符族 $M_\alpha$，使

$$
\Phi(X)=\sum_\alpha M_\alpha X M_\alpha^*.
$$

保迹等价于 $\sum_\alpha M_\alpha^*M_\alpha=I$。
因此任何有限完备量子仪器都能通过细记录形成一个复等距 $V$，
并满足 v80 的全部精确条件。

**证明。**

给输入正交基 $|j\rangle$，令

$$
C_\Phi=\sum_{j,k}|j\rangle \langle k|\otimes\Phi(|j\rangle \langle k|).
$$

若 $\Phi$ 完全正，令
$|\Gamma\rangle =\sum_j|j\rangle \otimes|j\rangle$，
则 $C_\Phi=(\operatorname{id}\otimes\Phi) (|\Gamma\rangle \langle \Gamma|)$；
秩一正算符经该扩张仍为正，故 $C_\Phi\ge0$。
对它作谱分解并吸收正特征值，写
$C_\Phi=\sum_\alpha|v_\alpha\rangle \langle v_\alpha|$。
唯一地将 $v_\alpha$ 写成
$\sum_j|j\rangle \otimes M_\alpha|j\rangle$；
比较 $(j,k)$ 块，得到每个矩阵单位上的 Kraus 式，再由线性推广到全部 $X$。
反向，每项在任意参考扩张上仍是算符夹乘，故完全正。
对全部 $X$ 取迹给保迹刻画。
对仪器的各个结果执行同一分解，把所有 $M_{e\alpha}x$ 收集到直和，
完备性使这个映射为复等距。

□

这是项目综合稿第 10 节已纳入的标准 Choi--Kraus--Stinespring 链[1](#ref-synthesis)、[12](#ref-watrous)。
本轮复述它以闭合理论，而非认领其为新增数学结果。
反向构造给出数学实现；实际记录载体、耦合及控制的供应仍需声明。

最少 Kraus 数等于 $\operatorname{rank}  C_\Phi$：
任何 $m$ 项分解使 $C_\Phi$ 为 $m$ 个秩一正矩阵之和，故秩不超过 $m$；
谱分解则达到该数。
它与 $\operatorname{rank}  E_e$ 是不同的容量概念。
例如二态完全混合通道
$\Phi(X)=\operatorname{Tr} (X)I_2/2$ 有 $E=I_2$、$\operatorname{rank}  E=2$，
而 $C_\Phi=I_2\otimes I_2/2$ 的秩为 $4$。
完整等距像的维数、单事件的可见输入秩与被忽略记录的最小维数不能相互代替。

**白话图景。**完整记录中的线性后继，把后续读口拉回输入，就给出密度矩阵上的过程。
忽略细记录时，同一个粗结果可以包含多个线性分支；
这正是 Kraus 和完全正映射的来源。
它们没有另加一个外部观察者，记录本身仍是整体内部的一部分。

<a id="section-11"></a>

## 11. 关系的关系：序贯、复合与内部参考

### 11.1 后续读口沿实际分支拉回

<a id="statement-11-1"></a>

#### 定理 11.1（序贯过程与结果树闭合）

先实施分支 $M_e:H\to W_e$，再实施该实际输出上的完备分支族
$N_{f|e}:W_e\to Z_{ef}$。则

$$
M_{ef}=N_{f|e}M_e,\qquad
E_{ef}=M_e^*N_{f|e}^*N_{f|e}M_e,
$$

并有 $\sum_fE_{ef}=E_e$。
沿任意已声明的有限结果树迭代，在每条最大路径恰取一次的完备有限截口上，
路径效果之和为 $I$。

**证明。**

线性分支按实际历史次序复合。对第二菜单求和，

$$
\sum_fE_{ef}
=M_e^*\left(\sum_fN_{f|e}^*N_{f|e}\right)M_e
=M_e^*M_e.
$$

在有限树中逐层向根使用这项恒等式，即得完备截口结论。

□

若后续只读效果 $B$，它在输入上的意义为 $M_e^*BM_e$。
这就是读出关系再作为下一次关系的输入。
不同顺序的门不因这项闭合而相同；若过程有返回记忆，
它应保留在相应 $W_e$ 和历史前缀中。
该结果继续使用 Closure 的有限结果树机制[2](#ref-closure)。

### 11.2 独立复合给张量积；它仍有自己的关系前件

<a id="statement-11-2"></a>

#### 定理 11.2（声明积核的最小复合表示）

若两个接口的产品历史满足

$$
K_{AB}((h,k),(h',k'))
=K_A(h,h')K_B(k,k'),
$$

且这些产品历史张成复合接口，则其最小表示与
$H_A\otimes H_B$ 通过标签保持酉同构相同。

**证明。**

把 $\psi_h\otimes\phi_k$ 送到对应产品历史向量。
积核等式使每个有限复线性组合的范数保持，故零表达下降，映射良定。
它是等距；产品历史张成性使其满射，故酉。

□

这是既有 Q4 的表示定理[1](#ref-synthesis)。
v80 的差分条件不独自推出独立准备的积核假设。
在该复合接口中，若实际联合后继在产品历史上分别实行这两个分支，
则其表示为 $M_e\otimes N_f$。
一般整体向量可以是产品向量的相干和，因此纠缠自然保留。

对同一个源态 $\rho_{AB}$，另一侧的完备局部过程满足

$$
\sum_f\operatorname{Tr} \!\left[\rho_{AB}
  (A\otimes N_f^*N_f)\right]
=\operatorname{Tr} [\rho_{AB}(A\otimes I)].
$$

这给未选择结果时的局部响应不变。
若设置与源在实际整体中相关，条件源可能随设置改变；
“共处一个纯整体”并不自动给出同一条件源。
最新设置--源稿把这项差别写成了明确联合态约束[3](#ref-whole)。

### 11.3 共同方向为何与完整正性相接

仅保实距离允许共轭。若把共轭在密度矩阵上解释为转置，
它在单系统上保正，却不能作为任意内部参考上的局部操作。
取

$$
|\Phi^+\rangle =\frac{|00\rangle +|11\rangle }{\sqrt2},
\qquad
|\psi^-\rangle =\frac{|01\rangle -|10\rangle }{\sqrt2}.
$$

只在一侧转置后，

$$
\langle \psi^-,(\operatorname{id}\otimes{\rm T})
(|\Phi^+\rangle \langle \Phi^+|)\psi^-\rangle
=-\frac12.
$$

这是直接的负读出见证。
共同四周方向在幅度层排除共轭式翻转，
完整复线性分支随后保证所有参考扩张上的正性。
标准转置反例及 CP 表示的文献背景见 Watrous[12](#ref-watrous)。

**白话图景。**一次结果后的记录，可以直接成为下一次比较的输入，所有子结果加起来仍是父结果。
独立接口按已有积核规则接成张量积，相关接口保留它们实际的整体态。
共同相位方向使一处操作能与其他内部参考一起使用，而不在完整比较中产生负权重。

<a id="section-12"></a>

## 12. 锐测量、自伴可观测量与理想投影更新

本轮已得到完整量子效果形式。教材中的锐测量还可以按已有内部定义恢复。

<a id="statement-12-1"></a>

#### 定理 12.1（完整效果区间的极端点就是投影）

在 $[0,I]$ 中，不能非平凡地写成不同效果凸组合的元素恰为正交投影。
若一组投影满足 $\sum_jP_j=I$，则它们两两正交。
给各结果标定实数 $a_j$，得到

$$
A=\sum_ja_jP_j=A^*,\qquad
\mathbb E_\rho[a]=\operatorname{Tr} (\rho A).
$$

**证明。**

若效果有本征值 $0<\lambda<1$，沿对应秩一投影作足够小的正负扰动，
仍为两个不同效果，且其平均为原效果，故它不极端。
反向，设 $P=tE+(1-t)F$、$0<t<1$。
在 $\ker P$ 上非负性迫使 $E,F$ 消去该空间；
在 $\operatorname{ran}  P$ 上对 $I-P=t(I-E)+(1-t)(I-F)$ 作同样论证，
使 $E,F$ 均为恒等，故 $E=F=P$。
若 $x\in\operatorname{ran}  P_k$，
$0=\sum_{j\ne k}\langle x,P_jx\rangle =\sum_{j\ne k}\left\lVert P_jx\right\rVert ^2$，
所以不同投影的像正交。其余由实线性组合及 Born 读出得到。

□

有限维谱定理反向把自伴矩阵分解为这种锐菜单。
一般 POVM 的一阶矩也可自伴，但其平方通常不等于测量的二阶矩，
因此不能用一个自伴矩阵替代任意带标签 POVM 的全部统计[1](#ref-synthesis)。

<a id="statement-12-2"></a>

#### 定理 12.2（理想锐读出的 Lüders 形式）

设同一输入输出空间上的粗事件已具有本轮推出的 CP 表示
$\Lambda(X)=\sum_\alpha M_\alpha XM_\alpha^*$，
其效果为投影 $P$。
若每个单位 $\psi\in\operatorname{ran}  P$ 都满足
$\Lambda(|\psi\rangle \langle \psi|)=|\psi\rangle \langle \psi|$，
则

$$
\boxed{\Lambda(X)=PXP.}
$$

**证明。**

若 $P=0$，效果等式使所有 $M_\alpha=0$，结论立即成立。
以下取 $P\ne0$。
$\sum_\alpha M_\alpha^*M_\alpha=P$ 使每个 $M_\alpha$ 消去 $\ker P$。
对 $\psi\in\operatorname{ran}  P$，输出正秩一矩阵的和仍支撑在 $\operatorname{span} \{\psi\}$，
所以每个 $M_\alpha\psi$ 都与 $\psi$ 共线。
一个线性算符若保持该子空间中的每条一维直线，
用两独立向量及它们的和比较系数，可知它在整个子空间上为同一标量：
$M_\alpha=c_\alpha P$。
效果式给 $\sum_\alpha|c_\alpha|^2=1$，代回得到结论。

□

因此发生概率为 $\operatorname{Tr} (\rho P)$，非零时的条件态为
$P\rho P/\operatorname{Tr} (\rho P)$。
“本征纯态不扰动”是这类理想测量的明确内部性质。
只重复同一结果仍允许子空间内酉转动，
所以一般实际测量不必都采用 Lüders 后继。
项目已有更强的仅正映射版本，本稿使用 CP 版本作直接衔接[1](#ref-synthesis)。

已有内积结构也给不确定关系。
对单位纯态 $\psi$，令
$a=(A-\langle A\rangle)\psi$、
$b=(B-\langle B\rangle)\psi$。
Cauchy--Schwarz 给

$$
(\Delta A)^2(\Delta B)^2
\ge|\langle a,b\rangle |^2
\ge\frac14|\langle[A,B]\rangle|^2.
$$

这是同一正比较在两种读出方向上的限制，不要求另外引入一条概率规则。

**白话图景。**锐读口可以定义成再也不能由两种不同效果随机掺合出来的读口，
于是投影和自伴可观测量被选出来。
再要求已经确定属于该结果的纯态保持原状态，
理想投影更新就被唯一锁定。
一般装置仍可以在结果子空间内继续改变后继，这些改变也属于整体中的实际关系。

<a id="section-13"></a>

## 13. 可逆历史、薛定谔形式与参数周期

<a id="statement-13-1"></a>

#### 定理 13.1（同维完整单结果过程是酉过程）

若只有一个结果，输入输出为同一个有限维 $H$，且满足 v80 条件，
则 $F(x)=Ux$，其中 $U^*U=UU^*=I$。
声明过程的合成对应酉算符乘积。

**证明。**

主定理给 $U^*U=I$。
有限同维使该等距满射，故 $UU^*=I$。
实际先后接续按函数复合，因而按算符乘积表示。

□

若输入输出维数不同，只能先得到等距嵌入；不能直接将它称为同空间酉演化。

<a id="statement-13-2"></a>

#### 定理 13.2（光滑内部历史的生成元）

若实际内部时钟参数给出同一 $H$ 上的 $C^1$ 酉族 $U(t)$，
并取 $U(0)=I$，定义

$$
H(t)=i\hbar\,\dot U(t)U(t)^*.
$$

则 $H(t)=H(t)^*$，且 $\psi(t)=U(t)\psi(0)$ 满足

$$
\boxed{i\hbar\,\dot\psi(t)=H(t)\psi(t).}
$$

若另有一参数群条件，生成元为常数，且
$U(t)=e^{-itH/\hbar}$。

**证明。**

微分 $U(t)U(t)^*=I$，得
$\dot U U^*+U\dot U^*=0$。
所以 $\dot UU^*$ 反自伴，所定义的 $H(t)$ 自伴。
再用 $\dot\psi=\dot UU^*\psi$ 得方程。
群条件对两参数分别在零点求导给
$\dot U(t)=U(t)\dot U(0)=\dot U(0)U(t)$，
故 $\dot U(t)U(t)^*=\dot U(0)$，生成元固定。
有限维线性微分方程给指数式。

□

光滑性、时钟参数及具体 $H$ 均由实际历史供应，非差分不等式独自产生。
$\hbar$ 在这里是时间与生成元的单位常数，本文不预测其物理数值。
这继续采用项目对门流形与历史生成元的既有条件式推导[1](#ref-synthesis)、[7](#ref-v78)。

在自治情形，若初态占据若干能量本征方向，射线精确返回的条件是

$$
\frac{(E_j-E_k)T}{\hbar}\in2\pi\mathbb Z
$$

对所有被占据的能级对成立。
一项相对相位是圆周变量，多项相位是否共同返回取决于相应频率关系。
它们一般可以产生准周期行为。
此外，读口返回不等于带有增长记录的完整历史返回[6](#ref-periods)。

**白话图景。**完整单结果历史保持所有关系，所以在同一有限空间里表现为酉门。
若内部钟让这条历史平滑推进，薛定谔方程就是它的变化率表示。
单项相位沿圆走，多个圆是否同时回到原处，要看实际频率；
这把周期放回具体历史与时钟，而不是从一个圆的图画推断所有过程都周期。

<a id="section-14"></a>

## 14. 近似比较：单位输入的稳定性与误差阶

本节取单位输入，完整强度及四周定向校准保持精确，
只允许锚比较出现加性误差：

<a id="eq-approx"></a>

$$
\left\lVert F(x)-F(a)\right\rVert ^2
\le\left\lVert x-a\right\rVert ^2+\delta,
\qquad \left\lVert x\right\rVert =1,\ a\in\mathcal A,\quad\delta\ge0.\tag{14.1}
$$

它是一条对全部单位输入的统一界，不是抽样统计置信区间。
该规范也不把固定加性误差无条件推广到任意振幅尺度。

<a id="statement-14-1"></a>

#### 定理 14.1（一般近似锚框的极分解修复）

令 $b_j=F(a_j)$，定义线性算符 $B:H\to W$ 满足 $Ba_j=b_j$。
置

$$
\eta=\sqrt{\frac d2}\,\delta,\qquad
\kappa=\frac{d-1}{\sqrt2}\,\delta<1.
$$

在式[(14.1)](#eq-approx)的条件下，$B^*B$ 正定，

$$
U=B(B^*B)^{-1/2}
$$

为复线性等距，且对全部单位 $x$，

<a id="eq-stable"></a>

$$
\boxed{\left\lVert F(x)-Ux\right\rVert
\le L:=\min\!\left\{2,\sqrt{\kappa+2\eta}
                     +1-\sqrt{1-\kappa}\right\}.}\tag{14.2}
$$

**证明。**

对每个 $j$，四个相反方向的近似比较夹定

$$
\left|\operatorname{Re} \!\left(\langle b_j,F(x)\rangle -\langle a_j,x\rangle \right)\right|
\le\frac\delta2,\qquad
\left|\operatorname{Im} \!\left(\langle b_j,F(x)\rangle -\langle a_j,x\rangle \right)\right|
\le\frac\delta2.
$$

故

<a id="eq-coorderr"></a>

$$
\left\lVert B^*F(x)-x\right\rVert \le\sqrt{d/2}\,\delta=\eta.\tag{14.3}
$$

在 $x=a_k$ 处应用该比较。Gram 矩阵 $G=B^*B$ 对角为 $1$，
非对角元满足 $|G_{jk}|\le\delta/\sqrt2$。
Hermitian 矩阵的算符范数不超过其最大绝对行和，因而

$$
\left\lVert G-I\right\rVert \le\kappa<1.
$$

所以 $G$ 正定，$U^*U=I$。
记 $\zeta=B^*F(x)-x$。由 $\left\lVert F(x)\right\rVert =\left\lVert x\right\rVert =1$，

$$
\begin{aligned}
\left\lVert F(x)-Bx\right\rVert ^2
&=1+\langle x,Gx\rangle -2\operatorname{Re} \langle x,B^*F(x)\rangle \\
&=\langle x,(G-I)x\rangle -2\operatorname{Re} \langle x,\zeta\rangle
\le\kappa+2\eta.
\end{aligned}
$$

又由 $B=UG^{1/2}$，

$$
\left\lVert B-U\right\rVert
=\left\lVert G^{1/2}-I\right\rVert
\le1-\sqrt{1-\kappa}.
$$

最后使用三角不等式及两个单位向量距离不超过 $2$，得到式[(14.2)](#eq-stable)。

□

<a id="statement-14-2"></a>

#### 推论 14.2（输出锚已正交时的简界）

若还精确满足 $\langle b_j,b_k\rangle =\delta_{jk}$，令 $Va_j=b_j$，则

<a id="eq-exactanchorbound"></a>

$$
\boxed{\left\lVert F(x)-Vx\right\rVert
\le\min\{2,(2d)^{1/4}\sqrt\delta\}.}\tag{14.4}
$$

**证明。**

此时 $G=I$，式[(14.3)](#eq-coorderr)及上式展开给
$\left\lVert F(x)-Vx\right\rVert ^2\le2\eta=\sqrt{2d}\,\delta$。

□

上述等距 $U$ 还给一个相同标签的合法量子结果族
$\widetilde M_e=P_eU$，且
$\sum_e\widetilde M_e^*\widetilde M_e=I$。
若 $p_e(x)=\left\lVert F_e(x)\right\rVert ^2$、
$q_e(x)=\left\lVert P_eUx\right\rVert ^2$，则

<a id="eq-TV"></a>

$$
\frac12\sum_e|p_e(x)-q_e(x)|
\le\min\{1,\left\lVert F(x)-Ux\right\rVert \}\le\min\{1,L\}.\tag{14.5}
$$

证明只需记 $r_e=\left\lVert F_e(x)\right\rVert$、$s_e=\left\lVert P_eUx\right\rVert$，
用
$\sum_e|r_e^2-s_e^2| \le(\sum_e(r_e-s_e)^2)^{1/2}(\sum_e(r_e+s_e)^2)^{1/2}$，
以及第一因子不超过 $\left\lVert F(x)-Ux\right\rVert$、第二因子不超过 $2$。
这是存在一个邻近合法表示的数学结论，
不自动给出装置能够实施该修复的内部控制。

### 14.1 为什么幅度误差一般出现平方根

<a id="statement-14-3"></a>

#### 命题 14.3（平方根阶不能统一改成线性阶）

即使 $d=1$、输出锚精确、原映射在单位圆上光滑，
式[(14.1)](#eq-approx)也不能统一推出 $O(\delta)$ 的线性幅度近似。

**证明。**

取 $0<\delta<2$，$t=\delta/2$，$|z|=1$，
$h(z)=\operatorname{Im} (z^2)$，定义

$$
F_\delta(z)=
\left(\sqrt{1-th(z)^2}\,z,\sqrt t\,h(z)\right)\in\mathbb C ^2.
$$

它具有单位范数，在 $a\in\{1,i,-1,-i\}$ 上等于 $(a,0)$。
对任意这样的锚，

$$
\left\lVert F_\delta(z)-(a,0)\right\rVert ^2-|z-a|^2
=2\bigl(1-\sqrt{1-th(z)^2}\bigr)\operatorname{Re} (\bar a z)
\le2t=\delta.
$$

取 $z_0=e^{i\pi/4}$，则 $h(z_0)=h(-z_0)=1$，故

$$
F_\delta(z_0)+F_\delta(-z_0)=(0,2\sqrt t).
$$

任何实线性或复线性算符 $M$ 都满足
$Mz_0+M(-z_0)=0$。三角不等式说明至少一个点满足

$$
\left\lVert F_\delta(\pm z_0)-M(\pm z_0)\right\rVert
\ge\sqrt t=\sqrt{\delta/2}.
$$

所以本类假设下的最坏幅度误差具有不可消除的平方根阶。

□

这里的最优阶针对完整幅度；它并未声称每种固定结果概率的误差都必须同阶。
此外，此例只满足所用的有限四周校准，
并未额外假定对所有输入的精确全相位协变。

**白话图景。**严格比较把关系点锁死；允许一点误差，关系点就落在一个薄区域内。
仍能找到邻近的合法线性量子过程，但藏在正交方向的小幅度，其强度是幅度的平方。
所以强度误差很小，并不总使幅度误差同样小：一般只能保证平方根量级。
这也把“近似成立”变成可以逐项核对的数值界，而不是口头宽容。

<a id="section-15"></a>

## 15. 量词与对象边界：哪些看似反例其实换了比较

### 15.1 有限输入测试不能代替全输入条件

<a id="statement-15-1"></a>

#### 命题 15.1（有限测试集上的完美伪装）

对任意有限测试输入集，包含全部四周锚，
都存在光滑、范数保持且精确全相位协变的映射，
在所有测试点等于恒等映射，却违反全输入差分条件。

**证明。**

令 $S$ 为这些输入的平方范数构成的有限集合，特别有 $1\in S$。
取 $r>0$ 使 $r^2\notin S$，定义实多项式

$$
g(s)=\pi\,\frac{\prod_{q\in S}(s-q)^2}
                     {\prod_{q\in S}(r^2-q)^2},
\qquad
F(x)=e^{ig(\left\lVert x\right\rVert ^2)}x.
$$

测试输入上 $g(\left\lVert x\right\rVert ^2)=0$，所以 $F(x)=x$。
该映射光滑、范数保持且 $F(e^{i\theta}x)=e^{i\theta}F(x)$。
然而对任意单位锚 $a$，
$F(ra)=-ra$、$F(a)=a$，从而

$$
\left\lVert ra-a\right\rVert ^2=(r-1)^2,\qquad
\left\lVert F(ra)-F(a)\right\rVert ^2=(r+1)^2.
$$

因 $r>0$，后一距离严格增加。

□

此例针对整个 $H$ 的有限测试，不把径向反例误称为单位球上方向测试的专用反例。
无论采用全空间版还是单位球版，主定理的第一槽量词都须按实际声明保留。
要从有限采样推出该量词，必须另外供应函数类别及相应认证定理。

### 15.2 选择一个稀有结果以后，状态可以更容易区分

取 $H=\mathbb C ^3$，$0<\epsilon<1$，令

$$
\psi_0=\sqrt{1-\epsilon}|2\rangle +\sqrt\epsilon|0\rangle ,\qquad
\psi_1=\sqrt{1-\epsilon}|2\rangle +\sqrt\epsilon|1\rangle .
$$

其内积为 $1-\epsilon$。
令 $P=|0\rangle \langle 0|+|1\rangle \langle 1|$、$Q=|2\rangle \langle 2|$。
完整输出
$F(\psi)=P\psi\oplus Q\psi$
是等距，满足本轮候选。
未归一的 $P$ 分支差分平方仍为 $2\epsilon$，与输入差分相同。
但若只保留概率为 $\epsilon$ 的 $P$ 结果并重新归一，
两个条件态变成 $|0\rangle$、$|1\rangle$，其差分平方为 $2$，射线夹角为 $\pi/2$。
条件归一引入了另一个非线性步骤，
因此“条件态更容易区分”与本轮的完整幅度条件相容。

### 15.3 丢弃内部记录可以丢失局部信息

取等距

$$
V|j\rangle =|j\rangle _S|j\rangle _R,\qquad j=0,1.
$$

输入 $(|0\rangle \pm|1\rangle )/\sqrt2$ 变为两个正交的整体态
$(|00\rangle \pm|11\rangle )/\sqrt2$。
若丢弃 $R$，两者在 $S$ 上都只留下 $I/2$。
完整后继保留差分，并不表示每个局部缩减态都保留可辨认信息。
本轮的 $F$ 包含声明的实际输出及相关记录；
粗化后的密度映射与它不是同一种对象。

### 15.4 从有限截口向共同整体延拓需要相容性

若一族递增有限维子空间 $H_n$ 的并在 $H$ 中稠密，
同一个实际映射 $F$ 在每个 $H_n$ 上满足相应候选，
且输出使用同一 Hilbert 比较，则有限主定理给等距 $V_n$。
因为它们在重叠处等于同一实际 $F$，所以彼此相容。
在稠密并上定义 $Vx=V_nx$，它良定、复线性且等距，
故唯一连续延拓到 $H$ 的完备化。
若 $F$ 在稠密并之外也已有指定的实际值，
还须要求这些值与极限相容，例如要求 $F$ 连续，才能断言全域 $F=V$。
有限截口本身不排除该实际函数在并集之外被另行指定。
这个结论保留“每个有限截口均满足条件”的量词；
它没有提供覆盖无限秩整体的单个固定有限证书。
无界可观测量、定义域与连续谱的进一步分析也不由有限版本自动完成。

**白话图景。**必须说清正在比较哪个层次。
全部结果和记录都保留时，整体关系可以完整接续；
挑一个稀有结果再归一，或者丢掉一部分记录，得到的是新的比较对象。
有限锚只让参考侧变短，不会让未知输入那一侧凭空变成有限几次实验。

<a id="section-16"></a>

## 16. 用新候选组成完整的有限量子理论

### 16.1 条件式重建定理与逐项对应

<a id="statement-16-1"></a>

#### 定理 16.1（v80 有限关系量子理论的闭合）

保留项目已经声明并供应的共同正比较、实际复参考及有限相干截口；
每个实际完整过程满足定义[3.2](#statement-3-2)；
读出满足同根概率标定，并在全部效果上是同一个非负、归一且合法可加的响应；
同一效果在不同菜单中具有同一响应。
对声明独立复合保留积核、产品张成及相应实际局部作用；
对动力学保留实际平滑时钟等所需条件。
则下表中的有限量子表示成立。

| 通常的量子规则 | 表示形式 | 在本理论中的来源 |
| --- | --- | --- |
| 复状态空间与叠加 | $H$ 上的向量、射线及复线性组合 | 共同正比较的零关系商、完备化及实际 $J$；Q1 继承条件 |
| 概率态 | $\rho\ge0,\ \operatorname{Tr} \rho=1$ | 全部效果上的正、归一、合法可加响应；纯态为秩一极点 |
| 测量及 Born 形式 | $E_e\ge0,\ \sum_eE_e=I$，
$p_e=\operatorname{Tr} (\rho E_e)$ | v80 推出 $M_e$，定义 $E_e=M_e^*M_e$；
概率解释接同根读出标定 |
| 测后态与量子仪器 | $\mathcal I_e(\rho)=\sum_\alpha M_{e\alpha}\rho M_{e\alpha}^*$ | 实际分支线性与内部记录细分；
条件态在 $p_e>0$ 时除以 $p_e$ |
| 完整过程的 CP 性 | $\Phi\otimes\operatorname{id}$ 在合法复合上保正 | Kraus 形式的直接结果；
有限反向实现需实际可用的记录与控制 |
| 复合系统与纠缠 | $H_{AB}\simeq H_A\otimes H_B$ | 声明积核与产品张成；局部操作还须实际只作用相应端口 |
| 锐可观测量 | $A=\sum_\lambda\lambda P_\lambda$ | 效果区间极点是投影；锐结果赋实标签 |
| 理想投影更新 | $P\rho P/\operatorname{Tr} (\rho P)$ | 投影效果加本征纯态不扰动；非全部仪器都满足此理想条件 |
| 封闭可逆演化 | $U^*U=UU^*=I$ | 同一有限空间的完整单结果过程 |
| 薛定谔方程 | $i\hbar\dot\psi=H(t)\psi$ | 额外实际 $C^1$ 酉历史；自治群条件才给固定 $H$ |

**证明。**

主定理及分支推论供应全部 $M_e$ 与 $E_e$。
第 9 节由响应的正性与可加性给密度矩阵及迹配对，
第 10 节由细记录给 CP 仪器及有限反向矩阵表示，
第 11 节给顺序、独立复合与固定源的局部响应相容。
第 12--13 节给锐更新、酉过程及相应光滑生成元。
每一步使用的结构前件均在表中明列，因此这些规则可以在同一模型中同时成立。

□

“完整”在这里指所声明有限接口的状态、概率、操作、复合与动力学规则闭合。
实际过程供应正效果、全部形式效果上的一致响应、
以及所有这些效果或仪器的实际可实现性，是不同的要求；
本轮不从前一项自动推出后一项。
它不声称单条差分不等式决定所有物理哈密顿量、时空结构、
基本常数或无界算符的分析问题。

### 16.2 从公理词句到内部定义间的约束

现在可将一个合法过程定义为如下关系图中的相容对象：
输入历史有共同正比较；输出历史带实际结果和共同参考；
两个层次的强度标尺一致；同一差分关系能穿过过程接续。
定义[3.2](#statement-3-2)把最后一项压成有限定向参考上的不等式，
主定理说明其更大结构正是复 Hilbert 等距及其分支。

这里的“内生”具有可核查的含义。
参考锚、结果标签、仪器、记忆、来源与时钟都在 $\Omega$ 的关系结构中；
外部观察者无需再给一个无法追踪的坍缩动作。
但从“所有对象都属于 $\Omega$”这句话本身，
不能逻辑推出某一特殊关系约束必成立。
定义可以选出一种结构类，实际整体是否满足它，仍由已有的供应定理、
协议条件与可检验关系负责。把前件写进定义能使其清楚，并不能把前件消失。

同理，$\Omega$、校准根向量 $\Omega_0$ 与
状态泛函 $\omega(E)=\operatorname{Tr} (\rho E)$ 分属整体、向量、函数三种对象。
把它们区分开，才能准确表达“整体内部的某个源如何读取一个关系”。

N1 对相干桥与共同方向的供应、N2 对共享历史和最小内部补全的说明，
继续按已证明的条件使用[8](#ref-n1)、[9](#ref-n2)。
本轮不把这些供应重新改写成未解决的笼统问题；
也不以实际后继的某个抽象线性替身代替装置已指定的输出。
v80 主定理的作用正是保证这些实际值本身可以下降为同一个线性过程。

### 16.3 一段完整的白话量子描述

**白话图景。**把量子想成整体内部一套能够互相比较的历史关系。
一条历史不只有“出现多少”，还有“相对于别的历史转到哪里”。
同一个内部参考把这些方向排在一起，叠加就是把历史放到同一个比较中，
相位说明它们怎样相长或相消。
量子态是这些关系在当前截口上的表达，读口则是整体中的一个实际分支。

**白话图景。**一个过程发生以后，所有结果以及需要保留的记录仍在整体中。
本轮的约束只要求：总强度保留，并且相对正、反及两个四分之一周参考，
两条历史的差分不能凭空被放大。
正方向说不能往一边偏，反方向就说不能往另一边偏；两个四分之一周方向锁住另一分量。
所有比较锁定后，再没有多余的强度可以藏进未知方向，
所以完整过程只能以同一个线性等距接续全部历史。
每个结果只是取它的一部分，于是结果的强度自然是一个二次式，
混合来源则给密度矩阵和 Born 概率。

**白话图景。**若输入沿圆变化，完整后继仍保留这个圆。
只看一个结果，圆的两个方向可能被不同程度压缩，于是未归一的分支幅度形成椭圆。
各个结果的压缩份额加起来，恰好还原完整圆。
平方读数把正反方向读成相同强度，因而产生双角周期。
如果历史、目标和内部钟又使轨迹转向，或者包含互不相称的多项频率，
轨迹可以不闭合；圆与椭圆说明一种精确关系，并不替代实际动力学。

**白话图景。**测量也是这种内部接续：一个结果被记录下来，就用该分支描述后继；
不知道或丢弃记录，就用密度矩阵汇总。
独立端口的比较相乘，得到张量积；整体里的相关关系可以形成纠缠。
同空间中不分支的完整过程成为酉门，平滑时钟把门序列写成薛定谔方程。
因此量子规则可以串成一套关系理论，每一个公式都说明哪种内部比较必须相容，
每一个额外条件也都有明确承担它的对象。

<a id="section-17"></a>

## 17. 来源位置、相邻文献与本轮新增范围

### 17.1 固定来源与证明归属

本稿采用上述固定提交的源文本，而不是将浮动分支标题当作版本证据。
本轮核对了 50 份与闭包、读出、实际后继、历史几何、复合及设置--源问题相关的文件；
有关新增状态与旧结论的陈述以具体对应段落为依据。
这不等于逐项审查整个项目每一条证明。

本轮连续稿的前一项是 v79《二元反向相容与量子读出》；
公开仓库中本次所审的 v78 扩充综合稿仍是共同基线。
这里的 v80 是当前研究稿的递增编号，不表示已向公开仓库提交了这些内容。
全部数学论证为解析推导；未用数学程序、枚举、数值实验或形式化助手替代证明。
文件读取、排版与图形渲染仅用于来源核对和可读性检查。

### 17.2 非扩张与校准的相邻工作

项目 V49 已引用 Aaron Lax 关于非扩张与校准的工作[10](#ref-v49)、[11](#ref-lax)。
该文的当前 v2 研究 PVM 的平方根概率读出：
在 Fubini--Study／Fisher 的度量约束、正则性及本征子空间确定性校准下，
证明 PVM 的 Born 形式；该文也给出一般非 PVM POVM 中，
相应较弱条件不能唯一选出 Born 读数的反例[11](#ref-lax)。

本轮与其共享“有限校准、非扩张比较、归一量饱和产生刚性”的方法方向。
本轮的接口则是*已经指定、具有跨输入相位参考的全部实际后继幅度*，
比较相干差向量的弦长，并采用正反与四分之一周锚。
因此能够同时约束一般事件的效果和实际后继，但所掌握的数据也更多。
这既不宣称首次提出广义的“非扩张加校准”思想，
也不宣称在该文相同的弱假设下克服其 POVM 反例。

CP、Choi、Kraus 与记录表示属于既有量子信息结构[12](#ref-watrous)；
项目此前已将其纳入闭包[2](#ref-closure)、[1](#ref-synthesis)。
线性图像的椭圆与极分解也是标准线性代数。
本轮新增范围是这些结构在当前项目中的具体二元入口、
其准确实际输出量词、有限三维约束解释、分支椭圆预算及相应稳定性连接。
$4d$ 锚为充分布局，不作最少锚数或数学优先权断言。

## 来源与证明归属

<a id="ref-synthesis"></a>

**[1]**
项目公开 v78 综合稿，24 节版本。
[Endogenous Relational Quantum Theory: Unified Relational Axioms v78 Synthesis](https://github.com/the-omega-institute/trureturing/blob/9bf2db5e96b1e6b9c96fdf9665ff9ec3ae0cf252/docs/develop/theory/AURIC_ENDOGENOUS_RELATIONAL_QUANTUM_THEORY_UNIFIED_RELATIONAL_AXIOMS_V78_SYNTHESIS.md)。
重点对应第 3--4、8--13 节及动力学部分。

<a id="ref-closure"></a>

**[2]**
项目 v78 闭包稿。
[Endogenous Closure, Finite Root Certificates and Outcome Kernel Recursion](https://github.com/the-omega-institute/trureturing/blob/9bf2db5e96b1e6b9c96fdf9665ff9ec3ae0cf252/docs/develop/theory/AURIC_ENDOGENOUS_CLOSURE_FINITE_ROOT_CERTIFICATES_AND_OUTCOME_KERNEL_RECURSION_V78_CONTINUATION.md)。
重点对应第 7--10 节。

<a id="ref-whole"></a>

**[3]**
项目设置--源关系稿。
[Single Pure Whole: Setting--Source Relations](https://github.com/the-omega-institute/trureturing/blob/9bf2db5e96b1e6b9c96fdf9665ff9ec3ae0cf252/docs/develop/theory/AURIC_SINGLE_PURE_WHOLE_SETTING_SOURCE_RELATIONS_V78_CONTINUATION.md)。
重点对应假设 1.2、定义 2.1、定理 2.3 及其协议限定。

<a id="ref-atlas3"></a>

**[4]**
项目截口图册 III。
[Quantum Origin: Endogenous Cut Atlas and Discrete Reconstruction Boundaries III](https://github.com/the-omega-institute/trureturing/blob/9bf2db5e96b1e6b9c96fdf9665ff9ec3ae0cf252/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_III.md)。
重点对应第 12--16 节的可见代数与未来闭合条件。

<a id="ref-arcs"></a>

**[5]**
项目历史轨迹稿。
[History Arcs, Elliptic Readout and Endogenous Relational Closure](https://github.com/the-omega-institute/trureturing/blob/9bf2db5e96b1e6b9c96fdf9665ff9ec3ae0cf252/docs/develop/theory/AURIC_HISTORY_ARCS_ELLIPTIC_READOUT_AND_ENDOGENOUS_RELATIONAL_CLOSURE_V78_CONTINUATION.md)。

<a id="ref-periods"></a>

**[6]**
项目周期稿。
[Circles, Periods and Endogenous Clocks](https://github.com/the-omega-institute/trureturing/blob/9bf2db5e96b1e6b9c96fdf9665ff9ec3ae0cf252/docs/develop/theory/AURIC_CIRCLES_PERIODS_AND_ENDOGENOUS_CLOCKS_V78_CONTINUATION.md)。

<a id="ref-v78"></a>

**[7]**
项目 v78 门流形稿。
[Gate Manifolds, Integrable Relations, Tangent Kernels and Recursive Error](https://github.com/the-omega-institute/trureturing/blob/9bf2db5e96b1e6b9c96fdf9665ff9ec3ae0cf252/docs/develop/theory/AURIC_GATE_MANIFOLDS_INTEGRABLE_RELATIONS_TANGENT_KERNELS_AND_RECURSIVE_ERROR_V78.md)。

<a id="ref-n1"></a>

**[8]**
项目 N1。
[Coherent Bridges, Lossless Compatibility and Effective Resistance](https://github.com/the-omega-institute/trureturing/blob/9bf2db5e96b1e6b9c96fdf9665ff9ec3ae0cf252/docs/develop/theory/AURIC_COHERENT_BRIDGES_LOSSLESS_COMPATIBILITY_AND_EFFECTIVE_RESISTANCE_N1_V78_CONTINUATION.md)。

<a id="ref-n2"></a>

**[9]**
项目 N2。
[Shared History Sufficiency, Minimal Internal Completion and Dimension Budget](https://github.com/the-omega-institute/trureturing/blob/9bf2db5e96b1e6b9c96fdf9665ff9ec3ae0cf252/docs/develop/theory/AURIC_SHARED_HISTORY_SUFFICIENCY_MINIMAL_INTERNAL_COMPLETION_AND_DIMENSION_BUDGET_N2_V78_CONTINUATION.md)。

<a id="ref-v49"></a>

**[10]**
项目 V49。
[Sum--Product Powers, Quadratic Relation Closure and Normalized Lifting](https://github.com/the-omega-institute/trureturing/blob/9bf2db5e96b1e6b9c96fdf9665ff9ec3ae0cf252/docs/develop/theory/AURIC_SUM_PRODUCT_POWERS_QUADRATIC_RELATION_CLOSURE_AND_NORMALIZED_LIFTING_V49.md)。
第 20 节所附文献包含下项。

<a id="ref-lax"></a>

**[11]**
Aaron Lax.
[The Born Rule for Projective Measurements from Metric Non-Expansion and Calibration](https://arxiv.org/abs/2604.27339).
arXiv:2604.27339，v2，2026 年 7 月 23 日，24 页。
本文比较其概率度量接口与本稿的实际相干幅度接口，不主张两套假设等强。

<a id="ref-watrous"></a>

**[12]**
John Watrous.
[The Theory of Quantum Information](https://cs.uwaterloo.ca/~watrous/TQI/).
作者公开版第 2 章，尤其定理 2.22、推论 2.27 及量子仪器部分。
[第 2 章原文](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)。
用于标准 CP、Choi、Kraus、Stinespring 表示的归属与对照。

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
\usepackage{amsmath,amssymb,amsthm,mathtools}
\usepackage{xcolor,booktabs,array,tabularx,longtable}
\usepackage{fancyhdr,enumitem,hyperref,needspace,tikz}
\usetikzlibrary{arrows.meta,calc,positioning}
\definecolor{ink}{HTML}{17384A}
\definecolor{accent}{HTML}{007D86}
\definecolor{warm}{HTML}{B75B39}
\hypersetup{colorlinks=true,linkcolor=ink,urlcolor=accent,citecolor=ink,
pdftitle={AURIC v80：全结果二元差分不增公理与内生量子过程}}
\pagestyle{fancy}\fancyhf{}
\fancyhead[L]{\small AURIC / v80 / 二元差分不增}
\fancyhead[R]{\small 定义、定理、证明与白话}
\fancyfoot[C]{\thepage}
\setlength{\parindent}{1.8em}
\setlength{\parskip}{4pt}
\setlength{\emergencystretch}{3em}
\setlist{nosep,leftmargin=2em}
\renewcommand{\baselinestretch}{1.10}
\renewcommand{\contentsname}{目录}
\renewcommand{\abstractname}{摘要}
\renewcommand{\figurename}{图}
\renewcommand{\refname}{来源与证明归属}
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
\newcommand{\Rea}{\operatorname{Re}}
\newcommand{\Ima}{\operatorname{Im}}
\newcommand{\Span}{\operatorname{span}}
\newcommand{\rank}{\operatorname{rank}}
\newcommand{\ran}{\operatorname{ran}}
\newcommand{\ket}[1]{|#1\rangle}
\newcommand{\bra}[1]{\langle#1|}
\newcommand{\plain}[1]{\par\noindent\textbf{白话图景。}#1\par}
\newcommand{\repo}[2]{\href{https://github.com/the-omega-institute/trureturing/blob/9bf2db5e96b1e6b9c96fdf9665ff9ec3ae0cf252/#1}{#2}}
\title{\color{ink}\bfseries 全结果二元差分不增公理\\[6pt]
\large 从有限定向锚统一重建量子读出与实际过程\\[4pt]
AURIC v80：完整候选、解析证明及理论闭合}
\author{项目连续研究稿}
\date{2026 年 11 月 2 日}
```

```latex
\begin{document}
\maketitle
\clearpage
\setcounter{tocdepth}{1}
{\small\setlength{\parskip}{0pt}\tableofcontents}
\newpage
\begin{quote}
\end{quote}
\begin{center}\small\texttt{9bf2db5e96b1e6b9c96fdf9665ff9ec3ae0cf252}\end{center}
\begin{center}\small
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.23\textwidth}X@{}}
\toprule
\midrule
\bottomrule
\end{tabularx}
\end{center}
\begin{center}\small
\begin{longtable}{@{}>{\raggedright\arraybackslash}p{.18\textwidth}
                    >{\raggedright\arraybackslash}p{.36\textwidth}
                    >{\raggedright\arraybackslash}p{.39\textwidth}@{}}
\toprule
\midrule
\endfirsthead
\toprule
\midrule
\endhead
\bottomrule
\end{longtable}
\end{center}
\begin{thebibliography}{99}\small
\end{thebibliography}
\end{document}
```
