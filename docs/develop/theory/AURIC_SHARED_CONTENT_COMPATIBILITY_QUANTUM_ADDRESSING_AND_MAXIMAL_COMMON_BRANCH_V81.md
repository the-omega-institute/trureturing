# 共享内容相容公理

从内容寻址到量子过程与最大共同分支

AURIC v81：一个完整候选及其有限量子理论

项目连续研究稿

2026 年 11 月 2 日

## 摘要

用户提出：量子门历史是内容寻址，不同量子态可以组合、分解并共享一段量子子态。
本稿在项目已经供应的共同复比较与实际输出接口上，
把这一图景收敛为一个公理候选：
给二元历史同时加入同一份相干内容，完整输出的差分强度不增加。
完整强度守恒和有限共同复方向校准继续作为接口条件。

主定理证明：共同加项的可逆性先把不等式夹成等式，
消去共同项后得到全部距离保持；实极化和无余量论证给实际实线性，
有限四分之一周校准再给复线性等距。
因此，在继承的同根强度--概率标定下，本候选供应 v80 所需的实际后继、效果与 Born 二次读出结构。
不预设实际后继连续、可加或线性。

本稿进一步给有限幅度族的最大一致分支：
若 $D=\operatorname{span} \{x_j-x_1\}$，则 $q=P_{D^\perp}x_1$ 为规范共同幅度，
最优强度 $`t_*=\left\lVert q\right\rVert ^2`$，等价于最大可容纳的秩一共同核
$`t\mathbf1\mathbf1^*\preceq G`$。
给出全部奇异边界、广义逆公式、二元三维球图及全族不相容反例。
该结果针对同一完整相干分支，不与任意粗通道的确定性重置混淆。

内容地址、状态地址、过程地址及可读取的经典记录分别定义。
既有 V67 的地址与残余容量、N2 的共享核补全及 v78--v80 闭包继续继承；
在明确状态、复合和时钟条件下，接成完整的有限量子表示。
全部数学由解析证明支持；文件读取和排版不承担数学验证。

## 目录

- [1. 本轮位置：已有内容寻址，推进共享怎样约束过程](#section-1)
- [2. 内容地址的四个层次](#section-2)
- [3. 一个完整候选：共同内容不制造二元差分](#section-3)
- [4. 先反着推：缺少哪项，会坏在哪两个元](#section-4)
- [5. 主定理：共享相容迫使实际复线性等距](#section-5)
- [6. 有限共同增量足够；地址替换随之成立](#section-6)
- [7. 关系的关系：共同加项的轨道与二元三维提升](#section-7)
- [8. 共享子态的类型：前缀、投影、因子与正子态](#section-8)
- [9. 有限地址族的最大共同幅度](#section-9)
- [10. 共同核预算：Gram 条件、闭式与奇异边界](#section-10)
- [11. 二元共享的三维球图与最大份额](#section-11)
- [12. 逐对共享为何不保证整个内容族同时共享](#section-12)
- [13. 允许地址携带不同相位或幅度：共同签名版](#section-13)
- [14. 共享部分怎样产生圆、椭圆与周期](#section-14)
- [15. 寻址、不可复制与记录守恒由同一个等距推出](#section-15)
- [16. 怎样接出现有量子力学公理：逐项给出定义与证明](#section-16)
- [17. 完整理论的对应表与内生含义](#section-17)
- [18. 用一段完整白话描述这一门量子理论](#section-18)

<a id="section-1"></a>

## 1. 本轮位置：已有内容寻址，推进共享怎样约束过程

本轮递增为 v81。固定公开快照为

`c63ab162315fddd0801cbe9f47dbf3eda6e13360`

提交时间为 2026 年 11 月 2 日 09:47:52 UTC。
此快照已包含公开 v79 与 v80 原文[2](#ref-v79)、[1](#ref-v80)。
所以本轮直接消费它们的结论，并将入口改写为共享内容的相容条件。

V67 第 2 节已有无损递归内容地址与全未来测试商，
第 6 节已有多对一可见地址所需的内部残余记录[3](#ref-v67)。
N2 已给共享块的 Schur 补、全部收缩补全、
最小内部共享补足及其误差预算[4](#ref-n2)。
这些是当前基础，不在本稿重新认领为新增结果。
基础与记录卷第 6 节还已有正交地址的共同振幅界、
任意固定记录族的同幅提取条件，以及一般 Gram 变换判据的文献归属[5](#ref-foundations)。
本稿将这些结构进一步显式求解为非正交、含奇异 Gram 情形的最优公式。

新快照的设置--源稿还增加第 8--12 节：
在明确的十六位完整黄金菜单、ready 域、结果反馈与返回记录条件下，
给出完整源联合独立及无条件非经典见证的有限存在构造[8](#ref-whole)。
该特定菜单的供应已经取得；它并不把任意来源或任意额外返回记录自动归入同一结论。
相干重建续卷 V 则对指定原生菜单继续细化旧标签恢复与 ready 边界[9](#ref-reconstruction)。
本稿保留这些实际权限，不把一个抽象投影存在误写成已经编译好的原生门。

| 项目已有结果 | 本轮的具体增量 |
| --- | --- |
| V67：内容地址与未来商 | 区分根态地址、相干地址与整个过程地址，并让共享条件约束实际过程 |
| N2：共享核补全 | 继承正核拼接，另求一组实际幅度的最大一致分支 |
| v80：有限定向锚差分不增 | 改用共同内容加入不增；正反方向和全距离保持成为结论 |
| v78：状态、仪器、复合与动力学 | 用本轮实际等距供应读出和后继入口，保留各层已声明条件 |

本轮提出的是项目中的一个完整候选及具体消费者。
等距刚性、投影、正核与量子态变换使用已有数学结构，
不作广泛思想或标准表示定理的首次提出断言。

**白话图景。**门历史可以指向内容，但“共享内容”必须说明共享的是代码、相干幅度，
还是某个实际读口中的分支。本轮先把共享写成两端加入同一项，
再问这个共同项能否凭空制造差别；随后精确求出一组态能在同一分支里共有多少。

<a id="section-2"></a>

## 2. 内容地址的四个层次

<a id="statement-2-1"></a>

#### 定义 2.1（整体、根与声明历史）

$\Omega$ 表示整体关系结构，$\Omega_0$ 表示当前表示中的校准根向量。
已声明门历史 $h$ 的执行读出记为

$$
\psi_h=\operatorname{Exec} (h)\Omega_0.
$$

这里的环境、参考、程序与相关记忆均是整体内部的自由度。
历史是带身份的对象，执行算符与末态是它的读出；不要求从一个末态唯一反演整个历史。

对非酉事件历史也可用实际分支乘积表示，幅度可未归一。
所有允许的替代输入和历史参数，均表示同一声明接口中的关系，
不是要求多个实际整体。
整体、路径运输与未来响应商的区分沿用项目静态相容纤维理论[10](#ref-omega)。

<a id="statement-2-2"></a>

#### 定义 2.2（地址类型）

分别定义：

1. **结构内容地址**：规范代码或展开内容相同。若实例身份、端口或物理别名也有作用，须计入这些信息。

2. **相干状态地址**：$\psi_h=\psi_k$，包含相对于共同参考的相位。

3. **射线状态地址**：非零向量归一化后相差单位相位；未归一强度如需保留，须另行记录。该地址只足以描述未加入额外相干参考的纯态读出。

4. **过程地址**：两个实际映射在整个声明输入域相同；仅在根上相同不足以成立。

结构地址与未来充分商已在 V67 证明[3](#ref-v67)。
未来充分性始终相对于固定的允许续接、读口、相干参考与操作合法域。
改变未来菜单时，原来的地址可能需要补足。

<a id="statement-2-3"></a>

#### 命题 2.3（根态同址只保证共同后续相容）

若 $U\Omega_0=V\Omega_0$，则对同一个允许后续映射 $W$，
$WU\Omega_0=WV\Omega_0$。
但不能由此推出 $U=V$，也不能在任意新输入上互换这两个过程。

**证明。**

第一句是函数在相同输入上的相同取值。
第二句取 $\Omega_0=|0\rangle$、$U=I$、$V=Z$。
有 $U|0\rangle =V|0\rangle =|0\rangle$，
而 $U|+\rangle =|+\rangle$、$V|+\rangle =|-\rangle$。

□

若把一个相干分支的输出逐输入重选相位，
可能保持每个输出的密度矩阵，却改变不同输入之间的相干差分。
因此本稿所有实际幅度比较都先固定跨输入的参考。
结构相同、状态相同和整个过程相同，均有自己的可替换范围。

**白话图景。**门历史像指向内容的路线。同一内容可以由不同路线到达；
到达同一完整内容以后，接上同一个后续，结果一致。
但两条路线在当前根上到达同一点，不表示它们作为门对所有输入都做同一件事。
地址必须与它承诺保留的未来关系一起定义。

<a id="section-3"></a>

## 3. 一个完整候选：共同内容不制造二元差分

<a id="statement-3-1"></a>

#### 定义 3.1（继承的相干接口）

取有限复 Hilbert 空间 $H$，$\dim_\mathbb C  H=d\ge1$，
内积对第二变量线性，共同方向为 $J=i$。
正比较、相干组合及共同 $J$ 使用项目 Q1 的既有供应[7](#ref-synthesis)、[6](#ref-closure)。
有限维限制作用在本次截口，不限制整个 $\Omega$。

对有限结果集 $\mathcal E$，给带共同相干参考的有限复 Hilbert 输出空间 $W_e$，
并给*已经指定的实际映射*

$$
F_e:H\longrightarrow W_e.
$$

目前不假定任何 $F_e$ 连续、可加、齐次或线性。
所有实际输入采用同一协议；会返回并改变输出的记忆必须包含在输入中。
令

$$
F=\bigoplus_eF_e,\qquad
D_F(x,y)=\sum_e\left\lVert F_e(x)-F_e(y)\right\rVert ^2.
$$

直和只是对同标签比较求和，不授予跨结果标签相干合并的控制。

<a id="statement-3-2"></a>

#### 定义 3.2（完整强度与有限共同方向）

保留完整强度标定

<a id="eq-mass"></a>

$$
\boxed{\sum_e\left\lVert F_e(x)\right\rVert ^2=\left\lVert x\right\rVert ^2\qquad(x\in H).}\tag{3.1}
$$

选择复正交单位基 $a_1,\ldots,a_d$，只要求 $d$ 项方向校准：

<a id="eq-J"></a>

$$
\boxed{F(ia_j)=iF(a_j),\qquad 1\le j\le d.}\tag{3.2}
$$

它等价于每个结果分量满足同一式。

式[(3.1)](#eq-mass)包含全部成功、失败、停止和声明记录结果，故 $F(0)=0$。
概率意义继续采用同根读出标定；本轮推出的是实际分支对输入的二次依赖。

<a id="statement-3-3"></a>

#### 定义 3.3（v81 共享内容相容候选）

在定义[3.2](#statement-3-2)的接口中，要求

<a id="eq-shared"></a>

$$
\boxed{
D_F(x+c,y+c)\le D_F(x,y),
\qquad x,y,c\in H.
}\tag{3.3}
$$

被比较的两个元是 $(x,y)$；$c$ 是同时加入两端的共享相干内容。
条件约束该二元关系在共同扩展下的变化。

同一相干内容的加入与减去是当前幅度接口中的关系操作，
没有预设 $F(x+c)=F(x)+F(c)$。
这是一个定义间的相容约束，不是预先写入后继的加法公式。

本候选在完整的*未归一幅度域*上表述。
单位球面不在共同加法下封闭；
若分别把 $x+c,y+c$ 重新归一，得到的是另一个关系。
同样，声明相干组合不等于已经供应一个接收两个任意未知量子态、
并确定性输出其归一化和的通用装置。

**白话图景。**两条内容原来有多少差别，给它们同时加上同一段带方向的内容，
这段共同内容就不应凭空制造更多剩余差别。
这里比较的是完整幅度，所有结果和记录都保留。
“同一段”包括同一相位与同一标尺，否则加到两边的本来就不是同一项。

<a id="section-4"></a>

## 4. 先反着推：缺少哪项，会坏在哪两个元

### 4.1 保强度和方向仍可能扭转共同内容

在 $H=\mathbb C ^2$ 上取一个结果：

$$
F(z_1,z_2)=\bigl(z_1,e^{i\pi|z_1|^2}z_2\bigr).
$$

它光滑、保范数，满足全局相位协变，
并通过标准基的全部方向校准。
取

$$
a=e_2,\qquad x=\frac{e_1+e_2}{\sqrt2}.
$$

先比较二元历史 $(x-a,0)$。由范数保持，

$$
D_F(x-a,0)=\left\lVert x-a\right\rVert ^2=2-\sqrt2.
$$

同时加入共同内容 $c=a$，变成 $(x,a)$，
但 $F(x)=(e_1+ie_2)/\sqrt2$、$F(a)=e_2$，所以

$$
\boxed{D_F(x,a)=2>2-\sqrt2.}
$$

失败的二元对及共同扩展都被直接定位。

### 4.2 方向校准与完整性各自承担什么

若删去式[(3.2)](#eq-J)，复共轭 $F(z)=\bar z$ 保强度并满足共享差分等号，
但反转共同复方向。
若删去式[(3.1)](#eq-mass)，零映射满足共同内容相容和方向校准，
却抹去全部强度。它们分别说明共同方向与完整标尺不能省去。

另一个精确边界是，只允许实方向的共同内容也不足：

$$
F(x+iy)=x+i|y|.
$$

它保范数，$F(i)=iF(1)$，对全部实 $c$ 满足共享差分等号，
却把负虚轴折叠到正虚轴。
共同内容的比较也必须覆盖相干接口的两个正交方向，
或另有足够的全局方向条件。

**白话图景。**非线性扭转可以把同一段共同内容，变成两端不同的附加作用；
共轭则把共同方向翻过来；零映射把所有内容漏掉。
这些反例说明，本轮每个条件都有具体工作：
共享条件管关系接续，方向校准管复方向，总强度管完整记录。

<a id="section-5"></a>

## 5. 主定理：共享相容迫使实际复线性等距

<a id="statement-5-1"></a>

#### 定理 5.1（共同内容刚性）

满足式[(3.1)](#eq-mass)、[(3.2)](#eq-J)及[(3.3)](#eq-shared)的实际映射 $F$，
唯一地等于一个复线性等距 $V$：

<a id="eq-isometry"></a>

$$
\boxed{F(x)=Vx\quad(x\in H),\qquad V^*V=I.}\tag{5.1}
$$

不另假定连续性、可加性、齐次性或输出满射。

**证明。**

**第一步：反向加入夹成等号。**
先对 $(x,y,c)$ 应用共享条件，再对 $(x+c,y+c,-c)$ 应用，
得到

<a id="eq-translation"></a>

$$
D_F(x+c,y+c)=D_F(x,y).\tag{5.2}
$$

**第二步：消去共同内容。**
取 $c=-y$，用 $F(0)=0$ 和完整强度：

<a id="eq-distance"></a>

$$
D_F(x,y)=D_F(x-y,0)=\left\lVert x-y\right\rVert ^2.\tag{5.3}
$$

**第三步：实极化。**
记 $g(u,v)=\operatorname{Re} \langle u,v\rangle$。由范数及距离保持，

$$
2g(Fx,Fy)
=\left\lVert Fx\right\rVert ^2+\left\lVert Fy\right\rVert ^2-\left\lVert Fx-Fy\right\rVert ^2
=2g(x,y).
$$

**第四步：真实坐标没有剩余量。**
$\{a_j,ia_j:1\le j\le d\}$ 为实正交单位基。
上式使它们的输出成为实正交单位框。
若 $x=\sum_j(s_ja_j+t_jia_j)$，$s_j,t_j\in\mathbb R$，
则 $F(x)$ 在该输出框上的正交投影是

$$
V_{\mathbb R }x=\sum_j\bigl(s_jF(a_j)+t_jF(ia_j)\bigr).
$$

该投影的范数平方为 $\sum_j(s_j^2+t_j^2)=\left\lVert x\right\rVert ^2=\left\lVert F(x)\right\rVert ^2$，
所以没有正交余量，$F(x)=V_{\mathbb R }x$。
实际映射已经实线性。

**第五步：有限共同方向给复线性。**
式[(3.2)](#eq-J)使

$$
F(x)=\sum_j(s_j+it_j)F(a_j).
$$

因此 $F$ 复线性，再由范数保持得 $`V^*V=I`$。
输入基张成性给唯一性。

□

<a id="statement-5-2"></a>

#### 推论 5.2（全部相干关系接续）

在同一实际输入域上，

$$
F(x+y)=F(x)+F(y),\qquad
F(\lambda x)=\lambda F(x),
\qquad
\langle F(x),F(y)\rangle =\langle x,y\rangle .
$$

特别地，正反、任意相位校准及 v80 的全部锚比较成为结论。

有限同维单结果时 $V$ 为酉；一般不同维输出只先给等距嵌入。
本定理约束的是已指定的实际值，
没有以某个抽象线性延拓替换尚未匹配的装置输出。

**白话图景。**先加上同一段，再减去同一段，两次都不能增加差别，
就把“不增加”夹成“完全相等”。
把共同项消去，差别只剩原来的余量；总强度由此锁住所有实内积。
内部四分之一周参考再锁住复方向。
所以后继必须用同一个线性规则接续所有内容。

<a id="section-6"></a>

## 6. 有限共同增量足够；地址替换随之成立

<a id="statement-6-1"></a>

#### 定理 6.1（有限共享增量供应）

令 $\mathcal C=\{\pm a_j,\pm ia_j:1\le j\le d\}$。
在式[(3.1)](#eq-mass)及[(3.2)](#eq-J)下，
只对 $c\in\mathcal C$、全部 $x,y\in H$ 要求式[(3.3)](#eq-shared)，
仍推出主定理。

**证明。**

$\mathcal C$ 关于取负封闭，故每个允许增量的共同平移均取等号。
对任意 $x$ 和任意 $a\in\mathcal C$，平移 $-a$ 给

$$
D_F(x,a)=D_F(x-a,0)=\left\lVert x-a\right\rVert ^2.
$$

输入范数和这些锚距离给
$g(Fx,F a)=g(x,a)$。
于是实基 $\{a_j,ia_j\}$ 的像实正交，
所有 $F(x)$ 在该框上的投影已具有完整范数。
主证明的最后两步给实线性及复线性。

□

有限的是 $4d$ 个共同增量；两个输入槽仍是全域。
$d$ 项点式 $J$ 校准比 v80 的四周校准更局部，
但整体量词布局已经改变，不宣称新候选在任意接口上逻辑更弱，
也不宣称最少锚数。
若这类点式 $J$ 校准的向量不复张成 $H$，
可在其复张成空间上取恒等，在正交补取共轭，
得到通过已校准点的非复线性实等距。

<a id="statement-6-2"></a>

#### 定理 6.2（同一实际接口的等价与地址下降）

在共同复输入输出接口及完整强度下，下列结构等价：

1. v81 的共享候选；

2. v81 的有限共享增量版；

3. 实际 $F$ 为复线性等距；

4. v80 的有限四周锚与差分不增条件。

并且若两个相干历史表达同一内容

$$
\sum_i\alpha_i\psi_{h_i}=\sum_j\beta_j\psi_{k_j},
$$

则每个实际分支满足

$$
\sum_i\alpha_iF_e(\psi_{h_i})
=\sum_j\beta_jF_e(\psi_{k_j}).
$$

**证明。**

前两项均由本稿定理给第三项；第三项直接给全部共享等号及方向校准。
第三、四项的等价使用 v80 已证明的同一实际接口定理[1](#ref-v80)。
最后一句由每个 $F_e=P_eV$ 的复线性得到。

□

因此相干表达的零关系确实能够穿过过程。
旧有 Gram 下降在这里作为已知结构被供应，
而非把线性重命名后再次列作假设。
如果只匹配一组生成历史的输出，仍只得到这些输出的线性延拓；
要证明全域实际 $F$ 与它相同，必须保留本定理的全输入条件。

**白话图景。**同一内容可以写成不同历史之和。共享相容一旦锁住实际过程，
这些不同写法经过过程以后仍表示同一内容。
这才使内容地址可以被后续合法使用：地址不靠某一种偶然展开维持正确。

<a id="section-7"></a>

## 7. 关系的关系：共同加项的轨道与二元三维提升

加法群 $(H,+)$ 在二元历史空间上作用：

$$
\tau_c(x,y)=(x+c,y+c).
$$

两个有序对属于同一轨道，当且仅当它们具有同一差向量：

$$
(x,y)\sim_\tau(u,v)
\quad\Longleftrightarrow\quad x-y=u-v.
$$

反向证明取 $c=u-x$；差向量相同给 $y+c=v$。
因此

$$
(H\times H)/\tau\simeq H,\qquad [(x,y)]\longmapsto x-y.
$$

本轮候选要求过程后的差分强度先沿共同加项单调；
可逆作用使其必须在轨道上恒定；完整强度再识别该轨道的范数。
这就是二元条件所属的更大结构。
它使用幅度关系中的可逆加法，不意味着实际历史事件能够倒退删除。

对非同时为零的 $x,y$，记

$$
a=\left\lVert x\right\rVert ^2,\quad b=\left\lVert y\right\rVert ^2,\quad
z=\langle x,y\rangle ,\quad s=a+b>0,
$$

采用与 v80 相同的坐标约定

<a id="eq-bloch"></a>

$$
R=\frac1s\begin{pmatrix}a&\bar z\\z&b\end{pmatrix}
=\frac12(I+\mathbf r\cdot\boldsymbol\sigma),
\qquad
\mathbf r=\left(\frac{2\operatorname{Re}  z}{s},\frac{2\operatorname{Im}  z}{s},\frac{a-b}{s}\right).\tag{7.1}
$$

该矩阵为 Gram 的转置，仍为正。于是

$$
1-\left\lVert \mathbf r\right\rVert ^2=\frac{4(ab-|z|^2)}{s^2}\ge0.
$$

完整二元数据是 $(s,\mathbf r)$，不丢掉尺度 $s$。

<a id="statement-7-1"></a>

#### 命题 7.1（共享加项保存的是带尺度差分）

写 $\mathbf r=(X,Y,Z)$，则

$$
\boxed{\left\lVert x-y\right\rVert ^2=s(1-X).}
$$

给两端共同加入 $c$，归一球坐标和 $s$ 一般都会改变，
但 $s(1-X)$ 不变。v81 迫使实际输出也保存这个共同加项轨道不变量。

**证明。**

展开范数平方给首式。
共同加入以后，

$$
\begin{aligned}
s'&=s+2\operatorname{Re} \langle x+y,c\rangle +2\left\lVert c\right\rVert ^2,\\
\operatorname{Re}  z'&=\operatorname{Re}  z+\operatorname{Re} \langle x+y,c\rangle +\left\lVert c\right\rVert ^2.
\end{aligned}
$$

所以 $s'-2\operatorname{Re}  z'=s-2\operatorname{Re}  z$。
实际输出部分由主定理或式[(5.2)](#eq-translation)得到。

□

若共同平移后两端同时为零，$s'=0$，不定义归一球点；
此时直接用未归一式 $s'-2\operatorname{Re}  z'=0$。其余情形才写 $s'(1-X')$。
因此不能把“共享内容相容”误画成所有共同平移后归一球点都不动。
本轮先锁定差分不变量，再由全部二元比较锁定同一复核。

<a id="figure-1"></a>

**图 1。**

```latex
\begin{figure}[htbp]
\centering
\begin{tikzpicture}[>=Latex,font=\small]
\begin{scope}[xshift=-3.5cm]
\draw[->,ink!55] (-1.6,-1.4)--(1.9,-1.4);
\draw[->,ink!55] (-1.4,-1.6)--(-1.4,1.5);
\coordinate (x) at (-.95,-.35);
\coordinate (y) at (-.45,.65);
\coordinate (xc) at (.65,-.05);
\coordinate (yc) at (1.15,.95);
\draw[->,accent,thick] (x)--(y);
\draw[->,accent,thick] (xc)--(yc);
\draw[->,warm,dashed] (x)--(xc) node[midway,below] {$+c$};
\draw[->,warm,dashed] (y)--(yc) node[midway,above] {$+c$};
\fill[ink] (x) circle(2pt) node[left] {$y$};
\fill[ink] (y) circle(2pt) node[left] {$x$};
\fill[ink] (xc) circle(2pt) node[right] {$y+c$};
\fill[ink] (yc) circle(2pt) node[right] {$x+c$};
\node[align=center,text width=5.8cm] at (.1,-2.02)
{共同加项改变两端\\同一差向量保持};
\end{scope}
\begin{scope}[xshift=3.5cm]
\draw[ink!65] (0,0) circle(1.4);
\draw[->,ink!55] (-1.65,0)--(1.75,0) node[right] {$X$};
\draw[->,ink!55] (0,-1.6)--(0,1.65) node[above] {$Y$};
\fill[accent] (.14,.42) circle(2.4pt);
\fill[warm] (.84,.14) circle(2.4pt);
\draw[->,warm,thick] (.22,.43) to[bend left=16] (.78,.22);
\node[anchor=east] at (.08,.5) {$(s,\mathbf r)$};
\node[anchor=north] at (.78,.02) {$(s',\mathbf r')$};
\node[align=center,text width=5.8cm] at (0,-2.02)
{归一球点可以改变\\必须连同强度尺度比较};
\end{scope}
\end{tikzpicture}
\caption{左图的箭头表示同一幅度差分；右图只示意归一坐标可以移动。
共同加项保持的是 $s(1-X)$，不是把尺度删除后的同一个球点。}
\end{figure}
```

**白话图景。**两条历史同时搬动同一份内容，它们之间的差别不变。
归一化会改变图上的比例，所以球里的点可以移动；
把强度标尺带回来，才看见同一个差别。
三维表示是每个二元关系的截面，共同核负责这些截面能否组成一个整体。

<a id="section-8"></a>

## 8. 共享子态的类型：前缀、投影、因子与正子态

“多个态共享一段”至少有四种准确含义：

1. **共同历史片段**：两条程序路线引用同一段门历史。

2. **共同投影关系**：给定内部子空间 $S$，比较 $P_Sx_j$。

3. **共同张量因子**：在已声明切分中有 $x_j=\phi\otimes\eta_j$。

4. **共同正算符子态**：有 $0\le A\le\rho_j$ 对所有 $j$ 成立。

这些类型彼此不能自动替代。
例如从 $|0\rangle$ 共同经过 Hadamard 到 $|+\rangle$，
随后一条取恒等、另一条取 $Z$，最终为正交的 $|+\rangle ,|-\rangle$。
共同前缀并不强制末态有非零内积。

<a id="statement-8-1"></a>

#### 命题 8.1（不同纯态没有非零共同正子算符）

若单位纯态 $x,y$ 不共线，且

$$
0\le A\le|x\rangle \langle x|,\qquad A\le|y\rangle \langle y|,
$$

则 $A=0$。

**证明。**

对 $v\perp x$，$0\le\langle v,Av\rangle \le0$。
由正平方根，$A^{1/2}v=0$，故 $Av=0$。
因此 $\operatorname{ran}  A\subseteq\operatorname{span} \{x\}$。
同理它也包含在 $\operatorname{span} \{y\}$，两条不同直线的交为零。

□

这不排除后选择投影产生共同分支。
两个正交态也可以经过同一个非零收缩分支得到同一幅度；
下节给出这项任务的精确最大值。

对已声明共享锚空间 $S$，始终有

$$
\langle x,y\rangle =\langle P_Sx,P_Sy\rangle +\langle (I-P_S)x,(I-P_S)y\rangle .
$$

两项分别形成正核。
N2 已完整说明：只有第二项在所要求的跨侧比较中为零，
共享部分才足以决定全部跨关系[4](#ref-n2)。
本稿不把共同前缀、同根来源或一个共享投影自动等同于这项充分性。

**白话图景。**“同一来源”“同一段代码”“同一个方向上的分量”和“能在同一结果中留下同样内容”，
说的是不同关系。把共享方式声明出来，就能给它一个精确大小。
本轮接下来求的是同一个分支能从一组实际幅度中取得的共同输出。

<a id="section-9"></a>

## 9. 有限地址族的最大共同幅度

<a id="statement-9-1"></a>

#### 定义 9.1（固定相位的共同分支任务）

给有限实际幅度 $x_1,\ldots,x_n\in H$，$n\ge1$，
它们相对于同一内部参考已确定。
共同分支是一个到非零输出空间的复线性收缩 $M:H\to W$，满足

$$
Mx_1=\cdots=Mx_n=\xi.
$$

其共同强度为 $t=\left\lVert \xi\right\rVert ^2$。
输出 $\xi$ 包括此成功支路中全部相关记录，不能暗留依赖输入标签的记录。

本任务是既有受支配核与共同振幅提取理论的具体应用：
基础与记录卷已有正交地址的 $1/m$ 特例及任意记录族的提取条件，
Closure 已有正核支配到收缩的表示[5](#ref-foundations)、[6](#ref-closure)。
下面显式求解非正交有限族，包括奇异情况。

令

$$
D=\operatorname{span} _\mathbb C \{x_j-x_1:1\le j\le n\},\qquad
P=P_{D^\perp},\qquad q=Px_1.
$$

于是所有 $Px_j=q$。

<a id="statement-9-2"></a>

#### 定理 9.2（最优共同幅度与强度）

所有满足定义[9.1](#statement-9-1)的收缩均有

<a id="eq-optgeom"></a>

$$
\boxed{\left\lVert Mx_j\right\rVert ^2\le t_*:=\left\lVert q\right\rVert ^2.}\tag{9.1}
$$

在允许该投影或等价分支的完整矩阵模型中，上界可达。
规范共同分量 $q$ 是仿射空间 $x_1+D$ 中唯一的最小范数点。

**证明。**

相同输出要求 $M(x_j-x_1)=0$，故 $M$ 消去 $D$，即 $M=MP$。
于是 $\left\lVert Mx_j\right\rVert =\left\lVert Mq\right\rVert \le\left\lVert q\right\rVert$。
取 $M=P$ 即达到。
若需要固定输出单位方向 $s_0$，在 $q\ne0$ 时取

$$
M=|s_0\rangle \langle q/\left\lVert q\right\rVert|.
$$

因为 $\langle q,x_j\rangle =\left\lVert q\right\rVert ^2$，得到 $Mx_j=\left\lVert q\right\rVert \,s_0$。
若 $q=0$，零分支达到。
最后 $x_1+D=q+D$，且 $q\perp D$；
任意 $q+d$ 的范数平方为 $\left\lVert q\right\rVert ^2+\left\lVert d\right\rVert ^2$，
故唯一最小点为 $q$。

□

由此得到规范正交分解

<a id="eq-qr"></a>

$$
\boxed{x_j=q+r_j,\qquad r_j\in D,\qquad q\perp r_j.}\tag{9.2}
$$

把投影及其补投影都保留，得到完整等距

$$
V_Px=Px\oplus(I-P)x.
$$

在该地址族上，输出是 $q\oplus r_j$。
共同分支相同，但

$$
\boxed{r_j-r_k=x_j-x_k}
$$

说明全部差异留在剩余分支中。

<a id="statement-9-3"></a>

#### 推论 9.3（最优效果在被声明空间上唯一）

记 $L=\operatorname{span} \{x_j\}$。若 $q\ne0$，

$$
L=D\oplus\operatorname{span} \{q\}.
$$

任何达到 $`t_*`$ 的收缩，其效果 $`E=M^*M`$ 在 $L$ 上必须为
$P_{\operatorname{span} \{q\}}$。
$L^\perp$ 上的过程不由这组地址决定。

**证明。**

$q=x_1-P_Dx_1\in L$，其余分解由式[(9.2)](#eq-qr)给出。
$M$ 消去 $D$，所以 $E$ 消去 $D$。
等号使 $\langle q,(I-E)q\rangle =0$；正性给 $(I-E)q=0$。
故 $Eq=q$，得到结论。

□

若 $q=0$，则 $L=D$，共同分支在 $L$ 上必为零，故 $E|_L=0$。
数学最优值是任何实际可用分支的上界。
若原生菜单尚未供应该精确投影、其等价效果或所需输出方向，
本稿不把数学可达性直接改写成原生有限门字可达性。

**白话图景。**把这组历史所有不同的部分张成一个差异空间。
一个结果若要对它们留下完全相同的内容，就必须消去这个差异空间。
剩下的垂直投影就是最多能共同留下的一份。
把其他结果也保留以后，差异仍在整体里，只是到了另外的记录。

<a id="section-10"></a>

## 10. 共同核预算：Gram 条件、闭式与奇异边界

定义合成算符及 Gram 矩阵

$$
X:\mathbb C ^n\to H,\qquad Xc=\sum_jc_jx_j,\qquad
G=X^*X,\quad G_{jk}=\langle x_j,x_k\rangle .
$$

记 $\mathbf1=(1,\ldots,1)^\mathsf T$。

<a id="statement-10-1"></a>

#### 定理 10.1（共同幅度的完整预算判据）

给定输出单位方向 $s_0$ 及 $t\ge0$。
存在同一收缩满足 $Mx_j=\sqrt t\,s_0$，当且仅当

<a id="eq-budget"></a>

$$
\boxed{
G-t\mathbf1\mathbf1^*\succeq0.
}\tag{10.1}
$$

等价地，对全部复系数 $c$，

<a id="eq-coherentbudget"></a>

$$
\boxed{
t\left|\sum_jc_j\right|^2
\le\left\lVert \sum_jc_jx_j\right\rVert ^2.
}\tag{10.2}
$$

这又等价于 $`0\le t\le t_*`$。

**证明。**

收缩作用于每个相干组合，直接给式[(10.2)](#eq-coherentbudget)；
矩阵二次型展开给式[(10.1)](#eq-budget)。
反向，在 $L=\operatorname{ran}  X$ 上定义

$$
M(Xc)=\sqrt t\,s_0(\mathbf1^*c).
$$

若 $Xc=0$，不等式使右边为零，故定义与表达式无关；
同一个不等式使该映射为收缩。
在 $L^\perp$ 上取零即可延拓。
最优强度及缩放最优分支给最后的区间刻画。

□

此判据是既有核支配定理的秩一常数核特化，
也在一般概率纯态变换的 Gram 框架内[6](#ref-closure)、[5](#ref-foundations)、[11](#ref-cjw)。
本稿的显式求解如下。

<a id="statement-10-2"></a>

#### 定理 10.2（非正交与奇异 Gram 的精确最优值）

令 $G^+$ 为 Moore--Penrose 逆，则

<a id="eq-optgram"></a>

$$
\boxed{
t_*=\min_{\mathbf1^*c=1}c^*Gc
=
\begin{cases}
(\mathbf1^*G^+\mathbf1)^{-1},&\mathbf1\in\operatorname{ran}  G,\\
0,&\mathbf1\notin\operatorname{ran}  G.
\end{cases}
}\tag{10.3}
$$

第一种情况下分母严格为正。

**证明。**

$`\{Xc:\mathbf1^*c=1\}=x_1+D`$，
故最小范数点定理给首项。
若 $\mathbf1\in\operatorname{ran}  G$，Cauchy--Schwarz 给

$$
|\mathbf1^*c|^2
=\left|(G^{+1/2}\mathbf1)^*G^{1/2}c\right|^2
\le(\mathbf1^*G^+\mathbf1)(c^*Gc).
$$

在约束下得到下界；取
$`c_*=G^+\mathbf1/(\mathbf1^*G^+\mathbf1)`$ 达到。
若 $\mathbf1\notin\operatorname{ran}  G=(\operatorname{ker}  G)^\perp$，
有 $k\in\operatorname{ker}  G$ 且 $`\mathbf1^*k\ne0`$。
令 $`c=k/(\mathbf1^*k)`$，则约束成立而 $`c^*Gc=0`$。

□

<a id="statement-10-3"></a>

#### 推论 10.3（最优剩余关系的秩）

若 $`t_*>0`$，则

$$
G=t_*\mathbf1\mathbf1^*+R,\qquad R\succeq0,\qquad
\boxed{\operatorname{rank}  R=\operatorname{rank}  G-1.}
$$

$R$ 是 $r_j=x_j-q$ 的 Gram 矩阵。

**证明。**

由正交分解，$\langle x_j,x_k\rangle =\left\lVert q\right\rVert ^2+\langle r_j,r_k\rangle$。
而 $L=D\oplus\operatorname{span} \{q\}$，并且 $r_j$ 张成 $D$：
一边 $r_j\in D$，另一边 $x_j-x_1=r_j-r_1$。
所以剩余 Gram 秩为 $\dim D=\dim L-1=\operatorname{rank}  G-1$。

□

该秩只计当前有限地址族的剩余幅度维数，
不能替代全输入仪器的 Choi 秩或整个装置的最小环境维数。

### 10.1 边界与可复核特例

若所有 $x_j=x\ne0$，则 $`t_*=\left\lVert x\right\rVert ^2`$，
即使 $`G=\left\lVert x\right\rVert ^2\mathbf1\mathbf1^*`$ 奇异也没有问题。
若包含零输入，则共同输出必须为零。
若 $x_j$ 为 $n$ 个正交单位向量，$G=I_n$，故

$$
t_*=\frac1n,
$$

恢复基础与记录卷已有的单纤维特例[5](#ref-foundations)。
增加必须同时合并的地址，差异空间只会增大，因此 $`t_*`$ 不增。

若 $x_2=e^{i\theta}x_1$、$e^{i\theta}\ne1$，
要求两个*固定幅度*的输出严格相同会迫使共同分支为零。
这不是说它们的纯态射线不同，而是当前任务还要求跨输入的相干相位相同。
后文的共享签名会准确处理不同系数。

**白话图景。**共同分支不能从一个相干组合里拿出比这个组合本来更多的强度。
如果某些地址组合起来恰好是零，而声称的共同输出组合后非零，
这个共享声明就不可能成立。
Gram 公式把所有这些限制一次写全，广义逆则把奇异情况也算清楚。

<a id="section-11"></a>

## 11. 二元共享的三维球图与最大份额

<a id="statement-11-1"></a>

#### 定理 11.1（二元共同强度的显式式子）

对 $x\ne y$，

<a id="eq-pair"></a>

$$
\boxed{
t_*=
\frac{\left\lVert x\right\rVert ^2\left\lVert y\right\rVert ^2-|\langle x,y\rangle |^2}
     {\left\lVert x-y\right\rVert ^2}.
}\tag{11.1}
$$

若 $x=y$，单独取 $`t_*=\left\lVert x\right\rVert ^2`$。
特别地，对单位态，记 $z=\langle x,y\rangle$，

$$
t_*=\frac{1-|z|^2}{2-2\operatorname{Re}  z}\quad(x\ne y).
$$

若实际相位已对齐使 $z\in[0,1)$，则 $`t_*=(1+z)/2`$。

**证明。**

当 $x\ne y$ 时，$D=\operatorname{span} \{x-y\}$，

$$
q=x-(x-y)\frac{\langle x-y,x\rangle }{\left\lVert x-y\right\rVert ^2}.
$$

由正交投影，
$\left\lVert q\right\rVert ^2=\left\lVert x\right\rVert ^2-|\langle x-y,x\rangle |^2/\left\lVert x-y\right\rVert ^2$。
记 $a=\left\lVert x\right\rVert ^2,b=\left\lVert y\right\rVert ^2,z=\langle x,y\rangle$，
分子化简为
$a(a+b-2\operatorname{Re}  z)-|a-\bar z|^2=ab-|z|^2$。
单位且实非负重叠时约去 $1-z$，得到最后一句。

□

对单位二元对，抽出同一强度 $t$ 后，剩余 Gram 正性是

$$
\begin{pmatrix}1-t&z-t\\\bar z-t&1-t\end{pmatrix}\succeq0,
$$

即

<a id="eq-disk"></a>

$$
\boxed{|z-t|\le1-t,\qquad 0\le t\le1.}\tag{11.2}
$$

在复重叠平面中，这是中心 $(t,0)$、半径 $1-t$ 的圆盘。

一般二元对采用式[(7.1)](#eq-bloch)，$s=a+b$。
共同幅度的归一关系点是 $\mathbf e_x=(1,0,0)$。
若 $s-2t>0$，剩余关系可归一，且

<a id="eq-commonbary"></a>

$$
\boxed{
\mathbf r=\lambda\mathbf e_x+(1-\lambda)\mathbf r_{\rm res},
\qquad\lambda=\frac{2t}{s},\quad\left\lVert \mathbf r_{\rm res}\right\rVert \le1.
}\tag{11.3}
$$

它由原二元 Gram 减去 $`t\mathbf1\mathbf1^*`$ 后按迹归一直接得到。
若 $x\ne y$，最大值满足

$$
\lambda_*=\frac{1-\left\lVert \mathbf r\right\rVert ^2}{2(1-r_x)}.
$$

因为
$\left\lVert \mathbf r-\lambda\mathbf e_x\right\rVert ^2\le(1-\lambda)^2$
恰等价于
$2\lambda(1-r_x)\le1-\left\lVert \mathbf r\right\rVert ^2$。
两者相同非零且全量提取时，$\lambda=1$，剩余为零，不定义剩余球点。
两者均零时也不定义原归一球点。

<a id="figure-2"></a>

**图 2。**

```latex
\begin{figure}[htbp]
\centering
\begin{tikzpicture}[>=Latex,font=\small]
\begin{scope}[xshift=-3.5cm]
\draw[ink,thick] (0,0) circle(1.65);
\draw[->,ink!60] (-1.85,0)--(1.95,0) node[right] {$X$};
\draw[->,ink!60] (0,-1.85)--(0,1.95) node[above] {$Y$};
\coordinate (S) at (1.65,0);
\coordinate (R) at (.825,.825);
\coordinate (T) at (0,1.65);
\draw[warm,thick] (S)--(T);
\fill[accent] (S) circle(2.5pt) node[below right] {$\mathbf e_x$};
\fill[ink] (R) circle(2.5pt) node[right] {$\mathbf r$};
\fill[warm] (T) circle(2.5pt) node[left] {$\mathbf r_{\rm res}$};
\node[align=center,text width=5.7cm] at (0,-2.35)
{抽出同一关系的份额\\剩余点最多到球面};
\end{scope}
\begin{scope}[xshift=3.8cm]
\draw[->,ink!55] (-.3,0)--(2.3,0);
\draw[->,ink!55] (0,-1.5)--(0,1.6);
\draw[->,accent,thick] (0,0)--(1.6,.8) node[right] {$x=q+r$};
\draw[->,warm,thick] (0,0)--(1.6,-.8) node[right] {$y=q-r$};
\draw[->,ink,thick] (0,0)--(1.6,0) node[midway,below] {$q$};
\draw[->,accent,dashed] (1.6,0)--(1.6,.8);
\draw[->,warm,dashed] (1.6,0)--(1.6,-.8);
\node[align=center,text width=5.7cm] at (1,-2.35)
{实非负重叠的二态\\共同部分与相反余量正交};
\end{scope}
\end{tikzpicture}
\caption{左图取单位二元关系 $z=(1+i)/2$，最大共同权重为 $1/2$，
原关系点位于共同纯关系点与剩余球面点的中点。
右图表示相位已对齐的二态分解，其比例只作示意。}
\end{figure}
```

当单位二态实际相位对齐为 $z\ge0$ 时，

$$
q=\frac{x+y}{2},\qquad r=\frac{x-y}{2},\qquad
q\perp r,\qquad
\left\lVert q\right\rVert ^2=\frac{1+z}{2},\quad\left\lVert r\right\rVert ^2=\frac{1-z}{2}.
$$

这给“共同内容加不同余量”一个直观的规范二元实例。
即使 $x\perp y$，仍有共同*后选择分支*强度 $1/2$；
它不是原纯密度算符的共同正子算符。

**白话图景。**共同分支在球上指向“这两条历史完全相同”的位置。
抽得越多，剩余关系就越向球面移动。
最大只能抽到剩余仍然合法的那一点；继续多抽，残差会失去正性。
共享的多少因此不是凭感觉指定，而由完整二元关系决定。

<a id="section-12"></a>

## 12. 逐对共享为何不保证整个内容族同时共享

<a id="statement-12-1"></a>

#### 命题 12.1（三地址的精确反例）

取

$$
x_1=e_1,\qquad x_2=e_2,\qquad
x_3=\frac{e_1+e_2}{\sqrt2}.
$$

任意一对都有非零共同幅度分支，但整个三元族的同幅共同强度为零。

**证明。**

二元公式给
$t_{12}=1/2$，
$t_{13}=t_{23}=(1+1/\sqrt2)/2>0$。
若同一线性 $M$ 将三者都送为 $q$，
则

$$
q=Mx_3=\frac{Mx_1+Mx_2}{\sqrt2}=\sqrt2\,q,
$$

所以 $q=0$。

□

这个失败仍可定位到两个元：

$$
u=x_3,\qquad v=\frac{x_1+x_2}{\sqrt2}.
$$

输入 $u=v$，不相容的共享声明却把它们送为 $q$ 与 $\sqrt2q$。
因此二元比较域必须包含已声明的相干组合。

甚至令每对都拟抽同一 $t=1/2$，全部原始 $2\times2$ 剩余块仍为正。
但取 $c=(1,1,-\sqrt2)^\mathsf T$，

$$
Xc=0,\qquad
c^*(G-t\mathbf1\mathbf1^*)c=-t(2-\sqrt2)^2<0.
$$

所以逐对合法的三维图不能替代共同正核的全相干正性。
本稿没有把原始标签的两两检查，当成自动覆盖所有组合态。

### 12.1 相位对齐也必须在同一个整体中完成

取

$$
x_1=e_1,\quad x_2=(e_1+e_2)/\sqrt2,\quad
x_3=(e_1+ie_2)/\sqrt2.
$$

三条重叠的环乘积为

$$
\langle x_1,x_2\rangle \langle x_2,x_3\rangle \langle x_3,x_1\rangle
=\frac{1+i}{4}.
$$

各向量重选相位时，三个相位因子相消，环乘积不变。
因此不能同时把这三对重叠都调成实非负：
否则环乘积必须实非负。
这种环相位是关系之间的相容信息；
它不是 Sorkin 意义的三阶干涉。
一般 Gram 与相位选择的关系已有成熟讨论[11](#ref-cjw)。

**白话图景。**一对历史能找到共同部分，不代表换另一对时找到的仍是同一份。
若要求整个族一起共享，所有相干表达都要对得上。
上面的失败落在“一个地址”和“另一段组合地址”这两个本来相同的内容上；
共同参考还要让各对相位在环上闭合，不能逐对随意换尺。

<a id="section-13"></a>

## 13. 允许地址携带不同相位或幅度：共同签名版

同幅要求有明确物理含义，但有时希望保留每个地址的已知系数。
令 $\lambda=(\lambda_1,\ldots,\lambda_n)\ne0$ 为已声明签名，要求

$$
Mx_j=\lambda_j\xi\quad(1\le j\le n),\qquad t=\left\lVert \xi\right\rVert ^2.
$$

这里成功后共同的是方向与完整记录，系数仍随地址变化。
概率也随系数变化；对单位输入为 $t|\lambda_j|^2$。

<a id="statement-13-1"></a>

#### 定理 13.1（固定共同签名的最优强度）

沿用含单位输出方向 $s_0$ 的非零输出空间。
记 $b=\overline\lambda$，共轭按分量取。
存在所要求的收缩当且仅当

$$
\boxed{tbb^*\preceq G.}
$$

最优值为

$$
\boxed{
t_*^{\lambda}=
\begin{cases}
(b^*G^+b)^{-1},&b\in\operatorname{ran}  G,\\
0,&b\notin\operatorname{ran}  G.
\end{cases}}
$$

**证明。**

对任意系数 $c$，收缩条件正是

$$
t\left|\sum_j\lambda_jc_j\right|^2
=t|b^*c|^2\le c^*Gc.
$$

反向用此不等式定义
$`M(Xc)=\xi\,b^*c`$，零关系保证定义无歧义，再在 $L^\perp$ 置零。
若 $b\notin\operatorname{ran}  G=(\operatorname{ker}  G)^\perp$，存在 $k\in\operatorname{ker}  G$ 而
$`b^*k\ne0`$，所以只能 $t=0$。
若 $b\in\operatorname{ran}  G$，Cauchy--Schwarz 给

$$
|b^*c|^2
\le (b^*G^+b)(c^*Gc),
$$

取 $c=G^+b$ 达到界。
更显式地令 $w=XG^+b$，则

$$
\langle w,x_j\rangle =\lambda_j,
\qquad \left\lVert w\right\rVert ^2=b^*G^+b.
$$

对任意单位输出 $s_0$，
$M=|s_0\rangle \langle w/\left\lVert w\right\rVert|$ 达到该最优值。

□

相位协变现在清楚可见：若输入重写为
$x'_j=e^{i\theta_j}x_j$，相同物理分支的签名应同时改为
$\lambda'_j=e^{i\theta_j}\lambda_j$。
此时 $`G'=U^*GU`$、$`b'=U^*b`$，其中
$U=\operatorname{diag}(e^{i\theta_j})$，最优 $t$ 不变。
若只改输入相位，却仍把所有签名强设为 $1$，已经改换了共同分支任务。
零签名未纳入优化，因为全部 $Mx_j=0$ 时 $\xi$ 的任意尺度没有分支强度意义。

**白话图景。**有时“共同内容”允许每条路线带一个不同的已知相位标签。
把这些标签写进同一个签名，公式仍然一致。
换参考时，态的坐标和标签要一起换；单独改一边，会把原来的共享问题变成另一件事。

<a id="section-14"></a>

## 14. 共享部分怎样产生圆、椭圆与周期

这一节把用户的图景变成一个有明确条件的完整消费者。
设已供应正交分解

$$
x=q+r,\qquad q\perp r,\qquad
\left\lVert q\right\rVert ^2=p\in(0,1),\qquad \left\lVert r\right\rVert ^2=1-p.
$$

若声明的内部控制可以让剩余部分改变相位，定义

<a id="eq-phasecircle"></a>

$$
\boxed{x(\theta)=q+e^{i\theta}r.}\tag{14.1}
$$

一个数学酉实现是
$U_\theta=P_{\mathbb C  q}+e^{i\theta}(I-P_{\mathbb C  q})$。
实际原生菜单能否供应该连续族，须遵守此前的控制条件。

<a id="statement-14-1"></a>

#### 定理 14.1（共同幅度固定的圆族）

式[(14.1)](#eq-phasecircle)在实化幅度空间中是仿射圆，中心 $q$，
半径 $\sqrt{1-p}$，平面为
$q+\operatorname{span} _\mathbb R \{r,ir\}$。
在正交基
$u=q/\sqrt p$、$v=r/\sqrt{1-p}$ 的纯态 Bloch 球中，轨迹为

<a id="eq-latitude"></a>

$$
\boxed{\mathbf r(\theta)=
\bigl(2\sqrt{p(1-p)}\cos\theta,
2\sqrt{p(1-p)}\sin\theta,2p-1\bigr).}\tag{14.2}
$$

它是纬圆；在 $0<p<1$ 内是大圆当且仅当 $p=1/2$。
若角度集包含两个模 $2\pi$ 不同的角，该族的最大同幅公共部分恰为 $q$，
最优强度为 $p$。

**证明。**

$r$ 与 $ir$ 在实内积下正交且等长，给第一句。
在基 $(u,v)$ 中，态坐标为
$(\sqrt p,e^{i\theta}\sqrt{1-p})$；直接展开其秩一密度矩阵即得
式[(14.2)](#eq-latitude)。
水平截平面经过球心恰在 $2p-1=0$。
任意两不同角的差为

$$
x(\theta_2)-x(\theta_1)
=(e^{i\theta_2}-e^{i\theta_1})r.
$$

所以差异空间是 $\mathbb C  r$，其正交补中的共同投影就是 $q$。
最大公共分支定理随即给最优强度 $p$。

□

<a id="statement-14-2"></a>

#### 命题 14.2（两读出的椭圆与菜单限制）

对两个固定效果 $E_1,E_2$，该圆族的响应满足

$$
\begin{pmatrix}p_{E_1}(\theta)\\p_{E_2}(\theta)\end{pmatrix}
=A+B\begin{pmatrix}\cos\theta\\\sin\theta\end{pmatrix},
$$

其中

$$
A_j=\langle q,E_jq\rangle +\langle r,E_jr\rangle ,\qquad
B_{j,\bullet}=
\bigl(2\operatorname{Re} \langle q,E_jr\rangle ,-2\operatorname{Im} \langle q,E_jr\rangle \bigr).
$$

$\operatorname{rank}  B=2$ 时为非退化椭圆，秩一时为线段，秩零时为点。
若 $E_1,E_2$ 构成同一个完备二结果菜单，只能出现后两种情况。

**证明。**

对任意固定效果 $E$，

$$
\begin{aligned}
p_E(\theta)
&=\langle x(\theta),Ex(\theta)\rangle \\
&=\langle q,Eq\rangle +\langle r,Er\rangle
 +2\operatorname{Re} \bigl(e^{i\theta}\langle q,Er\rangle \bigr).
\end{aligned}
$$

展开实部即得矩阵式。实线性像把单位圆变为所列三种情形。
若 $E_1+E_2=I$，则 $p_{E_2}=1-p_{E_1}$，
$B$ 的两行互为相反数，故秩至多一。

□

非退化椭圆可以使用两个不同设置，或者同一个至少三结果菜单的两个坐标。
例如在 $(u,v)$ 支撑上，取

$$
E_1=\frac{I+\sigma_x}{3},\quad
E_2=\frac{I-\sigma_x/2+\sqrt3\sigma_y/2}{3},\quad
E_3=\frac{I-\sigma_x/2-\sqrt3\sigma_y/2}{3}.
$$

各效果的特征值为 $0,2/3$，且三者之和为 $I$。
令 $R=2\sqrt{p(1-p)}>0$，前两响应为

$$
\begin{pmatrix}p_1\\p_2\end{pmatrix}
=\begin{pmatrix}1/3\\1/3\end{pmatrix}
+\frac R3
\begin{pmatrix}1&0\\-1/2&\sqrt3/2\end{pmatrix}
\begin{pmatrix}\cos\theta\\\sin\theta\end{pmatrix}.
$$

矩阵可逆，因此确为同一数学菜单中的非退化椭圆。
这里只给效果的合法表示；实际实施仍需原生供应。
这些坐标是统计响应，不是一次读出就能精确取得的未知相位。

### 14.1 周期究竟从哪里来

当 $0<p<1$ 时，这个纯态射线族的基本参数周期为 $2\pi$。
若 $x(\theta')=e^{i\alpha}x(\theta)$，非零 $q$ 分量迫使
$e^{i\alpha}=1$，再由非零 $r$ 分量得
$\theta'-\theta\in2\pi\mathbb Z$。
非恒定单效果响应是一阶正弦组合，也具有基本参数周期 $2\pi$。
若内部时钟供应 $\theta(t)=\omega t+\theta_0$、$\omega\ne0$，
相应时间周期才是 $2\pi/|\omega|$。
若该读口交叉项为零，响应恒定，不能从它识别一个基本周期。

v80 的 $u\cos t+v\sin t$ 是另一种幅度参数化；
二次读出中的双角给 $\pi$ 周期。
本稿固定共同部分，仅让剩余部分转相位，交叉项是一阶角。
因此“圆有周期”需要同时明确：哪个空间中的圆、哪一个读口、
怎样的参数推进，以及是否把全局相位商掉。

### 14.2 精确共享不自动连续

上面的两角只要仍不同，最大同幅公共强度一直是 $p$。
当两角完全重合，输入相同，最优值变为 $1$。
这给出 Gram 秩改变处的跳变。
原因是精确共同分支必须完全消去差异方向，即使差向量已经很短。
近似共享可以另行定义，但不能在无误差条件、无谱隙控制时，
把当前精确最优式宣称为统一稳定。

**白话图景。**共同部分像固定圆心，剩余部分带着相位绕它转。
在两个相干方向组成的态球上，它通常是一条纬圆；共同与剩余各占一半时才过球心。
固定读口把这条圆的两个方向以不同强度读出来，就出现椭圆，
而只有两个互补结果时读数只能在一条线上移动。
周期来自内部相位重新回到同一关系，具体时间还由时钟怎样走决定。

<a id="section-15"></a>

## 15. 寻址、不可复制与记录守恒由同一个等距推出

<a id="statement-15-1"></a>

#### 命题 15.1（完整地址不能无记录地合并）

在完整实际输出上，$F(x)=F(y)$ 当且仅当 $x=y$。
若一个可见分支把不同输入变成同一个幅度，区别须保留在其他结果或内部记录中。

**证明。**

主定理给
$\left\lVert F(x)-F(y)\right\rVert ^2=\left\lVert x-y\right\rVert ^2$。
最大公共分支的完整实现

$$
x\longmapsto Px\oplus(I-P)x
$$

进一步展示：共同投影之外，剩余分支保留了差异。

□

<a id="statement-15-2"></a>

#### 命题 15.2（非正交态没有无扰经典地址读口）

若完整等距满足

$$
V|\psi\rangle =|\psi\rangle \otimes|R_\psi\rangle ,\qquad
V|\phi\rangle =|\phi\rangle \otimes|R_\phi\rangle ,
$$

其中输入及记录都归一，且 $\langle \psi,\phi\rangle \ne0$，
则 $R_\psi=R_\phi$。

**证明。**

保持内积给

$$
\langle \psi,\phi\rangle
=\langle \psi,\phi\rangle \,\langle R_\psi,R_\phi\rangle .
$$

故记录内积为 $1$，两个单位记录相同。

□

因此内容等价类不是一个自动可读取、可区别任意非正交未知态的经典散列。
已知制备程序的经典标签，与未知态本身可无扰输出什么标签，是两件不同的事。

<a id="statement-15-3"></a>

#### 命题 15.3（不可复制无需另加禁止条款）

不存在同一个完整等距，把任意一对射线不同且非正交的单位纯态分别变成其两份副本。
即使允许输出依赖输入的附加记录，结论仍成立。

**证明。**

若
$V\psi=\psi\otimes\psi\otimes r_\psi$，
$V\phi=\phi\otimes\phi\otimes r_\phi$，
记 $c=\langle \psi,\phi\rangle$，则

$$
c=c^2\langle r_\psi,r_\phi\rangle ,\qquad
|c|\le|c|^2.
$$

当 $0<|c|<1$ 时矛盾。正交态不受这个论证禁止，
但复制控制仍须实际供应。

□

粗可见重置并不矛盾：完整等距

$$
x\longmapsto \Omega_0\otimes x
$$

可以把可见寄存器重置为同一个单位根态，同时把输入保留在另一个内部寄存器。
若忽略该记录，所有归一输入的可见态相同；未归一输入的可见算符仍带总强度 $\left\lVert x\right\rVert ^2$。
这不是本稿要求的
“整个成功幅度及其全部相关记录相同”。
V67 已证明确定地址归并时，来自正交历史的同纤维残余记录必须正交，
并求出最小残余容量[3](#ref-v67)。

最新相干恢复稿在特定原生菜单中进一步区分门算子返回、波函数返回、
当前配置返回及旧联合标签恢复[9](#ref-reconstruction)。
这些区别同样要求：当前状态地址已经返回，并不自动重建通往这里的完整路径。
本稿不把那个具体隐藏过程模型的恢复界推广到任意控制菜单。

**白话图景。**相同内容可以有不同来路；但完整量子过程不能把本来不同的内容
连同一切记录一起压成同一个点。一个读口看起来把它们合并时，
剩余差异在失败分支或别的内部记录里。
想无扰读出未知态的唯一经典地址，或者把任意未知态复制两份，
都会让原来的两两比较对不上；不可复制就是这条相容要求的直接后果。

<a id="section-16"></a>

## 16. 怎样接出现有量子力学公理：逐项给出定义与证明

这一节把理论闭合到有限维量子力学的标准结构。
本轮新增入口是共享条件；此前已经完成的比较、读出、复合及控制供应继续使用，
不把它们再列作尚未讨论的空白。
也不声称仅凭“所有东西都在 $\Omega$ 中”就能取消它们的具体内容。

### 16.1 状态空间：由内部比较核得到复 Hilbert 表示

令 $\mathcal H$ 为声明的历史集合，
$K(h,k)$ 为共同相干比较，使用既有 Q1 的正核供应：

$$
\sum_{j,k}\bar c_jc_kK(h_j,h_k)\ge0
\quad\text{对任意有限相干组合。}
$$

共同 $J$ 已固定复方向。
在有限形式历史空间上定义

$$
\left\langle\sum_jc_j[h_j],\sum_kd_k[k_k]\right\rangle
=\sum_{j,k}\bar c_jd_kK(h_j,k_k).
$$

把零强度空间 $N$ 商掉，得到 $H=\mathbb C ^{(\mathcal H)}/N$；
在本稿有限秩截口上它已经完备。

<a id="statement-16-1"></a>

#### 命题 16.1（正核表示与相干零关系）

该构造给一个由历史向量张成的复 Hilbert 空间，
$\langle \psi_h,\psi_k\rangle =K(h,k)$。
任何另一个最小实现都与它酉等价。

**证明。**

正半定形式的 Cauchy--Schwarz 不等式使零范数向量与全部向量正交，
故商上的内积无歧义且正定。
取 $\psi_h=[h]+N$ 即得所需比较。
两个实现之间，令同一形式历史组合相互对应；相同范数保证零关系一致，
所得映射保持内积。两侧张成性给满射等距，即酉同构。

□

这是对项目已有重建层的简要证明[7](#ref-synthesis)、[6](#ref-closure)。
它清楚区分：有限三维图画出一个二元比较，
全部相干组合的正性保证这些图能属于同一个 Hilbert 关系整体。
第[12.1](#statement-12-1)条反例说明，只检查原始标签的两两矩阵并不足够。

**白话图景。**态向量是全部内部比较的一种坐标表示。
先规定哪些历史之和没有任何可读强度，再把这些零差别认成同一内容，
就得到态空间。换一套保留全部比较的坐标，不会换掉物理关系。

### 16.2 叠加与门：共享相容锁住实际复线性

主定理使实际完整过程成为

$$
F(x)=Vx,\qquad V^*V=I,
$$

每个结果分量为 $M_e=P_eV$。
因此对于全部已声明相干表达，

$$
M_e\left(\sum_jc_jx_j\right)=\sum_jc_jM_ex_j.
$$

叠加经过同一门仍是对应后继的叠加。
连续性也成为结果：$\left\lVert Vx-Vy\right\rVert =\left\lVert x-y\right\rVert$。
这是对实际过程的约束，而不只是给样本后继另造一个线性插值。

**白话图景。**同一个内容无论怎样展开成历史之和，经过门以后仍必须对得上。
共同加入的内容不能凭空放大差别，便把每个门的续接方式锁成线性的。

### 16.3 效果与 Born 规则：结果是正的二次读出

<a id="statement-16-2"></a>

#### 定理 16.2（实际结果产生 POVM 与二次概率）

令 $`E_e=M_e^*M_e`$，则

$$
0\le E_e\le I,\qquad \sum_eE_e=I,
$$

且在已有同根强度--概率标定下，非零输入 $x$ 的结果概率为

<a id="eq-born"></a>

$$
\boxed{p(e\mid x)=\frac{\left\lVert M_ex\right\rVert ^2}{\left\lVert x\right\rVert ^2}
=\frac{\langle x,E_ex\rangle }{\left\lVert x\right\rVert ^2}.}\tag{16.1}
$$

对任意数学效果族 $E_e\ge0$、$\sum_eE_e=I$，
$Vx=\bigoplus_e\sqrt{E_e}x$ 给一个满足 v81 的完整等距实现。

**证明。**

$E_e$ 的正性来自平方范数，求和为 $`V^*V=I`$，故单项不超过 $I$。
式[(16.1)](#eq-born)是实际分支强度与根强度之比。
反向构造的范数平方为 $\sum_e\langle x,E_ex\rangle =\left\lVert x\right\rVert ^2$，
并且复线性，故满足完整共享等号和方向校准。

□

这表明完整矩阵模型中的效果结构恰为正收缩区间；
并不宣称每个效果已经可由指定原生门菜单实施。
概率的平方依赖由实际复线性和既有强度标定共同得到，
不是从一个没有任何读出含义的抽象范数单独创造概率。

### 16.4 混态：完整效果响应恰好是密度矩阵

<a id="statement-16-3"></a>

#### 定理 16.3（效果响应表示）

设同一态对全部数学效果 $0\le E\le I$ 的响应 $p(E)\in[0,1]$
满足 $p(I)=1$，且

$$
p(E+F)=p(E)+p(F)\quad(E,F\ge0,\ E+F\le I).
$$

同一个效果在不同菜单中代表同一个响应。
则存在唯一 $\rho\ge0$、$\operatorname{Tr} \rho=1$，使

$$
\boxed{p(E)=\operatorname{Tr} (\rho E).}
$$

该状态凸集的极端点恰为秩一投影。

**证明。**

可加性先给 $p(0)=0$ 与单调性；有理拆分给有理齐次性，
再用上下有理逼近与单调性得到区间中的实齐次性。
对 $A\ge0$，选 $t\ge\left\lVert A\right\rVert$、$t>0$，定义
$\ell(A)=t\,p(A/t)$。
齐次性使定义与 $t$ 无关。
用足够大的共同 $t$ 得正锥上的可加性。
继而以 $\ell(A-B)=\ell(A)-\ell(B)$ 延拓到全部自伴矩阵；
因为两个差分表达相同意味着 $A+B'=A'+B$，此定义无歧义。
有限维迹配对给唯一自伴 $\rho$，使 $\ell(X)=\operatorname{Tr} (\rho X)$。
正性给 $\rho\ge0$，$\ell(I)=1$ 给 $\operatorname{Tr} \rho=1$。

秩至少二的密度矩阵可沿两个正特征值方向作小幅相反扰动，
写成两个不同密度矩阵的平均，所以不极端。
若 $\rho=|\psi\rangle \langle \psi|$，任何正的凸分解都只能支撑在这条直线上，
迹一迫使每项等于 $\rho$，故它极端。

□

这使用全部效果的相容响应，适用于二能级情形；
不把仅有投影取值的较弱前件偷换进来。
若只给原生有限菜单，首先得到该菜单的响应商；
一般响应首先须有正相容的全效果扩展；在正密度模型内，
信息完备性才保证该有限菜单能唯一识别状态[7](#ref-synthesis)、[6](#ref-closure)。
对非零相干向量 $x$，式[(16.1)](#eq-born)对应
$\rho_x=|x\rangle \langle x|/\left\lVert x\right\rVert ^2$。

**白话图景。**一个态就是它对所有已声明读口怎样响应。
当同一读口在不同菜单里保持同一含义、互斥结果可以相加时，
这整张响应表恰好可以写成一个正的、总量为一的矩阵。
纯态是不能再混成两张不同响应表的极端情形。

### 16.5 测后态、仪器与完全正映射

若结果 $e$ 中还有可忽略的内部正交记录 $\alpha$，写

$$
M_ex=\sum_\alpha M_{e\alpha}x\otimes|\alpha\rangle .
$$

保留结果、忽略这些记录，得到

<a id="eq-instrument"></a>

$$
\boxed{\mathcal I_e(\rho)=\sum_\alpha
M_{e\alpha}\rho M_{e\alpha}^*,\qquad
\sum_{e,\alpha}M_{e\alpha}^*M_{e\alpha}=I.}\tag{16.2}
$$

结果概率为 $\operatorname{Tr} \mathcal I_e(\rho)$；若它为正，条件测后态为
$\mathcal I_e(\rho)/\operatorname{Tr} \mathcal I_e(\rho)$。
零概率结果不指定归一条件态。
对任意后续效果 $B$，实际记录分量给

$$
\operatorname{Tr} \!\left[\rho\sum_\alpha M_{e\alpha}^*BM_{e\alpha}\right]
=\operatorname{Tr} [\mathcal I_e(\rho)B].
$$

因此该更新精确重现忽略正交记录以后全部后续响应。

<a id="statement-16-4"></a>

#### 命题 16.4（完全正性与完整仪器表示）

式[(16.2)](#eq-instrument)给完全正、迹不增的结果映射；
完整带标签通道为 $\Phi(\rho)=\bigoplus_e\mathcal I_e(\rho)$，它迹保持。
若各结果共享同一可见输出空间，再忽略标签才可写作 $\sum_e\mathcal I_e$。
反向，任意有限维完全正仪器都有这样的 Kraus 与完整等距表示。

**证明。**

对任意有限辅助空间和任意 $X\ge0$，

$$
(\mathcal I_e\otimes\operatorname{id})(X)
=\sum_\alpha(M_{e\alpha}\otimes I)X(M_{e\alpha}^*\otimes I)\ge0.
$$

迹结论由效果求和给出。
反向，完全正映射的 Choi 矩阵

$$
C_\Phi=\sum_{j,k}|j\rangle \langle k|\otimes\Phi(|j\rangle \langle k|)
$$

为正，可写成有限个秩一正项之和。
把各项向量重排为矩阵 $K_\alpha$，逐个矩阵元比较便得
$`\Phi(\rho)=\sum_\alpha K_\alpha\rho K_\alpha^*`$。
对各结果作此分解，仪器完整性给
$`\sum_{e,\alpha}K_{e\alpha}^*K_{e\alpha}=I`$，
故带全部正交结果与记录的 $Vx=\bigoplus_{e,\alpha}K_{e\alpha}x$ 为等距。

□

这里使用的标准有限维表示可参见 Watrous[12](#ref-watrous)；
项目 v78 已把它接入实际结果核[7](#ref-synthesis)、[6](#ref-closure)。
一个效果只确定结果概率，并不唯一确定测后态；
实际后继与内部记录正是仪器中必须保留的部分。

### 16.6 投影测量与 Lüders 更新的准确条件

<a id="statement-16-5"></a>

#### 命题 16.5（尖锐效果与无扰投影支路）

效果区间 $[0,I]$ 的极端点恰为正交投影。
若同一输入输出空间 $H$ 上某结果的效果是投影 $P$，
且其实际仪器保持 $\operatorname{ran}  P$ 中每一个单位纯态不变，
则该结果映射必须为

$$
\boxed{\mathcal I_P(\rho)=P\rho P.}
$$

**证明。**

效果若有严格介于 $0,1$ 的特征值，可沿该特征方向作小幅正负扰动，故不极端。
若投影 $P=(E+F)/2$，在 $\operatorname{ker}  P$ 上正性迫使 $E,F$ 为零，
在 $\operatorname{ran}  P$ 上 $I-E,I-F$ 的正性迫使 $E,F$ 为恒等，故 $E=F=P$。

写实际仪器为 $`\sum_\alpha K_\alpha\rho K_\alpha^*`$，
$`\sum K_\alpha^*K_\alpha=P`$ 迫使每个 $K_\alpha$ 消去 $\operatorname{ker}  P$。
对 $\operatorname{ran}  P$ 中每个 $\psi$，纯态输出不变意味着各 $K_\alpha\psi$
都在 $\mathbb C \psi$ 内。
线性算符若保留该空间的每条向量直线，用基向量及其两两之和即可证明它为标量，
所以 $K_\alpha=c_\alpha P$。
若 $P\ne0$，效果式给 $\sum|c_\alpha|^2=1$，得到结论。
若 $P=0$，全部 $K_\alpha=0$，公式仍成立。

□

仅要求再次测得同一个结果，不足以指定 Lüders 仪器；
上面的所有范围内纯态不扰动条件承担了剩余限制。
给一组正交投影 $P_a$ 配上实读数 $a$，得到
$`A=\sum_a aP_a=A^*`$，即标准自伴可观测量。
读数的单位与数值标定仍由该实际仪器确定。

**白话图景。**结果概率与结果之后留下什么内容，是两份信息。
读口如果只做一个尖锐筛选，并且对已经在筛选范围里的任何态都不改动，
它才被锁成通常的投影更新；若允许额外转动，便有别的合法仪器。

### 16.7 复合系统：独立比较乘积给张量积

<a id="statement-16-6"></a>

#### 定理 16.6（乘积核的复合表示）

对已声明独立准备，若完整比较满足

$$
K_{AB}((h,k),(h',k'))=K_A(h,h')K_B(k,k'),
$$

并且这些乘积历史的相干组合张成该联合截口，
则其最小表示酉等价于 $H_A\otimes H_B$。

**证明。**

令 $\psi_h\otimes\phi_k$ 对应联合历史向量。
两个乘积向量的内积正是右边的核乘积。
双线性扩展保持全部有限组合内积，故零关系一致，诱导等距。
联合张成性使它满射，得到酉等价。

□

一般联合向量未必可分解成单个乘积，这就是纯态纠缠的空间来源。
把实际局部实验识别为仅作用一端的算符，还使用已有端口作用供应：
在产品历史上，局部续接只替换相应端口的后继，并保留另一端及相关参考。
乘积历史的张成性随即把它唯一延拓为 $M_A\otimes I_B$，
因此该实际局部读口由 $E\otimes I$ 表示。
唯一满足

$$
\operatorname{Tr} (\rho_{AB}(E\otimes I))=\operatorname{Tr} (\rho_AE)
$$

的局部态就是偏迹 $\rho_A=\operatorname{Tr} _B\rho_{AB}$。
任意密度矩阵的谱分解
$\rho=\sum_jp_j|j\rangle \langle j|$ 给纯化
$\sum_j\sqrt{p_j}|j\rangle \otimes|j\rangle$；
这是矩阵模型中的纯化表示，不自动供应任意原生纯化制备门。

完整局部通道的 $`\sum_\alpha K_\alpha^*K_\alpha=I`$ 还给

$$
\sum_\alpha
\operatorname{Tr} \!\left[\rho_{AB}(E\otimes K_\alpha^*K_\alpha)\right]
=\operatorname{Tr} [\rho_{AB}(E\otimes I)].
$$

所以未选择远端结果时，本地统计不变。
选择并通信一个结果后的条件统计，是另一项声明。

项目最新设置--源定理已在明确的十六位完整自适应菜单上供应
设置与完整源联合独立以及无后选择非经典见证[8](#ref-whole)。
这里继承其具体范围；不把该已证明供应再视作一般性悬缺，
也不把任意扩大来源或控制域自动纳入结论。

**白话图景。**当两份准备的全部比较独立相乘，整体坐标就是张量积。
整体允许相干相加后，会出现不能拆成两个独立态的关系，这就是纠缠。
每边把全部结果保留时，另一边的总统计不会被远处的局部操作改变。

### 16.8 连续演化：同维完整门给酉，平滑门族给薛定谔方程

<a id="statement-16-7"></a>

#### 定理 16.7（内部时间参数下的演化）

若完整输出仍为同一个有限维 $H$，主定理的 $`V^*V=I`$ 使 $V$ 为酉。
若已供应可微酉族 $U(t)$，$U(0)=I$，及非零正标度 $\hbar$，定义

$$
H(t)=i\hbar\dot U(t)U(t)^*.
$$

则 $`H(t)=H(t)^*`$，且 $\psi(t)=U(t)\psi(0)$ 满足

$$
\boxed{i\hbar\dot\psi(t)=H(t)\psi(t).}
$$

若另有自主群条件 $U(t+s)=U(t)U(s)$，则 $H$ 为常量，
$U(t)=e^{-itH/\hbar}$。

**证明。**

有限同维等距是满射，故酉。
微分 $`U(t)U(t)^*=I`$ 得
$`\dot U U^*+U\dot U^*=0`$，所以 $`i\dot U U^*`$ 自伴。
将定义代入 $`\dot\psi=\dot UU^*\psi`$ 即得方程。
群条件在第二参数零点微分给 $\dot U(t)=U(t)\dot U(0)$；
交换两个时间参数再微分也给 $\dot U(t)=\dot U(0)U(t)$。
因此 $`\dot U(t)U(t)^*=\dot U(0)`$，生成元固定，矩阵指数解给最后一句。

□

共享条件没有确定实际 Hamiltonian 的谱、$\hbar$ 的经验单位值，
也没有把一串离散门字自动变为唯一连续插值。
历史的平滑性、时钟和自主性按项目既有条件分别供应[7](#ref-synthesis)。
一般 Hamiltonian 轨迹不必是球面大圆；
一般多频谱也不必具有严格共同周期。
第[14.1](#statement-14-1)条给的是有固定公共部分、单一相位参数的可证圆族。

**白话图景。**一个完整门把所有比较留住；输入输出维数相同时，它就是酉门。
当内部时钟让门连续而平滑地变化，变化率必然由一个自伴生成元描述，
这就得到薛定谔方程。具体转多快、绕什么方向转，仍由实际相互作用决定。

### 16.9 顺序、干涉与理论闭合

若结果 $e$ 后接完整条件菜单 $\{N_{f|e}\}_f$，则

$$
M_{ef}=N_{f|e}M_e,\qquad
\sum_fM_{ef}^*M_{ef}=M_e^*M_e.
$$

因此细化结果求和回到原效果，理论在顺序接续下闭合。
已声明独立复合的过程由张量积接续；保留或忽略正交记录由直和与偏迹处理。
这些组合仍满足完全正性和总量条件。

对同一相干分支，

$$
\left\lVert M(x+y)\right\rVert ^2
=\left\lVert Mx\right\rVert ^2+\left\lVert My\right\rVert ^2
+2\operatorname{Re} \langle Mx,My\rangle .
$$

相位改变交叉项，产生干涉。
相同二次式的三条路径包含--排除组合恒为零：

$$
\begin{aligned}
I_3={}&w(x+y+z)-w(x+y)-w(x+z)-w(y+z)\\
&+w(x)+w(y)+w(z)=0,
\end{aligned}
$$

其中 $w(v)=\left\lVert Mv\right\rVert ^2$。
该结论比较同一个固定过程与一致路径组合；
若堵住路径时改变整个仪器，已经改变了被比较的映射，不能直接套用。
两门也不必交换，故历史顺序通常不能从过程地址中删去。

**白话图景。**量子概率不是先给每条路径一份概率再加起来。
先把带相位的内容相加，再读其强度，于是出现两两交叉项。
分支继续接分支、系统继续组合、记录继续保留或忽略，都留在同一套结构中。

<a id="section-17"></a>

## 17. 完整理论的对应表与内生含义

<a id="statement-17-1"></a>

#### 定理 17.1（v81 有限关系理论的表示闭合）

在下列已经明确的层次上工作：
共同复正核及其相干商；完整实际输出、同根强度标定与有限共同方向；
本稿共享内容相容；全效果响应的相容扩展；
已声明独立复合的乘积核、产品历史张成及相容的实际局部端口作用；
以及需要动力学时的内部可微门族。
则所得到的表示、概率、后继和组合满足有限维复量子理论的标准规则。
反向，有限维复量子理论的完整等距与记录表示满足本稿共享候选。

**证明。**

正核商给状态 Hilbert 表示；主定理给全部实际后继的复线性等距。
效果定理与响应表示给 POVM、Born 概率和密度矩阵。
记录分解给完全正仪器，其标准表示给反向闭包。
乘积核给张量积；完整结果求和给局部不传信和顺序边缘相容。
同维完整过程及内部可微族给酉与薛定谔演化。
最后，任意复线性等距直接满足

$$
\left\lVert V(x+c)-V(y+c)\right\rVert ^2
=\left\lVert V(x-y)\right\rVert ^2
=\left\lVert x-y\right\rVert ^2,
$$

并满足完整强度与方向校准。

□

这是有限矩阵层的表示闭合，不是宣称任意数学合法控制均已有原生门编译。
若实际菜单只供应其中一部分，得到的是该菜单及其合法接续的量子实现。
也不把有限截口的证明直接提升为含非有界算符的连续场论。

| 通常的量子规则 | 在本理论中的来处 | 不能略去的范围条件 |
| --- | --- | --- |
| 复 Hilbert 态空间 | 共同复正核的零空间商及最小表示唯一性 | 继承 Q1；正性覆盖全部相干组合，共同 $J$ 已固定 |
| 叠加与线性过程 | 共享相容、完整强度、有限方向推出实际等距 | 全域实际映射、跨输入共同相位、完整记录 |
| Born 概率与 POVM | $`E_e=M_e^*M_e`$，总效果 $I$，结果强度为二次式 | 同根强度--概率标定已供应 |
| 密度矩阵与混态 | 全效果上的正、归一、相容可加响应 | 同效果同响应；有限菜单须有正相容扩展，信息完备性保证唯一识别 |
| 测后态与 CP 仪器 | 完整等距的结果和正交记录分量 | 概率效果不能替代实际后继；零概率不归一化 |
| 投影与 Lüders 更新 | 极端效果是投影；每个范围内纯态无扰迫使 $P\rho P$ | 仅重复同结果不足以指定无扰仪器 |
| 复合与纠缠 | 独立乘积核与联合张成给张量积 | 作用于相应端口的实际局部续接；完整源与控制菜单固定 |
| 不可复制、无扰读址限制 | 等距保持非正交态的内积 | 已知程序标签与未知态读口必须区分 |
| 酉与薛定谔演化 | 同维完整等距；可微族的自伴生成元 | 时钟、平滑性、实际 Hamiltonian 与物理单位须另有供应 |
| 干涉及零三阶项 | 同一固定过程上的二次强度展开 | 不能在不同路径配置下暗换整个仪器 |

### 17.1 公理成为哪些定义之间的约束

“内生”在这里有一个可检验的意思。
用来比较两条历史的参考、承载 $J$ 的相位操作、加入的共同内容、
保留的分支记录以及读出时钟，都由 $\Omega$ 内的同一声明结构承载。
定义[3.3](#statement-3-3)不调用一个从整体之外操纵状态的观察者。
它约束内部准备、组合、续接、记录与读出之间能否相互替换。

三个位置不能因为改称“定义”就消失：

1. 共同正核和复方向说明采用了什么相干比较；实、复与其他关系模型在此具有不同内容。

2. 完整强度和共享约束说明哪些实际后继可与该比较一起成立。

3. 读出、独立复合与时钟说明如何把这些关系解释为概率、子系统与演化。

本轮已经把第二项的核心入口收敛为共同加项条件，并对删除条款给出反例。
因此它是可反驳、可定位的相容定义，不是只靠换名字就无需检验的必然真理。
例如“所有状态、门和读口都在一个集合中”这一闭包陈述，
同样可在有限经典模型中成立；它本身不供应复相干组合。
这里继续采用此前已经给出的供应，而不把那些问题重新提出为未讨论事项。

### 17.2 本轮没有改写成结论的直觉

用户直觉中的几个句子，现在各有精确落点：

1. “门序列是内容寻址”：成立于指定根和足够完整的未来接口；

   不同门字可以同址，状态地址不自动等于过程地址。
2. “多个态共享子态”：相对于声明共享方式成立；

   本稿的同幅分支具有精确最大值，不等于所有纯态都含同一正子密度块。
3. “共同加入不改变差别”：由可逆共享相容和完整强度证明，

   不是把真实事件倒退删除。
4. “三维分解非线性关系”：二元尺度与球坐标可以完整编码该对的 Gram 数据；

   所有对必须继续服从共同正核，不能只拼任意两两球点。
5. “圆解释周期、椭圆解释偏转”：固定公共幅度加单一相位给圆族，

   固定两读口给椭圆型响应；并没有证明任何偏离历史切线的目标都会产生椭圆。

例如自主三能级系统取 $H/\hbar=\operatorname{diag}(0,1,\sqrt2)$，
初态三个分量都非零。若存在严格正射线周期 $T$，则
$T\in2\pi\mathbb Z$ 且 $\sqrt2T\in2\pi\mathbb Z$，矛盾。
所以有限量子运动本身也不强制每条轨迹严格周期。
这一解析反例将“有一个相位圆”和“所有频率共同返回”明确区分。

**白话图景。**所有关系都由整体内部承载，意味着比较尺、参考、读口和记录都在同一张图里。
公理于是可以写成这些内部定义彼此不得冲突的要求。
但“都在图里”不会让每一种画法都自动一致；
本轮证明的正是哪些共同加入会迫使唯一的线性接续，
以及哪些看起来相近的共享说法其实对应不同任务。

<a id="section-18"></a>

## 18. 用一段完整白话描述这一门量子理论

整体 $\Omega$ 包含一切可用的准备、历史、参考和读出。
从其中一个指定根出发，门序列把内容接续成新的内容；
不同路线可以到达同一态，但当前地址不必保存整条路线。
态的意义来自它与其他态怎样比较，
而“相位”表示这些比较在共同内部参考下怎样转动。

两份内容可以写成共同部分与各自余量。
把同一份带相位的内容同时加入两端，不能凭空制造更大的剩余差别；
再把这份内容反向去掉，就知道差别其实必须完全相同。
把所有结果和记录保留下来的总强度，连同共同的相位方向，
于是锁住了每个门：同一内容的不同相干写法，经过门后仍须对得上，
实际过程因此只能复线性地接续。

读口从这份内容中取一个分支，分支强度就是出现该结果的权重；
全部分支之和回到总量，这给出 Born 概率与一般量子测量。
若几个地址想在同一分支里留下完全一样的幅度，就必须消去它们所有的差异方向；
垂直剩下的共同投影，是最多能一起保留的一份。
没有消失的区别留在其他分支或记录里，所以任意未知态不能被无扰辨址或复制。

共同部分固定、剩余部分转相位时，内容绕成一个圆；
固定读口把圆的不同方向读成不同强度，便出现椭圆与周期。
独立准备的比较相乘，使系统组合成张量积；整体的相干组合产生纠缠。
当完整门在内部时钟下平滑变化，它的变化率就是自伴生成元，
于是得到薛定谔演化。
量子在这套理论中，是同一个整体里，内容的组合、共同参考、分支读出和历史续接
必须同时相容时形成的关系结构。

## 核读、证明与增量说明

本稿固定在上述公开提交，不把后来变化混入本版本。
本轮缓存并核验了十七个源文件的 Git blob 身份，
另对上轮相关缓存作定向检索；这些范围相互重叠，
不合并声称已逐字审阅六十七篇全文。
关键内容地址、共同振幅预算、N2 共享补全、
最新设置--源供应及原生恢复边界均按各自前件使用。
本文关于等距与共享预算的推导由独立解析复核检查；
源文件下载、哈希核验、排版和页面检查不承担数学证明。
本稿未运行数值模拟、数学脚本、枚举实验或计算机代数来替代证明，
也未完成 Lean 形式化验证。

新候选的价值是把 v80 同一实际过程类别重新组织成更直接的共同内容约束，
并把既有核支配结构显式推进到最大共同分支、奇异边界和圆族读出。
标准等距表示、一般 Gram 概率变换和 Kraus 理论保留既有归属。
本稿给出的是条件明确的有限理论与候选，不额外宣称新的实验效应或已证明的普遍最小公理数。

## 固定来源与证明归属

<a id="ref-v80"></a>

**[1]**
项目 v80：[全部结果二元差分不增、有限定向锚与内生量子过程](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_ALL_OUTCOME_BINARY_DIFFERENCE_NONEXPANSION_FINITE_ORIENTED_ANCHORS_AND_ENDOGENOUS_QUANTUM_PROCESSES_V80.md)。
重点为第 3、5、6.3、16 节，同一实际接口的等价及范围。

<a id="ref-v79"></a>

**[2]**
项目 v79：[二元反向相容、有限相位证书与量子读出重建](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_BINARY_REVERSAL_COMPATIBILITY_FINITE_PHASE_CERTIFICATES_AND_QUANTUM_READOUT_RECONSTRUCTION_V79.md)。

<a id="ref-v67"></a>

**[3]**
项目 V67：[单一本体态中的历史脚本、内容寻址与量子纠缠](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_HISTORY_SCRIPTS_CONTENT_ADDRESSING_AND_QUANTUM_ENTANGLEMENT_IN_ONE_ONTIC_STATE_V67.md)。
重点为第 2.3--2.4、4.2、6.2、6.4 节。

<a id="ref-n2"></a>

**[4]**
项目 N2：[共享历史充分性、最小内部补全与维数预算](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_SHARED_HISTORY_SUFFICIENCY_MINIMAL_INTERNAL_COMPLETION_AND_DIMENSION_BUDGET_N2_V78_CONTINUATION.md)。

<a id="ref-foundations"></a>

**[5]**
项目基础与记录卷：[Foundations and Records](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/ContextualSpacetimeQuantum/001_016_FOUNDATIONS_AND_RECORDS.md)，第 6 节。
已有共同振幅分支界、任意记录族提取条件及一般 Gram 判据归属。

<a id="ref-closure"></a>

**[6]**
项目 v78 闭包续稿：[内生闭包、有限根证书与结果核递归](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_ENDOGENOUS_CLOSURE_FINITE_ROOT_CERTIFICATES_AND_OUTCOME_KERNEL_RECURSION_V78_CONTINUATION.md)。
重点为第 7.2、8.1 节的受支配核、效果与实际收缩。

<a id="ref-synthesis"></a>

**[7]**
项目 v78 综合稿：[内生关系量子理论与统一关系公理](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_ENDOGENOUS_RELATIONAL_QUANTUM_THEORY_UNIFIED_RELATIONAL_AXIOMS_V78_SYNTHESIS.md)。

<a id="ref-whole"></a>

**[8]**
项目设置--源续稿：[单一纯整体中的设置--源关系](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_SINGLE_PURE_WHOLE_SETTING_SOURCE_RELATIONS_V78_CONTINUATION.md)。
本快照新增第 8--12 节；第 9.1 定理给特定完整有限自适应菜单的内部供应。

<a id="ref-reconstruction"></a>

**[9]**
项目相干恢复续卷 V：[原生恢复前沿与精确 ready 边界](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_V.md)。
第 9--10 节的恢复结论以具体原生菜单、跳跃过程与未来核为前件。

<a id="ref-omega"></a>

**[10]**
项目整体结构稿：[Omega 静态相容纤维理论](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)。
定义 1.1 及第 3--4 节区分整体、路径运输与未来响应商。

<a id="ref-cjw"></a>

**[11]**
A. Chefles, R. Jozsa, A. Winter.
*On the existence of physical transformations between sets of quantum states*.
International Journal of Quantum Information 2(1), 11--21 (2004).
[arXiv:quant-ph/0307227v1](https://arxiv.org/abs/quant-ph/0307227v1)。
第 3 节定理 3 及式 (9) 给概率纯态变换的一般 Gram 半正定判据；
本稿共同完整幅度是其秩一固定记录特化。

<a id="ref-watrous"></a>

**[12]**
J. Watrous. *The Theory of Quantum Information*, Chapter 2.
[作者公开章稿：基本概念、通道与完全正表示](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)。
标准 Choi、Kraus 与完整记录表示。

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
pdftitle={AURIC v81：共享内容相容、量子寻址与最大共同分支}}
\pagestyle{fancy}\fancyhf{}
\fancyhead[L]{\small AURIC / v81 / 共享内容与量子寻址}
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
\renewcommand{\refname}{固定来源与证明归属}
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
\newcommand{\kerop}{\operatorname{ker}}
\newcommand{\ket}[1]{|#1\rangle}
\newcommand{\bra}[1]{\langle#1|}
\newcommand{\Exec}{\operatorname{Exec}}
\newcommand{\plain}[1]{\par\noindent\textbf{白话图景。}#1\par}
\newcommand{\repo}[2]{\href{https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/#1}{#2}}
\title{\color{ink}\bfseries 共享内容相容公理\\[6pt]
\large 从内容寻址到量子过程与最大共同分支\\[4pt]
AURIC v81：一个完整候选及其有限量子理论}
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
\begin{center}\small\texttt{c63ab162315fddd0801cbe9f47dbf3eda6e13360}\end{center}
\begin{center}\small
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.26\textwidth}X@{}}
\toprule
\\
\midrule
\\
\\
\\
\\
\bottomrule
\end{tabularx}
\end{center}
{\small
\begin{longtable}{@{}>{\raggedright\arraybackslash}p{.20\textwidth}
>{\raggedright\arraybackslash}p{.35\textwidth}
>{\raggedright\arraybackslash}p{.39\textwidth}@{}}
\toprule
\\
\midrule
\endfirsthead
\toprule
通常的量子规则 & 在本理论中的来处 & 不能略去的范围条件\\
\midrule
\endhead
\\[4pt]
\\[4pt]
\\[4pt]
\\[4pt]
\\[4pt]
\\[4pt]
\\[4pt]
\\[4pt]
\\[4pt]
\\
\bottomrule
\end{longtable}}
\begin{thebibliography}{20}
\end{thebibliography}
\end{document}
```
