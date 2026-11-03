# 重叠二元关系、三轴提升与量子 Markov 拼接

从同一共享部分到双向恢复、整体补全与链式闭合

**AURIC v91：一个完整候选的定义、定理与反向审计**

项目连续研究稿

2026 年 11 月 3 日（新加坡）

## 摘要

v90 证明了一个二态内生平方等式与共同恢复的等价。
v91 继续研究两份重叠关系：已知 $\rho_{AB}$ 与 $\rho_{BC}$ 在 $B$ 上读出一致，
它们何时足以通过同一个中间系统拼出一份没有额外跨翼条件关联的整体？
本轮唯一候选 C91 要求由左、右两侧分别构造的规范 Petz 补全相同。

记 $\Theta=\rho_{BC}^{1/2}\rho_B^{-1/2}\rho_{AB}^{1/2}$，
候选就是 $\Theta\Theta^\dagger=\Theta^\dagger\Theta$。
我们在共同支撑上证明：该条件等价于单侧补全保留另一边际、
存在局部恢复扩张，以及共享系统的直和左右因子分块。
核心结构证明直接使用 v89 的保忠实态固定代数，不预设熵等号条件。
进一步证明唯一 Markov 补全与最大熵性质，并将给定真实全态的恢复问题准确接回 v90。

一个完全解析的三比特 Pauli 家族把两项关系与它们的交叉关系提升到三条正交轴。
它同时分离共享读数一致、任意整体可行、Markov 拼接和原全态识别。
一般双向补全的 Gram 表另给有限三维证书；小缺额控制边际误差，
不被误称为任意原整体或精确 Markov 结构的恢复。
对有限链证明三节点 C91 可逐段拼成唯一全链 Markov 态，
并用严格正的经典三角形反例说明闭环需要额外全局相容。

正规性判据、Markov 分块和 Pauli 反例均有一手文献来源，
包括 2019 年的双边际恢复工作及 2026 年10月版本的 Markov 边际研究。
本稿的新角色是项目中的内部约束组织与完整接续，不作已有数学的优先权主张。
未运行数学程序、CAS、数值实验或候选枚举。

## 目录

- [1. 本轮接续的真实缺口：共享相同不等于整体可拼](#section-1)
- [2. 两个关系元、共同内部校准与唯一候选 C91](#section-2)
- [3. 先反着推：相同接口、可行整体与完整拼接并不相同](#section-3)
- [4. 有限三维提升：两条关系轴与它们的交叉关系](#section-4)
- [5. 两种规范拼接各自保留什么](#section-5)
- [6. 忠实固定态怎样迫出共同块因子](#section-6)
- [7. 双向相容、局部恢复与 Markov 分块的完整等价](#section-7)
- [8. 为什么这个拼接恰是唯一最大熵补全](#section-8)
- [9. 熵为什么给出同一个缺口：有限维强次可加的证明](#section-9)
- [10. 零熵缺口与左右分块：自证部分和调用部分](#section-10)
- [11. v90 的内生中点怎样认证实际全态](#section-11)
- [12. 近似误差与原整体：零资格能换，数值不能直接换](#section-12)
- [13. 两条补全的三维比较：长度相同仍须方向相同](#section-13)
- [14. 近似一致能保证什么：一个明确的边际误差界](#section-14)
- [15. 共享、兼容与真实整体是三种不同声明](#section-15)
- [16. 从三节点窗口到整条链：局部条件何时足够](#section-16)
- [17. 闭圈会增加独立约束：一个严格正的三角形反例](#section-17)
- [18. 树上的安全推广：每次检查完整的当前子树](#section-18)
- [19. 放回更大的结构：相对接口、共享内容与关系场](#section-19)
- [20. 怎样推回现有量子力学公理：完整的条件链](#section-20)
- [21. 反向审计：每一条约束到底排除了什么](#section-21)
- [来源、版本与核读范围](#references)

<a id="section-1"></a>

## 1. 本轮接续的真实缺口：共享相同不等于整体可拼

<a id="sec-c91-scope"></a>

版本由 v90 递增到 v91。对 GitHub 当前 HEAD 进行了一次有界公开读取，未成功；
因此本轮仓库依据仍固定于

`c63ab162315fddd0801cbe9f47dbf3eda6e13360`

下已取得的文本，以及本对话已经完成的 v88、v89、v90。
也检查了现存较早快照中的 Markov、Petz 和循环相容条目；它们的版本与问题范围不混用。

项目的 $\Omega$ 静态理论 §8 已经给出 Bell–Bell 反例：
两份二体态虽然具有同一个中间边际，却未必存在任何共同三体态。
V78 综合稿 §20.2 又明确限定：N2 的共享振幅残差补足，
不是一般混合态边际问题的解，也不会自动给量子 Markov 条件 [1](#ref-omega)、[2](#ref-v78)、[3](#ref-n2)。
本轮正接续这一已经写明的缺口。

v88 给保态条件期望及分块，v89 从具体过程得到稳定关系代数，
v90 用二态平方缺额认证共同恢复 [8](#ref-v88)、[9](#ref-v89)、[10](#ref-v90)。
本轮进一步问：**同一个共享系统怎样同时承接左右两份关系，
使两种内部补全得到同一个整体？**

标准数学中，这对应短量子 Markov 链的可恢复拼接。
Di Giorgio–Mateus–Mera 的 Theorem2 已证明重叠边际的正规性判据，
Hayden–Jozsa–Petz–Winter 给出中间系统的完整分块结构 [11](#ref-dgmm)、[12](#ref-hjpw)。
Lauritzen–Zwiernik 的 2026年10月1日 v3 进一步讨论弦图上的 Markov 边际与对数迹判据，
并给出本稿将展开的 Pauli 例子 [14](#ref-lz2026)。
这些来源帮助核定数学，而非被改名为新的物理实验事实。

**白话图景。**左边知道“甲与中间怎样相连”，右边知道“中间与乙怎样相连”。
两边对中间的读数一样，只说明接口对上了；还不说明两份关系能放进同一个整体。
本轮要比较从左边补右边、从右边补左边这两种构造。
如果它们给出同一份内容，共享部分才足以完成这次特定拼接。

<a id="section-2"></a>

## 2. 两个关系元、共同内部校准与唯一候选 C91

<a id="sec-c91-definition"></a>

### 定义 2.1（重叠二元输入）

给定有限维非零复 Hilbert 载体 $A,B,C$，以及归一正态
$\rho_{AB}$、$\rho_{BC}$，满足

$$
\operatorname{Tr}_A\rho_{AB}=\operatorname{Tr}_C\rho_{BC}=:\rho_B.
$$

先把 $B$ 限制为 $\operatorname{supp}\rho_B$，所以 $\rho_B>0$。
下面的算符乘积都嵌入 $A\otimes B\otimes C$，未显示的因子补单位。

两个输入元是两份关系 $\rho_{AB},\rho_{BC}$。
$A,B,C$ 是子系统接口，不能从字母数目推断物理空间维数。
共同 $B$ 由两份输入本身确定；本轮没有从 $\Omega$ 外再放入一个绝对锚。
原边际允许不满秩，只有实际共同支撑上的 $\rho_B$ 需要取逆。

### 定义 2.2（规范的双向补全）

定义

<a id="eq-c91-right-recovery"></a>

$$
\mathcal R^C(X)
=\rho_{BC}^{1/2}
 (\rho_B^{-1/2}X\rho_B^{-1/2}\otimes I_C)
 \rho_{BC}^{1/2},
\tag{2.1}
$$

$$
\mathcal R^A(X)
=\rho_{AB}^{1/2}
 (I_A\otimes\rho_B^{-1/2}X\rho_B^{-1/2})
 \rho_{AB}^{1/2}.
\tag{2.2}
$$

再令

<a id="eq-c91-theta-pq"></a>

$$
\Theta=\rho_{BC}^{1/2}\rho_B^{-1/2}\rho_{AB}^{1/2},
\qquad P=\Theta\Theta^\dagger,
\qquad Q=\Theta^\dagger\Theta.
\tag{2.3}
$$

这两个补全分别是

$$
P=(\operatorname{id}_A\otimes\mathcal R^C)(\rho_{AB}),\qquad
Q=(\mathcal R^A\otimes\operatorname{id}_C)(\rho_{BC}).
$$

后文会证明两个映射确实 CPTP，且 $P,Q$ 都是密度态。
它们无条件分别保留 $BC$ 与 $AB$ 边际；各自是否也保留另一边，正是需要检查的关系。
字母 $P,Q$ 在这里表示规范状态，不预设为投影。

### 定义 2.3（本轮唯一候选：双向内部拼接相容）

<a id="def-c91"></a>

被称为*可由共享系统 $B$ 完整 Markov 拼接*的二元关系，满足

<a id="eq-c91"></a>

$$
\boxed{\qquad P=Q,
\quad\text{即}\quad
\Theta\Theta^\dagger=\Theta^\dagger\Theta.\qquad}
\tag{C91}
$$

右式说 $\Theta$ 是正规算符。

C91 是当前声明的拼接类型的资格条件，不要求任意合法三体量子态都是 Markov 态。
已知边际能确定一个规范补全，与这些边际足以恢复未知真实全态，是两项不同声明。
后文分别给出定理和反例。

### 命题 2.4（保迹性固定正夹乘校准）

若在给定 $\rho_{BC}$ 上选择正定 $J_B$，并考虑同类夹乘规则

$$
\mathcal R_J(X)=\rho_{BC}^{1/2}(J_BXJ_B\otimes I_C)\rho_{BC}^{1/2},
$$

则它保迹当且仅当 $J_B=\rho_B^{-1/2}$。

**证明。**
对全部 $X$，有
$\operatorname{Tr}\mathcal R_J(X)=\operatorname{Tr}(XJ_B\rho_BJ_B)$。
因此保迹恰好等价于 $J_B\rho_BJ_B=I$。
两侧乘 $J_B^{-1}$ 得 $\rho_B=J_B^{-2}$，正性给唯一正解
$J_B=\rho_B^{-1/2}$。反向代入即得保迹。

这个有限唯一性只针对已声明的正夹乘类；不声称所有量子恢复都只能有该形式。
它说明共同边际的逆平方根如何由内部归一要求锁定。
若在共享部分使用不相容的校准，同样的公式就不再保持完整概率总量。

**白话图景。**这次比较的两个元本身就是关系。它们共同包含的中间部分，提供了校准尺度。
从左补右和从右补左，各自都能构成合法状态；本轮只加一个明确的闭合要求：两者必须相同。
这个要求不会预先宣布所有整体都没有额外关联；它检查的是我们何时有资格这样拼接。

<a id="section-3"></a>

## 3. 先反着推：相同接口、可行整体与完整拼接并不相同

<a id="sec-c91-pauli"></a>

先用一个全解析例子看清：删去 $C_{91}$ 会发生什么。
这个两份 Pauli 边际的家族及其圆盘可行域，见
Lauritzen–Zwiernik 2026 年 v3 的 §4.2、Example4.3、Lemma4.4；
其 Markov 资格见 §4.3、Lemma4.6 [14](#ref-lz2026)。
以下明确沿用该家族，并展开规范补全、第三关系轴和边界支撑的证明。

取 $A,B,C$ 都是 qubit，$X,Y,Z$ 表示标准 Pauli 矩阵。定义

<a id="eq-c91-three-pauli"></a>

$$
K=X_A\otimes X_B\otimes I_C,\qquad
 L=I_A\otimes Z_B\otimes Z_C,
 \qquad M=iKL=X_A\otimes Y_B\otimes Z_C.
\tag{3.1}
$$

由 $XZ=-iY$ 直接得到

$$
K^2=L^2=M^2=I,\qquad KL=-LK,
 \qquad \frac18\operatorname{Tr}(K_iK_j)=\delta_{ij},
 \quad (K_1,K_2,K_3)=(K,L,M).
$$

三者两两反对易。特别地，$[K,L]=-2iM$；本处的有向次序与标准
$(X,Y,Z)$ 的取向相反。交换 $K,L$ 会翻转 $M$，不产生绝对手性的物理结论。

给定重叠边际

<a id="eq-c91-pauli-marginals"></a>

$$
\rho_{AB}=\frac{I_{AB}+aX_A\otimes X_B}{4},\qquad
 \rho_{BC}=\frac{I_{BC}+bZ_B\otimes Z_C}{4},
 \qquad -1\le a,b\le1.
\tag{3.2}
$$

两者各自合法，并且对整个参数正方形始终具有相同的
$\rho_B=I_B/2$。相同接口没有再约束 $a,b$。

### 命题 3.1（一般整体可行域恰为圆盘）

<a id="prop-c91-pauli-disk"></a>

式 [(3.2)](#eq-c91-pauli-marginals) 存在任意共同三体扩张，当且仅当

<a id="eq-c91-pauli-disk"></a>

$$
a^2+b^2\le1.
\tag{3.3}
$$

**证明。**
令 $r=\sqrt{a^2+b^2}$。反对易性给出
$(aK+bL)^2=r^2I$。若 $r\le1$，则

<a id="eq-c91-pauli-maxent-state"></a>

$$
\omega_0=\frac18(I+aK+bL)
\tag{3.4}
$$

为正、迹为一，并有要求的两个边际，证明充分性。

反过来，任意兼容态 $\zeta$ 都满足
$\operatorname{Tr}(\zeta K)=a$、$\operatorname{Tr}(\zeta L)=b$。
若 $r>0$，$aK+bL$ 的最大特征值为 $r$，因此

$$
r^2=\operatorname{Tr}[\zeta(aK+bL)]\le r,
$$

得到 $r\le1$；$r=0$ 自动满足。这里不假定 $\zeta$ 只有 Pauli 三项。

### 命题 3.2（本家族中 C91 恰为两条坐标轴）

<a id="prop-c91-pauli-markov"></a>

两个规范补全精确为

<a id="eq-c91-pauli-p"></a>

$$
P=\frac18\left[I+bL+a\sqrt{1-b^2}\,K\right],
\tag{3.5}
$$

<a id="eq-c91-pauli-q"></a>

$$
Q=\frac18\left[I+aK+b\sqrt{1-a^2}\,L\right].
\tag{3.6}
$$

所以在整个参数正方形上，

<a id="eq-c91-pauli-axes"></a>

$$
C_{91}\quad\Longleftrightarrow\quad ab=0.
\tag{3.7}
$$

**证明。**
由 $\rho_B^{-1/2}=\sqrt2 I$，有

$$
\Theta=\frac1{2\sqrt2}\sqrt{I+bL}\sqrt{I+aK}.
$$

写 $\sqrt{I+bL}=uI+vL$，其中

$$
u=\frac{\sqrt{1+b}+\sqrt{1-b}}2,
 \qquad v=\frac{\sqrt{1+b}-\sqrt{1-b}}2.
$$

于是 $u^2-v^2=\sqrt{1-b^2}$，且

$$
(uI+vL)K(uI+vL)=(u^2-v^2)K,
$$

交叉项因反对易相消。这就给出式 [(3.5)](#eq-c91-pauli-p)；另一式同理。
$K,L$ 线性独立，所以 $P=Q$ 等价于

$$
a(\sqrt{1-b^2}-1)=0,
 \qquad b(1-\sqrt{1-a^2})=0.
$$

若 $ab\ne0$，第一式要求 $b=0$，矛盾；若 $ab=0$，两式直接成立。
端点 $|a|=1$ 或 $|b|=1$ 也被以上公式覆盖。

因此，$P$ 保留右侧关系强度 $b$，却把左侧强度 $a$ 缩成
$a\sqrt{1-b^2}$；$Q$ 的作用相反。
两个规范补全在整个正方形都合法；在圆盘外，它们各自改变了另一边际，
所以并没有构成不存在的共同扩张。
在圆盘内、坐标轴之外，确实存在共同整体，但不存在本轮声明的 Markov 拼接。

<a id="fig-c91-disk"></a>

```text
                         b
                         ↑
          ┌──────────────●──────────────┐
          │         ·    ║    ·         │
          │    ·         ║         ·    │
          │ ·            ║            · │
   a = −1 ●══════════════╬══════════════● a = 1 → a
          │ ·            ║            · │
          │    ·         ║         ·    │
          │         ·    ║    ·         │
          └──────────────●──────────────┘
                       b = −1

          上端 b = 1；中心 a = b = 0。
          ┌─┐ 方形边界；· 单位圆；═║ 两条 Markov 坐标轴。
```

图中三类精确区域（上方字符图仅作示意）：

| 区域 | 原图图例与含义 |
|---|---|
| 参数正方形：−1 ≤ a ≤ 1，−1 ≤ b ≤ 1 | 两份边际分别合法，共享读数始终相同。 |
| 单位圆盘：a² + b² ≤ 1 | 存在某个共同整体；圆盘外没有共同整体。 |
| 两条坐标轴：ab = 0 | 满足 C91，可作规范 Markov 拼接。 |

**图 1。**三个不同层次的资格。图为参数空间的精确区域，不是空间中粒子的轨道。
第三关系坐标 $m$ 将圆盘提升为下节的逻辑 Bloch 球。

**白话图景。**两边都能单独把自己的关系调得很强，且中间读数完全一样；
但两边合起来，可能要求同一个量子比特同时承担不相容的关系。
圆盘划出“至少有一个整体能容纳”的范围。
再要求从两边拼接得到同一份内容，范围就收缩到两条轴。
所以删去本轮条件的后果很具体：有时整个拼不起来，有时拼得起来却还需要额外的整体关系。

<a id="section-4"></a>

## 4. 有限三维提升：两条关系轴与它们的交叉关系

<a id="sec-c91-three-axis-lift"></a>

取 $m\in\mathbb R$，考虑三项关系共同描述的态族

<a id="eq-c91-logical-bloch"></a>

$$
\omega_m=\frac18(I+aK+bL+mM).
\tag{4.1}
$$

因为 $M$ 在 $A$ 与 $C$ 上都含无迹 Pauli 因子，它在任意一个相邻二体边际中消失。
因此改变 $m$ 不改变式 [(3.2)](#eq-c91-pauli-marginals) 的任何输入内容。

### 定理 4.1（真实交叉关系的三轴球与逻辑 qubit）

<a id="thm-c91-three-axis"></a>

在上述态族中有

<a id="eq-c91-three-ball"></a>

$$
\omega_m\ge0
 \quad\Longleftrightarrow\quad a^2+b^2+m^2\le1.
\tag{4.2}
$$

三轴算符生成的代数酉等价于 $M_2\otimes I_4$。
在一种这样的等价中，

<a id="eq-c91-logical-factorization"></a>

$$
\omega_m\simeq
 \frac{I+a\sigma_z+b\sigma_x-m\sigma_y}{2}
 \otimes\frac{I_4}{4}.
\tag{4.3}
$$

所以球面上的态在这份逻辑 qubit 关系上纯，却在整个三比特空间上秩为 $4$。

**证明。**
两两反对易使

$$
(aK+bL+mM)^2=(a^2+b^2+m^2)I.
$$

除原点外，因该算符无迹，其两个特征值为
$\pm\sqrt{a^2+b^2+m^2}$，各重数为 $4$。
故 $I+aK+bL+mM$ 为正恰好给式 [(4.2)](#eq-c91-three-ball)。

取 $K$ 的正特征空间的一组正交基 $e_1,\ldots,e_4$。
由 $KL=-LK$ 及 $L^2=I$，向量 $Le_1,\ldots,Le_4$ 是负特征空间的正交基。
在这组配对基中，$K=\sigma_z\otimes I_4$，$L=\sigma_x\otimes I_4$，
因而 $M=iKL=-\sigma_y\otimes I_4$。
这证明代数形式及式 [(4.3)](#eq-c91-logical-factorization)。
球面时第一个因子秩一，第二个因子秩四，故总秩为四。

对满足 $a^2+b^2\le1$ 的固定 $a,b$，不可见于两份输入的交叉关系可取范围为

$$
-\sqrt{1-a^2-b^2}\le m\le\sqrt{1-a^2-b^2}.
$$

这不是说所有兼容态都只有这个参数；它给出兼容集合中一个精确的可见切片。
三条轴也不是靠“把复杂对象画成球”任意指定的：前两条来自给定二元关系，
第三条由其算符乘积 $iKL$ 产生，范数边界由正性锁定。

### 命题 4.2（圆盘上最大熵补全的独立核对）

<a id="prop-c91-pauli-maxent"></a>

对所有 $a^2+b^2\le1$，式 [(3.4)](#eq-c91-pauli-maxent-state) 的
$\omega_0$ 是给定两边际的唯一最大熵态；但只有 $ab=0$ 时它是 Markov 态。

**证明。**
令 $H=aK+bL$、$r=\sqrt{a^2+b^2}$。若 $0<r<1$，谱演算给出

$$
\log\omega_0=\alpha I+\beta H,
 \quad
 \alpha=\tfrac12\log(1-r^2)-\log8,
 \quad \beta=\frac{\operatorname{arctanh}r}{r}.
$$

对每个兼容 $\zeta$，$\operatorname{Tr}(\zeta H)=r^2$，所以
$\operatorname{Tr}(\zeta\log\omega_0)=\operatorname{Tr}(\omega_0\log\omega_0)$。
因此

$$
D(\zeta\Vert\omega_0)=S(\omega_0)-S(\zeta)\ge0,
$$

等号只在 $\zeta=\omega_0$ 成立。
所用相对熵正性将在引理 [8.1](#lem-c91-klein) 给出有限证明。
$r=0$ 时 $\omega_0=I/8$，同样直接成立。

若 $r=1$，则 $H^2=I$，且任意兼容态都满足 $\operatorname{Tr}(\zeta H)=1$。
正性迫使 $\zeta$ 只支撑于 $H$ 的 $+1$ 特征空间，该空间维数为四。
而 $\omega_0=(I+H)/8$ 正是这个空间上的均匀态，
在该支撑上再用相对熵正性，得到唯一最大熵。
最后的 Markov 资格由命题 [3.2](#prop-c91-pauli-markov) 与后文结构等价定理给出。

**白话图景。**左边一条关系，右边一条关系，它们相遇后还能形成第三条交叉关系。
三者可以在同一个有限球中比较；两张局部图却看不到第三轴上的位置。
这里的球是这一组关系所生成的逻辑量子比特，整个三比特世界还有别的方向。
最大熵补全给出一个确定代表，但真实整体也可以带着额外的交叉内容。
这让“关系的关系仍是关系”落到可写出、可区分、可证明的结构上。

<a id="section-5"></a>

## 5. 两种规范拼接各自保留什么

<a id="sec-c91-petz-support"></a>

沿用前文的共同边际、$\mathcal R^C,\mathcal R^A,\Theta,P,Q$ 与唯一候选 $C_{91}$。
所有算符都在有限维空间上；未写出的端口补单位算符。
首先检查：两个拼接确实是合法状态，且各自自动保留一边。

### 引理 5.1（支撑限制与规范恢复的归一）

<a id="lem-c91-support-cptp"></a>

令 $p_B=\operatorname{supp}\rho_B$。两份边际分别支撑于
$\mathcal H_A\otimes p_B\mathcal H_B$ 与
$p_B\mathcal H_B\otimes\mathcal H_C$。
在这个共同 $B$ 支撑上，$\mathcal R^C$ 与 $\mathcal R^A$ 均为 CPTP，且

$$
\mathcal R^C(\rho_B)=\rho_{BC},\qquad
 \mathcal R^A(\rho_B)=\rho_{AB}.
$$

原始 $\rho_{AB},\rho_{BC}$ 可以不满秩。

**证明。**
若 $q_B=I-p_B$，则
$\operatorname{Tr}[\rho_{AB}(I_A\otimes q_B)]=\operatorname{Tr}(\rho_Bq_B)=0$。
正矩阵的平方根给出
$(I_A\otimes q_B)\rho_{AB}=0$；另一份边际同理。
因此只需把 $B$ 限制到 $p_B\mathcal H_B$，此时 $\rho_B>0$。

以右侧恢复为例，其公式是三个完全正映射的组合：
左右乘 $\rho_B^{-1/2}$、嵌入 $X\mapsto X\otimes I_C$，再左右乘
$\rho_{BC}^{1/2}$。而

$$
\begin{aligned}
 \operatorname{Tr}\mathcal R^C(X)
 &=\operatorname{Tr}\!\left[
   (\rho_B^{-1/2}X\rho_B^{-1/2}\otimes I_C)\rho_{BC}\right]\\
 &=\operatorname{Tr}(\rho_B^{-1/2}X\rho_B^{-1/2}\rho_B)
 =\operatorname{Tr} X.
 \end{aligned}
$$

代入 $X=\rho_B$ 得到恢复边际的等式；$\mathcal R^A$ 完全类似。
若要在原大空间上定义通道，可取

$$
\widetilde{\mathcal R}^C(X)
 =\mathcal R^C(p_BXp_B)+\operatorname{Tr}[(I-p_B)X]\rho_{BC}.
$$

它仍完全正保迹，且不改变本轮内容上的作用。

由此 $P,Q$ 均为密度矩阵，且恒有

<a id="eq-c91-automatic-marginals"></a>

$$
\operatorname{Tr}_A P=\rho_{BC},\qquad \operatorname{Tr}_C Q=\rho_{AB}.
\tag{5.1}
$$

例如，$P=(\operatorname{id}_A\otimes\mathcal R^C)(\rho_{AB})$，所以
$\operatorname{Tr}_A P=\mathcal R^C(\rho_B)=\rho_{BC}$。
**另一边的边际尚未自动成立**：$\operatorname{Tr}_C P$ 一般不同于 $\rho_{AB}$。
这正是 $C_{91}$ 需要检查的闭合内容。

任意候选恢复 $\mathcal S:B\to BC$ 也可以限制到同一支撑。
若 $\mathcal S(\rho_B)=\rho_{BC}$，则对支撑内任意 $X\ge0$，存在有限 $c$ 使
$X\le c\rho_B$，从而
$\mathcal S(X)\le c\rho_{BC}$。
因此输出不逃出 $p_B\mathcal H_B\otimes\mathcal H_C$。
以下直接在限制后的空间工作。

**白话图景。**从左边资料出发补上右边，可以保证新补上的那份资料正确；
但补的过程中可能改坏原先的左边关联。反向拼接也有同样的问题。
两条路线得到同一个完整状态，才说明这两份重叠内容可以在这个接口上无矛盾地闭合。
这里不需要给原本为零的方向添加人为小权重。

<a id="section-6"></a>

## 6. 忠实固定态怎样迫出共同块因子

<a id="sec-c91-fixed-algebra"></a>

下面把 v88–v89 的保态条件期望与固定代数结论压成所需的有限引理
 [8](#ref-v88)、[9](#ref-v89)。它是本轮结构证明的工具，不另立公理。

### 引理 6.1（固定可观测代数与固定状态）

<a id="lem-c91-fixed-state-blocks"></a>

设 $\mathcal T:M_B\to M_B$ 为 CPTP，并固定一个忠实状态 $\beta>0$。
则存在分解

$$
\mathcal H_B=\bigoplus_j(\mathcal H_{L_j}\otimes\mathcal H_{R_j}),
 \qquad
 \mathcal F:=\operatorname{Fix}(\mathcal T^*)
 =\bigoplus_j(M_{L_j}\otimes I_{R_j}),
$$

以及每块上固定的忠实状态 $\tau_j\in M_{R_j}$，使

<a id="eq-c91-fixed-states"></a>

$$
\operatorname{Fix}(\mathcal T)
 =\left\{\bigoplus_jY_j\otimes\tau_j:
                 Y_j\in M_{L_j}\right\}.
\tag{6.1}
$$

这里 $\mathcal T^*$ 是普通迹伴随。

**证明。**
若 $X\in\mathcal F$，UCP 映射 $\mathcal T^*$ 的 Schwarz 不等式给

$$
D_X=\mathcal T^*(X^\dagger X)-X^\dagger X\ge0.
$$

由于 $\mathcal T(\beta)=\beta$，有 $\operatorname{Tr}(\beta D_X)=0$。
忠实性迫使 $D_X=0$；对 $XX^\dagger$ 也成立。
v89 的乘法域等式因此给出

$$
\mathcal T^*(XY)=X\mathcal T^*(Y),\qquad
 \mathcal T^*(YX)=\mathcal T^*(Y)X.
$$

特别地，固定元的乘积仍固定。结合伴随保持与含单位性，
$\mathcal F$ 是有限维 $C^*$ 子代数，故有上述直和张量标准形。

为明确其状态端，取 Cesàro 极限

$$
E=\lim_{n\to\infty}\frac1n
      \sum_{k=0}^{n-1}(\mathcal T^*)^k.
$$

这个有限维极限存在：UCP 映射的各次幂在算符范数下有界，
故谱在单位圆盘内，且单位圆上的 Jordan 块只能是一阶；
平均后只有特征值 $1$ 的部分保留。
于是 $E$ 是 UCP 幂等映射，像为 $\mathcal F$，并满足 $E_*(\beta)=\beta$。
每个 $\mathcal F$ 元都是 $E$ 的乘法域元，所以 $E$ 为双模映射。

记 $\Pi_j$ 为上述直和块投影。
双模性给出 $E(\Pi_jX\Pi_k)=\Pi_jE(X)\Pi_k$，因此跨块项为零。
在单块内，$E(I_{L_j}\otimes Z)$ 与全部 $M_{L_j}\otimes I_{R_j}$ 对易，
又属于该代数，故必为标量乘单位。
由正性与保单位性，这个标量是某个状态 $\tau_j$ 给出的正泛函。
因此

$$
E(X_L\otimes X_R)
 =\operatorname{Tr}(\tau_jX_R)X_L\otimes I_{R_j},
$$

其对偶公式为

<a id="eq-c91-expectation-dual"></a>

$$
E_*(Y)=\bigoplus_j
 \operatorname{Tr}_{R_j}(\Pi_jY\Pi_j)\otimes\tau_j.
\tag{6.2}
$$

又因 $E_*$ 是 $\mathcal T$ 的 Cesàro 投影，其像恰为
$\operatorname{Fix}(\mathcal T)$，得到式 [(6.1)](#eq-c91-fixed-states)。
最后，$\beta=E_*(\beta)>0$，所以每个非空块中的
$\operatorname{Tr}_{R_j}(\Pi_j\beta\Pi_j)$ 与 $\tau_j$ 都严格正。

这个引理同时说明，所用条件期望 $E$ 在 Heisenberg 端保单位并保 $\beta$；
它不必保持普通迹。其对偶 $E_*$ 才是状态端的 CPTP 投影。
普通幂 $\mathcal T^n$ 也不必收敛，证明只使用始终存在的 Cesàro 极限。

**白话图景。**反复经过一个接口仍保持不变的内容，不会任意散落在矩阵里。
它们共享一套块结构：每块有一部分可以变化，另一部分保持同一个固定状态。
块标签、可变部分和固定部分，都是从接口实际保留的关系中读出的，
不是额外摆进去的三种物质。

<a id="section-7"></a>

## 7. 双向相容、局部恢复与 Markov 分块的完整等价

<a id="sec-c91-structure-theorem"></a>

称共同扩张 $\omega_{ABC}$ 在 $A$–$B$–$C$ 次序上可局部恢复，
是指存在 CPTP 的 $\mathcal S:B\to BC$，使

$$
\omega_{AB}=\rho_{AB},\quad \omega_{BC}=\rho_{BC},\quad
 \omega_{ABC}=(\operatorname{id}_A\otimes\mathcal S)(\rho_{AB}).
$$

这就是本节使用的量子 Markov 扩张定义；不在定义中预先要求熵等式。
以下等价属于已知的量子 Markov 结构与正规性判据
 [12](#ref-hjpw)、[11](#ref-dgmm)。这里用固定代数和乘法域给出不经过强次可加性的证明。

### 定理 7.1（唯一候选的五种等价表达）

<a id="thm-c91-gluing-equivalence"></a>

对前述两份重叠边际，以下条件等价：

1. $C_{91}$ 成立，即 $P=Q$，等价地 $\Theta$ 正规；

2. $\operatorname{Tr}_C P=\rho_{AB}$；

3. $\operatorname{Tr}_A Q=\rho_{BC}$；

4. 存在上述可由 $B$ 局部恢复的共同扩张；

5. 存在 $B$ 的直和左右因子分解，使共同扩张具有形式


   <a id="eq-c91-markov-blocks"></a>

   $$
   \omega_{ABC}
      =\bigoplus_jp_j\,\alpha_{AL_j}\otimes\eta_{R_jC},
      \qquad p_j>0,\quad\sum_jp_j=1.
   \tag{7.1}
   $$

成立时，Markov 共同扩张唯一，且

<a id="eq-c91-theta-positive"></a>

$$
\Theta
 =\bigoplus_j\sqrt{p_j}\,
       \alpha_{AL_j}^{1/2}\otimes\eta_{R_jC}^{1/2}
 =\omega_{ABC}^{1/2}\ge0,
 \qquad P=Q=\omega_{ABC}.
\tag{7.2}
$$

**证明。**
由式 [(5.1)](#eq-c91-automatic-marginals)，条件 1 蕴含 2、3。
条件 2 蕴含 4：取 $\omega=P$、$\mathcal S=\mathcal R^C$。
接着证明关键的 $4\Rightarrow5$。

给定条件 4 中的 $\mathcal S$，定义
$\mathcal T=\operatorname{Tr}_C\circ\mathcal S$。边际条件给出

$$
\mathcal T(\rho_B)=\rho_B,
 \qquad
 (\operatorname{id}_A\otimes\mathcal T)(\rho_{AB})=\rho_{AB}.
$$

对忠实 $\rho_B$ 应用引理 [6.1](#lem-c91-fixed-state-blocks)。
式 [(6.2)](#eq-c91-expectation-dual) 及
$(\operatorname{id}_A\otimes E_*)(\rho_{AB})=\rho_{AB}$ 得到

<a id="eq-c91-left-blocks"></a>

$$
\rho_{AB}=\bigoplus_jp_j\,\alpha_{AL_j}\otimes\tau_j,
 \qquad
 \rho_B=\bigoplus_jp_j\,\lambda_j\otimes\tau_j,
 \quad \lambda_j=\operatorname{Tr}_A\alpha_{AL_j}.
\tag{7.3}
$$

这里 $p_j=\operatorname{Tr}(\Pi_j\rho_B)>0$，各 $\alpha_{AL_j}$ 归一；
$\rho_B>0$ 还给出 $\lambda_j>0$、$\tau_j>0$。

剩下的问题是：$\mathcal S$ 能否把这些左因子重新混入右侧？
令 $\mathcal F=\operatorname{Fix}(\mathcal T^*)$。
对每个 $X\in\mathcal F$，有

$$
\mathcal S^*(X\otimes I_C)=X,
 \qquad
 \mathcal S^*(X^\dagger X\otimes I_C)=X^\dagger X,
$$

对 $XX^\dagger$ 也一样。因此 $X\otimes I_C$ 位于
$\mathcal S^*$ 的乘法域。
将其双模等式对偶化，得到

<a id="eq-c91-recovery-bimodule"></a>

$$
\mathcal S(XYZ)
 =(X\otimes I_C)\mathcal S(Y)(Z\otimes I_C),
 \qquad X,Z\in\mathcal F.
\tag{7.4}
$$

固定一块 $j$，在 $L_j$ 取矩阵单位 $e_{ab}$。
用 $e_{11}\otimes I_{R_j}$ 在式 [(7.4)](#eq-c91-recovery-bimodule) 两侧夹取，
可知某个正矩阵 $\eta_j$ 满足

$$
\mathcal S(e_{11}\otimes\tau_j)=e_{11}\otimes\eta_j.
$$

迹保持给 $\operatorname{Tr}\eta_j=1$。再用 $e_{a1}$ 和 $e_{1b}$ 左右相乘，得到

$$
\mathcal S(e_{ab}\otimes\tau_j)=e_{ab}\otimes\eta_j.
$$

由于 $e_{11}\otimes\tau_j\in\operatorname{Fix}(\mathcal T)$，还得到
$\operatorname{Tr}_C\eta_j=\tau_j$。
将 $\alpha_{AL_j}$ 在这些矩阵单位上展开，最终有

$$
\omega_{ABC}=(\operatorname{id}_A\otimes\mathcal S)(\rho_{AB})
 =\bigoplus_jp_j\,\alpha_{AL_j}\otimes\eta_{R_jC},
$$

证明了条件 5。

现在证明 $5\Rightarrow1$。
记 $\lambda_j=\operatorname{Tr}_A\alpha_j$、$\tau_j=\operatorname{Tr}_C\eta_j$，则

$$
\begin{aligned}
 \rho_{AB}&=\bigoplus_jp_j\,\alpha_j\otimes\tau_j,\\
 \rho_{BC}&=\bigoplus_jp_j\,\lambda_j\otimes\eta_j,\\
 \rho_B&=\bigoplus_jp_j\,\lambda_j\otimes\tau_j.
 \end{aligned}
$$

逐块代入 $\Theta=\rho_{BC}^{1/2}\rho_B^{-1/2}\rho_{AB}^{1/2}$。
$\lambda_j^{1/2}\lambda_j^{-1/2}$ 先消去；
$\alpha_j^{1/2}$ 与右因子上的算符对易，随后
$\tau_j^{-1/2}\tau_j^{1/2}$ 消去。
系数为 $\sqrt{p_j}$，得到式 [(7.2)](#eq-c91-theta-positive)，故 $P=Q$。
这里没有要求 $\alpha_j$ 与 $I_A\otimes\lambda_j$ 对易，
也没有要求 $\eta_j$ 与 $\tau_j\otimes I_C$ 对易。

最后，条件 3 给出的 $Q$ 是从 $BC$ 经 $B\to AB$ 恢复的共同扩张。
把刚才的 $4\Rightarrow5\Rightarrow1$ 对 $A,C$ 交换使用，仍得到条件 1。
至此五项等价完整。
对任何条件 4 的扩张，以上证明均给出
$\omega_{ABC}=\Theta^2$；而 $\Theta$ 只由已给边际决定，故 Markov 扩张唯一。

### 推论 7.2（共享端口是 qubit 时的三种结构）

<a id="cor-c91-qubit-blocks"></a>

若 $\dim\mathcal H_B=2$，Markov 扩张在适当 $B$ 基底下必属于下列三种形式之一：

$$
\alpha_{AB}\otimes\gamma_C,\qquad
 \gamma_A\otimes\eta_{BC},\qquad
 \sum_{j=0}^1p_j\,
 \alpha_A^{(j)}\otimes\lvert j\rangle\langle j\rvert_B\otimes\eta_C^{(j)}.
$$

这些形式可以重叠，不要求互斥。

**证明。**
直和张量分解的维数只能是 $2=2\cdot1=1\cdot2=1+1$，逐一代入
式 [(7.1)](#eq-c91-markov-blocks) 即得。

### 说明 7.3（不要求原始重叠边际对易）

取 $0<s<1$、$s\ne1/2$，令
$\lvert \psi\rangle=\sqrt{s}\lvert 00\rangle+\sqrt{1-s}\lvert 11\rangle$，并取任意状态 $\gamma_C$。
状态 $\omega=\lvert \psi\rangle\langle \psi\rvert_{AB}\otimes\gamma_C$ 显然满足本定理，
但 $\rho_B=\operatorname{diag}(s,1-s)$，且

$$
\langle 00\rvert[\rho_{AB},I_A\otimes\rho_B]\lvert 11\rangle
 =(1-2s)\sqrt{s(1-s)}\ne0.
$$

所以 $[\rho_{AB}\otimes I_C,I_A\otimes\rho_{BC}]\ne0$。
本轮检查的是带共同边际归一的完整拼接次序，不能把它替换成原始边际的直接对易。

**白话图景。**如果补上右侧后还能原样保住左侧已经建立的全部关联，
中间端口就被迫出现一套结构：先区分块标签，再在每块里分出承接左侧和承接右侧的部分。
两侧仍然可以各自包含真正的量子相干与纠缠。
双向拼接相容认证的是这套共同组织方式，并没有把量子关系都改成经典对易关系。

<a id="section-8"></a>

## 8. 为什么这个拼接恰是唯一最大熵补全

<a id="sec-c91-maxent"></a>

这节从已证分块结构出发独立证明最大熵性质，不借用强次可加性。
取自然对数，定义 $S(\rho)=-\operatorname{Tr}(\rho\log\rho)$，并按连续延拓取 $0\log0=0$。

### 引理 8.1（有限维相对熵的正性与等号）

<a id="lem-c91-klein"></a>

若状态 $\zeta,\omega$ 满足 $\operatorname{supp}\zeta\subseteq\operatorname{supp}\omega$，则

$$
D(\zeta\Vert\omega)
 :=\operatorname{Tr}[\zeta(\log\zeta-\log\omega)]\ge0,
$$

等号当且仅当 $\zeta=\omega$。

**证明。**
在 $\zeta$ 的本征基中记其概率为 $r_i$，并记
$s_i=\langle i\rvert\omega\lvert i\rangle$。
只对 $r_i>0$ 的方向应用 $\omega$ 谱分解与标量对数的凹性，得到
$\langle i\rvert\log\omega\lvert i\rangle\le\log s_i$，所以
$D(\zeta\Vert\omega)\ge\sum_i r_i\log(r_i/s_i)\ge0$。
最后一步是有限概率的 Gibbs 不等式，可由 $\log u\le u-1$ 直接得到。
若等号成立，则 $r_i=s_i$，且对每个 $r_i>0$，对数凹性的等号使
$\lvert i\rangle$ 位于 $\omega$ 的单一本征子空间；故 $\omega\lvert i\rangle=r_i\lvert i\rangle$。
对 $r_i=0$ 有 $s_i=0$，正性又给 $\omega\lvert i\rangle=0$，因此 $\omega=\zeta$。
反向直接成立。所有对数均在对应正支撑上取。

### 定理 8.2（全部兼容补全的精确熵差）

<a id="thm-c91-maxent"></a>

若 $C_{91}$ 成立，令 $\omega=P=Q$。
对每个具有同样 $AB,BC$ 边际的状态 $\zeta$，都有

<a id="eq-c91-maxent-gap"></a>

$$
\operatorname{supp}\zeta\subseteq\operatorname{supp}\omega,
 \qquad
 D(\zeta\Vert\omega)=S(\omega)-S(\zeta).
\tag{8.1}
$$

因此 $\omega$ 是唯一最大熵兼容补全。

**证明。**
在式 [(7.1)](#eq-c91-markov-blocks) 的分解中，$\lambda_j,\tau_j$ 严格正。
将边际支撑投影提升到 $ABC$，得到

$$
\begin{aligned}
 K_1&=\operatorname{supp}(\rho_{AB})\otimes I_C
     =\bigoplus_j(\operatorname{supp}\alpha_j)\otimes I_{R_jC},\\
 K_2&=I_A\otimes\operatorname{supp}(\rho_{BC})
     =\bigoplus_j I_{AL_j}\otimes(\operatorname{supp}\eta_j).
 \end{aligned}
$$

两者对易，并且 $K_1K_2=\operatorname{supp}\omega$。
兼容边际与正性分别给 $K_1\zeta K_1=\zeta$、$K_2\zeta K_2=\zeta$；
故 $\zeta$ 支撑于它们的交，证明了式 [(8.1)](#eq-c91-maxent-gap) 的第一项。
这一步允许 $\zeta$ 含有不同 $j$ 块之间的相干项，并未擅自先把它去相干。

在这个共同支撑内，

$$
\log\omega
 =\bigoplus_j\left[
   (\log p_j)I+\log\alpha_j\otimes I
                    +I\otimes\log\eta_j\right].
$$

记 $\zeta_j=(I_A\otimes\Pi_j\otimes I_C)\zeta
(I_A\otimes\Pi_j\otimes I_C)$。
其迹为 $p_j$，且 $AL_j$、$R_jC$ 边际分别为
$p_j\alpha_j$、$p_j\eta_j$。
因此跨块项虽可存在，却不贡献这个块对角对数的期望；于是

$$
\begin{aligned}
 \operatorname{Tr}(\zeta\log\omega)
 &=\sum_jp_j\left[
       \log p_j+\operatorname{Tr}(\alpha_j\log\alpha_j)
                       +\operatorname{Tr}(\eta_j\log\eta_j)\right]\\
 &=\operatorname{Tr}(\omega\log\omega)=-S(\omega).
 \end{aligned}
$$

代入相对熵定义，得到式 [(8.1)](#eq-c91-maxent-gap)。
引理 [8.1](#lem-c91-klein) 随即给出最大性与唯一性。

一般非空边际兼容集是紧凸集，熵连续且严格凹，因而本来就有唯一最大熵态。
不能把这一事实写成 $C_{91}$ 的等价条件。
本轮特殊的结论是：**该二元拼接可 Markov 闭合，等价于规范双向构造相等；
成立时，这个显式状态达到该兼容集的最大熵。**
最大熵结论与已有恢复文献一致 [11](#ref-dgmm)；这里的证明另外处理了奇异支撑与可能的跨块相干。

**白话图景。**两份边际只固定它们确实包含的内容，仍可能留下真正的三方关联。
相容时，规范拼接给出一个不再额外指定这些关联的共同补全；
任何其他兼容全态与它的相对熵，正好等于少掉的熵。
所以它是唯一最大熵补全，但边际本身没有证明未知真实全态就等于这个补全。

<a id="section-9"></a>

## 9. 熵为什么给出同一个缺口：有限维强次可加的证明

<a id="sec-v91-ssa"></a>

本节只增加描述已有状态的量，不增加第二个拼接公理。取自然对数，定义

$$
S(\rho)=-\operatorname{Tr}(\rho\log\rho),\qquad 0\log0:=0,
 \qquad D(\rho\Vert\sigma)=\operatorname{Tr}\rho(\log\rho-\log\sigma).
$$

相对熵的有限值公式在 $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$ 时使用；否则记为
$+\infty$。强次可加是 Lieb–Ruskai 的既有定理 [13](#ref-ssa)。
下面给出所需有限矩阵证明，并把其等号刻画的文献依赖单独注明。

### 引理 9.1（压缩后的负对数不增）

设 $T>0$ 为有限维 Hilbert 空间上的正定算子，$V^\dagger V=I$。则

<a id="eq-v91-log-compression"></a>

$$
-\log(V^\dagger TV)\ \le\ V^\dagger(-\log T)V.
\tag{9.1}
$$

**证明。**
对任意 $A>0$，配平方给出

$$
\langle u,A^{-1}u\rangle
 =\max_z\{2\operatorname{Re}\langle u,z\rangle-\langle z,Az\rangle\}.
$$

令 $A=T+sI$，$s\ge0$，并将右侧的候选向量限制为 $Vz$，即得

$$
(V^\dagger TV+sI)^{-1}\le V^\dagger(T+sI)^{-1}V.
$$

正定矩阵的谱演算又给出范数收敛的积分

$$
-\log T=\int_0^\infty
 \left((T+sI)^{-1}-\frac{I}{1+s}\right)\,ds.
$$

在两侧减去同一标量项，再积分，得到式 [(9.1)](#eq-v91-log-compression)。
这里的收敛可逐个正特征值核对；有限维不涉及无限维算子域问题。

### 引理 9.2（部分迹的相对熵单调性：正定情形）

若 $\rho,\sigma>0$ 是 $H_{AB}\otimes H_C$ 上的归一态，记
$\rho_0=\operatorname{Tr}_C\rho$、$\sigma_0=\operatorname{Tr}_C\sigma$，则

<a id="eq-v91-dpi-positive"></a>

$$
D(\rho_0\Vert\sigma_0)\le D(\rho\Vert\sigma).
\tag{9.2}
$$

**证明。**
在矩阵空间上使用 Hilbert–Schmidt 内积
$\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}(X^\dagger Y)$，定义相对模算子

$$
\Delta_{\sigma,\rho}(X)=\sigma X\rho^{-1}.
$$

左乘 $\sigma$ 与右乘 $\rho^{-1}$ 是相互对易的正定自伴算子，故
$\Delta_{\sigma,\rho}>0$。分别取两态的谱基，可直接验证

<a id="eq-v91-modular-entropy"></a>

$$
\langle \rho^{1/2},(-\log\Delta_{\sigma,\rho})\rho^{1/2}\rangle_{\rm HS}
 =D(\rho\Vert\sigma).
\tag{9.3}
$$

具体地，$\lvert s_i\rangle\langle r_j\rvert$ 的模算子特征值为 $s_i/r_j$，所以
$\log\Delta(X)=(\log\sigma)X-X\log\rho$。

现在定义两个矩阵 Hilbert 空间之间的映射

$$
V(X)=(X\rho_0^{-1/2}\otimes I_C)\rho^{1/2},\qquad
 V^\dagger(Y)=\operatorname{Tr}_C(Y\rho^{1/2})\rho_0^{-1/2}.
$$

部分迹的定义直接给出

<a id="eq-v91-modular-compression"></a>

$$
V^\dagger V=I,\qquad V(\rho_0^{1/2})=\rho^{1/2},\qquad
 V^\dagger\Delta_{\sigma,\rho}V(X)=\sigma_0X\rho_0^{-1}.
\tag{9.4}
$$

例如最后一式先将
$\Delta V(X)=\sigma(X\rho_0^{-1/2}\otimes I_C)\rho^{-1/2}$
代入 $V^\dagger$，再取部分迹即可。对式 [(9.1)](#eq-v91-log-compression)
取 $T=\Delta_{\sigma,\rho}$，并与 $\rho_0^{1/2}$ 配对，
式 [(9.3)](#eq-v91-modular-entropy)–[(9.4)](#eq-v91-modular-compression)
便给出所需不等式。

### 定理 9.3（有限维强次可加，包含零特征值）

任意有限三方态 $\rho_{ABC}$ 都满足

<a id="eq-v91-ssa"></a>

$$
I_\rho(A:C\mid B):=S(\rho_{AB})+S(\rho_{BC})
                   -S(\rho_B)-S(\rho_{ABC})\ge0.
\tag{9.5}
$$

**证明。**
先设 $\rho=\rho_{ABC}>0$，并在上一引理中取
$\sigma=\rho_A\otimes\rho_{BC}>0$。输出参照为
$\sigma_0=\rho_A\otimes\rho_B$。乘积态对数分解与部分迹给出

$$
D(\rho\Vert\rho_A\otimes\rho_{BC})
 -D(\rho_{AB}\Vert\rho_A\otimes\rho_B)=I_\rho(A:C\mid B),
$$

故结论成立。一般态取
$\rho_\varepsilon=(1-\varepsilon)\rho+\varepsilon I/d_{ABC}$，
$0<\varepsilon<1$；对它及其自身边际使用刚才的结论。
有限矩阵的有序特征值连续，且 $-x\log x$ 在 $[0,1]$ 上连续延伸到零，
所以四项熵都在 $\varepsilon\downarrow0$ 时收敛。这就证明所有有限维态的结论。

**白话图景。**把右边的一部分暂时看不见，原来两份整体内容之间的区别不会因此变得更清楚。
这条“丢掉内容不能增加区别”的关系，改写成四份熵的分账，就是强次可加。
这里证明了缺口非负；缺口恰好为零为什么能恢复，还需要下一节的等号条件。

<a id="section-10"></a>

## 10. 零熵缺口与左右分块：自证部分和调用部分

<a id="sec-v91-entropy-equality"></a>

前文已经建立的 Markov 分块具有形式

$$
H_B=\bigoplus_j H_{B_L^j}\otimes H_{B_R^j},\qquad
 \chi_{ABC}=\bigoplus_jp_j\,\alpha_{AB_L^j}\otimes\beta_{B_R^jC}.
$$

零权块可以省略。记 $\alpha_{B_L^j}=\operatorname{Tr}_A\alpha_{AB_L^j}$、
$\beta_{B_R^j}=\operatorname{Tr}_C\beta_{B_R^jC}$。

### 命题 10.1（分块结构使四项熵逐块抵消）

上述态满足 $I_\chi(A:C\mid B)=0$。

**证明。**
直和乘积态的特征值为 $p_j a_{jk}b_{j\ell}$，故

$$
S\!\left(\bigoplus_jp_j\alpha_j\otimes\beta_j\right)
 =H(p)+\sum_jp_j\bigl(S(\alpha_j)+S(\beta_j)\bigr),
 \quad H(p)=-\sum_jp_j\log p_j.
$$

分别用于 $ABC,AB,BC,B$，四个 $H(p)$ 的系数为 $1+1-1-1$。
每块的其余项为

$$
\begin{aligned}
&S(\alpha_{AB_L^j})+S(\beta_{B_R^j})
  +S(\alpha_{B_L^j})+S(\beta_{B_R^jC})\\
 &\quad-S(\alpha_{B_L^j})-S(\beta_{B_R^j})
  -S(\alpha_{AB_L^j})-S(\beta_{B_R^jC})=0.
\end{aligned}
$$

因此全部相消；零特征值按既定约定处理。

为陈述反向关系，给定一份*实际全态* $\chi=\chi_{ABC}$，定义

<a id="eq-v91-product-reference"></a>

$$
\kappa:=\chi_A\otimes\chi_{BC},\qquad \mathcal N:=\operatorname{Tr}_C,
 \qquad\mathcal N\kappa=\chi_A\otimes\chi_B.
\tag{10.1}
$$

总有 $\operatorname{supp}\chi\subseteq\operatorname{supp}\kappa$。事实上，令 $P_A$ 为 $\chi_A$ 的支撑投影，
则 $\operatorname{Tr}[((I-P_A)\otimes I)\chi]=0$；正性使
$((I-P_A)\otimes I)\chi^{1/2}=0$。对 $\chi_{BC}$ 的支撑投影同理，
两个不同因子上的投影相乘就给出所需支撑包含。
以下逆幂均在相应正支撑上取；若要求整个输出矩阵空间上的通道，
在未占用正交补上以固定态补全。

### 命题 10.2（零条件互信息的恢复表述：调用既有等号定理）

对任意有限维 $\chi$，有

<a id="eq-v91-entropy-petz"></a>

$$
I_\chi(A:C\mid B)=0
 \quad\Longleftrightarrow\quad
 \chi=\chi^{\mathrm P}:=(\operatorname{id}_A\otimes\mathcal P_B)(\chi_{AB}),
\tag{10.2}
$$

其中

<a id="eq-v91-local-petz"></a>

$$
\mathcal P_B(Y)=\chi_{BC}^{1/2}
 \bigl(\chi_B^{-1/2}Y\chi_B^{-1/2}\otimes I_C\bigr)
 \chi_{BC}^{1/2}.
\tag{10.3}
$$

**证明。**
这里明确调用有限维 Petz 相对熵等号定理：当 $D(\rho\Vert\sigma)<\infty$，
相对熵在通道 $\mathcal N$ 下取等号，当且仅当由参照 $\sigma$ 定义的
Petz 映射同时恢复两态；支撑上的公式及补全约定见
Hayden–Jozsa–Petz–Winter 定理 3 [12](#ref-hjpw)。
对式 [(10.1)](#eq-v91-product-reference) 的两态应用它。
上面的支撑包含保证相对熵有限，而直接展开仍有

$$
I_\chi(A:C\mid B)
 =D(\chi\Vert\kappa)-D(\mathcal N\chi\Vert\mathcal N\kappa).
$$

该参照的 Petz 映射为

$$
\mathcal R_\kappa(X)=\kappa^{1/2}\mathcal N^*
 \bigl((\mathcal N\kappa)^{-1/2}X(\mathcal N\kappa)^{-1/2}\bigr)
 \kappa^{1/2}.
$$

在所占支撑上，左右两侧的 $\chi_A^{1/2}$ 分别与
$\chi_A^{-1/2}$ 抵消，因此

<a id="eq-v91-reference-factorization"></a>

$$
\mathcal R_\kappa=\operatorname{id}_A\otimes\mathcal P_B.
\tag{10.4}
$$

这给出式 [(10.2)](#eq-v91-entropy-petz)。

式 [(10.3)](#eq-v91-local-petz) 的完全正性来自夹乘；
$\operatorname{Tr}_C\chi_{BC}=\chi_B$ 给保迹性，且 $\mathcal P_B(\chi_B)=\chi_{BC}$。
这里没有把熵连续性的极限论证充当等号分类的证明。
全秩与非全秩的熵等号刻画采用上述既有定理；其左右分块形式也是
同文定理 6 的标准结论 [12](#ref-hjpw)。
前文 C91 的双向矩阵拼接及分块证明有自己的代数路线，
不以强次可加或这一熵等号定理为前提。

**白话图景。**共享的中间部分若已经分清“接左边的关系”和“接右边的关系”，
四份熵里重复计算的内容就恰好抵消。
反过来，零熵缺口能保证局部恢复，是一个已经建立的等号定理。
本轮把它作为同一结构的另一种读法，明确保留证明从哪里来的。

<a id="section-11"></a>

## 11. v90 的内生中点怎样认证实际全态

<a id="sec-v91-midpoint-bridge"></a>

继续使用实际 $\chi$ 与其乘积参照 $\kappa$，取二元内生中点和区别

$$
m=\frac{\chi+\kappa}{2},\qquad d=\frac{\chi-\kappa}{2},\qquad
 J_m(d)=\operatorname{Tr}\!\left[(m^{-1/4}dm^{-1/4})^2\right].
$$

因为 $m\ge\kappa/2$ 且 $\operatorname{supp}\chi\subseteq\operatorname{supp}\kappa$，
$m$ 和 $\kappa$ 的支撑相同，$m$ 在这个共同支撑上忠实；输出同理。
v90 因而适用于这一对实际指定的比较态。其损失为

<a id="eq-v91-midpoint-loss"></a>

$$
\ell_m=J_m(d)-J_{\mathcal Nm}(\mathcal Nd)\ge0.
\tag{11.1}
$$

### 定理 11.1（中点零损失与实际 Markov 性等价）

在上述支撑约定下，下列条件等价：

1. $\ell_m=0$；

2. 有同一个 CPTP 映射 $\mathcal S$ 同时满足
    $\mathcal S\mathcal N\chi=\chi$、$\mathcal S\mathcal N\kappa=\kappa$；

3. $\chi=\chi^{\mathrm P}$，即实际全态满足规范局部恢复式；

4. $I_\chi(A:C\mid B)=0$。

前两项到第三项只需 v90 的平方恢复理论；第三项与第四项的熵等价，
按上一节明确调用的既有定理理解。

**证明。**
第一项与第二项的等价正是 v90 的二元中点定理 [10](#ref-v90)。
要从第二项得到局部恢复，*先保留共同恢复，再改用参照 $\kappa$*。
记 v90 已证单调的对称平方区别为

$$
Q_\kappa(\chi)=\operatorname{Tr}\!\left[
 \bigl(\kappa^{-1/4}(\chi-\kappa)\kappa^{-1/4}\bigr)^2\right].
$$

依次对 $\mathcal N$ 和 $\mathcal S$ 使用其数据处理不等式，得到

$$
Q_\kappa(\chi)\ge
 Q_{\mathcal N\kappa}(\mathcal N\chi)\ge
 Q_{\mathcal S\mathcal N\kappa}(\mathcal S\mathcal N\chi)
 =Q_\kappa(\chi).
$$

所以参照 $\kappa$ 下的损失也为零。v90 的一般参照恢复界随即给出
$\mathcal R_\kappa\mathcal N\chi=\chi$；
再用式 [(10.4)](#eq-v91-reference-factorization) 得第三项。
反过来，第三项成立时，$\mathcal R_\kappa$ 同时恢复 $\chi$ 与 $\kappa$，
故第二项成立。最后一项的等价由式 [(10.2)](#eq-v91-entropy-petz) 给出。

这里的 $\kappa$ 由 $\chi$ 自身的边际定义，无须向整体之外指定一个任意标定态。
但这一数学定义不自动提供额外副本、边际层析或乘积制备的执行资源。
若用于实际实验，仍须按项目原有菜单声明这两份比较准备及其获取方式。

**白话图景。**先比较“真实整体”与“保留两边自身、暂时撤去跨边联系的参照”，
再把右端暂时藏起来。如果这对内容的中点平方区别一分未少，
v90 保证同一个操作可以恢复两者。
因为参照本身有乘积结构，换到这个参照后，恢复就能只在共同的中间部分上进行。
这一步不能把中点恢复直接改名为局部恢复，必须经过共同可恢复性的证明。

<a id="section-12"></a>

## 12. 近似误差与原整体：零资格能换，数值不能直接换

<a id="sec-v91-quantitative-reference"></a>

定义与局部 Petz 恢复相配套的平方损失

<a id="eq-v91-product-loss"></a>

$$
L_\kappa=Q_\kappa(\chi)
          -Q_{\mathcal N\kappa}(\mathcal N\chi)\ge0.
\tag{12.1}
$$

v90 的一般参照定理直接给出

<a id="eq-v91-local-recovery-bound"></a>

$$
\boxed{\quad
 \frac12\left\lVert \chi-\chi^{\mathrm P}\right\rVert_1
 \le\frac12\sqrt{L_\kappa}.
 \quad}
\tag{12.2}
$$

同一完整未来实验的输出总变差也不超过右侧，因为通道和完整读出使迹距离收缩。
该界不要求把熵缺口替换成平方缺口；两者的零点相同，数值定义不同。

若只给中点损失，v90 原样认证的是

$$
\frac12\left\lVert \chi-\mathcal R_m\mathcal N\chi\right\rVert_1
 \le\frac12\sqrt{\ell_m},
$$

其中 $\mathcal R_m$ 是中点参照的 Petz 映射。
一般不能把这里的 $\mathcal R_m$ 直接替换为
$\operatorname{id}_A\otimes\mathcal P_B$，也不能把式 [(12.2)](#eq-v91-local-recovery-bound)
中的 $L_\kappa$ 直接换成 $\ell_m$ 而保留同一常数。
上一节证明的是零损失成员资格可换；非零误差的转换还需要另证权重比较或稳定性估计。

最后，C91 只检验两份边际是否容许规范 Markov 完成；
本节的 $\ell_m$ 检验的是*实际全态*是否就是那个完成。
例如 $\lvert \mathrm{GHZ}\rangle=(\lvert 000\rangle+\lvert 111\rangle)/\sqrt2$ 的两份相邻边际
容许规范拼接

$$
\chi^{\mathrm P}=\tfrac12\lvert 000\rangle\langle 000\rvert
                   +\tfrac12\lvert 111\rangle\langle 111\rvert,
$$

但原纯态还保留跨三方相干，二者不同；原态的条件互信息为 $\log2$。
后面的反例节会展开这个差别。因而，从边际得到相容代表，并不自动恢复原来的
$\Omega$ 切面；原态的额外关系必须纳入比较，或明确采用 Markov 模型限制。

**白话图景。**两张局部关系图能拼成一个没有额外跨翼缺口的整体，
并不表示真实整体只有这些关系。
真实整体还可能保存一份两张局部图都看不到的共同相位。
本轮一方面给规范拼接，另一方面给检查真实整体是否能被这种拼接恢复的证书；
有误差时，还要保留与具体恢复方式配套的那一份尺度。

<a id="section-13"></a>

## 13. 两条补全的三维比较：长度相同仍须方向相同

<a id="sec-c91-gram"></a>

沿用前述规范候选 $P=\Theta\Theta^\dagger$、$Q=\Theta^\dagger\Theta$。
它们都是同一 $ABC$ 空间上的密度态，并且

$$
P_{BC}=\rho_{BC},\qquad Q_{AB}=\rho_{AB},\qquad
 P_B=Q_B=\rho_B.
$$

所以两者各自准确接回一侧；C91 要求这两种接法给出同一个全态。

### 命题 13.1（相同纯度与交叉比较）

记 $\nu=\dim\mathcal H_{ABC}$，并令

$$
\alpha=\operatorname{Tr}(P^2)=\operatorname{Tr}(Q^2),\qquad
 \gamma=\operatorname{Tr}(PQ),\qquad \Delta=\left\lVert P-Q\right\rVert_2.
$$

则

<a id="eq-c91-gram-defect"></a>

$$
\frac1\nu\le\alpha\le1,\qquad
 0\le\gamma\le\alpha,\qquad
 \Delta^2=2(\alpha-\gamma).
\tag{13.1}
$$

特别地，C91 等价于 $\gamma=\alpha$；仅要求两种补全的纯度相同没有约束力。

**证明。**
迹的循环性给出
$\operatorname{Tr}((\Theta\Theta^\dagger)^2)=\operatorname{Tr}((\Theta^\dagger\Theta)^2)$。
两者都是密度态，故纯度介于 $1/\nu$ 与 $1$ 之间。
又因 $\operatorname{Tr}(PQ)=\operatorname{Tr}(P^{1/2}QP^{1/2})\ge0$，
HS Cauchy–Schwarz 给出 $\gamma\le\left\lVert P\right\rVert_2\left\lVert Q\right\rVert_2=\alpha$。
展开 $\left\lVert P-Q\right\rVert_2^2$ 即得最后的恒等式。

它们在 HS 空间中的二元 Gram 块为

$$
G=\begin{pmatrix}\alpha&\gamma\\\gamma&\alpha\end{pmatrix}.
$$

由于 $\alpha>0$，可将其归一表示为

<a id="eq-c91-gram-sphere"></a>

$$
\mathbf q=\left(
 \frac\gamma\alpha,\,0,\,
 \sqrt{1-\frac{\gamma^2}{\alpha^2}}\right)\in S^2,
 \qquad \gamma/\alpha\in[0,1].
\tag{13.2}
$$

这只是一个子午线的四分之一圆弧；C91 对应 $\mathbf q=(1,0,0)$。
若将 $G/(2\alpha)$ 看作辅助 qubit 密度矩阵，其 Bloch 向量则为
$(\gamma/\alpha,0,0)$，位于球内的一条半径上。
这两个三维图形不能互相混称，也没有编码整个 $ABC$ 态空间。
保留 $\alpha$ 与 $\mathbf q$ 才能重建上述 Gram 数据及绝对 HS 缺额。

还有一个直接的正交分解。令
$\zeta=(P+Q)/2$、$\eta=(P-Q)/2$，则

$$
\operatorname{Tr}(\zeta\eta)=0,
 \qquad \left\lVert \zeta\right\rVert_2^2=\frac{\alpha+\gamma}{2},
 \qquad \left\lVert \eta\right\rVert_2^2=\frac{\alpha-\gamma}{2}.
$$

这里的正交发生在算符的 HS 空间中；它不表示两个物理纯态正交。

**白话图景。**两种接法天生具有相同的平方长度，但仍可能朝向不同内容。
因此还要比较它们之间的交叉关系：长度相同且方向重合，才是同一个补全。
三维图能把这一对接法画清楚；原来的整体有多少内容，仍由完整算符保留。

### 命题 13.2（独立旁端口揭示 HS 尺度不能省略）

把一个独立的均匀旁端口并入 $A$，令
$P_m=P\otimes I_m/m$、$Q_m=Q\otimes I_m/m$。
则

$$
\alpha_m=\frac\alpha m,\qquad
 \gamma_m=\frac\gamma m,\qquad
 \left\lVert P_m-Q_m\right\rVert_2^2=\frac{\Delta^2}{m},
 \qquad
 \left\lVert P_m-Q_m\right\rVert_1=\left\lVert P-Q\right\rVert_1.
$$

归一 Gram 图形不变；绝对 HS 缺额可以趋于零，实际迹距离却完全不变。

**证明。**
利用张量积的迹与 Schatten 范数乘法性，以及
$\operatorname{Tr}((I_m/m)^2)=1/m$、$\left\lVert I_m/m\right\rVert_1=1$。
该例也保留规范来源：新的边际取
$\rho_{AB}\otimes I_m/m$ 与原来的 $\rho_{BC}$，
就有 $\Theta_m=\Theta\otimes I_m/\sqrt m$，从而得到所示 $P_m,Q_m$。

<a id="section-14"></a>

## 14. 近似一致能保证什么：一个明确的边际误差界

<a id="sec-c91-approximate"></a>

把两份规范补全自身作为 v90 的二元输入，定义

<a id="eq-c91-midpoint-defect"></a>

$$
\mathcal I(P,Q)=
 \left\lVert \zeta^{-1/4}\eta\zeta^{-1/4}\right\rVert_2^2,
 \qquad
 \zeta=\frac{P+Q}{2},\quad\eta=\frac{P-Q}{2}.
\tag{14.1}
$$

逆幂在 $\zeta$ 的支撑内取值；因为 $P,Q\le2\zeta$，这里没有遗漏支撑。
由 v90 的二元比较与归一迹范数界 [10](#ref-v90)，

<a id="eq-c91-midpoint-trace"></a>

$$
\begin{gathered}
 0\le\mathcal I(P,Q)\le1,
 \qquad \mathcal I(P,Q)=0\ \Longleftrightarrow\ P=Q,\\
 \varepsilon:=\frac12\left\lVert P-Q\right\rVert_1
 \le\sqrt{\mathcal I(P,Q)}.
 \end{gathered}
\tag{14.2}
$$

这只是把同一 C91 写成内生的标量证书，没有另添一个候选。
在前述独立旁端口例子中，$\mathcal I(P_m,Q_m)=\mathcal I(P,Q)$：
白化后的差只增加 $I_m/\sqrt m$ 因子，其 HS 平方范数为一。

### 定理 14.1（近似一致给出近似兼容的合法全态）

令 $\varepsilon=\tfrac12\left\lVert P-Q\right\rVert_1$，并取 $\zeta=(P+Q)/2$。
则 $\zeta$ 为密度态，$\zeta_B=\rho_B$，且

<a id="eq-c91-marginal-bound"></a>

$$
\begin{aligned}
 \frac12\left\lVert \zeta_{AB}-\rho_{AB}\right\rVert_1
 &\le\frac\varepsilon2
 \le\frac12\sqrt{\mathcal I(P,Q)},\\
 \frac12\left\lVert \zeta_{BC}-\rho_{BC}\right\rVert_1
 &\le\frac\varepsilon2
 \le\frac12\sqrt{\mathcal I(P,Q)}.
 \end{aligned}
\tag{14.3}
$$

若选 $P$ 本身，则 $BC$ 边际精确而 $AB$ 的迹距离误差至多 $\varepsilon$；
选择 $Q$ 时两侧互换。

**证明。**
由 $Q_{AB}=\rho_{AB}$，
$\zeta_{AB}-\rho_{AB}=\tfrac12\operatorname{Tr}_C(P-Q)$。
偏迹为 CPTP，故迹范数收缩给出第一个界。
由 $P_{BC}=\rho_{BC}$ 同理得到第二个界；
共有的 $B$ 边际及关于 $P,Q$ 单独使用的断言直接成立。
最后使用式 [(14.2)](#eq-c91-midpoint-trace)。

若只报告 HS 缺额，令 $r=\operatorname{rank}(P-Q)$，还须保留秩因子：

$$
\varepsilon\le\frac{\sqrt r}{2}\Delta,
 \qquad
 \frac12\left\lVert \zeta_{AB}-\rho_{AB}\right\rVert_1,
 \ \frac12\left\lVert \zeta_{BC}-\rho_{BC}\right\rVert_1
 \le\frac{\sqrt r}{4}\Delta.
$$

同一个后续 CPTP 协议及完整读出的分布误差，也不超过相应的迹距离界。
这里证明的是一个*近似满足给定边际*的有效全态。
它没有证明接近某个精确 Markov 态，也没有给未知真实全态与 $\zeta$ 的距离；
更没有把 $\mathcal I(P,Q)$ 等同于条件互信息。

**白话图景。**两种接法还差一点时，可以把它们取平均，得到一份合法的整体候选。
这份候选对左右两块的误差都有明确上限，共用部分则仍然精确。
这个结论回答“边际能对得多准”；真实整体还有什么高阶内容，不能从这个误差界中补猜出来。

<a id="section-15"></a>

## 15. 共享、兼容与真实整体是三种不同声明

<a id="sec-c91-hidden-content"></a>

### 命题 15.1（同一个共享部分仍可无法拼接）

令 $A,B,C$ 都为 qubit，记
$\lvert \Phi^+\rangle=(\lvert 00\rangle+\lvert 11\rangle)/\sqrt2$，指定
$\rho_{AB}=\lvert \Phi^+\rangle\langle \Phi^+\rvert_{AB}$、
$\rho_{BC}=\lvert \Phi^+\rangle\langle \Phi^+\rvert_{BC}$。
两者共有 $\rho_B=I/2$，但不存在具有这两个边际的全态。

**证明。**
若全态 $\omega$ 的 $AB$ 边际为秩一投影 $\Pi_{AB}$，则
$\operatorname{Tr}(((I-\Pi_{AB})\otimes I_C)\omega)=0$。
正性迫使 $\omega$ 支撑在 $\operatorname{ran}\Pi_{AB}\otimes\mathcal H_C$，
因此 $\omega=\Pi_{AB}\otimes\omega_C$。
其 $BC$ 边际为 $I_B/2\otimes\omega_C$，秩至少为二，不可能等于 Bell 纯态。
在这个例子里，规范构造确实给出

$$
P=\frac{I_A}{2}\otimes\Pi_{BC},\qquad
 Q=\Pi_{AB}\otimes\frac{I_C}{2},
 \qquad \alpha=\frac12,\quad\gamma=\frac18.
$$

这些式子可由
$\Pi_{BC}\Pi_{AB}\Pi_{BC}=\tfrac14\Pi_{BC}$
直接核算，其中投影均按恒等扩张到 $ABC$。

### 命题 15.2（Markov 补全唯一不等于真实全态唯一）

取

$$
\lvert g_\pm\rangle=\frac{\lvert 000\rangle\pm\lvert 111\rangle}{\sqrt2},\qquad
 \omega_{\mathrm{mix}}=
 \frac{\lvert 000\rangle\langle 000\rvert+\lvert 111\rangle\langle 111\rvert}2.
$$

这三个态具有相同的 $AB,BC$ 边际；对应的 C91 成立，
且 $P=Q=\omega_{\mathrm{mix}}$。
然而两种 GHZ 纯态都不是这一顺序的 Markov 态。

**证明。**
偏迹抹去 $\lvert 000\rangle\langle 111\rvert$ 及其伴随，所以三个态的给定边际都是
$\tfrac12(\lvert 00\rangle\langle 00\rvert+\lvert 11\rangle\langle 11\rvert)$。
把这些对角边际代入 $\Theta$，得到
$\Theta=(\lvert 000\rangle\langle 000\rvert+\lvert 111\rangle\langle 111\rvert)/\sqrt2$，
故 $P=Q=\omega_{\mathrm{mix}}$。
两种纯态均有

$$
I(A:C\mid B)=\log2+\log2-\log2-0=\log2>0,
$$

而混合态的条件互信息为零。三者是不同的全态，不能因局部边际相同而合并。

相同边界也发生在完全经典的高阶关系中。
把偶校验字符串 $000,011,101,110$ 各赋概率 $1/4$，得到对角态
$\omega_{\mathrm{even}}$。它的每个二体边际都是 $I_4/4$，
与 $I_8/8$ 完全相同；于是 $P=Q=I_8/8$。
但 $S(\omega_{\mathrm{even}})=2\log2$，其条件互信息仍为 $\log2$。
因此被两块资料省去的内容可以是全局相位，也可以是经典的三体校验关系。

**白话图景。**同一个中间部分，不保证左右两块真的能共存；
能共存，也不保证存在无额外跨块关联的补全。
即使规范 Markov 补全已经唯一，原来的整体仍可能带着这些边际看不见的内容。
选择规范补全，是声明当前保留哪一层关系，不是证明那些高阶内容不存在。

<a id="section-16"></a>

## 16. 从三节点窗口到整条链：局部条件何时足够

<a id="sec-c91-chain"></a>

考虑有限链 $X_1-X_2-\cdots-X_n$，$n\ge2$。
给定每条边的密度态 $\rho_{i,i+1}$，相邻两边在公共单点上的边际相同，
记为 $\rho_i$。为简化记号，以下在各单点的支撑空间内工作，
因此 $\rho_i>0$。边态本身不必可逆。

### 定义 16.1（全链 Markov 补全）

称全态 $\omega_{1:n}$ 为这些边态的全链 Markov 补全，是指它具有给定边际，
并且对每个内部切口 $j=2,\ldots,n-1$ 满足

<a id="eq-c91-chain-cuts"></a>

$$
I_\omega(X_{1:j-1}:X_{j+1:n}\mid X_j)=0.
\tag{16.1}
$$

这里 $X_{a:b}$ 表示从 $a$ 到 $b$ 的整段；空段条件自动成立。
依据前述恢复等价，这要求同一份状态可由切口 $X_j$ 上的 CPTP 映射
从左段边际接回整个右段。

量子 Markov 补全与局部恢复的联系已有系统研究 [11](#ref-dgmm)、[12](#ref-hjpw)。
下面把本轮能直接得到的链结论完整证明；
证明不预先假设给定边态已经来自某个共同全态。

### 定理 16.2（每个相邻三节点窗口满足 C91，便有唯一全链补全）

<a id="thm-c91-chain"></a>

在上述有限链上，以下条件等价：

1. 每一对相邻边 $\rho_{i-1,i},\rho_{i,i+1}$ 都满足 C91，
          $i=2,\ldots,n-1$；

2. 存在全链 Markov 补全。

该 Markov 补全唯一，可从 $\rho_{12}$ 逐个添加尾端点构造；
它还是全部兼容全态中的唯一最大熵态。

**证明。**
先说明必要性。若全态满足式 [(16.1)](#eq-c91-chain-cuts)，
在相应切口的恢复公式中偏迹掉两侧多余端口，
就得到 $X_{i-1}-X_i-X_{i+1}$ 的 Markov 补全。
前述二边际定理于是给出每个局部 C91。

下面证明充分性，并把不扰动旧内容这一步单独列出。
由新边 $\rho_{k,k+1}$ 定义规范 CPTP 恢复

<a id="eq-c91-chain-recovery"></a>

$$
\mathcal R_k(Y)=\rho_{k,k+1}^{1/2}
 \bigl(\rho_k^{-1/2}Y\rho_k^{-1/2}\otimes I_{k+1}\bigr)
 \rho_{k,k+1}^{1/2},
 \qquad \mathcal E_k=\operatorname{Tr}_{k+1}\circ\mathcal R_k.
\tag{16.2}
$$

它满足 $\mathcal R_k(\rho_k)=\rho_{k,k+1}$。
从 $\omega^{(2)}=\rho_{12}$ 开始，拟递推

<a id="eq-c91-chain-recursion"></a>

$$
\omega^{(k+1)}
 =\bigl(\operatorname{id}_{1:k-1}\otimes\mathcal R_k\bigr)
       (\omega^{(k)}).
\tag{16.3}
$$

首个三节点窗口满足 C91，故 $\omega^{(3)}$ 已是所需 Markov 补全。
$n=2$ 的情形无需这一步，结论直接成立。

*归纳中的旧前缀不扰动。*
设 $k\ge3$，已构成全链 Markov 态 $\omega^{(k)}$。
局部窗口 $(k-1)-k-(k+1)$ 满足 C91，故

<a id="eq-c91-tail-fixed"></a>

$$
\bigl(\operatorname{id}_{k-1}\otimes\mathcal E_k\bigr)
 (\rho_{k-1,k})=\rho_{k-1,k}.
\tag{16.4}
$$

另一方面，旧链在 $k-1$ 的切口为 Markov。
因此存在反向 CPTP 恢复 $\mathcal S_{k-1}:X_{k-1}\to X_{1:k-1}$，使

<a id="eq-c91-reverse-prefix"></a>

$$
\omega^{(k)}=
 \bigl(\mathcal S_{k-1}\otimes\operatorname{id}_k\bigr)
 (\rho_{k-1,k}).
\tag{16.5}
$$

它可明确取为从旧前缀边际得到的 Petz 映射

$$
\mathcal S_{k-1}(Y)=
 (\omega^{(k)}_{1:k-1})^{1/2}
 \bigl(I_{1:k-2}\otimes
       \rho_{k-1}^{-1/2}Y\rho_{k-1}^{-1/2}\bigr)
 (\omega^{(k)}_{1:k-1})^{1/2}.
$$

$\mathcal S_{k-1}$ 只读取 $k-1$，$\mathcal E_k$ 只作用于 $k$；
它们作用于不同的输入端口，因而可以交换先后。
结合式 [(16.4)](#eq-c91-tail-fixed) 得到

$$
\begin{aligned}
 &(\operatorname{id}_{1:k-1}\otimes\mathcal E_k)(\omega^{(k)})\\
 &\quad=(\mathcal S_{k-1}\otimes\operatorname{id}_k)
     (\operatorname{id}_{k-1}\otimes\mathcal E_k)(\rho_{k-1,k})\\
 &\quad=(\mathcal S_{k-1}\otimes\operatorname{id}_k)(\rho_{k-1,k})
 =\omega^{(k)}.
 \end{aligned}
$$

因此新态偏迹掉 $k+1$ 后，恢复整个旧前缀，而不只是恢复最后一条边。
同时其新边际等于 $\mathcal R_k(\rho_k)=\rho_{k,k+1}$，所有已给边态均保留。

*全部切口继续保持。*
对旧切口 $j\le k-1$，把旧链从 $X_j$ 接回 $X_{j:k}$ 的恢复，
再复合尾端 $\mathcal R_k$，便得到从 $X_j$ 接回 $X_{j:k+1}$ 的 CPTP 映射。
刚才已经证明实际左段边际没有改变，所以该复合确实恢复新全态。
新切口 $j=k$ 的恢复则正是式 [(16.3)](#eq-c91-chain-recursion)。
由恢复与 Markov 的等价，新态满足全部切口条件，归纳完成。

*唯一性。*
任何满足全部切口条件的兼容全态，在最后一个切口都必须由
式 [(16.2)](#eq-c91-chain-recovery) 的规范 Petz 映射恢复。
偏迹掉尾端后，旧前缀仍满足各自全部切口条件。
归纳退回固定的 $\rho_{12}$，整个递推遂被给定边态唯一决定。
最大熵断言由下一个精确熵恒等式证明。

**白话图景。**新边能接在最后一个点上，还不够；关键是接完后整条旧链都必须原样保留。
旧链的 Markov 条件使它能够从最后两点反向接回。
反向接旧前缀的动作与检查新尾端的动作发生在不同端口，所以不会互相干扰。
这样，一个个局部窗口的条件才真正传到整个链，而不是凭图形想当然。

### 命题 16.3（最大熵的逐项配平）

对任意具有给定边态的全态 $\nu_{1:n}$，有

<a id="eq-c91-chain-entropy"></a>

$$
\begin{aligned}
 S(\nu_{1:n})
 ={}&\sum_{i=1}^{n-1}S(\rho_{i,i+1})
       -\sum_{i=2}^{n-1}S(\rho_i)\\
    &-\sum_{k=2}^{n-1}
       I_\nu(X_{1:k-1}:X_{k+1}\mid X_k).
 \end{aligned}
\tag{16.6}
$$

因此定理 [16.2](#thm-c91-chain) 构造的全态达到唯一最大熵，且

$$
S(\omega)=\sum_{i=1}^{n-1}S(\rho_{i,i+1})
       -\sum_{i=2}^{n-1}S(\rho_i).
$$

**证明。**
按定义展开每一项条件互信息：

$$
\begin{aligned}
 I_\nu(X_{1:k-1}:X_{k+1}\mid X_k)
 ={}&S(\nu_{1:k})+S(\rho_{k,k+1})\\
    &-S(\rho_k)-S(\nu_{1:k+1}).
 \end{aligned}
$$

对 $k$ 求和，前缀熵望远镜相消，得到式 [(16.6)](#eq-c91-chain-entropy)。
各条件互信息由强次可加性非负 [13](#ref-ssa)，而构造态的各项为零。
若另一态同样达到上界，每项都必须为零，因而每个前缀都按同一 Petz 递推生成；
它只能是已经构造的 $\omega$。

这里的最大熵态是当前边际资料对应的规范补全。
即使它唯一，也不表示任意实际兼容全态必然等于它；
上一节的 GHZ 与偶校验例子已经说明这个区别。

<a id="section-17"></a>

## 17. 闭圈会增加独立约束：一个严格正的三角形反例

<a id="sec-c91-cycle"></a>

### 命题 17.1（每个两边窗口通过 C91，循环仍可没有全态）

在三个 qubit $A,B,C$ 上，对三条边都指定同一形式的对角态

<a id="eq-c91-triangle-data"></a>

$$
\rho_{XY}=\frac14\left(I-\frac12 Z_XZ_Y\right),
 \qquad XY\in\{AB,BC,CA\}.
\tag{17.1}
$$

每条边严格正，单点边际都是 $I/2$，每个相邻两边窗口满足 C91，
但不存在同时具有三条边际的量子全态。

**证明。**
每条边的本征值为 $1/8,3/8,3/8,1/8$。
任取两条边，它们与公共单点边际在计算基中同时对角，
因此 $\Theta$ 为正算符，必满足 $P=Q$。

但在三个端口的整个空间中有算符不等式

<a id="eq-c91-cycle-obstruction"></a>

$$
Z_AZ_B+Z_BZ_C+Z_CZ_A\ge-I.
\tag{17.2}
$$

因为这三个可对易统计在每个共同本征向量上的取值之和只能为 $3$ 或 $-1$。
任何全态的期望都必须至少为 $-1$；
指定边际却要求三项各为 $-1/2$，总和为 $-3/2$，矛盾。
这个证明对任意量子全态成立，不需要另外假定全态是对角的。

**白话图景。**沿两条边走，每次都能把相邻内容接起来。
但绕成三角形以后，最后一条边会再提出一个要求：
三个二值方向不能两两都过强地反向。
所以“每个局部接法都合法”与“闭圈后的所有要求能同时满足”，是两层不同的约束。

<a id="section-18"></a>

## 18. 树上的安全推广：每次检查完整的当前子树

<a id="sec-c91-tree-scope"></a>

在一般树上，可以采用一个明确的构造性充分条件。
假设已经有当前子树 $S$ 的状态 $\omega_S$，
准备沿边 $u-v$ 加入新叶 $v$，其中 $u\in S$。
先检查 $\omega_u=(\rho_{uv})_u$，
再把*完整*的 $\omega_S$ 与 $\rho_{uv}$ 作为二元输入，
以 $u$ 为共享部分检查 C91。
通过时，二边际定理给出新的状态 $\omega_{S\cup\{v\}}$，
它同时保留整个旧子树和新边，并在这次声明的切口上为 Markov。
逐叶归纳即可得到满足全部给定边际的全态。

这里实际检查的是完整当前子树，并非只检查公共单点，
也没有把链证明中两个不相交端口上的交换步骤直接搬到分叉处。
若要进一步把检查压缩到树上原始的少体窗口，
需另行证明那些局部恢复与不动点结构足以保留整个旧子树。
相关量子 Markov 树与弦图条件已有更一般的研究 [11](#ref-dgmm)、[14](#ref-lz2026)；
本轮只使用上述已经逐步证明的范围。

**白话图景。**没有闭圈让逐步拼接更容易，但它不会替代量子相容条件。
一条新枝接入时，要确认它接住的是已经形成的整块旧内容。
做到这一点，就能继续长成树；若只看到共享的一个点相同，证明还没有完成。

<a id="section-19"></a>

## 19. 放回更大的结构：相对接口、共享内容与关系场

<a id="sec-c91-larger-structure"></a>

本轮已经证明三种层次的同一闭合：矩阵上是 $\Theta$ 正规，
操作上是从共享系统局部恢复而不破坏另一边际，
结构上是共享系统的直和左右因子分解。
把它用于一条有限链，可以逐段得到同一个整体；用于环形关系网络，
还必须检查闭环的整体相容。这给“关系的关系”一个明确的有限结构位置。

### 命题 19.1（内部基底改变不影响拼接资格）

取任意局部酉 $U_A,U_B,U_C$，将两边际同时变换到相应局部基底。
若 $U=U_A\otimes U_B\otimes U_C$，则

$$
\Theta'=U\Theta U^\dagger,\qquad P'=UPU^\dagger,
 \qquad Q'=UQU^\dagger.
$$

因此 C91、迹距离缺额及本轮 Markov 结构不依赖所选局部坐标。

**证明。**
酉共轭与正平方根、支撑逆平方根相容。
将变换后的三个因子逐项代入 $\Theta$，中间的 $U^\dagger U$ 抵消。
后两式及距离不变性随即成立。

这里固定的是同一个子系统划分。若把“共享部分”从 $B$ 改成另一组物理自由度，
就改变了条件化问题本身，Markov 资格可以变化。
因此相对锚的坐标协变与不同切口下的物理同一性必须分别证明；
本定理不会把所有选取都自动识别为同一问题。

### 命题 19.2（Markov 拼接不能容纳跨翼纠缠）

若 $C_{91}$ 成立，其唯一 Markov 补全 $\omega$ 满足

$$
\omega_{AC}=\sum_jp_j\,\alpha_A^{(j)}\otimes\eta_C^{(j)},
$$

所以两翼 $A,C$ 的边际可分离。

**证明。**
对式 [(7.1)](#eq-c91-markov-blocks) 逐块取 $L_j,R_j$ 的部分迹即得。

这说明为什么不能要求任意实际全态都等于其当前边际的规范 Markov 补全：
这种要求会排除本来合法的跨翼纠缠。
仅要求两份边际通过 C91，并不排除真实全态的跨翼纠缠。
例如 $\chi=\lvert \Phi^+\rangle\langle \Phi^+\rvert_{AC}\otimes\beta_B$ 的
$AB,BC$ 边际是乘积态并通过 C91；其规范补全为
$I_A/2\otimes\beta_B\otimes I_C/2$，而真实 $\chi_{AC}$ 仍是 Bell 纠缠态。
本轮候选锁定的是“共享部分已足以作这一类完整拼接”的定义资格。
不满足它时，应保留未被当前接口承接的整体关系，或声明不同的关系划分。
在一般情形，仅仅添加一个任意标签并不能保证消除这些量子关联。

内容即地址在此可写成一个可检验的要求：若两条内部构造被声明为
同一份完整拼接内容，全部读出就必须一致；在已声明的完整矩阵效果空间中，
这恰好意味着输出密度态相同，即 $P=Q$。
只要存在 $P\ne Q$，取差矩阵正谱部分的投影，就有一个读口区分这两条构造。
不能仅因两条构造共享同一个 $B$ 边际，就预先把它们当作同一地址。

**白话图景。**共同部分不只是两张图里重复出现的名字。
它必须真实地承接两边的关系，且换一条补全路线不能把内容改掉。
能做到时，内部会出现可拼接的块结构；做不到时，遗漏的关联仍属于整体，
不会因为我们换一种说法而消失。
沿链可以把这些局部接口接成一个整体，闭成环则还要检查绕一圈能否相容。

<a id="section-20"></a>

## 20. 怎样推回现有量子力学公理：完整的条件链

<a id="sec-c91-reconstruction"></a>

本轮继承此前的共同复关系载体、读出与完整操作条件。
这些是已经明示的重构接口；C91 的证明使用了它们，不能倒过来声称
C91 单独从无结构的“关系”推出复数、Born 规则和完全正性。
下面把每一条标准表述的入口写清，并保留有限证明。

| 标准量子表述 | 内部比较或组合条件 | 得到的结构与本轮位置 |
|---|---|---|
| 复 Hilbert 空间 | 共同复核、全部有限 Gram 正性、零比较取商及张成范围 | 正内积商空间；复结构由前序合同继承，有限三轴切片不替代整体载体 |
| 状态与 Born 概率 | 归一正泛函、正交细分相容、混合一致与完整效果 | $\rho\ge0$, $\operatorname{Tr}\rho=1$；$p_e=\operatorname{Tr}(\rho E_e)$，$\sum_eE_e=I$ |
| 复合与纠缠 | 独立关系核相乘、产品准备张成共同载体、可用关联态声明 | $H_A\otimes H_B$；产品态之外的合法关联；C91 检验重叠边际的特定拼接 |
| 完整量子过程 | 仿射混合、任意辅助系统的正性、全结果归一 | CPTP 与 Kraus 表示；规范恢复是其中一个由边际确定的过程 |
| 测量与更新 | 已声明的 CP 仪器及分支记录 | 概率与条件后态；POVM 本身不唯一决定扰动 |
| 可逆量子门 | 全载体上的 CPTP 过程和 CPTP 逆；v90 给生成态对的恢复入口 | 同维时酉共轭；门的可逆性并非仅由地址相同得到 |
| Schrödinger 方程 | 可微酉路径、内部时钟与相位提升 | $H=i\hbar\dot U U^\dagger$；自治另需单参数群组合 |
| 不确定性 | 正内积、自伴读口及 Born 期望 | Robertson 不等式；可恢复性不消去不可交换读口的不确定性 |
| 局部到整体 | 两份边际共用 $B$，并满足本轮 C91 | 唯一 Markov 补全、左右因子分块、最大熵；链上可递归，环上另需整体相容 |
| 连续场论 | 上述有限接口，再加尺度间相容、局域性、动力学与极限存在 | 本轮只提供有限拼接层；连续相对论场与质量隙尚不由 C91 单独推出 |

共同相位与读出合同沿用 V67、V79，完整过程接口沿用 V80；
v88–v90 提供稳定关系、条件期望及恢复链 [4](#ref-v67)、[5](#ref-v79)、[6](#ref-v80)、[8](#ref-v88)、[9](#ref-v89)、[10](#ref-v90)。
这里重述的简短证明只在各自列出的前件下成立。

### 20.1 正关系核、平方读出与张量组合

设内部标签集 $\mathcal S$ 上给出共同复核 $k(s,t)$，满足 Hermitian 对称，且
每个有限系数族有 $\sum_{s,t}\overline{c_s}k(s,t)c_t\ge0$。
在形式向量 $e_s$ 的有限线性组合上定义

$$
\left\langle\sum_sc_se_s,\sum_td_te_t\right\rangle
 =\sum_{s,t}\overline{c_s}k(s,t)d_t.
$$

正二次式给 Cauchy–Schwarz，故零范数向量与全部向量正交。
按这些零方向取商就得到正内积空间；有限秩时已经完备。
这说明 Hilbert 结构怎样来自完整的正比较核，
也说明为什么只检查每两个元的 $2\times2$ 主块正性还不够：
任意有限线性组合的正性仍是明示条件。

再设归一正交分支的权重 $w(r)\ge0$ 只依赖范数，$w(1)=1$，并满足

$$
w(\sqrt{a^2+b^2})=w(a)+w(b),\qquad a^2+b^2\le1.
$$

令 $f(x)=w(\sqrt{x})$，它在 $[0,1]$ 上非负、加性、归一。
非负性给单调性，有理细分给 $f(q)=q$，有理上下夹逼给 $f(x)=x$。
因此 $w(r)=r^2$。对完整线性分支 $M_e$，

$$
p_e=\left\lVert M_e\psi\right\rVert^2
 =\langle \psi\rvert M_e^\dagger M_e\lvert \psi\rangle,
 \qquad\sum_eM_e^\dagger M_e=I.
$$

混合一致遂给 $p_e=\operatorname{Tr}(\rho E_e)$，其中 $E_e=M_e^\dagger M_e$。
一般归一正线性泛函也由有限迹对偶唯一写为 $\operatorname{Tr}(\rho X)$：
秩一投影上的正性保证 $\rho\ge0$，单位上的归一保证 $\operatorname{Tr}\rho=1$。
其极端态恰为秩一投影，因为更高秩有非平凡谱混合，而秩一正混合只占同一射线。

若独立产品标签的共同核满足
$k_{AB}((s,u),(t,v))=k_A(s,t)k_B(u,v)$，则映射
$e_{(s,u)}\mapsto e_s\otimes e_u$ 保内积。
在产品准备张成已声明载体的条件下，它给出张量空间同构。
是否允许哪些非产品准备，仍由整体准备空间声明；仅写乘积核不自动决定所有资源。

**白话图景。**先使所有有限比较能放在同一个正内积里，再要求一次分支细分前后总权重不变，
就分别得到 Hilbert 表示和平方读出。
组合规则说明两套独立关系如何进入同一个载体。
本轮接着解决的是：两份已经共享部分内容的关系，何时足以闭合成一个共同整体。

### 20.2 完整过程、测量更新与可逆门

混合相容使操作线性延拓到矩阵空间。对所有辅助系统要求
$\operatorname{id}_n\otimes\mathcal N$ 保正，恰是完全正性；全结果归一给保迹性。
有限维时取未归一最大纠缠向量 $\lvert \Gamma\rangle=\sum_i\lvert i\rangle\lvert i\rangle$，则

$$
C_{\mathcal N}=(\operatorname{id}\otimes\mathcal N)(\lvert \Gamma\rangle\langle \Gamma\rvert)\ge0.
$$

将 $C_{\mathcal N}$ 的正分解写成向量化的矩阵
$C_{\mathcal N}=\sum_\alpha\lvert K_\alpha\rangle\!\langle K_\alpha\rvert$，比较矩阵单位得

$$
\mathcal N(X)=\sum_\alpha K_\alpha X K_\alpha^\dagger,
 \qquad\sum_\alpha K_\alpha^\dagger K_\alpha=I.
$$

反向由这个公式直接看到完全正性与归一。
辅助系统上的要求承担了实质约束：单系统正性不能替代它。

对仪器分支 $\mathcal M_e(X)=\sum_\alpha K_{e\alpha}XK_{e\alpha}^\dagger$，

$$
p_e=\operatorname{Tr}\mathcal M_e(\rho),\qquad
 \rho_e=\mathcal M_e(\rho)/p_e\quad(p_e>0),
 \qquad E_e=\sum_\alpha K_{e\alpha}^\dagger K_{e\alpha}.
$$

同一个 $E_e$ 可以来自不同的 $K_{e\alpha}$，所以 Born 效果只固定概率，
完整仪器才固定测后态。门的记录化与测量过程必须保留这一声明。

本轮的 Markov 态链也不能直接改名为量子门序列的经典 Markov 记录律。
项目的有限记录稿定理16.5明确要求指定理想仪器、没有额外量子记忆，
并且控制不依赖完整既往历史，才得到只依赖当前标签的转移概率
$K_t(y\mid x)=|\langle y\rvert U_t\lvert x\rangle|^2$ [7](#ref-foundations)。
仅对未测量的酉路径插入一组完备基，不等于已经产生这些经典中间记录。

若 $\mathcal R\mathcal N=\operatorname{id}$ 在全矩阵空间成立，且输入输出同维，
则 $\mathcal N$ 必为酉通道。一个有限证明如下：设 $A_k,B_l$ 分别为两通道 Kraus 算符。
恒等通道的 Choi 矩阵秩一，故全部 $B_lA_k=c_{lk}I$。
于是

$$
A_j^\dagger A_k
 =\sum_l A_j^\dagger B_l^\dagger B_lA_k
 =\left(\sum_l\overline{c_{lj}}c_{lk}\right)I.
$$

对右侧系数 Gram 矩阵作酉对角化，相应变换 Kraus 族后有
$\widetilde A_j^\dagger\widetilde A_k=\lambda_j\delta_{jk}I$。
每个非零 $\widetilde A_j/\sqrt{\lambda_j}$ 在同维空间上为酉；
两个非零酉的乘积不可能为零，所以只剩一个，且保迹使其系数为一。
因此 $\mathcal N(X)=UXU^\dagger$。
v90 的生成态对条件提供把二态恢复升级为这项全载体左逆资格的入口 [10](#ref-v90)。

**白话图景。**一个完整操作必须在连着任何保留的辅助关系时仍给出合法概率，
这才得到完全正过程。测量后的内容还取决于仪器保存了哪些记录。
如果同一个恢复能无损接回整个载体，同维操作就只能是酉门；
局部两个状态看起来回来，并不自动满足这个全载体条件。

### 20.3 动力学与不确定性

对可微酉路径 $U(t)$，定义 $H(t)=i\hbar\dot U(t)U(t)^\dagger$。
由 $U(t)U(t)^\dagger=I$ 求导，得到 $H(t)=H(t)^\dagger$，并有

$$
i\hbar\frac{d}{dt}\lvert \psi(t)\rangle=H(t)\lvert \psi(t)\rangle.
$$

若再声明连续自治组合 $U(t+s)=U(t)U(s)$，则有限维中生成元固定，
$U(t)=\exp(-itH/\hbar)$。能标、时钟刻度及具体 $H$ 仍须由内部模型与观测标定。
常生成元不保证任意多能级态恰好周期回返；
实际参与该态相干演化的非零谱隙还须有共同周期。
本轮的三轴球是关系代数的有限切片，不把一般动力学都改成一条闭合圆轨道。

对自伴 $A,B$，令 $\Delta A=A-\operatorname{Tr}(\rho A)I$、
$\Delta B=B-\operatorname{Tr}(\rho B)I$。在 Hilbert–Schmidt 空间对
$\Delta A\sqrt\rho$、$\Delta B\sqrt\rho$ 使用 Cauchy–Schwarz，得到

$$
(\Delta_\rho A)^2(\Delta_\rho B)^2
 \ge\left|\operatorname{Tr}(\rho\Delta A\Delta B)\right|^2
 \ge\frac14\left|\operatorname{Tr}(\rho[A,B])\right|^2.
$$

这就是 Robertson 关系。本轮的 Pauli 例子给了更具体的可行域：
多个反对易读口的期望不能独立取满，而须共同满足球内正性。

**白话图景。**酉路径的局部变化率给出自伴生成元，选好内部时钟后就是 Schrödinger 形式。
不相容读口的区别则体现在同一个正内积中，不能同时任意尖锐。
三维球展示了一组关系的有限限制；是否周期、采用什么能标、怎样进入连续场，
都还要在相应的时间和尺度接口上继续证明。

<a id="section-21"></a>

## 21. 反向审计：每一条约束到底排除了什么

<a id="sec-c91-reverse-audit"></a>

| 撤掉或错用的条件 | 可见后果 | 所定位的内部关系 |
|---|---|---|
| 共同边际相同 | 两份输入连共享接口的读数都冲突 | 先确认 $\operatorname{Tr}_A\rho_{AB}=\operatorname{Tr}_C\rho_{BC}$ |
| 仅保留共享读数，忽略整体正性 | Pauli 参数落在圆盘外；Bell–Bell 边际也无共同态 | 共享读数是必要接口，不能代替全态存在 |
| 忽略 C91 双向闭合 | 圆盘内非轴点仍有合法整体，却无 Markov 拼接 | 两种规范补全相互改变对方关系强度 |
| 把可拼接代表当成未知原态 | GHZ 相干或经典三体偶校验被遗漏 | 还需把实际全态纳入 v90 的恢复比较 |
| 只记录有限 Gram 形状，不留尺度 | 同加均匀辅助态可缩小 Hilbert–Schmidt 差却不缩小迹距离 | 三维证书必须注明读取哪个缺额、保留什么归一尺度 |
| 把链的局部定理直接推广到闭环 | 三条严格正经典边际分别通过局部拼接，却不存在环上共同态 | 关系网络的闭环相容是额外全局问题 |
| 对所有状态强加 Markov | 合法跨翼纠缠被排除 | C91 是完整 Markov 接口资格，不能替代全部量子态空间 |
| 把定义约束叫作无前提物理必然 | 已使用的复结构、正性与操作条件被隐藏 | 内生性消除任意外锚，逻辑前件仍须列出并可检验 |

这轮得到一个有限而完整的理论模块：指定重叠边际、在共同支撑归一、
构造两种规范补全、以 C91 判定资格、证明共同块结构、得到唯一最大熵代表、
计算近似边际误差、对真实全态另作恢复检验，并沿有限链递归组合。
每一步都有明确对象与失败方式，不把未检查的全局关系悄悄设为零。

2026 年10月版 Lauritzen–Zwiernik 预印本研究更一般的 Markov 边际与弦图问题，
提供了本轮 Pauli 家族及更广图结构的研究背景 [14](#ref-lz2026)。
本稿的有限链定理给出独立完整证明；没有把尚未在这里核定的全部图论推广或
连续量子场极限，写成本轮已经解决的结论。
量子场论还需要尺度间兼容、局域可观测代数、动力学、极限与具体物理预测。
这也是继续从“关系场”走向可验证场论时，剩余问题应当所在的位置。

**白话图景。**整体中的两份内容如果共享一部分，我们先在这部分上把尺度对齐。
从左边补右边、从右边补左边，若得到同一份内容，就说明这次拼接的全部关系已能由共享部分承接。
共享部分会自然分成若干块，每块分别连接左、右；两项关系及它们的交叉关系还能构成一个有限三轴球。
但两张局部图可能藏着共同看不到的第三方内容，所以规范补全并不冒充未知原整体。
沿一条链可以逐段闭合，绕成环还须检验一圈的相容。
这就是 v91 将“内容即地址、关系的关系、内部归一与整体闭合”落实成同一个可证明条件的方式。

<a id="references"></a>

## 来源、版本与核读范围

<a id="ref-omega"></a>

### [1]

trureturing 项目，*AURIC Omega Static Compatibility Fiber Theory*。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)。
本轮核读 §8：同中间边际的双 Bell 不可拼接，以及全逻辑输入纠错条件。

<a id="ref-v78"></a>

### [2]

trureturing 项目，V78 综合稿：内生关系量子理论与统一关系约束。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_ENDOGENOUS_RELATIONAL_QUANTUM_THEORY_UNIFIED_RELATIONAL_AXIOMS_V78_SYNTHESIS.md)。
本轮核读 §20.2：N2 的共享振幅补足不是一般混合态边际解，亦不自动给 Markov 性。

<a id="ref-n2"></a>

### [3]

trureturing 项目，V78 continuation N2：共享历史充分性、最小内部补足与维数预算。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_SHARED_HISTORY_SUFFICIENCY_MINIMAL_INTERNAL_COMPLETION_AND_DIMENSION_BUDGET_N2_V78_CONTINUATION.md)。
延续前稿已核读的共享投影、残差与有限维数范围；本轮改以混合态重叠边际为对象。

<a id="ref-v67"></a>

### [4]

trureturing 项目，V67：历史脚本、内容寻址与同一整体中的量子纠缠。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_HISTORY_SCRIPTS_CONTENT_ADDRESSING_AND_QUANTUM_ENTANGLEMENT_IN_ONE_ONTIC_STATE_V67.md)。
沿用前稿明示的全实正交细化与平方读出前件。

<a id="ref-v79"></a>

### [5]

trureturing 项目，V79：二元反向相容、有限相位证书与量子读出重构。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_BINARY_REVERSAL_COMPATIBILITY_FINITE_PHASE_CERTIFICATES_AND_QUANTUM_READOUT_RECONSTRUCTION_V79.md)。
沿用效果与共同复结构的相容接口；该版本的相位锚校准不被改称为从无前提选择复数域。

<a id="ref-v80"></a>

### [6]

trureturing 项目，V80：全结果二元差异不扩张、有限有向锚与内生量子过程。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_ALL_OUTCOME_BINARY_DIFFERENCE_NONEXPANSION_FINITE_ORIENTED_ANCHORS_AND_ENDOGENOUS_QUANTUM_PROCESSES_V80.md)。
沿用全结果与辅助系统相容的完整过程接口。

<a id="ref-foundations"></a>

### [7]

trureturing 项目，*情境时空算术的量子扩展：载体、演化与有限记录*。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/ContextualSpacetimeQuantum/001_016_FOUNDATIONS_AND_RECORDS.md)。
本轮核读 §16.3、定理16.5 中单标签 Markov 记录律的仪器、记忆及反馈条件。

<a id="ref-v88"></a>

### [8]

本对话研究稿，*AURIC v88: Recursive Spheres and Relative Resolution Fields*，2026。
[已交付 v88 PDF](https://chatgpt.com/library?file_id=libfile_abe42acba7fc8191bad08d801bf443f2&account_id=personal)。
继承保忠实态条件期望与共同分块。

<a id="ref-v89"></a>

### [9]

本对话研究稿，*AURIC v89: Quadratic Closure, Recursive Stability and Quantum Field Boundaries*，2026。
继承乘法域、保忠实态固定点代数及 Cesàro 条件期望。

<a id="ref-v90"></a>

### [10]

本对话研究稿，*AURIC v90: Intrinsic Binary Recovery and Shared Quantum Structure*，2026。
本轮直接接续其二态内生中点、对称平方缺额、一般参照 Petz 残差界、
共同恢复的固定结构，以及生成态对到全载体酉性的证明。

<a id="ref-dgmm"></a>

### [11]

Serena Di Giorgio, Paulo Mateus and Bruno Mera,
*Recoverability from direct quantum correlations*, arXiv:1902.10087 (2019).
[论文与版本记录](https://arxiv.org/abs/1902.10087)；
[全文](https://arxiv.org/pdf/1902.10087)。
本轮核读 Theorem2 的正规性判据、Theorem3 的分块，以及最大熵与树恢复背景。
本稿逐块展开的 $\Theta$ 系数为 $\sqrt{p_j}$，由三个平方根因子直接核定。

<a id="ref-hjpw"></a>

### [12]

Patrick Hayden, Richard Jozsa, Dénes Petz and Andreas Winter,
*Structure of states which satisfy strong subadditivity of quantum entropy with equality*,
Communications in Mathematical Physics **246**, 359–374 (2004),
[doi:10.1007/s00220-004-1049-z](https://doi.org/10.1007/s00220-004-1049-z)。
[arXiv 全文](https://arxiv.org/pdf/quant-ph/0304007)。
核读 Theorem3 的 Petz 相对熵等号、Theorem6 的 Markov 直和因子结构与相关附录。
本稿核心拼接另给固定代数证明；熵零的逆向恢复明确调用该等号定理。

<a id="ref-ssa"></a>

### [13]

Elliott H. Lieb and Mary Beth Ruskai,
*Proof of the strong subadditivity of quantum-mechanical entropy*,
Journal of Mathematical Physics **14**(12), 1938–1941 (1973),
[doi:10.1063/1.1666274](https://doi.org/10.1063/1.1666274)。
另核读同题档案全文：
[RCP25, tome19, exp.5, pp.36–55](https://www.numdam.org/item/RCP25_1973__19__A5_0.pdf)。
本稿的有限相对模压缩证明用于独立验证所需 SSA 不等式，不重新主张该定理的来源。

<a id="ref-lz2026"></a>

### [14]

Steffen Lauritzen and Piotr Zwiernik,
*The Markov Marginal Problem for Density Operators*,
arXiv:2605.19453，首次提交2026年5月19日，核读 v3（2026年10月1日），预印本。
[版本记录](https://arxiv.org/abs/2605.19453)；
[v3 全文](https://arxiv.org/html/2605.19453v3)。
本轮重点核读 §3.1 的 Markov 边际判据，§4.2 Example4.3、Lemma4.4 的
相同 Pauli 家族及圆盘可行域，§4.3 Lemma4.6 的 Markov 资格。
更广的弦图结构只作为相关研究背景，不冒充本稿已自证的全部推广。
