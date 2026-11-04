# 内生纤维平衡、支撑递归与量子关系场

从共同全态存在到规范补全、预测区间与分层光滑

**AURIC v93：一个完整候选的定义、定理与反向审计**

项目连续研究稿

2026 年 11 月 3 日（新加坡）

## 摘要

v92 的谱界相容证明局部资料何时存在共同量子全态。
v93 研究非唯一补全：怎样确定所有合法整体共同允许的支撑，
怎样选择一份有明确内部标准的规范代表，以及这一选择与真实预测之间还有什么差别。

本轮唯一候选 C93 是内生纤维平衡：
在共同最小支撑上，候选状态相对于内部参照的对数差，
与全部保持当前读数的 Hermitian 切向变化正交。
它是量子推断与规范补全的候选原则，不要求每个未知实际全态都最大熵。
证明它当且仅当唯一最小相对熵补全、压缩 Gibbs 形式及精确相对熵勾股同时成立。

先用有限次正零关系压缩得到共同最小支撑；三维两轮例子证明原始零见证不一定一次足够。
再证明压缩对数参照的必要性、参照等价、固定支撑上的光滑 Gibbs 关系场与 BKM 响应矩阵。
将候选失败落实成两个同读数状态、一个对偶二元效果及球内偏置报告，
并与 v92 的球外不相容见证区别。

未来读出的完整区间由谱对偶给出；Pauli 例子显示一项隐藏交叉关系怎样控制未来二元概率，
并给出最小新增读数及响应椭圆。另以三维态证明规范补全在支撑变化处可以不连续，
增加一个内部读数后该实例恢复仿射连续，但仍不自动成为完全正物理门。
最后衔接标准量子力学，说明共同载体、复方向、实际过程与时间前件的继承位置。
全部数学采用解析证明与独立解析复核，未运行数学程序、CAS、数值求值、枚举或测试。

## 目录

- [1. 项目接续：存在一个整体以后，还剩哪一层问题](#section-1)
- [2. 本轮唯一候选的含义与完整逻辑路线](#section-2)
- [3. 从共同态存在，走到全部补全共同允许的支撑](#section-3)
- [4. 正关系零响应，为什么必须继续压缩载体](#section-4)
- [5. 三维例子：第一轮全看过，第二轮仍会出现新约束](#section-5)
- [6. 相对熵比较与压缩后的内部参照](#section-6)
- [7. 唯一候选 C93：内生纤维平衡](#section-7)
- [8. 改变内部参照，什么时候只是同一种补全的改写](#section-8)
- [9. 两个必要边界：压缩次序与实际整体](#section-9)
- [10. 反向定位 C93：哪两个元被候选额外区分了](#section-10)
- [11. 相对参照怎样改变，才算改写同一份内容](#section-11)
- [12. 从纤维平衡到关系势：固定支撑内的光滑响应](#section-12)
- [13. 关系球上的代价椭圆：径向与横向的精确尺度](#section-13)
- [14. 规范代表之外：全部兼容整体对一个读口允许什么答案](#section-14)
- [15. 隐藏交叉关系怎样经一扇门变成可见预测差](#section-15)
- [16. 推断代表的两个边界：不普遍最优预测，也不是普适仿射门](#section-16)
- [17. 圆形读出仍会跳跃：补一个坐标如何修复](#section-17)
- [18. 怎样接回现有量子力学：完整而有前件的重构链](#section-18)
- [19. C93 怎样产生 Gibbs 统计形式](#section-19)
- [20. 为什么采用相对熵：一个不可省略的反向比较](#section-20)
- [21. 关系场与近期量子场研究：可以接在哪里](#section-21)
- [22. 完整反向审计：删去一个条件，具体坏在哪里](#section-22)
- [23. 用一段完整白话描述本轮的量子理论](#section-23)
- [来源、版本与核读范围](#references)

<a id="section-1"></a>

## 1. 项目接续：存在一个整体以后，还剩哪一层问题

<a id="sec-c93-position"></a>

本轮由 v92 递增到 v93。2026 年 11 月 3 日读取的项目公开首页显示默认分支为
`dev`，并将局部边际遗漏联合关联作为显式研究方向。
链接的 `LocalMarginalCorrelationBlindSpot` 源码与说明给出
局部扇区、相关扇区的分解，以及同局部边际而不同整体的 Bell–经典混合例子
 [1](#ref-currentrepo)、[2](#ref-blindspot)。
本轮只读了相关声明与源文，未执行 Lean 构建，也不据此认证全部仓库。

公开页面未提供可固定的最新 SHA，API 读取亦未成功。
精确版本的理论依据仍分别取已取得的
`c63ab162315f…`（2026 年 11 月 2 日）及
`7878c7ff9b75…`（2026 年 11 月 1 日）。
实时页面观察与固定快照的理论复核在来源表中分别记录。

项目 V17 已有特定 AURIC 纤维的唯一最大熵完成、KL 勾股及量子熵缺口分解；
V42 已明确最大熵代表与 minimax 中心一般不同 [3](#ref-v17)、[4](#ref-v42)。
Atlas III 已有缺失预测量的纤维宽度、范数对偶及动态自治接口 [5](#ref-atlas)。
v91 证明了 Markov 拼接的最大熵性质，也明确一般非空有限纤维具有唯一最大熵态；
v92 给出任意边际资料的共同全态存在性及正性边界 [10](#ref-v91)、[11](#ref-v92)。

因此，本轮的接续不以“第一次有最大熵或勾股”为内容。
它把这些接口推进到**任意非对易读出纤维、递归取得的最小支撑、
压缩对数参照及支撑变化的连续性边界**，并把规范代表与真实预测区间共同保留。
面约简、量子信息投影与边界不连续均有既有文献；
本文使用其标准数学机制，给出本轮所需的自足有限维证明 [12](#ref-facial2017)、[13](#ref-weis2014)、[14](#ref-weis2015)。

**白话图景。**上一轮保证这些局部说法能属于某个整体。
但同一套局部读数，仍可能对应许多个不同整体。
这一轮先找出它们共同还能存在的方向，再按一项明确的内部比较选出规范代表。
代表用于组织已有内容；尚未读出的关系仍属于允许整体的集合，
必须在后续预测中保留。

<a id="section-2"></a>

## 2. 本轮唯一候选的含义与完整逻辑路线

<a id="sec-c93-overview"></a>

设当前资料已经通过 C92，所有兼容全态组成纤维 $\mathcal F$。
令 $P_*$ 为它们全部支撑所张成的子空间投影，$\tau>0$ 为已声明的内部参照。
记压缩读出空间为 $\mathcal S_{P_*}$。
本轮候选将严格定义为：规范补全 $\sigma$ 在 $P_*$ 上忠实，并且

$$
\boxed{\quad
 \operatorname{Tr} X\bigl(\log\sigma-(P_*\log\tau P_*)|_{P_*\mathcal H}\bigr)=0
 \quad\text{对全部保持当前读数的自伴切向 }X.
 \quad}
$$

这项相容比较把两种定义连接起来：
一边是“当前读数完全不变”的变化方向；
另一边是“候选相对于内部参照”的信息偏置。
前者未区分的方向，在规范代表处不获得后一种比较的一阶倾向。

后文证明其完整等价结构：

$$
\text{纤维内一阶平衡}
 \ \Longleftrightarrow\
 \text{压缩 Gibbs 形式}
 \ \Longleftrightarrow\
 \text{唯一最小相对熵补全与精确勾股}.
$$

所有对数均在相应正支撑上定义。
压缩前后的对数顺序不能交换；原始空间中不存在满秩补全时，
先进行有限支撑递归，再使用平衡条件。

这条候选的消费者是*规范推断*。
若将它当成每个实际全态的普遍资格，会错误排除合法隐藏关联：
两端各自均为 $I/2$ 时，最大熵代表是 $I_4/4$，
Bell 态却同样具有这些边际，并且仍是合法量子态。
两者的区别须由新增联合读数或其他内部关系来决定。

**白话图景。**当前读数没有区分的正反变化，在规范代表处不应凭空带有某个方向的一阶偏好。
这个平衡条件会选出唯一代表。
实际整体可以带着当前尚未读出的额外内容；
因此“选出代表”与“证明实际整体就是它”是两个有不同前件的命题。

<a id="section-3"></a>

## 3. 从共同态存在，走到全部补全共同允许的支撑

<a id="sec-c93-support"></a>

v92 的 C92 已经回答共同全态是否存在。本节沿用那个资格，研究所有兼容补全究竟
允许落在哪个共同载体上。为同时包含完整边际与单项读出，使用如下统一记法。

### 定义 3.1（有限读出空间与兼容纤维）

令 $H$ 为 $d$ 维复 Hilbert 空间，$\mathcal S\subseteq\operatorname{Herm}(H)$ 为含 $I$ 的实线性空间。
局部边际问题中，$\mathcal S$ 就是所有局部自伴算符嵌入后的线性张成。
给定实线性响应 $\ell:\mathcal S\to\mathbb R$，$\ell(I)=1$，并假定它已通过 C92。
定义

<a id="eq-c93-fiber"></a>

$$
\mathcal F_\ell=
 \{\rho\ge0:\ \operatorname{Tr}\rho=1,\quad \operatorname{Tr}(\rho s)=\ell(s)\text{ 对全部 }s\in\mathcal S\}.
\tag{3.1}
$$

由 v92 的充要定理，$\mathcal F_\ell$ 非空；它也是有限维紧凸集。
称其为当前资料的兼容纤维。

一般有限读出空间使用 v92 的同一个证明：对 $\mathcal S$ 选有限实基，
将密度态送到这些基元的期望向量，其像仍为紧凸集。
若给定资料不在像中，有限维分离会给出某个 $s\in\mathcal S$，
使 $\ell(s)>\lambda_{\max}(s)$，与 C92 矛盾。
因此这里从局部边际推广到任意有限读口，并未另加全态存在假设。

这里 $\mathcal S$ 一般不是代数。把它直接替换为它生成的全部代数，
会额外加入当前资料未给出的乘积关系；后文始终保留这个区别。

### 定义 3.2（最小共同支撑）

令

<a id="eq-c93-common-support"></a>

$$
P_*=\bigvee_{\rho\in\mathcal F_\ell}\operatorname{supp}\rho,
\tag{3.2}
$$

即所有兼容态的值域共同张成的子空间所对应的正交投影。
它是容纳全部补全的最小投影，不能与所有支撑的交混淆。

### 定理 3.3（同一纤维有最大支撑补全）

<a id="thm-c93-max-support"></a>

存在 $\rho_0\in\mathcal F_\ell$，使 $\operatorname{supp}\rho_0=P_*$。
因此 $\rho_0$ 在 $P_*H$ 上严格正。尤其

$$
\operatorname{rank} P_*=\max_{\rho\in\mathcal F_\ell}\operatorname{rank}\rho.
$$

**证明。**
从任一兼容态开始。若已选态的值域尚未张成 $P_*H$，
按定义必有另一兼容态的值域增加这个张成空间。
每次至少增加一维，故有限次即可选出 $\rho_1,\ldots,\rho_m$，
使其值域张成 $P_*H$。
取等权混合 $\rho_0=m^{-1}\sum_j\rho_j$。
它仍属于同一纤维。正性给

$$
\ker\Bigl(\sum_j\rho_j\Bigr)=\bigcap_j\ker\rho_j,
$$

因为零二次型迫使每项的平方根都消去该向量。
故 $\rho_0$ 的支撑正好是 $P_*$，证明结论。

所有补全可以不同，但它们共同允许的最大支撑 $P_*$ 是唯一的。
这个支撑由资料与既定正序共同决定，不靠任意选一份补全来定义。

**白话图景。**当前读数可能容许多个整体。先把它们全部可能使用的方向放在一起，
就得到这份资料真正允许的载体。总能把有限个候选混合成一份补全，
使它在这个载体的每个方向都留有正余量。
这份混合态用于证明载体完整，并不把它宣称为实际整体。

<a id="section-4"></a>

## 4. 正关系零响应，为什么必须继续压缩载体

<a id="sec-c93-facial-recursion"></a>

### 引理 4.1（零响应消去支撑）

<a id="lem-c93-zero-support"></a>

若 $\rho,W\ge0$，则

$$
\operatorname{Tr}(\rho W)=0
 \quad\Longleftrightarrow\quad
 W^{1/2}\rho^{1/2}=0
 \quad\Longleftrightarrow\quad
 \operatorname{supp}\rho\subseteq\ker W.
$$

**证明。**
迹等于 $\|W^{1/2}\rho^{1/2}\|_2^2$，故前两个条件等价；
平方根与原正算符有相同的核，给出第三项。

下一步的正性必须在当前仍允许的载体上判断。
一个原来不正的关系，压到当前载体后可能成为正关系，
从而产生原始层看不见的新零支撑。

设 $P$ 为任一包含全部兼容态支撑的投影。定义

$$
\mathcal S_P=\{PsP|_{PH}:s\in\mathcal S\},
 \qquad
 \ell_P(PsP)=\ell(s).
$$

这个定义良好：若 $PsP=0$，取任一 $\rho\in\mathcal F_\ell$，
利用 $\rho=P\rho P$，得到 $\ell(s)=\operatorname{Tr}(\rho PsP)=0$。
相应的零读出切向空间为

<a id="eq-c93-zero-tangent"></a>

$$
\mathcal T_P=
 \{X\in\operatorname{Herm}(PH):\operatorname{Tr}(Xs)=0\text{ 对全部 }s\in\mathcal S_P\}.
\tag{4.1}
$$

因为 $I_{PH}=P|_{PH}$ 属于 $\mathcal S_P$，所有 $X\in\mathcal T_P$ 自动迹零。

### 引理 4.2（无忠实补全必有新的正零见证）

<a id="lem-c93-face-alternative"></a>

若当前 $PH$ 上没有严格正的兼容补全，
则存在 $0\ne W\in\mathcal S_P$，满足

<a id="eq-c93-exposing-witness"></a>

$$
W\ge0,\qquad \ell_P(W)=0.
\tag{4.2}
$$

**证明。**
令 $\mathcal L_P$ 为 $PH$ 上满足全部线性读出等式的 Hermitian 仿射空间，
则其方向空间为 $\mathcal T_P$。
它非空，并且与严格正矩阵组成的开凸锥不相交。
有限维分离定理给非零 Hermitian $W$ 与实数 $a$，使

$$
\operatorname{Tr}(WX)\le a\le\operatorname{Tr}(WY)
 \quad(X\in\mathcal L_P,\ Y>0).
$$

沿 $\mathcal T_P$ 的正负任意平移，说明 $W\perp\mathcal T_P$，
所以 $W\in\mathcal S_P$，并且左侧常为 $\ell_P(W)$。
右边对全部正定 $Y$ 成立，迫使 $W\ge0$；
再令 $Y$ 趋向零，得到 $a\le0$。
取一个已知存在的兼容密度态 $X_0\in\mathcal L_P$，
则 $0\le\operatorname{Tr}(WX_0)=\ell_P(W)\le a\le0$。
因此 $\ell_P(W)=0$，且 $W\ne0$。

这里用到的是标准 facial reduction 的分离机制；
其一般形式和非严格可行性的处理见文献 [12](#ref-facial2017)。
本稿把它写成当前读出空间上的零响应递归。

### 定理 4.3（有限零关系递归精确取得最小共同支撑）

<a id="thm-c93-support-reduction"></a>

从 $P_0=I$ 开始，按以下规则：

1. 若 $P_jH$ 上存在忠实兼容态，停止；

2. 否则取引理 [4.2](#lem-c93-face-alternative) 的 $W_j$，
          令 $P_{j+1}$ 为 $W_j$ 在 $P_jH$ 内的核投影。

无论每轮如何选取允许的非零见证，过程均在至多
$d-\operatorname{rank} P_*$ 次严格降维后停止，最终投影恰为 $P_*$。

**证明。**
每份兼容态对 $W_j$ 的期望为零，故由引理 [4.1](#lem-c93-zero-support)
支撑在 $P_{j+1}$ 内。于是全部兼容态都被保留，并且

$$
P_*\le P_{j+1}<P_j.
$$

严格不等号来自 $W_j\ne0$，而且其核不可能为零，
因为仍有迹一兼容态支撑于其中。
每轮至少减少一维，故严格降维次数不超过 $d-\operatorname{rank} P_*$。
如果尚未有忠实补全，引理总能供应下一轮见证，因而只能在有忠实补全时停止。
终止态在最终载体上有完整支撑，而它又是兼容态，所以最终投影不大于 $P_*$；
反向包含在每轮均保持，故相等。

每个见证都可写成二元读口：

$$
E_j=\frac{W_j}{\|W_j\|_{\mathrm{op}}},
 \qquad I_{P_jH}-E_j,\qquad
 \ell_{P_j}(E_j)=0.
$$

其二元报告为 $\operatorname{diag}(0,1)$，Bloch 坐标为 $(0,0,-1)$。
若保留相干项，正矩阵
$\left(\begin{smallmatrix}0&\gamma\\\bar\gamma&1\end{smallmatrix}\right)$
的行列式为 $-|\gamma|^2$，因此 $\gamma=0$。
这就是零分支与其补分支之间交叉关系被共同正性锁死的二元三维含义。

v92 的负见证把候选推到球外；这里的精确零见证把允许内容锁在球面边界，
再由零支撑决定下一层载体。该递归是有限维存在证明，不提供寻找见证的统一低成本算法。
它也使用精确零关系；把小而非零的实验误差直接删成零，会改变原问题。

**白话图景。**某个正事件被当前全部资料确定为零，它就不能偷偷保留幅度或交叉相干。
删去它不可能占据的方向后，再看其余关系，可能出现新的正零事件。
这样继续下去，每次都保留所有合法整体，同时至少删去一个无效方向。
在有限载体里，它最终恰好停在全部补全共同允许的最小支撑上。

<a id="section-5"></a>

## 5. 三维例子：第一轮全看过，第二轮仍会出现新约束

<a id="sec-c93-two-round-example"></a>

在 $H=\mathbb C^3$ 的正交基 $\lvert 1\rangle,\lvert 2\rangle,\lvert 3\rangle$ 中，令

$$
P_i=\lvert i\rangle\langle i\rvert,\qquad
 A=\lvert 1\rangle\langle 2\rvert+\lvert 2\rangle\langle 1\rvert+P_3,
 \qquad
 \mathcal S=\operatorname{span}_{\mathbb R}\{I,P_1,A\}.
$$

指定资料

<a id="eq-c93-two-round-data"></a>

$$
\ell(I)=1,\qquad \ell(P_1)=0,\qquad \ell(A)=0.
\tag{5.1}
$$

状态 $P_2$ 已实现这些资料，所以它们确实通过 C92。

### 命题 5.1（两轮归约不能并为一次原始正零检验）

<a id="prop-c93-two-round"></a>

上述纤维仅有 $P_2$。然而原始 $\mathcal S$ 中所有正且零响应的见证，
都只是 $P_1$ 的非负倍数；第一轮只能将载体压为 $\operatorname{span}\{\lvert 2\rangle,\lvert 3\rangle\}$。
在该载体上，$A$ 才成为新的正零见证 $P_3$，
第二轮才到达最终支撑 $P_*=P_2$。

**证明。**
若 $\rho$ 兼容，则 $\operatorname{Tr}(\rho P_1)=0$ 迫使第一行、第一列均为零。
于是 $\operatorname{Tr}(\rho A)=\rho_{33}=0$，正性再迫使第三行、第三列为零。
迹一给 $\rho=P_2$。

另一方面，任取原始见证
$W=aI+bP_1+cA$。零响应要求 $a=0$。
若 $W\ge0$，其 $\lvert 1\rangle,\lvert 2\rangle$ 主块必须正：

$$
\begin{pmatrix}b&c\\c&0\end{pmatrix}\ge0.
$$

行列式为 $-c^2$，所以 $c=0$，再得 $b\ge0$。
因此所有原始正零见证只消去 $\lvert 1\rangle$。
取 $P=I-P_1$，则
$PAP=P_3$，其压缩响应仍为零，
所以第二轮消去 $\lvert 3\rangle$，留下 $P_2$。

原算符 $A$ 的特征值为 $1,-1,1$，本身不正。
压缩后新增的是它在已经认证的允许载体上的正性；
这没有凭空加入新的测量资料。
这一机制属于半定规划的多轮 facial reduction，
与一般的二步退化例子相同 [12](#ref-facial2017)。

**白话图景。**第一条关系说第一个方向完全没有内容，因此它与别的方向的交叉项也同时消失。
原来混着交叉项、看不出正负的第二条关系，随后只剩第三个方向的权重。
这个权重也为零，第三个方向便被排除。
最后只剩第二个方向。新的约束来自旧关系在已认证支撑上的重新解释。

<a id="section-6"></a>

## 6. 相对熵比较与压缩后的内部参照

<a id="sec-c93-relative-reference"></a>

取得 $P_*$ 后，全部补全仍可能不唯一。
现在固定同一整体内部已经声明的忠实参照态 $\tau>0$、$\operatorname{Tr}\tau=1$，
研究如何为当前资料选择一个规范代表。
这是一项推断规则的定义问题；它不把实际全态自动等同于所选代表。

### 定义 6.1（相对熵与有效参照）

对密度态 $\rho,\sigma$ 定义

$$
D(\rho\Vert\sigma)=
 \begin{cases}
 \operatorname{Tr}\bigl(\rho(\log\rho-\log\sigma)\bigr),
       &\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma,\\
 +\infty,&\text{否则}.
 \end{cases}
$$

对数在各自支撑上取，零本征值在 $\operatorname{Tr}(\rho\log\rho)$ 中按 $0\log0=0$ 处理。
在 $K=P_*H$ 上记

<a id="eq-c93-compressed-reference"></a>

$$
L_\tau=P_*\log\tau P_*|_K,\qquad
 Z_\tau=\operatorname{Tr}_K e^{L_\tau},\qquad
 \widehat\tau_K=\frac{e^{L_\tau}}{Z_\tau}.
\tag{6.1}
$$

对全部 $\rho\in\mathcal F_\ell$，

<a id="eq-c93-compressed-divergence"></a>

$$
D(\rho\Vert\tau)
 =D_K(\rho\Vert\widehat\tau_K)-\log Z_\tau.
\tag{6.2}
$$

证明只需使用 $\rho=P_*\rho P_*$，从而
$\operatorname{Tr}(\rho\log\tau)=\operatorname{Tr}_K(\rho L_\tau)$。
注意这里先取 $\log\tau$ 再压缩，一般不能换成 $\log(P_*\tau P_*)$。
压缩指数族是已有量子信息几何中的标准结构 [13](#ref-weis2014)。

### 引理 6.2（相对熵非负与严格等号）

<a id="lem-c93-klein"></a>

对密度态 $\rho,\sigma$，
$D(\rho\Vert\sigma)\ge0$；等号当且仅当 $\rho=\sigma$。

**证明。**
支撑不包含时结论显然。否则限制到 $\operatorname{supp}\sigma$，此时 $\sigma>0$。
取 $\rho$ 的本征基，写其本征值为 $p_i\ge0$，
令 $q_i=\langle i\rvert\sigma\lvert i\rangle>0$。
对 $\sigma$ 的谱分解应用标量 $\log$ 的严格凹性，有

$$
\langle i\rvert\log\sigma\lvert i\rangle\le\log q_i.
$$

故

$$
D(\rho\Vert\sigma)\ge
 \sum_{p_i>0}p_i\log\frac{p_i}{q_i}
 \ge\sum_{p_i>0}(p_i-q_i)
 =\sum_{p_i=0}q_i\ge0.
$$

第二个不等式来自 $-\log t\ge1-t$。
若等号成立，不能有 $p_i=0$，且必须 $p_i=q_i$。
对数凹性中的等号又要求每个 $\lvert i\rangle$ 只落在 $\sigma$ 的一个本征子空间内，
因此 $\sigma\lvert i\rangle=q_i\lvert i\rangle=p_i\lvert i\rangle$，即 $\rho=\sigma$。
反向代入即可。

### 引理 6.3（对数的序与迹微分）

<a id="lem-c93-log-differential"></a>

若 $R>0$、$X=X^\dagger$，则

$$
\mathrm D\log_R[X]
 =\int_0^\infty(R+tI)^{-1}X(R+tI)^{-1}\,dt,
$$

且

$$
\left.\frac{d}{du}\right|_{u=0}
 \operatorname{Tr}\bigl[(R+uX)\log(R+uX)\bigr]
 =\operatorname{Tr}\bigl[X(\log R+I)\bigr].
$$

另外，$R\ge S>0$ 蕴含 $\log R\ge\log S$。

**证明。**
使用谱函数的积分表达

$$
\log R=\int_0^\infty
 \left[\frac{1}{1+t}I-(R+tI)^{-1}\right]dt.
$$

对逆矩阵微分，得到第一式。
在迹内利用循环性，

$$
\operatorname{Tr}\bigl[R\,\mathrm D\log_R[X]\bigr]
 =\operatorname{Tr}\left[X\int_0^\infty R(R+tI)^{-2}dt\right]
 =\operatorname{Tr} X,
$$

最后一步逐个正本征值积分即得单位算符，因而得到迹微分公式。
正定矩阵的逆序关系及同一积分表达给对数保序。

这两个引理只用于有限矩阵的解析证明。
这里并未把相对熵函数的数学定义当作已经实现的实验装置。

**白话图景。**参照给出比较内容的共同起点。
资料若已经排除某些方向，就要把参照的对数比较规则压到剩余载体上。
它与简单截取原参照的概率块一般不同。
相对熵随后提供一种非负差异尺度：差异为零，两个完整态才相同。

<a id="section-7"></a>

## 7. 唯一候选 C93：内生纤维平衡

<a id="sec-c93-candidate"></a>

令 $\mathcal T_*=\mathcal T_{P_*}$，
$\mathcal S_*=\mathcal S_{P_*}$，
并将 $P_*H$ 的单位写作 $I_K$。
切向 $X\in\mathcal T_*$ 改变完整态，但对当前全部读出都没有一阶变化；
它还自动满足 $\operatorname{Tr}_KX=0$。

### 定义 7.1（本轮唯一候选：内生纤维平衡）

<a id="def-c93-balance"></a>

在已经通过 C92 的资料、最小共同支撑 $P_*$ 和内部参照 $\tau$ 下，
规范补全 $\sigma$ 要求属于 $\mathcal F_\ell$，
在 $K=P_*H$ 上忠实，并满足

<a id="eq-c93"></a>

$$
\boxed{\quad
 \operatorname{Tr}_K\!\left[X\bigl(\log_K\sigma-L_\tau\bigr)\right]=0
 \quad\text{对全部 }X\in\mathcal T_*.
 \quad}
 \tag{C93}
$$

这个条件直接比较一对相反的同资料变化。
对每个 $X\in\mathcal T_*$，足够小的 $u>0$ 使
$\sigma+uX$、$\sigma-uX$ 都是合法且具有同一资料的状态。
式 [(C93)](#eq-c93) 表示：这些当前不可区分的正反变化，
不应在规范代表处带有相对参照的信息代价的一阶偏置。
它没有要求所有合法物理态都处在该平衡点。

### 定理 7.2（C93、唯一最优、压缩 Gibbs 与精确 Pythagorean）

<a id="thm-c93-balance-gibbs"></a>

每个已通过 C92 的有限资料和每个忠实参照 $\tau$，
都存在唯一的 C93 规范补全 $\sigma_*$。
对一个在 $K$ 上忠实的 $\sigma\in\mathcal F_\ell$，以下条件等价：

1. $\sigma$ 满足 C93；

2. $\log_K\sigma-L_\tau\in\mathcal S_*$；

3. 存在 $H_0\in\mathcal S_*$，使


   <a id="eq-c93-gibbs"></a>

   $$
   \sigma=\frac{\exp_K(L_\tau+H_0)}
                   {\operatorname{Tr}_K\exp_K(L_\tau+H_0)};
   \tag{7.1}
   $$

4. 对每个 $\rho\in\mathcal F_\ell$，有


   <a id="eq-c93-pythagorean"></a>

   $$
   \boxed{D(\rho\Vert\tau)
          =D(\rho\Vert\sigma)+D(\sigma\Vert\tau);}
   \tag{7.2}
   $$

5. $\sigma$ 是 $\mathcal F_\ell$ 上 $D(\rho\Vert\tau)$ 的唯一最小点。

而且这个最小点的支撑恰为 $P_*$。

**证明。**
*存在最小点。*
由于 $\tau>0$，函数
$\rho\mapsto\operatorname{Tr}(\rho\log\rho)-\operatorname{Tr}(\rho\log\tau)$
在有限维密度态集合上连续。
兼容纤维非空紧，故最小点存在。

*最小点在 $K$ 上忠实。*
取定理 [3.3](#thm-c93-max-support) 给出的 $\rho_0>0$ 于 $K$。
假设某个最小点 $\sigma$ 在 $K$ 上奇异。
令 $m=\lambda_{\min}(\rho_0|_K)>0$，
$\rho_t=(1-t)\sigma+t\rho_0$，$0<t<1$。
它仍兼容且在 $K$ 上严格正。
所有密度态本征值不超过一，所以 $\log\rho_t\le0$，
由 $\rho_0\ge mI_K$ 得

$$
\operatorname{Tr}(\rho_0\log\rho_t)\le m\operatorname{Tr}(\log\rho_t).
$$

选择 $\sigma$ 核内的单位向量，可得
$\lambda_{\min}(\rho_t)\le t\|\rho_0\|_{\mathrm{op}}\le t$。
其余本征值也不超过一，因此
$\operatorname{Tr}(\log\rho_t)\le\log t$。
另一方面，对
$\rho_t+\varepsilon I_K\ge(1-t)\sigma+\varepsilon I_K$
使用引理 [6.3](#lem-c93-log-differential)，再在 $\sigma$ 的迹配对中令
$\varepsilon\downarrow0$，得到

$$
\operatorname{Tr}(\sigma\log\rho_t)
 \ge\operatorname{Tr}(\sigma\log\sigma)+\log(1-t).
$$

故

$$
\operatorname{Tr}\bigl[(\rho_0-\sigma)(\log\rho_t-L_\tau)\bigr]
 \le m\log t+O(1)\longrightarrow-\infty.
$$

精确恒等式

$$
\begin{split}
 D(\rho_t\Vert\tau)-D(\sigma\Vert\tau)
 &=t\,\operatorname{Tr}\bigl[(\rho_0-\sigma)(\log\rho_t-L_\tau)\bigr]
   -D(\sigma\Vert\rho_t)
 \end{split}
$$

与引理 [6.2](#lem-c93-klein) 表明，充分小时该差严格为负，
矛盾。因此每个最小点在 $K$ 上忠实。

*最小点满足 C93。*
对任意 $X\in\mathcal T_*$，忠实性保证 $\sigma+uX$ 在
$u=0$ 的某个双侧邻域内都可行。
引理 [6.3](#lem-c93-log-differential) 给导数

$$
\operatorname{Tr}\bigl[X(\log\sigma+I_K-L_\tau)\bigr]
 =\operatorname{Tr}\bigl[X(\log\sigma-L_\tau)\bigr],
$$

其中用了 $\operatorname{Tr} X=0$。最小值的一阶导数为零，所以 C93 成立。

*其余等价。*
由 $\mathcal T_*=\mathcal S_*^\perp$，
条件 1 与条件 2 等价。
条件 2 直接给条件 3；反之，式 [(7.1)](#eq-c93-gibbs) 的对数
减去 $L_\tau$ 等于 $H_0$ 减一个单位倍数，仍在 $\mathcal S_*$。

若条件 2 成立，令 $G=\log\sigma-L_\tau\in\mathcal S_*$。
所有兼容态对 $G$ 的响应相同，因此

$$
\begin{split}
 D(\rho\Vert\tau)-D(\rho\Vert\sigma)
 &=\operatorname{Tr}(\rho G)
 =\operatorname{Tr}(\sigma G)
 =D(\sigma\Vert\tau).
 \end{split}
$$

这证明条件 4。再由相对熵非负与严格等号，条件 4 给条件 5。
最小点已证明存在、忠实并满足 C93，故全部等价及唯一性成立。

这是一项标准量子指数族与信息投影结构的有限自足推导，
与完整 Pythagorean 和投影理论相接 [13](#ref-weis2014)。
本轮的作用在于把它放到 v92 取得的兼容纤维上，
并先由有限零关系递归处理一般边界。
对边界资料，不能直接在原完整载体上写有限指数并声称得到奇异状态：
有限 Hermitian 矩阵的指数总严格正。

### 推论 7.3（支撑约简后的精确变分对偶）

<a id="cor-c93-dual"></a>

有

<a id="eq-c93-variational-dual"></a>

$$
\min_{\rho\in\mathcal F_\ell}D(\rho\Vert\tau)
 =
 \max_{H_0\in\mathcal S_*}
 \left\{\ell_{P_*}(H_0)
       -\log\operatorname{Tr}_K e^{L_\tau+H_0}\right\}.
\tag{7.3}
$$

右侧最大值达到。

**证明。**
对任意 $H_0\in\mathcal S_*$，令 $\sigma_{H_0}$ 为
式 [(7.1)](#eq-c93-gibbs) 的归一指数，不要求它预先满足给定资料。
引理 [6.2](#lem-c93-klein) 给每个可行 $\rho$：

$$
D(\rho\Vert\tau)
 \ge \ell_{P_*}(H_0)-\log\operatorname{Tr}_K e^{L_\tau+H_0}.
$$

取主定理所得规范态的 $H_0$，便达到等号。

$H_0$ 只在加上单位倍数的规范下决定同一指数态。
它首先是约束关系的对数势；将它解释为物理能量或实际时间生成元，
还须给相应物理标尺与动力学接口。

**白话图景。**在资料真正允许的支撑里，仍可能有许多完整态。
规范代表要求：沿当前全部读出都看不见的正反方向，比较代价没有一阶偏向。
这个简单的平衡条件恰好选出唯一的相对熵最小补全。
任何其他兼容态比参照多出的代价，又恰好分成“规范代表的代价”
与“它相对规范代表仍多出的完整区别”两部分。

<a id="section-8"></a>

## 8. 改变内部参照，什么时候只是同一种补全的改写

<a id="sec-c93-reference-equivalence"></a>

### 定理 8.1（参照等价的精确条件）

<a id="thm-c93-reference-equivalence"></a>

固定同一非空纤维及其 $P_*$。设 $\tau,\kappa$ 都是忠实参照态，
其 C93 规范代表分别为 $\sigma_\tau,\sigma_\kappa$。
则

<a id="eq-c93-reference-equivalence"></a>

$$
\sigma_\tau=\sigma_\kappa
 \quad\Longleftrightarrow\quad
 P_*(\log\tau-\log\kappa)P_*|_K\in\mathcal S_*.
\tag{8.1}
$$

**证明。**
若代表相同，分别使用主定理的条件 2 并相减，立即得到右侧。
反之，若右侧成立，则对任意 $\rho\in\mathcal F_\ell$，

$$
D(\rho\Vert\tau)-D(\rho\Vert\kappa)
 =\operatorname{Tr}\bigl[\rho(\log\kappa-\log\tau)\bigr]
$$

是由同一资料固定的常数。
两个目标函数在整个纤维上只差常数，故具有同一个唯一最小点。

这给出参照变化的准确范围：它的对数差只包含当前已固定的读出关系时，
规范补全不变。任意两份内部参照不必都等价。
例如 $\mathcal S=\mathbb R I$、没有其他读出时，规范代表分别就是 $\tau$ 与 $\kappa$。

### 推论 8.2（单点乘积参照退化为最大熵选择）

<a id="cor-c93-product-maxent"></a>

在 v92 的局部边际接口中，设窗口覆盖所有节点，
并已限制到共同单点边际的实际支撑。取

$$
\tau=\bigotimes_i\rho_i>0.
$$

则 $\log\tau\in\mathcal S$，所以 C93 规范代表恰为当前纤维上的唯一最大
von Neumann 熵态。

**证明。**
各张量因子作用于不同节点，谱分解直接给

$$
\log\tau=\sum_i
 I\otimes\cdots\otimes(\log\rho_i)\otimes\cdots\otimes I.
$$

每个单点算符可嵌入某个覆盖它的窗口，因此上述和属于 $\mathcal S$。
所以对全部 $\rho\in\mathcal F_\ell$，

$$
D(\rho\Vert\tau)
 =-S(\rho)-\ell(\log\tau),
 \qquad
 S(\rho)=-\operatorname{Tr}(\rho\log\rho).
$$

第二项在纤维上固定，故最小相对熵与最大熵完全等价。
唯一性由主定理给出。

若两重叠边际满足 v91 的 C91，前稿已经证明其规范 Markov 补全为唯一最大熵补全。
因此采用本推论的参照时，C93 在该范围内选回同一个状态 [10](#ref-v91)。
一般 C92 兼容资料即使没有 Markov 补全，本轮仍给唯一的规范代表 [11](#ref-v92)。

**白话图景。**参照可以改变，但不是每次改变都只是换一个说法。
若两个参照的对数差，全部由当前已经固定的关系组成，它们会选择同一个代表。
特别地，用各点自身的读数组成乘积参照时，选择只是在所有兼容整体中找熵最大的那一个。
这让“参照相对”有了一个精确的等价条件。

<a id="section-9"></a>

## 9. 两个必要边界：压缩次序与实际整体

<a id="sec-c93-reference-boundaries"></a>

### 9.1 先取对数再压缩，不能偷换次序

取 $0<a<1$，在 $\mathbb C^3$ 上令

$$
\tau=\frac13
 \begin{pmatrix}
 1&0&a\\
 0&1&0\\
 a&0&1
 \end{pmatrix},
 \qquad
 P=P_1+P_2.
$$

它的本征值为 $(1+a)/3,1/3,(1-a)/3$，所以忠实。
只要求 $\operatorname{Tr}(\rho P_3)=0$，则兼容纤维正好是 $PH$ 上的全部密度态。
直接压缩并归一给

$$
\frac{P\tau P}{\operatorname{Tr}(P\tau P)}=\frac12I_{PH}.
$$

而在 $\lvert 1\rangle,\lvert 3\rangle$ 块的对称、反对称本征基中取对数可得

$$
P\log\tau P|_{PH}
 =
 \begin{pmatrix}
  \log(\sqrt{1-a^2}/3)&0\\
  0&\log(1/3)
 \end{pmatrix}.
$$

因此真正的最小相对熵补全是

<a id="eq-c93-log-compression-counterexample"></a>

$$
\sigma_*=
 \frac1{1+\sqrt{1-a^2}}
 \begin{pmatrix}
 \sqrt{1-a^2}&0\\
 0&1
 \end{pmatrix}_{PH},
\tag{9.1}
$$

它与直接压缩归一所得的均匀态不同。
这由式 [(6.2)](#eq-c93-compressed-divergence) 和
引理 [6.2](#lem-c93-klein) 立即认证，不需要任何数值计算。

### 9.2 规范补全不把未知的实际关联抹成不存在

只给两个 qubit 的单点边际 $I_2/2$，取内部乘积参照 $\tau=I_4/4$。
该参照已经兼容，故 C93 选出

$$
\sigma_*=I_4/4.
$$

但 Bell 纯态 $\Phi$ 具有完全相同的两个单点边际，也通过 C92。
二者的相对熵分别为

$$
D(I_4/4\Vert I_4/4)=0,\qquad
 D(\Phi\Vert I_4/4)=\log4.
$$

所以 C93 不能被解释为“实际整体只要局部读数如此，就必须是最大熵态”。
它规范选择当前资料的推断代表，同时把实际全态可能额外携带的关联保留在纤维中。
补入新的关联读口以后，纤维与规范代表都可以改变。

**白话图景。**少量读数可以有一个明确、唯一的规范解释，但实际内容仍可能比这些读数更丰富。
两边各自看起来完全均匀，整体既可能独立，也可能纠缠。
本轮的平衡条件选择在给定参照下不另加偏置的代表；
它没有证明那些尚未读出的关联已经从实际整体中消失。

<a id="section-10"></a>

## 10. 反向定位 C93：哪两个元被候选额外区分了

<a id="sec-c93-binary-witness"></a>

本节在已经固定的共同最小支撑 $P=P_*$ 上工作，
所有矩阵均视为 $PH$ 上的算符，单位为 $I_P$。
当前资料的零读出切向空间记为

$$
\mathcal N=
 \{X=X^\dagger:\operatorname{Tr}(XW)=0\text{ 对全部 }W\in\mathcal S_P\}.
$$

因为 $I_P\in\mathcal S_P$，每个 $X\in\mathcal N$ 都满足 $\operatorname{Tr} X=0$。
对纤维内的忠实候选 $\sigma$，定义

$$
G_\sigma=\log\sigma-(P\log\tau P)|_{PH}.
$$

以下反向见证针对 C93 的信息平衡资格；资料本身已通过 C92。

### 定理 10.1（每个不平衡候选都有同读数的正反下降见证）

<a id="thm-c93-descent-witness"></a>

若忠实候选 $\sigma\in\mathcal F_\ell$ 不满足 C93，
则存在 $X\in\mathcal N$ 与充分小的 $\varepsilon>0$，
使 $\rho_\pm=\sigma\pm\varepsilon X$ 都在同一纤维内，
且其中一个方向使 $D(\,\cdot\,\Vert\tau)$ 严格下降。
反过来，若全部这类一阶比较均无方向偏置，则 $\sigma$ 是唯一规范补全。

**证明。**
取相对于 Hilbert–Schmidt 实内积的正交投影，
令 $X=-\operatorname{proj}_{\mathcal N}G_\sigma$。
C93 失败恰意味着 $X\ne0$，并且

$$
\operatorname{Tr}(XG_\sigma)=-\left\lVert \operatorname{proj}_{\mathcal N}G_\sigma\right\rVert_2^2<0.
$$

选 $0<\varepsilon<\lambda_{\min}(\sigma)/\left\lVert X\right\rVert_{\mathrm{op}}$，
则 $\rho_\pm>0$，迹均为一，全部当前读数不变。
由前节的微分公式，

$$
\left.\frac d{dt}D(\sigma+tX\Vert\tau)\right|_{t=0}
 =\operatorname{Tr}(XG_\sigma)<0.
$$

因此进一步缩小同一个 $\varepsilon>0$，即可保证
$D(\rho_+\Vert\tau)<D(\sigma\Vert\tau)$，而 $\rho_\pm$ 仍保持上述可行性。
反向由平衡与 Gibbs 表示的充要定理 [7.2](#thm-c93-balance-gibbs) 成立。

这不是只找到一个偶然坏例子：
每个忠实而不平衡的候选都给出上述投影见证。
若候选在 $P_*$ 内仍缺少允许支撑，则先由前节的秩与 $t\log t$ 论证排除它的最优性；
此时不能直接对它在整个 $P_*$ 上取有限对数。

**白话图景。**先把当前资料完全看不见的方向找出来。
如果候选对这些方向仍带有信息偏好，就沿偏好的反方向作一点变化：
全部已知读数不动，相对信息量却下降。
这说明它没有达到所定义的规范平衡，而不说明它不再是合法量子态。

### 10.1 二元效果与三维偏置报告

### 命题 10.2（合法比较的偏置在球内，而非负概率）

<a id="prop-c93-binary-bias"></a>

固定任意忠实候选 $\sigma\in\mathcal F_\ell$。
对任意 $X\in\mathcal N$，选取足够小的 $\varepsilon>0$，使
$\rho_\pm=\sigma\pm\varepsilon X$ 都在同一纤维内且在 $PH$ 上忠实。
若 $G_\sigma$ 不是标量，令

$$
m=\lambda_{\min}(G_\sigma),\qquad
 M=\lambda_{\max}(G_\sigma),\qquad
 E=\frac{G_\sigma-mI_P}{M-m}.
$$

则 $0\le E\le I_P$，而两份同读数状态对这个对偶读口的概率差为

<a id="eq-c93-binary-bias"></a>

$$
\delta_X=
 \operatorname{Tr}(\rho_+E)-\operatorname{Tr}(\rho_-E)
 =\frac{2\varepsilon\operatorname{Tr}(XG_\sigma)}{M-m}.
\tag{10.1}
$$

C93 等价于对全部 $X\in\mathcal N$ 及上述允许的 $\varepsilon$，这些差都为零。
以一份内部二值标签记录正反方向后，该差可表示为 Bloch 球中的

$$
\mathbf b_X=(0,0,\delta_X),\qquad |\delta_X|\le1.
$$

**证明。**
前两项由谱归一及 $\operatorname{Tr} X=0$ 直接得到。
因 $M-m>0$ 且 $\varepsilon>0$，全部 $\delta_X$ 为零当且仅当
$\operatorname{Tr}(XG_\sigma)=0$ 对全部 $X\in\mathcal N$ 成立，这正是 C93。
写 $p_\pm=\operatorname{Tr}(\rho_\pm E)$，它们都属于 $[0,1]$。
在带标签的整体上取

$$
\Xi=\frac12\left(
   \lvert 0\rangle\langle 0\rvert\otimes\rho_+
   +\lvert 1\rangle\langle 1\rvert\otimes\rho_-\right),
$$

并问二元效果

$$
F=\lvert 0\rangle\langle 0\rvert\otimes E
   +\lvert 1\rangle\langle 1\rvert\otimes(I_P-E).
$$

该事件的概率为
$q=(p_++1-p_-)/2=(1+\delta_X)/2$。
把事件与其补记录到一个 qubit，得到

$$
B_X=
 \begin{pmatrix}
 (1+\delta_X)/2&0\\0&(1-\delta_X)/2
 \end{pmatrix}
 =\frac12(I+\delta_X\sigma_z).
$$

其正性与球内性由 $|\delta_X|\le1$ 保证。
如果 $G_\sigma$ 是标量，$\operatorname{Tr}(XG_\sigma)=0$ 对全部零迹方向成立，
平衡已经满足，无须进行退化谱归一。

这里的 $\Xi$ 是对两种已指定制备及内部开关的数学表示；
它不复制同一个未知输入，也不自动提供候选制备与对偶效果的实际设备。
三维报告把一项偏置集中在一条轴上，未保存组成见证所用的全部维数与关系。
若另有相干比较接口，可以使用其余坐标；二元概率本身不供应相位。

| 比较层次 | 失败报告 | 失败的准确含义 |
|---|---|---|
| C92 整体正性 | 候选二元值在 $[0,1]$ 外，归一 Bloch 点在球外 | 指定资料不存在共同正归一态。 |
| C93 纤维内平衡 | $\delta_X\ne0$，仍是球内合法报告 | 当前候选不是相对于 $\tau$ 的规范信息投影。 |
| 实际来源识别 | 真实态与规范代表的新增联合读数不同 | 旧资料未确定这项真实关系；不因此否定任一态的量子合法性。 |

**白话图景。**两份状态对当前全部读口都一样，再用候选自己定义的对偶读口比较它们。
如果正反两边得到不同概率，就看见了规范选择中的偏置。
它仍然是一项合法概率，所以点留在球内。
上一轮的球外点表示根本没有共同整体；本轮的非零球内偏置表示代表尚未平衡。

<a id="section-11"></a>

## 11. 相对参照怎样改变，才算改写同一份内容

<a id="sec-c93-anchor-meaning"></a>

前面的参照等价定理给出了一个比“所有锚都无关”更准确的条件：
在固定纤维与固定最小支撑上，如果

$$
(P\log\tau P)-(P\log\kappa P)\in\mathcal S_P,
$$

则两个参照给出同一规范代表；反过来，同一规范代表也迫使这个包含成立。
因此已经可见的对数参照变化，只改变纤维上共同的常数项；
落在未读方向上的参照变化则可能改变代表。

另一个协变来自共同酉坐标变换。
若所有资料、参照、支撑与读口同时变换为

$$
\rho\mapsto U\rho U^\dagger,\quad
 \tau\mapsto U\tau U^\dagger,\quad
 P\mapsto UPU^\dagger,\quad W\mapsto UWU^\dagger,
$$

则谱函数演算给
$D(U\rho U^\dagger\Vert U\tau U^\dagger)=D(\rho\Vert\tau)$。
纤维与切向空间也被同一个双射运输；
唯一性因而使规范代表按同一酉共轭运输。
这是坐标无关性，不把任意改变物理来源当作同一操作。

相对熵与独立组合还满足明确的加性关系：

$$
D(\rho_A\otimes\rho_B\Vert\tau_A\otimes\tau_B)
 =D(\rho_A\Vert\tau_A)+D(\rho_B\Vert\tau_B).
$$

证明只需使用正支撑上的
$\log(\rho_A\otimes\rho_B)=\log\rho_A\otimes I+I\otimes\log\rho_B$
及迹一性；奇异 $\rho$ 按其正支撑计算。
这使本轮所选内部比较接到项目已有的组合与相对熵恢复接口。

**白话图景。**改锚有两种不同的作用。
共同换坐标，只是把同一结构转到另一套描述里，规范代表随之一起转。
改变参照内容，则要检查变化是否全部落在已经读到的方向；
如果是，它不改变同一纤维内的选择；如果触及未读关系，就可能改变推断。

<a id="section-12"></a>

## 12. 从纤维平衡到关系势：固定支撑内的光滑响应

<a id="sec-c93-response-geometry"></a>

前面的 C93 为每份兼容资料选择唯一的规范推断代表。
本节研究资料改变时，这个代表怎样响应。所有光滑结论都先固定同一个支撑 $P$；
不将支撑改变处的极限擅自包含进来。
也就是说，以下参数化始终保留 $P\rho P=\rho$ 这个压缩模型前件；
它不宣称未压缩问题中任意邻近资料都会自动强制同一个最小支撑。

在 $P\mathcal H$ 上记单位为 $P$，令

$$
L_\tau=P(\log\tau)P.
$$

这是先在原载体求 $\log\tau$ 再压缩，通常不等于 $\log(P\tau P)$。
选择自伴 $F_1,\ldots,F_q$，使

$$
\mathcal S_P=\operatorname{span}_{\mathbb R}\{P,F_1,\ldots,F_q\},
$$

且 $F_1,\ldots,F_q$ 模标量方向线性独立：
若 $\sum_jt_jF_j=cP$，则全部 $t_j=0$，继而 $c=0$。
重复或依赖的读口应先合并，不能将它们的零方向叫作几何退化的物理新效应。

### 定义 12.1（内生关系势与配分函数）

对 $\theta\in\mathbb R^q$ 定义

<a id="eq-c93-gibbs-response"></a>

$$
H(\theta)=L_\tau+\sum_j\theta_jF_j,\qquad
 \psi(\theta)=\log\operatorname{Tr}_{P}e^{H(\theta)},\qquad
 \sigma_\theta=e^{H(\theta)-\psi(\theta)P}.
\tag{12.1}
$$

其中 $\operatorname{Tr}_P$ 是压缩载体上的迹。
每个 $\sigma_\theta$ 在 $P\mathcal H$ 上忠实、归一。
参数 $\theta_j$ 是与已声明读口配对的对偶关系强度，
没有在此被赋予能量、温度或物理时间单位。

因为
$\log\sigma_\theta-L_\tau=\sum_j\theta_jF_j-\psi(\theta)P$ 属于 $\mathcal S_P$，
所以 $\sigma_\theta$ 正好满足它自身资料的 C93。
这个 Gibbs 形式表达既有平衡条件，没有再添加一条物理态资格公理。

### 引理 12.2（有限矩阵指数的方向导数）

<a id="lem-c93-duhamel"></a>

对自伴矩阵 $H,V$，

<a id="eq-c93-duhamel"></a>

$$
\left.\frac{d}{dt}e^{H+tV}\right|_{t=0}
 =\int_0^1e^{(1-s)H}Ve^{sH}\,ds.
\tag{12.2}
$$

**证明。**
对固定 $t$，令
$g(s)=e^{(1-s)(H+tV)}e^{sH}$。
利用同一个矩阵与其指数对易，求导得
$g'(s)=-t e^{(1-s)(H+tV)}Ve^{sH}$。
积分并代入 $g(0),g(1)$，得到

$$
e^{H+tV}-e^H
 =t\int_0^1e^{(1-s)(H+tV)}Ve^{sH}\,ds.
$$

有限矩阵指数连续；除以 $t$ 再令 $t\to0$ 即得结论。

### 定理 12.3（读出梯度与 BKM 响应矩阵）

<a id="thm-c93-bkm-response"></a>

令 $m_j(\theta)=\operatorname{Tr}_P(\sigma_\theta F_j)$，
并记 $\widetilde F_j=F_j-m_jP$。则

<a id="eq-c93-gradient-means"></a>

$$
\partial_j\psi=m_j,
\tag{12.3}
$$

<a id="eq-c93-bkm-covariance"></a>

$$
\chi_{ij}:=\partial_i\partial_j\psi
 =\int_0^1
   \operatorname{Tr}_P
   \bigl(\sigma_\theta^s\widetilde F_i
         \sigma_\theta^{1-s}\widetilde F_j\bigr)\,ds.
\tag{12.4}
$$

$\chi$ 是实对称正定矩阵。
若不删除模标量依赖，它仍为半正定，零方向恰好对应
$\sum_jt_jF_j$ 为标量。

**证明。**
引理 [12.2](#lem-c93-duhamel) 与迹的循环性给

$$
\partial_j\operatorname{Tr}_Pe^{H(\theta)}
 =\operatorname{Tr}_P(e^{H(\theta)}F_j),
$$

所以 $\partial_j\psi=m_j$。
对归一指数求导，再将标量归一项并入积分，得

$$
\partial_j\sigma_\theta
 =\int_0^1
   \sigma_\theta^{1-s}\widetilde F_j\sigma_\theta^s\,ds.
$$

与 $F_i$ 作迹配对并循环移动因子，得到式 [(12.4)](#eq-c93-bkm-covariance)。
它作为实光滑函数的 Hessian 实对称。

为直接核定正性，在 $\sigma_\theta$ 的本征基写其严格正本征值为 $p_a$。
定义对数平均

$$
L(x,y)=
 \begin{cases}
 \dfrac{x-y}{\log x-\log y},&x\ne y,\\[4pt]
 x,&x=y.
 \end{cases}
$$

它由积分 $\int_0^1x^sy^{1-s}\,ds$ 给出，因此对正 $x,y$ 严格为正。
对任意实系数 $t_j$，令
$G=\sum_jt_j\widetilde F_j$，则

<a id="eq-c93-bkm-spectral-positive"></a>

$$
\sum_{i,j}t_i\chi_{ij}t_j
 =\sum_{a,b}L(p_a,p_b)|G_{ab}|^2\ge0.
\tag{12.5}
$$

等号当且仅当 $G=0$，即 $\sum_jt_jF_j$ 为标量。
模标量独立性将这唯一压成 $t=0$，证明正定。

式 [(12.4)](#eq-c93-bkm-covariance) 是 Bogoliubov–Kubo–Mori
（BKM）响应形式。这里给出全部所需有限证明。
它由本轮采用的相对熵 Hessian 决定；
此前 v90 为完整正反比较和独立组合选择的恢复度量承担另一项任务 [9](#ref-v90)。
不能把这两个不同问题中的规范，误说成只有一个度量才合法。
此外，对自伴读口，这个 BKM 矩阵是实对称的；
不能从其虚部凭空增加手性，实际交叉方向仍要由算符关系供应。

**白话图景。**当前读数改变一点，规范代表也会改变。
配分函数的一阶变化就是各个读数，二阶变化则记录这些读数怎样互相响应。
所有真正独立的读出方向都有正的响应尺度；
如果某个方向只是重复已有问题或加一个常数，它才会成为零方向。
这里的几何来自所选推断代价的变化，而不是先画一个球再给它命名。

### 定理 12.4（固定支撑内的光滑一一参数化）

<a id="thm-c93-interior-diffeomorphism"></a>

定义压缩均值体

$$
\mathcal C_P=
 \left\{
 \bigl(\operatorname{Tr}_P(\rho F_j)\bigr)_{j=1}^q:
 \rho\ge0,\ \operatorname{Tr}_P\rho=1
 \right\}.
$$

在上述模标量独立坐标下，
$\theta\mapsto m(\theta)=\nabla\psi(\theta)$
是 $\mathbb R^q$ 到 $\operatorname{ri}\mathcal C_P$ 的光滑一一映射，逆也光滑。
对这些资料的最小相对熵值

$$
J(m)=\min_{\rho:\,\operatorname{Tr}_P(\rho F_j)=m_j}
       D(\rho\Vert\tau),
$$

有

<a id="eq-c93-legendre-response"></a>

$$
J(m)=\theta(m)\cdot m-\psi(\theta(m)),\qquad
 \nabla_mJ=\theta(m),\qquad
 \nabla_m^2J=\chi(\theta(m))^{-1}.
\tag{12.6}
$$

**证明。**
先说明均值体具有所声明的完整仿射维数。
若存在非零 $t$ 使 $t\cdot m=c$ 对所有态成立，则
$\sum_jt_jF_j=cP$，与模标量独立性矛盾。

任何忠实态的均值都属于相对内部：在迹零 Hermitian 空间上，
均值映射对自己的像有有界线性右逆；
足够小的均值扰动可提升成足够小的矩阵扰动，并保持原忠实态为正。
反过来，对任意相对内点 $m$，令 $m_0$ 为均匀态 $P/\operatorname{rank}P$ 的均值。
若 $m=m_0$ 已有忠实实现。否则，沿 $m-m_0$ 稍作延长仍在均值体内；
将延长点的一份实现与均匀态作正权混合，就得到 $m$ 的忠实实现。

因此 $\sigma_\theta>0$ 的均值位于相对内部。
反向给定相对内点，前文 C93 的存在及满支撑结论给一个忠实的最小相对熵代表。
其一阶平衡意味着
$\log\sigma-L_\tau$ 属于 $\mathcal S_P$，所以归一后恰为式 [(12.1)](#eq-c93-gibbs-response)。
这证明参数化满射。

若 $\theta\ne\theta'$，记 $v=\theta-\theta'$，则

$$
v\cdot(m(\theta)-m(\theta'))
 =\int_0^1 v^{\mathsf T}
   \chi(\theta'+sv)v\,ds>0.
$$

故它是单射。有限指数及对数均光滑，$\chi$ 处处可逆，
逆函数定理给局部光滑逆；单射性使这些局部逆拼成全局逆。

对任意具有均值 $m$ 的 $\rho$，

$$
\operatorname{Tr}_P\rho(\log\sigma_{\theta(m)}-L_\tau)
 =\theta(m)\cdot m-\psi(\theta(m)).
$$

代入相对熵的差，得到

$$
D(\rho\Vert\tau)
 =
 D(\rho\Vert\sigma_{\theta(m)})
 +\theta(m)\cdot m-\psi(\theta(m)).
$$

在 $\rho=\sigma_{\theta(m)}$ 处达到最小值，证明第一式。
对它求导，$\nabla_\theta\psi=m$ 使链式法则的额外项相消，
得到 $\nabla J=\theta$；再求导并使用 $dm=\chi\,d\theta$，得到最后一式。

零读口情形 $q=0$ 时，均值体只有一点，上述参数化按唯一点理解。
对 $q>0$，若资料在固定 $\mathcal C_P$ 内趋向其边界，
相应 $\theta$ 不可能留在有界集合：
否则有限子列会收敛至某个有限 $\theta$，其忠实态均值仍为内点，产生矛盾。
这说明边界需要支撑约简或无界对偶参数。
它没有证明跨不同支撑的推断连续；量子最大熵推断确有不连续现象 [13](#ref-weis2014)。

**白话图景。**只要固定同一个承载空间，并在相容体内部移动，
资料与关系势就能光滑地互相确定。
走向边界时，有的方向被压掉，原来的有限参数可能不再够用。
因此一张内部光滑图与跨边界的整体连续性，是两个不同的结论。

<a id="section-13"></a>

## 13. 关系球上的代价椭圆：径向与横向的精确尺度

<a id="sec-c93-pauli-bkm"></a>

复用 v91 已核定的三轴关系 [10](#ref-v91)：

$$
K=X_AX_BI_C,\qquad
 L=I_AZ_BZ_C,\qquad
 M=iKL=X_AY_BZ_C.
$$

它们平方为 $I$、两两反对易，并生成 $M_2\otimes I_4$ 的逻辑代数。
令 $\mathbf r=(a,b,m)$、$r=|\mathbf r|<1$，定义

$$
\omega_{\mathbf r}=\frac18(I+aK+bL+mM),\qquad \tau_0=I_8/8.
$$

本节新增的是这个已知关系球上的相对熵响应尺度，
不将 v91 的球与最大熵补全再次算作新结论。

### 定理 13.1（Pauli 关系球的精确熵势与 Hessian）

<a id="thm-c93-pauli-hessian"></a>

定义

<a id="eq-c93-pauli-entropy-potential"></a>

$$
\begin{aligned}
 \varphi(r)&=
 \frac{1+r}{2}\log(1+r)+
 \frac{1-r}{2}\log(1-r),\\
 \beta(r)&=\frac{\operatorname{arctanh}r}{r},
 \qquad \beta(0)=1.
 \end{aligned}
\tag{13.1}
$$

则

$$
D(\omega_{\mathbf r}\Vert\tau_0)=\varphi(r),
 \qquad
 \theta=\nabla_{\mathbf r}\varphi(r)=\beta(r)\mathbf r.
$$

对 $r>0$，记 $\mathbf n=\mathbf r/r$，
将切向增量分解为
$\delta\mathbf r=\delta\mathbf r_{\parallel}+\delta\mathbf r_{\perp}$。
其 Hessian 二次型恰为

<a id="eq-c93-pauli-hessian"></a>

$$
g_{\mathbf r}(\delta\mathbf r,\delta\mathbf r)
 =
 \frac{|\delta\mathbf r_{\parallel}|^2}{1-r^2}
 +\frac{\operatorname{arctanh}r}{r}
      |\delta\mathbf r_{\perp}|^2.
\tag{13.2}
$$

在 $r=0$ 时它连续成为普通欧氏平方。

**证明。**
反对易性使 $aK+bL+mM$ 的本征值为 $\pm r$，各重数四。
代入相对熵得到式 [(13.1)](#eq-c93-pauli-entropy-potential)。
直接微分给

$$
\varphi'(r)=\operatorname{arctanh}r,\qquad
 \varphi''(r)=\frac1{1-r^2}.
$$

径向函数的梯度为 $\varphi'(r)\mathbf n$。
再分别沿径向与正交方向微分：
径向权为 $\varphi''(r)$，横向权为 $\varphi'(r)/r$，
正是式 [(13.2)](#eq-c93-pauli-hessian)。
极限 $\operatorname{arctanh}r/r\to1$ 给原点公式。

也可以从关系势一侧直接核对。
对 $\boldsymbol\theta=(\theta_1,\theta_2,\theta_3)$、$s=|\boldsymbol\theta|$，

$$
\psi(\boldsymbol\theta)=\log\cosh s,\qquad
 \mathbf r=\frac{\tanh s}{s}\boldsymbol\theta.
$$

它的 Hessian 在径向为 $1-r^2$、横向为
$\tanh s/s=r/\operatorname{arctanh}r$，
与定理 [12.4](#thm-c93-interior-diffeomorphism) 的逆矩阵关系完全一致。

更精确地，对球内 $\mathbf r,\mathbf s$，

<a id="eq-c93-pauli-bregman"></a>

$$
D(\omega_{\mathbf s}\Vert\omega_{\mathbf r})
 =
 \varphi(|\mathbf s|)-\varphi(r)
 -\beta(r)\mathbf r\cdot(\mathbf s-\mathbf r).
\tag{13.3}
$$

这是因为 $\log\omega_{\mathbf r}$ 只有标量项与
$\beta(r)(aK+bL+mM)$ 两部分。
于是对固定球内点，

$$
D(\omega_{\mathbf r+\varepsilon\delta\mathbf r}
       \Vert\omega_{\mathbf r})
 =
 \frac{\varepsilon^2}{2}
 g_{\mathbf r}(\delta\mathbf r,\delta\mathbf r)
 +O(\varepsilon^3).
$$

### 推论 13.2（局部等代价截面的精确椭圆轴）

在一条径向与一条横向组成的切平面里，
$g_{\mathbf r}(\delta\mathbf r,\delta\mathbf r)\le1$
是椭圆盘，其两个半轴为

$$
\sqrt{1-r^2},\qquad
 \sqrt{\frac{r}{\operatorname{arctanh}r}}.
$$

对 $0<r<1$，径向半轴严格更短。

**证明。**
由

$$
\beta(r)=\int_0^1\frac{dt}{1-r^2t^2}
$$

可见 $1<\beta(r)<1/(1-r^2)$。
在式 [(13.2)](#eq-c93-pauli-hessian) 中令二次型不超过一，
即可读出半轴与严格次序。

这些椭圆属于固定点处的二阶代价模型。
有限大小的精确相对熵等值集还受更高阶项影响，不能把它们全部称为同一椭圆。
它们也不是已推出的粒子时间轨道。
给出实际门历史以后，轨迹仍须由相应生成元计算。

**白话图景。**同一个关系球上，向外推近边界与沿旁边转动，消耗的推断代价并不相同。
在中心，两种方向一样，局部等代价线是圆。
离开中心，径向更快触及正性边界，其尺度更紧，局部等代价线就成为椭圆。
这个圆到椭圆的变化由相对熵的二阶变化严格给出，尚未给它附加物理运动的含义。

### 13.1 隐藏第三轴的额外内容有精确代价

固定 $a,b$，记 $r_0=\sqrt{a^2+b^2}<1$，
以及 v91 的最大熵代表 $\omega_0=(I+aK+bL)/8$。
对允许的 $m$，令 $R=\sqrt{r_0^2+m^2}\le1$。
由于第三轴不改变两份给定边际，
式 [(13.3)](#eq-c93-pauli-bregman) 立即给

<a id="eq-c93-hidden-entropy-cost"></a>

$$
D(\omega_m\Vert\omega_0)
 =\varphi(R)-\varphi(r_0)
 =\frac12\int_0^{m^2}
       \beta\!\left(\sqrt{r_0^2+u}\right)\,du
 \ge\frac{\beta(r_0)}2m^2.
\tag{13.4}
$$

端点 $R=1$ 以连续极限理解；该相对熵仍有限，因为 $\omega_0>0$。
积分式由对 $m^2$ 求导得到，不等式由 $\beta$ 单调不减得到。
同时

$$
D(\omega_m,\omega_0)=\frac{|m|}{2},
$$

因为两态之差为 $mM/8$，而 $M$ 有八个绝对值为一的本征值。
这里左侧的 $D(\cdot,\cdot)$ 为迹距离，带双竖线的
$D(\cdot\Vert\cdot)$ 为相对熵，二者不可混用。

**白话图景。**当前两份局部记录看不到第三轴，但第三轴可以带着真实内容。
规范最大熵代表把这一方向置于中心；实际态偏离中心多少，
可以用迹距离和相对熵分别精确记账。
下一节会让这个暂时隐藏的方向经过一扇门，变成可直接读取的差异。

<a id="section-14"></a>

## 14. 规范代表之外：全部兼容整体对一个读口允许什么答案

<a id="sec-c93-prediction-ranges"></a>

C93 选择唯一的规范推断代表；实际整体仍可能是同一纤维中的其他态。
因此还须同时保留一个独立问题：
若暂不补入更多资料，某个新读口究竟能取哪些值？
项目 Atlas 已分析全状态纤维的预测宽度与缺失算符方向 [5](#ref-atlas)；
本节针对一份固定资料纤维给出完整区间、谱对偶和支撑内的单值判据。

设有限合成关系空间为含单位的实算符系统 $\mathcal S$，
当前资料给正归一响应 $\ell$，
其非空兼容纤维为

$$
\mathcal F_\ell
 =
 \{\rho\ge0:\operatorname{Tr}\rho=1,\quad
             \operatorname{Tr}(\rho W)=\ell(W)\quad(W\in\mathcal S)\}.
$$

对自伴 $B$ 定义

$$
l_\ell(B)=\min_{\rho\in\mathcal F_\ell}\operatorname{Tr}(\rho B),
 \qquad
 u_\ell(B)=\max_{\rho\in\mathcal F_\ell}\operatorname{Tr}(\rho B).
$$

纤维紧而凸，故两个端点达到，中间每个数值也由两端态的凸混合达到。

### 定理 14.1（固定资料纤维的精确谱对偶）

<a id="thm-c93-fixed-fiber-duality"></a>

有

<a id="eq-c93-upper-dual"></a>

$$
u_\ell(B)
 =\inf_{W\in\mathcal S}
   \bigl\{\ell(W)+\lambda_{\max}(B-W)\bigr\},
\tag{14.1}
$$

<a id="eq-c93-lower-dual"></a>

$$
l_\ell(B)
 =\sup_{W\in\mathcal S}
   \bigl\{\ell(W)+\lambda_{\min}(B-W)\bigr\}.
\tag{14.2}
$$

原载体上的右侧不预先保证达到。
这两个等式仍对边界资料成立，不要求先假定严格可行性。

**证明。**
对任意兼容 $\rho$ 与 $W\in\mathcal S$，

$$
\operatorname{Tr}(\rho B)
 =\ell(W)+\operatorname{Tr}[\rho(B-W)]
 \le\ell(W)+\lambda_{\max}(B-W).
$$

因此上式右侧至少为 $u_\ell(B)$。

反向取任意 $\beta>u_\ell(B)$。
将原有读出与新增读数 $\operatorname{Tr}(\rho B)=\beta$ 放在一起，
这组资料没有共同态。
对有限紧凸资料像使用 v92 的最近点分离证明 [11](#ref-v92)，
便存在 $W_0\in\mathcal S$ 与实数 $t$，使

$$
\ell(W_0)+t\beta>\lambda_{\max}(W_0+tB).
$$

任取原纤维中的 $\rho_0$，记 $b_0=\operatorname{Tr}(\rho_0B)\le u_\ell(B)$，
则

$$
\ell(W_0)+tb_0
 \le\lambda_{\max}(W_0+tB).
$$

两式相减，得到 $t(\beta-b_0)>0$，所以 $t>0$。
除以 $t$ 并令 $W=-W_0/t$，有

$$
\ell(W)+\lambda_{\max}(B-W)<\beta.
$$

由于对每个 $\beta>u_\ell(B)$ 都成立，右侧下确界不超过 $u_\ell(B)$。
结合弱界得等号。对 $-B$ 应用同一结论，再取负号，即得下界公式。

这就是 C92 的一个直接预测用途：
不断尝试给新读口填入一个候选答案，全部合成谱界恰好留下允许区间。
原始资料可以是局部边际，也可以是已声明的有限读口响应；
证明只使用有限算符系统及共同态的存在。

### 14.1 为什么边界需要先约简支撑

即使原始数据与最优预测都十分简单，对偶读口也未必有有限最优值。
取一个 qubit，
$\mathcal S=\operatorname{span}_{\mathbb R}\{I,P_0\}$，
$P_0=\lvert 0\rangle\langle 0\rvert$，并给 $\ell(P_0)=1$。
唯一兼容态是 $P_0$。若新读口为 $B=X$，其唯一预测为零。

任意 $W=aI+bP_0$ 的上对偶目标却等于

$$
\ell(W)+\lambda_{\max}(X-W)
 =\frac{b+\sqrt{b^2+4}}2>0.
$$

当 $b\to-\infty$ 时才趋于零，因此原载体上的下确界不达到。
压到真实共同支撑 $P=P_0$ 后，$PXP=0$，零读口已经达到最优值。

### 定理 14.2（支撑约简恢复对偶极值的达到）

<a id="thm-c93-face-dual-attainment"></a>

令 $P$ 为 $\mathcal F_\ell$ 的共同最小支撑，
$\mathcal S_P=P\mathcal SP$，$B_P=PBP$，
并以 $\ell_P(PWP)=\ell(W)$ 表示压缩响应。
则式 [(14.1)](#eq-c93-upper-dual)–[(14.2)](#eq-c93-lower-dual)
在压缩载体上的 $\inf,\sup$ 均达到。

**证明。**
前面的支撑结论给一份 $\rho_0\in\mathcal F_\ell$，
在 $P\mathcal H$ 上满足 $\rho_0\ge\mu P$，其中 $\mu>0$。
相同压缩的原读口在全部纤维态上给同一值，故 $\ell_P$ 定义良好。

取上对偶目标的一列逼近最小值的 $W_j\in\mathcal S_P$。
目标在 $W_j\mapsto W_j-cP$ 下不变，
所以可令 $\ell_P(W_j)=0$。
由于逼近目标值有统一上界，
存在 $C>0$ 使 $W_j\ge-CP$ 对全部 $j$ 成立。
写 $W_j=W_{j,+}-W_{j,-}$。
从 $\operatorname{Tr}(\rho_0W_j)=0$ 得

$$
\mu\operatorname{Tr}W_{j,+}
 \le\operatorname{Tr}(\rho_0W_{j,+})
 =\operatorname{Tr}(\rho_0W_{j,-})
 \le C.
$$

又 $0\le W_{j,-}\le CP$，故 $W_j$ 在算符范数下有界。
有限维闭子空间中取收敛子列，连续目标在极限达到下确界。
对 $-B_P$ 作同样论证，得到下对偶的上确界达到。

### 定理 14.3（一份资料何时唯一决定新读口）

<a id="thm-c93-face-predictability"></a>

在上述共同最小支撑上，

<a id="eq-c93-face-predictability"></a>

$$
l_\ell(B)=u_\ell(B)
 \quad\Longleftrightarrow\quad
 PBP\in P\mathcal SP.
\tag{14.3}
$$

**证明。**
右侧成立时，响应由 $\ell_P$ 固定，故预测单值。

反向，设全部兼容态给出同一响应。
令 $X=X^\dagger$ 是压缩载体上任意不可见方向：
$\operatorname{Tr}(XW)=0$ 对所有 $W\in\mathcal S_P$ 成立。
因 $P\in\mathcal S_P$，有 $\operatorname{Tr}X=0$。
取上一证明中的忠实 $\rho_0$；充分小的 $\varepsilon>0$ 使
$\rho_0\pm\varepsilon X$ 都合法且保留全部资料。
其 $B_P$ 响应相同，故 $\operatorname{Tr}(XB_P)=0$。
因此 $B_P$ 正交于 $\mathcal S_P^\perp$，
有限维双正交给 $B_P\in\mathcal S_P$。

对一个已声明过程 $\Phi$ 和未来读口 $E$，只需把
$B=\Phi^*(E)$ 代入，就得到当前资料能否确定该未来读数的准确判据。
这是固定资料、固定支撑及指定未来问题的条件；
不要求当前窗口已经决定整个全态。

**白话图景。**选一个规范代表可以给出一个答案，但完整资料还允许一个答案区间。
谱对偶从全部合成比较中精确划出这个区间。
先把所有整体都不可能占据的方向删掉，再看新读口是否已由现有关系张成，
就能判断答案是否已经唯一。
边界上的“需要无限大比较参数”，有时只是尚未删去这些空方向。

<a id="section-15"></a>

## 15. 隐藏交叉关系怎样经一扇门变成可见预测差

<a id="sec-c93-pauli-prediction"></a>

继续使用前节 $K,L,M$，以及 v91 的两份固定边际

$$
\rho_{AB}=\frac14(I+aX_AX_B),\qquad
 \rho_{BC}=\frac14(I+bZ_BZ_C).
$$

记 $r_0^2=a^2+b^2\le1$。
v91 已给出
$\omega_m=(I+aK+bL+mM)/8$ 的合法球切片 [10](#ref-v91)。
下面把第三轴的区间升级为*全部兼容全态的精确预测区间*，
并研究它怎样被指定门读出。

### 命题 15.1（所有兼容全态的第三轴范围）

<a id="prop-c93-full-hidden-axis-range"></a>

在所有具有这两份完整边际的全态中，
$m=\operatorname{Tr}(\rho M)$ 的可达范围恰为

<a id="eq-c93-full-hidden-axis-range"></a>

$$
-\sqrt{1-r_0^2}\le m\le\sqrt{1-r_0^2}.
\tag{15.1}
$$

**证明。**
任意兼容 $\rho$ 都有
$\operatorname{Tr}(\rho K)=a$、
$\operatorname{Tr}(\rho L)=b$。
令 $R=\sqrt{a^2+b^2+m^2}$。
反对易性给
$(aK+bL+mM)^2=R^2I$，从而其最大本征值为 $R$。
若 $R>0$，则

$$
R^2=\operatorname{Tr}[\rho(aK+bL+mM)]\le R,
$$

所以 $R\le1$；$R=0$ 显然成立。
这证明任何兼容态都满足式 [(15.1)](#eq-c93-full-hidden-axis-range)。
反过来，区间内每个 $m$ 都由上述 $\omega_m$ 实现，
它的两个完整边际正是指定资料。

声明一个实际酉门族

$$
U_\theta=e^{-i\theta L/2},
$$

并在门后读取二元效果 $(I+K)/2$。
这里 $\theta$ 是已给的门参数；它不是从 C93 自动产生的物理时钟。

### 定理 15.2（未来二元读出的精确区间与最小补充）

<a id="thm-c93-future-pauli-interval"></a>

对当前全部兼容态，门后概率的可达区间恰为

<a id="eq-c93-future-pauli-interval"></a>

$$
p_\theta\in
 \left[
 \frac{1+a\cos\theta}{2}
 -\frac{|\sin\theta|}{2}\sqrt{1-a^2-b^2},
 \quad
 \frac{1+a\cos\theta}{2}
 +\frac{|\sin\theta|}{2}\sqrt{1-a^2-b^2}
 \right].
\tag{15.2}
$$

新增一个标量 $m=\operatorname{Tr}(\rho M)$，
就足以确定这个读出轨道中所有 $\theta$ 的概率。
若 $a^2+b^2<1$ 且 $\sin\theta\ne0$，原资料不能确定该概率，
因此确实需要一个独立于现有资料的额外内容。

**证明。**
由 $L^2=I$，
$U_\theta=\cos(\theta/2)I-i\sin(\theta/2)L$。
利用 $LK=-KL$、$M=iKL$ 展开，得

$$
U_\theta^\dagger K U_\theta
 =K\cos\theta-M\sin\theta.
$$

因此

<a id="eq-c93-future-pauli-probability"></a>

$$
p_\theta(\rho)=
 \frac{1+a\cos\theta-m\sin\theta}{2}.
\tag{15.3}
$$

代入命题 [15.1](#prop-c93-full-hidden-axis-range) 即得全部范围。
两个端点由相应的 $\omega_m$ 达到，故它不是松上界。
给出 $m$ 后，式 [(15.3)](#eq-c93-future-pauli-probability) 对全部 $\theta$ 已确定。
若 $a^2+b^2<1$ 且 $\sin\theta\ne0$，两个端点不同，
它们来自相同旧资料，故任何只使用旧资料的单值规则都无法同时等于二者。

这项最小补充只针对指定的 $K$ 读出轨道。
它不声称一个 $m$ 就决定全部三比特全态或所有未来二体边际。
在逻辑代数
$\operatorname{span}_{\mathbb C}\{I,K,L,M\}\simeq M_2\otimes I_4$
中，它确实补齐了所缺的第三方向。
门还给
$U_\theta^\dagger M U_\theta=M\cos\theta+K\sin\theta$，
所以 $(a,m)$ 作圆周旋转，而 $b$ 保持不变。
这是在已经明确指定的酉动力学下成立的圆与周期，
与前节相对熵的局部代价椭圆属于不同的数学问题。

### 推论 15.3（此对称模型中的精确中心预测）

只预测这一个二元读出、以最大绝对概率误差计分时，
唯一最优标量预测是区间中心

$$
\widehat p_\theta=\frac{1+a\cos\theta}{2},
$$

最坏误差为

$$
\frac{|\sin\theta|}{2}\sqrt{1-a^2-b^2}.
$$

v91 的最大熵代表 $\omega_0$ 恰好给这个中心。

**证明。**
对任意闭区间 $[l,u]$，标量预测 $c$ 的最坏误差为
$\max(|c-l|,|c-u|)$。
它唯一在 $c=(l+u)/2$ 取最小值 $(u-l)/2$。
应用式 [(15.2)](#eq-c93-future-pauli-interval) 即得。

对具体 $\omega_m$，其与中心预测的误差为
$e_\theta=|\sin\theta|\,|m|/2$。
若 $r_0<1$ 且 $\sin\theta\ne0$，
式 [(13.4)](#eq-c93-hidden-entropy-cost) 进一步给

$$
D(\omega_m\Vert\omega_0)
 \ge
 \frac{2\beta(r_0)}{\sin^2\theta}\,e_\theta^2.
$$

这是该解析家族中隐藏内容、相对熵代价与未来读出误差的精确连接，
没有把未知实际态强制设成最大熵代表。

**白话图景。**两张局部图现在看不见第三条交叉关系。
让系统经过一扇明确的门，这条隐藏方向就会旋转进原本可见的读口。
原来的资料因此只能给一个精确区间；补上第三轴，整条读出轨道就都确定了。
在这个对称模型里，最大熵代表给区间中心，
但实际内容可以在中心两边，仍是完全合法的量子状态。

<a id="section-16"></a>

## 16. 推断代表的两个边界：不普遍最优预测，也不是普适仿射门

<a id="sec-c93-inference-boundaries"></a>

项目 V42 已明确区分最大熵补全与标量 minimax 中点 [4](#ref-v42)。
下面给两个完整、有限、可直接核算的实例，
防止把本轮的规范推断原则扩张成未经证明的物理演化规律。

### 命题 16.1（最大熵代表不普遍给预测区间的中心）

<a id="prop-c93-maxent-not-minimax"></a>

给两个 qubit 的单点边际

$$
\rho_A=\rho_B=\operatorname{diag}(3/4,1/4).
$$

取事件 $E=\lvert 11\rangle\langle 11\rvert$。
它在全部兼容全态中的概率范围为 $[0,1/4]$。
唯一最大熵补全给概率 $1/16$，
而以最坏绝对概率误差计分的唯一最优预测为 $1/8$。

**证明。**
由于
$0\le E\le I_A\otimes\lvert 1\rangle\langle 1\rvert$，
任意兼容态都有 $0\le\operatorname{Tr}(\rho E)\le1/4$。
对任意 $t\in[0,1/4]$，计算基对角态

$$
\rho_t=\operatorname{diag}
 (1/2+t,\ 1/4-t,\ 1/4-t,\ t)
$$

合法，具有给定两份完整单点边际，并给事件概率 $t$。
所以该区间精确。

乘积态 $\rho_A\otimes\rho_B$ 是唯一最大熵补全：
对任意兼容 $\rho$，

$$
D(\rho\Vert\rho_A\otimes\rho_B)
 =S(\rho_A)+S(\rho_B)-S(\rho)\ge0,
$$

等号只在乘积态处成立。
它给事件概率 $(1/4)(1/4)=1/16$。
区间中心则为 $1/8$，其最坏误差为 $1/8$；
最大熵预测的最坏误差为 $1/4-1/16=3/16$。
因此两种最优性并不相同。

本轮 C93 优化的是相对熵与纤维内偏置，
而不是对每个尚未指定的未来问题同时优化所有可能损失函数。
保留完整预测区间，才不会让一个规范代表掩盖资料仍未决定的内容。

### 定理 16.2（不存在全域仿射的精确单点补全选择器）

<a id="thm-c93-no-affine-completion"></a>

不存在一个仿射映射 $F$，对所有两 qubit 单点资料 $(\rho_A,\rho_B)$
都输出一份具有这两份边际的共同密度态。
因此最大熵补全也不能在全部未知输入上，
被解释为一台只依赖单点边际的普适线性或 CPTP 门。

**证明。**
若一个边际为纯态 $P_a$，正性迫使整体支撑于
$\operatorname{ran}P_a\otimes H_B$：
因为正算符 $(I-P_a)\otimes I_B$ 的期望为零，其支撑方向不能出现。
若两个边际都纯，则整体唯一为 $P_a\otimes P_b$。
所以对 $a,b\in\{0,1\}$，

$$
F(P_a,P_b)=P_a\otimes P_b.
$$

可是资料空间中有两个相同的凸混合：

$$
\frac12(P_0,P_0)+\frac12(P_1,P_1)
 =
 \frac12(P_0,P_1)+\frac12(P_1,P_0)
 =(I_2/2,I_2/2).
$$

仿射性一方面要求该资料的输出为

$$
\frac12(P_0\otimes P_0+P_1\otimes P_1),
$$

另一方面又要求输出为

$$
\frac12(P_0\otimes P_1+P_1\otimes P_0).
$$

两矩阵具有不同且正交的支撑，矛盾。

若有一台全域 CPTP 门只依赖输入的单点边际并保持它们，
它在四个纯乘积输入上同样被迫给上述唯一输出。
将线性性用于两份输入混合，再用相同边际要求输出相同，
就得到完全相同的矛盾。

该反例全部位于经典对角态中，不依赖纠缠或非对易测量。
它限制的是对一份未知输入的全域单通道解释。
若要实现依据已有经典记录作推断、再制备代表态的更大流程，
必须保留记录、所给信息和相应控制接口，不能将它们从模型中省略。

**白话图景。**知道两个局部内容，并不等于知道它们当初怎样相关。
两种不同的混合历史，可以给完全相同的单点资料，却保留相反的整体关联。
因此任何只看单点内容的规范补全，都不能同时作为一扇保持所有未知输入关系的线性门。
规范代表、实际整体和针对某个未来问题的最佳预测，各有明确用途，也各有自己的条件。

<a id="section-17"></a>

## 17. 圆形读出仍会跳跃：补一个坐标如何修复

<a id="sec-c93-boundary-continuity"></a>

最小支撑上的规范代表存在且唯一，不保证它随读出在全部边界连续。
这种现象在量子最大熵推断中已有明确文献；以下圆盘例是 Weis 的
Type II 例子的酉换基形式 [14](#ref-weis2015)。
我们给出完整解析证明，并进一步指出：一个遗漏的二元读出足以修复本例的推断连续性，
但该修复仍不自动成为可作用于未知输入的物理通道。

在 $\mathbb C^3$ 的标准基 $e_1,e_2,e_3$ 中，记
$P_j=\lvert e_j\rangle\langle e_j\rvert$、$\Pi=P_1+P_2$、$Q=P_3$，并取

<a id="eq-c93-disk-observables"></a>

$$
A=\sigma_z\oplus1=\operatorname{diag}(1,-1,1),\qquad
 B=\sigma_x\oplus0,
 \qquad \tau=I_3/3.
\tag{17.1}
$$

这里 $\sigma_z,\sigma_x$ 作用于 $\Pi\mathbb C^3$。
给定读数 $a=\operatorname{Tr}(\rho A)$、$b=\operatorname{Tr}(\rho B)$，
以 $\mathfrak m_2(a,b)$ 表示同纤维中唯一的最大熵态。
因 $D(\rho\Vert I_3/3)=\log3-S(\rho)$，这也正是本轮的相对熵规范完成。

### 定理 17.1（连续圆周读数与二分之一的边界跳跃）

<a id="thm-c93-maxent-discontinuity"></a>

上述两读出的可行域为闭单位圆盘

$$
\mathcal C_2=\{(a,b):a^2+b^2\le1\}.
$$

对 $0<|\theta|<\pi$，有

<a id="eq-c93-boundary-pure"></a>

$$
\mathfrak m_2(\cos\theta,\sin\theta)
 =\rho_\theta
 =\frac12(I_2+\cos\theta\,\sigma_z+\sin\theta\,\sigma_x)\oplus0.
\tag{17.2}
$$

但在 $(a,b)=(1,0)$，

<a id="eq-c93-boundary-jump"></a>

$$
\mathfrak m_2(1,0)=\frac{P_1+P_3}{2},\qquad
 \lim_{\theta\to0}\rho_\theta=P_1.
\tag{17.3}
$$

用 $d_{\rm tr}(\rho,\sigma)=\tfrac12\left\lVert \rho-\sigma\right\rVert_1$ 记迹距离，则

<a id="eq-c93-half-jump"></a>

$$
\lim_{\theta\to0}
 d_{\rm tr}\bigl(\mathfrak m_2(\cos\theta,\sin\theta),
                 \mathfrak m_2(1,0)\bigr)=\frac12.
\tag{17.4}
$$

**证明。**
对任意状态，记 $c=\operatorname{Tr}(\rho Q)$、$t=1-c$。
当 $t>0$ 时，$\Pi\rho\Pi/t$ 是二位状态，其两项 Pauli 读数 $(z,x)$ 满足
$z^2+x^2\le1$；于是

$$
(a,b)=t(z,x)+c(1,0)
$$

属于单位圆盘。$t=0$ 时仍得到圆盘上的 $(1,0)$。
反过来，圆盘内任意 $(a,b)$ 都由
$\tfrac12(I_2+a\sigma_z+b\sigma_x)\oplus0$ 实现，所以可行域恰为圆盘。

现在取圆周上的 $(\cos\theta,\sin\theta)$。正算符

$$
W_\theta=I_3-\cos\theta\,A-\sin\theta\,B
$$

在上方二位块中的特征值为 $0,2$，在第三方向的特征值为
$1-\cos\theta>0$。所有满足指定读数的 $\rho$ 都有
$\operatorname{Tr}(\rho W_\theta)=0$，故其支撑包含于 $\ker W_\theta$。
这一步仅用：正矩阵 $\rho,W$ 满足 $\operatorname{Tr}(\rho W)=0$ 时，
$W^{1/2}\rho W^{1/2}=0$，从而 $\operatorname{supp}\rho\subseteq\ker W$。
$\ker W_\theta$ 是向量
$u_\theta=(\cos(\theta/2),\sin(\theta/2),0)$ 张成的一维空间，
所以整个纤维只有 $\rho_\theta=\lvert u_\theta\rangle\langle u_\theta\rvert$ 一个状态。

当 $(a,b)=(1,0)$ 时，$I_3-A=2P_2$ 的零读数只强制支撑落在
$R=P_1+P_3$。而 $RBR=0$，第二个读数没有再缩小这个支撑。
因此纤维恰为 $R\mathbb C^3$ 上的全部密度态，其中唯一最大熵态为 $R/2$。
另一方面，式 [(17.2)](#eq-c93-boundary-pure) 直接给出
$\rho_\theta\to P_1$。最后

$$
P_1-R/2=(P_1-P_3)/2,
 \qquad \left\lVert (P_1-P_3)/2\right\rVert_1=1.
$$

迹范数连续，遂得所述二分之一跳跃。

这说明圆周读数的光滑性，无法单独保证“只凭这些读数挑出的规范全态”光滑。
沿圆周到达特殊点时，兼容支撑从一维突然增为二维；
最大熵原则在这个更大的纤维中重新选择了中心。
因此，唯一性、支撑内的光滑性与跨支撑层的连续性是三个不同结论。

**白话图景。**仪表上的两个指针沿着一个很平滑的圆走，仍可能漏掉一条内部方向。
在圆上的普通点，读数已经把状态钉死；到那个特殊点，却突然有一整片内部状态给出相同读数。
若规则是在所有可能状态中选最不偏向某个方向的代表，它就会转到这片状态的中间。
跳跃来自原来的读数没有分开这些内容，不能归咎于圆周本身不连续。

### 17.1 补读第三方向：规范代表成为仿射连续函数

补充一个二元读出 $\{Q,I_3-Q\}$，记 $c=\operatorname{Tr}(\rho Q)$。
这一坐标与原先的 $a,b$ 一同报告，不改变已有两个读数的含义。
令 $\mathfrak m_3(a,b,c)$ 表示三个读数固定后的最大熵态。

### 定理 17.2（三坐标域、唯一完成与定量连续性）

<a id="thm-c93-third-coordinate-repair"></a>

三项读数的完整可行域为

<a id="eq-c93-three-coordinate-domain"></a>

$$
\mathcal C_3=
 \left\{(a,b,c):0\le c\le1,\quad
 (a-c)^2+b^2\le(1-c)^2\right\}.
\tag{17.5}
$$

对全部可行资料，唯一最大熵态为

<a id="eq-c93-affine-maxent"></a>

$$
\boxed{\quad
 \mathfrak m_3(a,b,c)=
 \begin{pmatrix}
  (1+a-2c)/2 & b/2 & 0\\
  b/2 & (1-a)/2 & 0\\
  0&0&c
 \end{pmatrix}.
 \quad}
\tag{17.6}
$$

它是资料的仿射函数，且任意两组可行资料都满足

<a id="eq-c93-affine-lipschitz"></a>

$$
d_{\rm tr}\bigl(\mathfrak m_3(a,b,c),\mathfrak m_3(a',b',c')\bigr)
 \le\frac{|a-a'|+|b-b'|}{2}+|c-c'|.
\tag{17.7}
$$

**证明。**
先对任意兼容态作块压缩 $\rho\mapsto\Pi\rho\Pi+Q\rho Q$。
三个可见读数保持不变；上方二位块的迹为 $t=1-c$，可写成

$$
T=\frac12\bigl(t I_2+b\sigma_x+y\sigma_y+(a-c)\sigma_z\bigr)
$$

其中 $y\in\mathbb R$。正性等价于
$(a-c)^2+b^2+y^2\le t^2$，故必有
式 [(17.5)](#eq-c93-three-coordinate-domain)。
反过来，取 $y=0$ 并将跨块项设为零，就得到
式 [(17.6)](#eq-c93-affine-maxent)；该矩阵正且迹一，证明域的充分性。

再证明唯一最大熵性。这里使用的熵严格凹性可由前文相对熵非负直接得到：
对 $0<t<1$、$\eta=t\rho+(1-t)\sigma$，有

$$
S(\eta)-tS(\rho)-(1-t)S(\sigma)
 =tD(\rho\Vert\eta)+(1-t)D(\sigma\Vert\eta)\ge0,
$$

等号只在 $\rho=\sigma$ 时成立。上述块压缩等于

$$
\frac12(\rho+U\rho U^*),\qquad U=\Pi-Q.
$$

熵的凹性及酉不变性说明这一步不减熵，
严格凹性说明取等必有 $\rho=U\rho U^*$，即原态已经块对角。
对块对角态 $\rho'=T\oplus c$，在这组固定基中取转置并平均，得到

$$
\frac12(\rho'+(\rho')^{\mathsf T})
 =\mathfrak m_3(a,b,c).
$$

转置保持单个状态的谱，因而保持熵；两项平均再次不减熵。
严格凹性说明取等必有 $\rho'=(\rho')^{\mathsf T}$，即 $y=0$。
两步同时取等只可能是式 [(17.6)](#eq-c93-affine-maxent)，
该论证也包括 $c=0,1$ 及其余退化边界。

最后，将两份规范态之差按 $\Delta a,\Delta b,\Delta c$ 展开。
三个系数矩阵分别为

$$
\tfrac12\operatorname{diag}(1,-1,0),\qquad
 \tfrac12(\sigma_x\oplus0),\qquad
 \operatorname{diag}(-1,0,1),
$$

迹范数分别为 $1,1,2$。由迹范数三角不等式得到
式 [(17.7)](#eq-c93-affine-lipschitz)。

原先 $(a,b)=(1,0)$ 的纤维，现在被 $c$ 分成

$$
\mathfrak m_3(1,0,c)=(1-c)P_1+cP_3,\qquad 0\le c\le1.
$$

沿圆周来的纯态资料为 $(\cos\theta,\sin\theta,0)$，
极限是 $(1,0,0)$，相应代表连续趋于 $P_1$。
原先的二读数最大熵代表 $R/2$ 则有新读数 $c=1/2$，
对应另一个资料点 $(1,0,1/2)$。
补读 $Q$ 将原来叠在一个地址上的不同内容分开了。

<a id="fig-c93-third-coordinate"></a>

```text
       两个读数的圆盘                         三维资料域的 b = 0 截面
                b                                          c
                ↑                                          ↑
            · · · · ·                                      │        ● P₃
         ·      │      ·                                   │      / │
        ·       │       ·            补读 Q                │    /   ● R/2
    ───·────────0────────●──→ a      ───────→               │  /     │
        ·       │       · (1,0)                     (−1,0) ●─────────● P₁ → a
         ·      │      ·                                            (1,0)
            · · · · ·

    同一点容纳不同的 c；补读后，原来的单点展开为一条可读线段。
```

字符图仅作示意；原图的精确区域、标记和投影关系如下：

| 图示对象 | 精确区域或坐标 |
|---|---|
| 左图：两个读数的圆盘 | a² + b² ≤ 1；特殊点为 (a, b) = (1, 0)。 |
| 右图：三维资料域的 b = 0 截面 | 0 ≤ c ≤ 1，−1 + 2c ≤ a ≤ 1；三角形顶点为 (a, c) = (−1, 0)、(1, 0)、(1, 1)。 |
| 右侧可读线段 | a = 1，0 ≤ c ≤ 1。 |
| 三个状态标记 | P₁ 位于 (a, c) = (1, 0)，R/2 位于 (1, 1/2)，P₃ 位于 (1, 1)。 |
| 忽略新增读数 c 的投影 | 右侧整条线段都投到左图同一点 (a, b) = (1, 0)。 |

**图 1。**左图是完整的两读数域，右图是式 [(17.5)](#eq-c93-three-coordinate-domain)
在 $b=0$ 的精确截面 $-1+2c\le a\le1$。
图中的 $R=P_1+P_3$。忽略 $c$ 时，右侧竖线都投到左图的同一点 $(1,0)$。

**白话图景。**多看一个问题：“第三个方向占了多少？”原先突然变宽的状态集合就有了自己的坐标。
沿圆周来的状态一直回答零，所以它会连续回到第一个方向；
原来那个混合代表回答二分之一，已经是另一个地址。
这个修复只要求补上本例遗漏的一项关系，也给出了读数误差如何传到预测误差的明确界。

### 17.2 连续的状态完成，仍须接受带参考的过程检查

### 命题 17.3（该仿射完成不是未知输入上的量子通道）

<a id="prop-c93-repair-not-channel"></a>

定义状态完成映射

$$
\mathcal R(\rho)=
 \mathfrak m_3\bigl(\operatorname{Tr}(\rho A),\operatorname{Tr}(\rho B),\operatorname{Tr}(\rho Q)\bigr).
$$

它的线性延拓为正、保迹映射，却不完全正。
不存在对所有未知输入都给出这个完成态的单一 CPTP 通道。

**证明。**
由显式公式，$\mathcal R$ 先去掉跨块项，再对上方二位块作

$$
\Psi(T)=\frac{T+T^{\mathsf T}}2,
$$

第三个对角元保持不变。这两步在单个输入上均保持正性与迹。
若 $\mathcal R$ 完全正，则将输入和输出限制于 $\Pi\mathbb C^3$ 后，
$\Psi$ 也必须完全正。

在二位输入旁保留一个二位参考，令
$\lvert \Phi\rangle=(\lvert 00\rangle+\lvert 11\rangle)/\sqrt2$、$\Phi=\lvert \Phi\rangle\langle \Phi\rvert$，
以 $F$ 表示交换两个二位因子的算符。
直接展开四项矩阵单位，得到

$$
(\operatorname{id}\otimes\mathsf T)(\Phi)=F/2,
 \qquad
 (\operatorname{id}\otimes\Psi)(\Phi)=\Phi/2+F/4.
$$

反对称单位向量
$\lvert \psi_-\rangle=(\lvert 01\rangle-\lvert 10\rangle)/\sqrt2$
同时满足 $\Phi\lvert \psi_-\rangle=0$ 与 $F\lvert \psi_-\rangle=-\lvert \psi_-\rangle$。
因此这个带参考输出在该方向的特征值为 $-1/4$，不是正算符。
这里用的是归一化二位 Bell 输入的 Choi 检查；嵌入三位输出后，负方向仍然存在。
故 $\Psi$、$\mathcal R$ 都不完全正。
密度态线性张成 Hermitian 算符空间，
因此任何对全部密度态给出同样输出的线性通道都必须有这一延拓。

这项失败也正好对应项目 V78、V80 已要求保留的内部参考检查
 [6](#ref-v78)、[8](#ref-v80)：在单独输入上看似合理的读出重建，
接上参考后仍可能给出负的二元投影响应。
已知经典资料 $(a,b,c)$ 后，可以按式 [(17.6)](#eq-c93-affine-maxent)
另行制备代表态；此事不要求把 $\mathcal R$ 作为未知输入上的物理门。
而获取精确期望资料，本身也不等同于对未知单份输入完成一次这种门操作。

补读 $Q$ 还没有恢复上方块的 $\sigma_y$ 相干，也没有读出两块之间的相干。
例如 $\lvert \pm\rangle=(e_1\pm e_3)/\sqrt2$ 两个纯态，
都给出 $(a,b,c)=(1,0,1/2)$，规范代表仍是 $R/2$。
因此本节证明的是特定资料菜单下的连续规范推断，
而完整内容识别与可实现过程仍由各自的关系检验决定。

**白话图景。**把几个已知读数整理成一个连续、明确的预测代表，和真的给未知量子态施加一个门，
是两种需要分别验证的工作。本例的整理规则在单份状态上始终合法，
但连同旁边的参考一起检查，会出现负概率方向，所以它不能直接当成物理通道。
新增读数修复了这次地址压叠造成的跳跃；还没被读出的相位，仍然保留为真实的不确定内容。

<a id="section-18"></a>

## 18. 怎样接回现有量子力学：完整而有前件的重构链

<a id="sec-c93-quantum-reconstruction"></a>

本轮 C93 解决的是共同全态已经存在之后的规范推断问题。
复状态空间、实际过程及读出概率的供应，继续使用项目 V79、V80 已明确的接口
 [7](#ref-v79)、[8](#ref-v80)。下面把完整链条放在同一张表中；
这样既能看见本轮增加了什么，也能准确追踪每条标准规则来自哪一层关系。

| 标准规则或理论环节 | 内部前件与推导来源 | 得到的表示 |
|---|---|---|
| 复 Hilbert 状态空间 | 共同正比较、零关系商、共同复方向；这些是前稿供应的结构 | 正复核的线性张成除去零范数关系，完成为 $H$；归一向量及射线描述纯态。 |
| 密度态与概率 | 同一完整效果接口上的正性、归一与可加响应 | $\rho\ge0$、$\operatorname{Tr}\rho=1$，读出 $p(E)=\operatorname{Tr}(\rho E)$。 |
| 实际完整过程 | V80 的完整强度、定向锚校准与二元差分不增 | 实际输出 $F(x)$ 本身等于复线性等距 $Vx$；不是另找线性替身。 |
| 效果、仪器与 Born 律 | 同根强度标定、完整结果分支与内部细记录 | $E_e=\sum_\alpha M_{e\alpha}^\dagger M_{e\alpha}$， $p_e=\operatorname{Tr}(\rho E_e)$，条件态由仪器归一。 |
| 复合与纠缠 | 已声明独立端口的积核、产品张成与局部作用 | $H_{AB}\simeq H_A\otimes H_B$；整体态不必是乘积或可分态。 |
| 完全正性 | 同一实际过程作用时保留任意合法内部参考 | Kraus 夹乘在参考扩张下仍保正；只检查单个输入不够。 |
| 锐观测与投影更新 | 效果区间极点、完整锐菜单；结果子空间内全部纯态不扰动的理想条件另列 | $A=\sum_aaP_a$；理想情形为 $P_a\rho P_a/p_a$。 |
| 酉演化与薛定谔式 | 有限同维完整单结果过程；实际 $C^1$ 时间历史 | $U^\dagger U=I$，$H=i\hbar\dot U U^\dagger$， $i\hbar\dot\psi=H\psi$。 |
| 局部资料共同成立 | v92 的全部合成谱界 C92 | 非空全态纤维 $\mathcal F_\ell$；有限层相容不等于随便拼接。 |
| 规范补全与统计响应 | 本轮 C93、内部参照、最小支撑递归 | 唯一相对熵投影、压缩 Gibbs、精确勾股与 BKM 响应。 |
| 未决内容的预测 | 完整兼容纤维与指定未来读口 | 精确谱对偶区间；$PBP\in P\mathcal SP$ 当且仅当答案唯一。 |

### 18.1 正比较怎样表示为 Hilbert 空间

设前稿供应的共同复比较核为 $k(x,y)$，对每组有限内容 $x_i$ 与复系数 $c_i$ 都有
$\sum_{ij}\bar c_i c_j k(x_i,x_j)\ge0$。
在形式线性组合上定义

$$
\left\langle\sum_i c_i[x_i],\sum_jd_j[y_j]\right\rangle
 =\sum_{ij}\bar c_i d_j k(x_i,y_j).
$$

正半定性给 Cauchy–Schwarz 不等式：在
$\langle u+zv,u+zv\rangle\ge0$ 中改变复数 $z$，即得
$|\langle u,v\rangle|^2\le\langle u,u\rangle\langle v,v\rangle$。
零范数方向因此与所有方向正交，可以取商；再完备化得到 Hilbert 空间。
有限截口中商空间已有限维，无须另加极限步骤。

这里复方向与共同正核是已供应的前件。
单个二元报告可用三个实 Bloch 坐标表示，并不意味着任意全态可以无损压进一个球。
本轮的任意维纤维、支撑与参考都仍在完整载体中，三维提升只集中一项二元见证。

### 18.2 同一分支同时给出概率与状态更新

### 命题 18.1（从实际等距分支到量子仪器）

<a id="prop-c93-instrument-reconstruction"></a>

若前稿的实际完整过程给出复线性等距
$V:H\to\bigoplus_e(W_e\otimes\mathbb C^{r_e})$，
其中 $\alpha$ 标记结果 $e$ 的内部细记录，
令相应分支为 $M_{e\alpha}:H\to W_e$，则

$$
\sum_{e,\alpha}M_{e\alpha}^\dagger M_{e\alpha}=I.
$$

同根平方强度标定给

$$
E_e=\sum_\alpha M_{e\alpha}^\dagger M_{e\alpha},\qquad
 p_e(\rho)=\operatorname{Tr}(\rho E_e),\qquad
 \mathcal I_e(\rho)=\sum_\alpha M_{e\alpha}\rho M_{e\alpha}^\dagger.
$$

其中 $\mathcal I_e:\mathcal B(H)\to\mathcal B(W_e)$ 完全正，
$p_e$ 为标量概率且 $\sum_ep_e=1$。
当 $p_e>0$ 时，结果 $e$ 的条件态为 $\mathcal I_e(\rho)/p_e$。
不同结果的输出空间可以不同；保留经典结果时，完整仪器输出为
$\bigoplus_e\mathcal I_e(\rho)$，其总迹为一。

**证明。**
等距性给所有 $x$ 的完整平方范数恒等式
$\sum_{e,\alpha}\|M_{e\alpha}x\|^2=\|x\|^2$，
由极化得到算符恒等式。
对纯态 $\rho=\lvert \psi\rangle\langle \psi\rvert$，分支的同根概率为
$\sum_\alpha\|M_{e\alpha}\psi\|^2=\langle \psi\rvert E_e\lvert \psi\rangle$。
对混合来源使用可加响应，得到迹配对。

任意内部参考 $R$ 与正的联合输入 $T$ 都满足

$$
(\mathcal I_e\otimes\operatorname{id}_R)(T)
 =\sum_\alpha(M_{e\alpha}\otimes I_R)
 T(M_{e\alpha}^\dagger\otimes I_R)\ge0,
$$

故完全正。迹的循环性给
$\operatorname{Tr}\mathcal I_e(\rho)=\operatorname{Tr}(\rho E_e)=p_e$，
总和为一，归一条件态也随之成立。

密度态表示也可直接核对：完整自伴矩阵空间上的实线性归一响应，
由有限维迹内积唯一写作 $W\mapsto\operatorname{Tr}(\rho W)$。
对全部秩一正投影响应非负，迫使 $\rho\ge0$；单位响应为一，迫使 $\operatorname{Tr}\rho=1$。
如果起点只给效果区间上的响应，则沿正倍数延拓、再作正负分解，
使用正性、可加性与同一效果不依赖菜单的条件取得这个实线性泛函。
这些条件在 V80 中已有逐项展开 [8](#ref-v80)。

**白话图景。**一扇完整门保留全部结果记录时，输入与输出使用同一个比较标尺。
把输出按结果分开，同一份分支内容的平方大小给概率，分支本身给后续状态。
因此概率公式和状态更新不是两套互不相关的规定。
保留旁边的内部参考，再检查这个过程，便得到完全正性所表达的组合一致性。

### 18.3 实际时间历史的切向量

有限同维等距矩阵满足 $U^\dagger U=UU^\dagger=I$。
若实际历史 $U(t)$ 为 $C^1$ 并取 $U(0)=I$，
微分 $U(t)U(t)^\dagger=I$ 给
$\dot U U^\dagger$ 反自伴，因此

$$
H(t)=i\hbar\dot U(t)U(t)^\dagger=H(t)^\dagger.
$$

于是 $\psi(t)=U(t)\psi(0)$ 满足

$$
i\hbar\dot\psi=H(t)\psi,\qquad
 \dot\rho=-\frac{i}{\hbar}[H(t),\rho].
$$

这正是有限维薛定谔与 von Neumann 形式。
只有进一步声明一参数自治群，才得到固定生成元。
一扇有限门 $U$ 与某一状态处的切向量不是一一对应：
同一 $U$ 可以有不同的参数化历史；同一状态处的生成元也可因稳定子而不同。
本轮采用的 $\mathcal T_*$ 则是保持当前读数的推断切向空间，
不自动等于某个实际时间向量场。

同一内积还给出不确定关系。对自伴 $A,B$ 与状态 $\rho$，
在 Hilbert–Schmidt 空间对
$(A-\langle A\rangle)\sqrt\rho$ 和
$(B-\langle B\rangle)\sqrt\rho$ 应用 Cauchy–Schwarz，得到

$$
(\Delta A)^2(\Delta B)^2
 \ge|\operatorname{Tr}\rho(A-\langle A\rangle)(B-\langle B\rangle)|^2
 \ge\frac14|\operatorname{Tr}\rho[A,B]|^2.
$$

这项不确定性来自不对易关系；读出纤维里由于资料不足而保留的预测区间，
是另外一项可分别核定的限制。

**白话图景。**当内部历史真的提供一条光滑的可逆门轨迹，它的瞬时变化就有自伴生成元，
薛定谔方程由此出现。当前资料允许怎样改写一个推断代表，则是另一种切向问题。
二者可以放在同一个整体里研究，但要保留各自的参数和作用对象。
这样既能谈轨迹，也能谈我们对轨迹还不知道多少。

<a id="section-19"></a>

## 19. C93 怎样产生 Gibbs 统计形式

<a id="sec-c93-statistical-mechanics"></a>

### 推论 19.1（给定平均能量的规范统计态）

<a id="cor-c93-canonical-gibbs"></a>

设已有实际自伴能量读口 $H$，取 $\tau=I_d/d$，
当前资料只固定归一与平均值 $E=\operatorname{Tr}(\rho H)$。
若 $E$ 位于 $H$ 的最小与最大特征值之间的内部，则 C93 给

$$
\sigma_\beta=\frac{e^{-\beta H}}{Z(\beta)},\qquad
 Z(\beta)=\operatorname{Tr} e^{-\beta H},
$$

其中实参数 $\beta\in\mathbb R$ 由该平均值确定，$H$ 非标量时唯一。
并且

$$
-\frac{d\log Z}{d\beta}=E(\beta),\qquad
 \frac{d^2\log Z}{d\beta^2}=\operatorname{Var}_{\sigma_\beta}(H),\qquad
 S(\sigma_\beta)=\beta E(\beta)+\log Z(\beta).
$$

**证明。**
内部平均值可由全部本征方向都占正权重的概率分布实现，因而 $P_*=I$。
均匀参照把 C93 化为最大熵。
Gibbs 等价定理使 $\log\sigma$ 位于 $\operatorname{span}\{I,H\}$，归一后即得所述形式。
对 $H$ 作谱分解，$Z(\beta)$ 是有限指数和。
两次微分分别给平均值与方差；
对 $\log\sigma_\beta=-\beta H-\log Z$ 取负迹配对给熵式。
若 $H$ 非标量，有限 $\beta$ 处方差严格正，
所以 $dE/d\beta<0$。
当 $\beta$ 分别趋向正、负无穷时，平均值趋向最小、最大特征值，
连续性与严格单调性给内部平均值对应的唯一参数。
端点先约简到相应本征支撑，再使用 C93。

这条结论把统计态的指数形式变成已给平均关系下的唯一规范完成。
将 $\beta$ 标定为 $1/(k_BT)$，以及把这份规范态解释为某个装置的实际热平衡，
仍须相应的温度、热接触及动力学条件。
对多个不对易读口，指数形式仍成立，但响应应使用
式 [(12.4)](#eq-c93-bkm-covariance) 的 BKM 形式，不能直接把每项都换成普通经典协方差。

**白话图景。**只知道平均能量时，允许的整体有很多。
把当前资料没有区分的正反方向放到信息平衡点，唯一代表自然成为 Gibbs 形式。
平均值怎样随它的对偶参数变化，由方差精确控制。
实际温度与能量单位需要由内部装置和标尺接上，指数形式本身先由关系约束得到。

<a id="section-20"></a>

## 20. 为什么采用相对熵：一个不可省略的反向比较

<a id="sec-c93-metric-choice"></a>

本轮将 C93 写成定义间的平衡约束，并没有证明
“所有概念都内生”这一句话唯一决定相对熵。
为使这一点可直接检查，考虑同一份三维经典读数。

### 命题 20.1（两种内部差异尺度可以选出不同的代表）

<a id="prop-c93-metric-not-forced"></a>

取 $\tau=I_3/3$、$A=\operatorname{diag}(-1,0,1)$，固定
$\operatorname{Tr}(\rho A)=1/2$。
最小化平方 Hilbert–Schmidt 差异
$\operatorname{Tr}(\rho-\tau)^2$，得到

$$
\rho_{\rm HS}=\operatorname{diag}\left(\frac1{12},\frac13,\frac7{12}\right).
$$

它不满足 C93；最小相对熵代表则为

$$
\rho_*=
 \operatorname{diag}\left(
 \frac{5-\sqrt{13}}{12},\quad
 \frac{\sqrt{13}-2}{6},\quad
 \frac{11-\sqrt{13}}{12}\right).
$$

两个状态都合法，都具有相同的当前读数。

**证明。**
对 $A$ 的本征基，任一非零非对角项只会增加平方 Hilbert–Schmidt 代价，
却不改变约束，所以其最优态是对角的。
写 $p_- =x$、$p_+=x+1/2$、$p_0=1/2-2x$。
对这个严格凸二次函数微分，得到唯一极小 $x=1/12$，三项均为正。

同一纤维的对角不可见切向为 $X=\operatorname{diag}(1,-2,1)$。
由于均匀参照的对数为标量，C93 要求

$$
0=\operatorname{Tr}(X\log\rho)=\log\frac{p_-p_+}{p_0^2}.
$$

在 $\rho_{\rm HS}$ 处，该比值为 $7/16$，不等于一，故 C93 失败。
解 $x(x+1/2)=(1/2-2x)^2$，
得到 $3x^2-\tfrac52x+\tfrac14=0$。
唯一落在 $0\le x\le1/4$ 内的根为 $(5-\sqrt{13})/12$，
给出上式。其对数属于 $\operatorname{span}\{I,A\}$，
由 C93 主定理，它就是整个量子纤维的唯一相对熵代表，
而不只是对角子集里的极小点。

这项反例并不否定任何一个状态的量子资格。
它准确显示：选择何种内部比较，是规范推断的一个实质条件。
本轮沿用项目已有相对熵的组合加性、信息投影及恢复接口，
再证明其平衡、勾股、Gibbs 与 BKM 结构相互一致。
若要进一步证明相对熵由更弱的组合、粗粒化与局部规则唯一刻画，
需要给出那组规则及相应唯一性定理；本文不把它写成已经完成的结论。

**白话图景。**两套都在整体内部定义的比较方法，仍可能对同一份资料选出不同代表。
因此“内生”保证比较对象没有跳到整体外面，却不会自动替我们决定用哪一种比较。
本轮明确采用相对熵，并证明选它以后，平衡、指数态、精确分解与响应几何连成一套。
这个选择的后果可以逐项检验，不能靠改名让它消失。

<a id="section-21"></a>

## 21. 关系场与近期量子场研究：可以接在哪里

<a id="sec-c93-qft-interface"></a>

在固定支撑的资料域相对内部，$m\mapsto\sigma(m)$ 是一族规范整体，
$\psi(\theta)$ 是关系势，$\chi=\partial m/\partial\theta$ 给读出对关系势参数的一阶响应，
$\partial\chi$ 再给响应的变化。
这些导数都在同一套已声明读口与相对熵比较中定义，
因此可以递归研究“关系怎样改变关系”。
本轮把这种可计算的结构称为*量子推断的关系场*。
它的底空间是资料域，而非已经推导出的物理时空；
其 Hessian 正性也不自动给出物理场方程。

与这一接口直接相邻的近期论文，是 Rupak Chatterjee 的
*Modular self-duality, symmetrized relative entropy, and
Bogoliubov–Kubo–Mori susceptibility in quantum field theory*，
发表于 2026 年 9 月 14 日的 *Physical Review D* 114, 065016
 [15](#ref-chatterjee2026)。
其出版页摘要讨论模反射、自对偶处的对称相对熵及 BKM 易感性，
并以算符代数和 Araki 相对熵推进到 III 型局部代数。
本轮核读范围为出版页、摘要和版本元数据；不据此认证其全部证明。

双方共同出现的是“相对熵的二阶结构给出响应尺度”。
本文的相容纤维信息投影，与该文的模反射自对偶有不同的定义和前件。
后者不是 C93 的直接证明，C93 也没有导出后者的全部 QFT 结论。
若继续推广本轮，下一项明确任务是：
在一般算符代数中重写资料纤维、支撑及信息投影，
检查存在性、可微性、拓扑连续性和物理局域性分别需要什么。
有限维矩阵中的 $\operatorname{Tr}\rho\log\rho$ 不能直接代替所有无限维局部场论对象。

**白话图景。**这轮得到了一张由读数组织起来的关系图：读数决定规范整体，
读数的变化决定响应，响应的变化还可以继续研究。
它与现代量子信息几何、量子场论中的相对熵响应确有精确接口。
但要成为物理场论，还要让这些关系落在实际时空、局域操作和动力学上，
逐项证明，而不是只因同样出现“场”或“曲率”就合并。

<a id="section-22"></a>

## 22. 完整反向审计：删去一个条件，具体坏在哪里

<a id="sec-c93-reverse-audit"></a>

| 删去或混淆的条件 | 受影响的两个对象及明确后果 | 所属更大结构 |
|---|---|---|
| 共同谱界 C92 | 同一读口与其补不能同时给合法概率；全态纤维可能为空 | 正归一泛函与有限整体延拓。 |
| 压缩后的再检查 | 原始正零关系只排除第一方向，却漏掉压缩后才显露的第三方向 | 半定锥的面与有限支撑递归。 |
| 对数与压缩的次序 | $P\log\tau P$ 与 $\log(P\tau P)$ 选择不同规范代表 | 非对易函数演算及压缩指数族。 |
| C93 正反平衡 | $\sigma+\varepsilon X$、$\sigma-\varepsilon X$ 同读数，但有非零一阶偏置 | 纤维与指数族的迹正交、信息投影。 |
| 规范与实际的区别 | Bell 态与最大混态局部相同，强制最大熵会删去合法实际关联 | 全态纤维、推断代表及来源识别。 |
| 支撑变化的检查 | 圆周唯一纯态极限与端点最大熵态相差迹距离 $1/2$ | 分层状态空间与推断连续性。 |
| 内部参考的过程检查 | 补全映射单独保正，作用在 Bell 输入一端却给出 $-1/4$ 负方向 | 完全正性与可实现量子仪器。 |
| 比较规则的明确声明 | 同一三维资料的 HS 代表与相对熵代表不同 | 推断原则的选择及其唯一性问题。 |

这里每个后果都有明确的对象、等式或反例。
对不满足 C93 的态，结论是它不属于所定义的规范代表类；
对不满足 C92 的资料，结论才是它没有共同量子全态。
不同资格的失败不能相互替换。

<a id="section-23"></a>

## 23. 用一段完整白话描述本轮的量子理论

<a id="sec-c93-complete-plain"></a>

**白话图景。**把 $\Omega$ 看作全部内容、比较、记录和变化都在其中的整体。
我们从里面提出有限个问题，得到一份局部记录。
同一份记录可能对应许多个完整量子态，它们共同构成当前还允许的整体集合。
先检查所有合成比较是否能同时成立；不能成立时，一个二元读口就能指出冲突。
能够成立以后，凡是被全部资料判定为零的正方向都必须退出，
它与其他方向的交叉内容也同时退出。删掉以后再看旧关系，可能还有新零方向；
有限次之后，就得到这份资料真正允许的支撑。

在这份支撑里，用一个已经声明的内部参照比较全部候选。
当前记录没有区分的正反变化，在规范代表处不带一阶信息偏向；
这一条平衡要求，唯一选出一个 Gibbs 形式的代表。
任何实际整体若还带着额外内容，它与参照的差异会精确分成两段：
一段是当前记录已经要求的差异，另一段是它相对规范代表尚未读出的差异。
这不是把未知内容宣布成不存在，而是把已确定与未确定的部分都保留下来。

读数在固定支撑的相容资料域相对内部变化时，规范代表光滑变化，响应的二阶尺度可以呈现椭圆。
但走到支撑改变的边界，原先一条平滑读数轨迹可能突然对应更多整体，
所以只凭旧读数选出的代表可能跳跃；补读遗漏的关系，有时就能把这个跳跃拆开。
一项现在看不见的交叉关系，还可能被下一扇实际门旋转进可见读口。
因此我们保留完整预测区间，直到新增资料足以把它缩成一个值。

实际门、测量概率和可逆轨迹由此前的共同正比较、完整分支及内部参考约束接上：
状态成为正归一矩阵，结果概率来自同一分支的平方强度，
带参考的合法过程成为完全正映射，光滑可逆历史成为酉演化和薛定谔形式。
本轮再把局部资料、规范推断、隐藏关联与未来预测连成一套。
所有对象都在 $\Omega$ 内部，但每条关系为何成立，仍由它的定义、前件和证明负责。

本稿的“完整”指：在声明的有限复量子接口下，
存在性、支撑、规范代表、读出、过程、组合、动态预测及其反向失败见证构成闭合理论。
这一范围没有宣称从零前件导出复数、任意物理哈密顿量、时空、基本常数或统一场方程。
本轮 C93 的正式新增内容是规范推断的关系约束；
其数学效果和适用边界均已给出定义、定理、证明与明确反例。

<a id="references"></a>

## 来源、版本与核读范围

<a id="ref-currentrepo"></a>

### [1]

the-omega-institute，*trureturing* 项目。
[公开仓库首页](https://github.com/the-omega-institute/trureturing)。
本轮在 2026 年 11 月 3 日（新加坡）读取当前公开页面：默认分支显示为
`dev`，首页明确链接局部边际相关盲区的源码与说明。
页面未供应可固定的最新提交 SHA，API 读取未成功，
故不把实时公开内容与先前固定提交混记为同一版本。

<a id="ref-blindspot"></a>

### [2]

trureturing 项目，*LocalMarginalCorrelationBlindSpot*。
[当前 Lean 源码](https://github.com/the-omega-institute/trureturing/blob/dev/D5/S3/Quantum/Entanglement/LocalMarginalCorrelationBlindSpot.lean)；
[当前 Blueprint 说明](https://github.com/the-omega-institute/trureturing/blob/dev/Blueprint/D5/S3/Quantum/Entanglement/LocalMarginalCorrelationBlindSpot.md)。
本轮核读局部扇区与相关扇区分解、联合关联不由单点边际决定的声明，
以及 Bell 态与经典混合态的相关读数例子。
只读源码及说明，没有在本轮执行 Lean 构建或核验全部仓库。

<a id="ref-v17"></a>

### [3]

trureturing 项目，V17：*加乘电路、对数与量子勾股：AURIC 五模式的三角几何与黄金门*。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/7878c7ff9b75b9cb49dd84f440e15fd65f2dc665/docs/develop/theory/AURIC_SUM_PRODUCT_LOGARITHMS_AND_QUANTUM_PYTHAGOREAN_GEOMETRY_V17.md)。
本轮核读第 5 节的唯一最大熵完成、KL 勾股，
以及第 10 节的量子熵差与相干分解。
固定提交为 `7878c7ff9b75b9cb49dd84f440e15fd65f2dc665`。
本轮一般纤维推导不将这些已有项目结论重新宣称为首次出现。

<a id="ref-v42"></a>

### [4]

trureturing 项目，V42：*AURIC：$F[13]$ 的关系语义——量子三轴与递归相容性*。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/7878c7ff9b75b9cb49dd84f440e15fd65f2dc665/docs/develop/theory/AURIC_F13_RELATIONAL_SEMANTICS_QUANTUM_THREE_AXES_AND_RECURSIVE_COMPATIBILITY_V42.md)。
本轮核读第 4 节、定理 4.2：最大熵代表、遗漏内容及标量 minimax 中心的区别。
本轮的两 qubit 例子用于直接展示已有区分，并非把该区分记为 v93 首创。

<a id="ref-atlas"></a>

### [5]

trureturing 项目，
*Quantum Origin: Endogenous Cut Atlas and Discrete Reconstruction Boundaries III*。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_III.md)。
本轮核读第 10 节的预测纤维宽度、范数对偶，以及相邻动态自治接口。
本文将这个已有框架细化到一份给定资料及其最小共同支撑。
固定提交为 `c63ab162315fddd0801cbe9f47dbf3eda6e13360`，
相应快照日期为 2026 年 11 月 2 日。

<a id="ref-v78"></a>

### [6]

trureturing 项目，V78 continuation：*二元失败见证与整体量子关系*。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/9bf2db5e96b1e6b9c96fdf9665ff9ec3ae0cf252/docs/develop/theory/AURIC_BINARY_FAILURE_WITNESSES_AND_GLOBAL_QUANTUM_RELATIONS_V78_CONTINUATION.md)。
继承二元正性失败见证及内部参考检查；
本轮 C93 的球内偏置与 C92 的球外不相容报告有不同含义。

<a id="ref-v79"></a>

### [7]

trureturing 项目，V79：*二元反向相容、有限相位证书与量子读出重构*。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_BINARY_REVERSAL_COMPATIBILITY_FINITE_PHASE_CERTIFICATES_AND_QUANTUM_READOUT_RECONSTRUCTION_V79.md)。
沿用已声明的共同正比较、共同复方向、有限相干截口及同根概率标定，
不将这些继承前件改说成由 C93 单独产生。

<a id="ref-v80"></a>

### [8]

trureturing 项目，V80：*全结果二元差分不增、有限有向锚与内生量子过程*。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_ALL_OUTCOME_BINARY_DIFFERENCE_NONEXPANSION_FINITE_ORIENTED_ANCHORS_AND_ENDOGENOUS_QUANTUM_PROCESSES_V80.md)。
本轮复核第 5 节实际输出等距刚性、第 9–13 节的状态、仪器、复合、理想更新及时间历史，
并核读第 16 节的有限量子理论重构表与内生性边界。
本稿的量子力学衔接保留这些结论各自的前件。

<a id="ref-v90"></a>

### [9]

本对话研究稿，*AURIC v90：二元内生中点、平方可恢复性与共享量子结构*，2026。
沿用共同参考、恢复及内部组合的已有接口。
本轮 BKM 形式用于相对熵的二阶响应，不能与前稿承担恢复任务的比较尺度混同。

<a id="ref-v91"></a>

### [10]

本对话研究稿，*AURIC v91：重叠二元关系、三轴提升与量子 Markov 拼接*，2026。
沿用 C91、Markov 补全、有限非空纤维唯一最大熵、
反对易 $K,L,M$ 三轴关系及 $\omega_0=(I+aK+bL)/8$ 的最大熵补全。
本轮新增该例的完整未来读数区间及相对熵响应尺度，不重算原有球与最大熵结论。

<a id="ref-v92"></a>

### [11]

本对话研究稿，*AURIC v92：二元谱界相容、整体量子延拓与椭圆关系*，2026。
本轮直接接续 C92 的全部合成谱界与共同全态存在性，
以其凸分离证明作为一般有限读出资料纤维及未来读数谱对偶的入口。

<a id="ref-facial2017"></a>

### [12]

Dmitriy Drusvyatskiy and Henry Wolkowicz,
*The Many Faces of Degeneracy in Conic Optimization*,
Foundations and Trends in Optimization **3**(2), 77–170 (2017).
[doi:10.1561/2400000011](https://doi.org/10.1561/2400000011)；
[作者公开稿](https://sites.math.washington.edu/~ddrusv/asurveyFR.pdf)。
本轮核读作者稿关于严格可行性替代条件与 facial reduction 的分离和递归机制；
所用作者稿封面日期为 2017 年 5 月 9 日，正式刊载信息另据出版页核对。
正文给出适用于当前读出空间的自足有限证明，未运行数值约简程序。

<a id="ref-weis2014"></a>

### [13]

Stephan Weis, *Information topologies on non-commutative state spaces*,
Journal of Convex Analysis **21**(2), 339–399 (2014).
[arXiv 记录](https://arxiv.org/abs/1003.5671)；
[作者全文](https://arxiv.org/pdf/1003.5671)。
本轮核读关于压缩指数族、Pythagorean 与投影定理的相关段落，
包括 Theorem 6.12；本文的有限矩阵证明自足列出。
相对熵投影、Gibbs 与勾股本身均为已有数学结构。

<a id="ref-weis2015"></a>

### [14]

Stephan Weis, *The MaxEnt extension of a quantum Gibbs family, convex geometry and geodesics*,
AIP Conference Proceedings **1641**, 173–180 (2015).
[doi:10.1063/1.4905976](https://doi.org/10.1063/1.4905976)；
[arXiv 记录](https://arxiv.org/abs/1411.0015)；
[全文](https://arxiv.org/pdf/1411.0015)。
本轮核读 Type II 圆盘例、MaxEnt extension 及边界不连续性的论证。
第 [17](#sec-c93-boundary-continuity) 节的两读数例是该例的酉换基形式，
随后补读 $Q$ 的闭式连续完成和非 CP 检查由本文逐式证明。

<a id="ref-chatterjee2026"></a>

### [15]

Rupak Chatterjee,
*Modular self-duality, symmetrized relative entropy, and
Bogoliubov–Kubo–Mori susceptibility in quantum field theory*,
Physical Review D **114**, 065016, 14 September 2026.
[doi:10.1103/vxkq-xb7l](https://doi.org/10.1103/vxkq-xb7l)；
[出版页与摘要](https://journals.aps.org/prd/abstract/10.1103/vxkq-xb7l)；
[预印本版本记录](https://arxiv.org/abs/2605.19106)。
本轮只用已核读摘要中的对称相对熵、BKM Hessian 与 III 型代数接口作为近期背景。
没有把模反射自对偶与本文纤维信息投影视为同一条件，也没有认证整篇场论推导。

**原稿核查记录。**
本稿数学部分均为解析推导与独立解析审阅。
未执行数学程序、CAS、数值求值、枚举、模拟或测试；文档编译与页面渲染仅用于排版检查。
仓库保持只读，本轮未修改、提交或推送任何项目文件。
当前公开页面的观察、固定快照的理论核读与本对话前稿的继承，在来源表中分别注明。

## 24. 两参数含噪纤维的精确泄漏与纯态目标距离

<a id="sec-c93-exact-noisy-qutrit"></a>

### 定义 24.1（两项零读数的独立容差）

沿用第 5 节的 $H=\mathbb C^3$、$P_i=\lvert i\rangle\langle i\rvert$ 及

$$
A=\lvert1\rangle\langle2\rvert+\lvert2\rangle\langle1\rvert+P_3.
$$

对每个 $(a,b)\in[0,1]^2$，定义

$$
\mathcal F(a,b)=\left\{\rho\in M_3(\mathbb C):
\rho=\rho^*,\quad \rho\succeq0,\quad \operatorname{Tr}\rho=1,\quad
\rho_{11}\le a,\quad |\operatorname{Tr}(\rho A)|\le b\right\}.
\tag{24.1}
$$

这里包括全部复 Hermitian 态，不限制相位、秩或其余矩阵元。
相对于零资料的唯一态 $P_2$，定义支撑外权重及固定目标的最大偏差

$$
\begin{aligned}
q(\rho)&=\operatorname{Tr}\bigl(\rho(I-P_2)\bigr)=1-\rho_{22},\\
q_*(a,b)&=\max_{\rho\in\mathcal F(a,b)}q(\rho),\\
R_*(a,b)&=\max_{\rho\in\mathcal F(a,b)}\|\rho-P_2\|_1,
\qquad \|X\|_1=\operatorname{Tr}\sqrt{X^*X}.
\end{aligned}
\tag{24.2}
$$

$P_2\in\mathcal F(a,b)$，且该纤维是密度矩阵紧集的闭子集，故两个最大值均存在。
$R_*$ 使用完整迹范数；通常的半迹距离最大值为 $R_*/2$。
这里的参照固定为 $P_2$，并非纤维直径或允许改变中心的最小包围半径。

### 定理 24.2（全复纤维的精确极值与同时达到）

对所有 $(a,b)\in[0,1]^2$，令 $t_+=\max\{t,0\}$，则

$$
\boxed{\begin{aligned}
q_*(a,b)&=1-\bigl(\sqrt{1-b}-\sqrt a\bigr)_+^2,\\
R_*(a,b)&=2\sqrt{q_*(a,b)}.
\end{aligned}}
\tag{24.3}
$$

更具体地，令

$$
m=\min\{a,1-b\},\qquad
s=\sqrt{1-b}-\sqrt m,\qquad
w=b+2\sqrt m\,s.
\tag{24.4}
$$

同一个可行纯态

$$
\begin{aligned}
\lvert\psi_{a,b}\rangle
&=\sqrt m\,\lvert1\rangle-s\lvert2\rangle+\sqrt w\,\lvert3\rangle,\\
\rho_{a,b}&=\lvert\psi_{a,b}\rangle\langle\psi_{a,b}\rvert
\end{aligned}
\tag{24.5}
$$

同时满足 $q(\rho_{a,b})=q_*(a,b)$ 与
$\|\rho_{a,b}-P_2\|_1=R_*(a,b)$。
这些公式在全部边界上成立，特别是

$$
\begin{aligned}
q_*(0,b)&=b,&R_*(0,b)&=2\sqrt b,\\
q_*(a,0)&=2\sqrt a-a,&R_*(a,0)&=2\sqrt{2\sqrt a-a},\\
a+b\ge1&\ \Longrightarrow\ q_*(a,b)=1,
& R_*(a,b)&=2.
\end{aligned}
\tag{24.6}
$$

在 $(a,b)=(0,0)$，纤维恰为 $\{P_2\}$，两个最大值都为零。

证明。先取任意 $\rho\in\mathcal F(a,b)$，记
$x=\rho_{11}$、$y=\rho_{22}$、$z=\rho_{33}$ 及 $c=\rho_{12}$。
正性给 $x,y,z\ge0$、$x+y+z=1$，并由 $\{1,2\}$ 主块得到
$|c|^2\le xy$。由于 $\rho$ 为 Hermitian，

$$
\operatorname{Tr}(\rho A)=z+2\operatorname{Re}c.
$$

从 $z+2\operatorname{Re}c\le b$ 及
$-\operatorname{Re}c\le|c|\le\sqrt{xy}$ 得

$$
\begin{aligned}
z&\le b+2\sqrt{xy},\\
1-b&\le x+y+2\sqrt{xy}=(\sqrt x+\sqrt y)^2,\\
\sqrt y&\ge\bigl(\sqrt{1-b}-\sqrt a\bigr)_+.
\end{aligned}
\tag{24.7}
$$

最后一步使用 $x\le a$ 及 $\sqrt y\ge0$。
这给出式 (24.3) 中 $q_*$ 的上界；推导没有令 $c$ 为实数，也没有消去其余复矩阵元。

对式 (24.4)，有 $m,s,w\ge0$，且

$$
\begin{aligned}
m+s^2+w&=(\sqrt m+s)^2+b=1,\\
s&=\bigl(\sqrt{1-b}-\sqrt a\bigr)_+.
\end{aligned}
\tag{24.8}
$$

故式 (24.5) 的向量归一，其投影为半正定迹一矩阵，并满足

$$
(\rho_{a,b})_{11}=m\le a,\qquad
\operatorname{Tr}(\rho_{a,b}A)=w-2\sqrt m\,s=b,\qquad
(\rho_{a,b})_{22}=s^2.
\tag{24.9}
$$

于是 $\rho_{a,b}\in\mathcal F(a,b)$ 并达到 $q_*$ 的上界。
尤其当 $a+b\ge1$ 时，$s=0$、$m=1-b$、$w=b$，
达到态仍由同一公式给出；在分界 $a+b=1$ 无需取极限或另选不可兼容的极值态。

对距离上界，使用 Fuchs--van de Graaf 的既有不等式
[16](#ref-fuchs-vandegraaf)（Theorem 1，式 (46)）。
以根保真度 $B(\rho,\sigma)=\operatorname{Tr}\sqrt{\sqrt\rho\,\sigma\sqrt\rho}$ 记，
该不等式的右半边为
$\frac12\|\rho-\sigma\|_1\le\sqrt{1-B(\rho,\sigma)^2}$。
对纯态目标 $\sigma=P_2$，有 $B(\rho,P_2)^2=\rho_{22}$，从而对每个可行态

$$
\|\rho-P_2\|_1\le2\sqrt{1-\rho_{22}}
\le2\sqrt{q_*(a,b)}.
\tag{24.10}
$$

验证同一态的等号。记 $q=1-s^2=m+w$。
若 $q>0$，取与 $\lvert2\rangle$ 正交的单位向量

$$
\lvert v\rangle=\frac{\sqrt m\,\lvert1\rangle+\sqrt w\,\lvert3\rangle}{\sqrt q}.
$$

$\rho_{a,b}-P_2$ 在有序正交基 $(\lvert2\rangle,\lvert v\rangle)$ 上的矩阵为

$$
\begin{pmatrix}
-q&-s\sqrt q\\
-s\sqrt q&q
\end{pmatrix},
\tag{24.11}
$$

并在其正交补上为零。
该矩阵迹为零、行列式为 $-q(q+s^2)=-q$，故特征值为 $\sqrt q,-\sqrt q$。
于是 $\|\rho_{a,b}-P_2\|_1=2\sqrt q$，达到式 (24.10) 的上界。
若 $q=0$，则 $s=1$、$m=w=0$，直接有 $\rho_{a,b}=P_2$，等号仍成立。

最后，将 $a=0$、$b=0$ 或 $a+b\ge1$ 代入式 (24.3) 得式 (24.6)。
当 $a=b=0$ 时，式 (24.7) 迫使 $y=1$，其余对角元为零，
正性又迫使其余行列为零，故整个纤维仅有 $P_2$。∎

### 推论 24.3（等容差的完整曲线与四次根尺度）

令 $a=b=\varepsilon\in[0,1]$。则

$$
q_*(\varepsilon,\varepsilon)=
\begin{cases}
2\sqrt{\varepsilon(1-\varepsilon)},&0\le\varepsilon\le\frac12,\\
1,&\frac12\le\varepsilon\le1,
\end{cases}
\qquad
R_*(\varepsilon,\varepsilon)=
\begin{cases}
2\sqrt2\,[\varepsilon(1-\varepsilon)]^{1/4},&0\le\varepsilon\le\frac12,\\
2,&\frac12\le\varepsilon\le1.
\end{cases}
\tag{24.12}
$$

特别地，

$$
\lim_{\varepsilon\downarrow0}
\frac{R_*(\varepsilon,\varepsilon)}{\varepsilon^{1/4}}=2\sqrt2.
\tag{24.13}
$$

因此，对每个 $\alpha>1/4$、每个有限 $C\ge0$ 及每个 $\delta>0$，
都存在 $0<\varepsilon<\min\{\delta,1/2\}$ 使
$R_*(\varepsilon,\varepsilon)>C\varepsilon^\alpha$。

证明。当 $\varepsilon\le1/2$ 时，
$(\sqrt{1-\varepsilon}-\sqrt\varepsilon)_+^2
=1-2\sqrt{\varepsilon(1-\varepsilon)}$；
当 $\varepsilon\ge1/2$ 时，正部为零。
定理 24.2 随即给出式 (24.12)，同一 $\rho_{\varepsilon,\varepsilon}$ 达到两个极值，
包括 $\varepsilon=0$ 与 $\varepsilon=1/2$。
由式 (24.12) 除以 $\varepsilon^{1/4}$ 得式 (24.13)；
对 $\alpha>1/4$ 再除以 $\varepsilon^{\alpha-1/4}$，所得比值趋于无穷，给出最后的量词结论。
面约简的一般 Hölder 指数及其尖锐性是既有结果
[12](#ref-facial2017)（Theorem 4.5.1、Example 4.5.1）；
式 (24.12) 给出式 (24.1) 的复迹一纤维在独立容差相等时的精确值与达到态。∎

<a id="ref-fuchs-vandegraaf"></a>

### [16]

Christopher A. Fuchs and Jeroen van de Graaf,
*Cryptographic Distinguishability Measures for Quantum Mechanical States*，
[原文](https://arxiv.org/pdf/quant-ph/9712042)。
Theorem 1，式 (46) 给出完整迹范数的一半与根保真度的上下界；
式 (24.10) 使用其纯态目标特例。

## 追加锚（本行以下为增补区）
