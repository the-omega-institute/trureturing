# 二元谱界相容、整体量子延拓与椭圆关系

从局部读出到共同正归一态、精确修复与可数整体

**AURIC v92：一个完整候选的定义、定理与反向审计**

项目连续研究稿

2026 年 11 月 3 日（新加坡）

## 摘要

v91 给出重叠边际的规范 Markov 拼接，并用闭环反例说明局部窗口可以全部通过，
整体仍不存在。v92 转向更一般的问题：在不预设共同全态、不强加 Markov 结构时，
怎样从全部局部读出本身判定是否存在一个共同量子实现？

本轮唯一候选 C92 要求：任意局部自伴关系的合成读数，不超过合成算符的最大谱值。
负号同时给下界，零算符同时给表达身份一致；局部归一与正性也由同一条件推出。
通过有限维最近点分离，证明 C92 当且仅当全部资料具有共同密度态延拓。
随后将该条件改写成合成二元效果菜单，证明最大读出超额精确等于最小加权边际迹距离。

有限三维报告复用项目 V78 的二元球机制，但对象从已给全态转为尚待拼接的局部资料。
经典三角环和量子双 Bell 关系给出完整解析见证、精确误差与共同噪声阈值。
两项 Bell 关系在有效二维块中成为夹角 $120^\circ$ 的读出轴，
其关系球的投影给出精确椭圆，并完整刻画两个 isotropic 边际的兼容域。

进一步以单点边际的内部乘积参照定义序半径，统一不兼容、边界与忠实补全三种情形，
证明最小噪声及阈值支撑。任意奇环说明固定大小局部窗口不完备；
全部有限资料通过 C92 则经对角紧性给出相容的可数局部态族，接入 $C^*$ 态与 GNS 表示。
一般兼容见证、椭圆兼容域和 GNS 均有既有文献来源；本稿的新角色是项目中的条件组织与接续。
全文为解析证明，未运行数学程序、CAS、数值求值、枚举或测试。

## 目录

- [1. 接续位置：从可 Markov 拼接到任意共同量子实现](#section-1)
- [2. 同一合成关系的两种定义：唯一候选 C92](#section-2)
- [3. 一个谱区间条件怎样同时锁定归一、正性与地址一致](#section-3)
- [4. 完整扩张定理：通过全部二元见证，恰好存在同一个全态](#section-4)
- [5. 固定二元读出菜单：同一候选的有界形式](#section-5)
- [6. 操作距离的精确对偶：缺额就是最少需要改动的局部读数](#section-6)
- [7. 每个失败怎样压成一个二元读出](#section-7)
- [8. 二元效果的一量子比特实现，以及第三坐标从哪里来](#section-8)
- [9. 三角形闭环：精确可行区间、球外点与最小修复](#section-9)
- [10. 两份 Bell 关系：精确共享阈值与最小修复](#section-10)
- [11. 两条非正交读出怎样把球投影成椭圆](#section-11)
- [12. 内部参照怎样统一不兼容、边界与忠实补全](#section-12)
- [13. 最少撤去多少相关，才能重新成为共同整体](#section-13)
- [14. 有限窗口为何不能代替整圈：任意奇环的严格正反例](#section-14)
- [15. 奇环的精确噪声阈值与共同零支撑](#section-15)
- [16. 所有有限资料都相容，怎样得到同一个可数整体](#section-16)
- [17. 由整体正响应到 Hilbert 关系核：GNS 的完整接口](#section-17)
- [18. 同一相容条件怎样成为量子通道与不可克隆的约束](#section-18)
- [19. 如何接回现有量子力学：完整链条与每一步的前件](#section-19)
- [20. 反向审计：撤去哪里，就在哪一对关系上失败](#section-20)
- [21. 与当前量子研究的接点及本轮完成的范围](#section-21)
- [来源、版本与核读范围](#references)

<a id="section-1"></a>

## 1. 接续位置：从可 Markov 拼接到任意共同量子实现

<a id="sec-c92-position"></a>

版本由 v91 递增到 v92。当前 GitHub HEAD 的有界公开读取未成功；本轮不宣称已经取得最新提交。
可核对基线仍为 $\texttt{c63ab162315f\ldots}$，并对需要的早期 V77、V78 文本
使用已取得的固定提交 $\texttt{9bf2db5e96b1\ldots}$。
正文及来源表按文件实际版本引用，不把不同快照混成一份已核定的当前仓库。

项目 V77 已将完整正性改写为合成二元 Gram 关系，V78 后续稿 §6.1 已证明：
一个 Hermitian 迹一候选的负方向，可以在二元报告中表现为 Bloch 球外点 [6](#ref-v77)、[7](#ref-v78)。
Atlas III 已给当前读出空间的纤维宽度与范数距离对偶 [8](#ref-atlas)。
$\Omega$ 静态主稿 §12 则从一族*已经精确相容*的局部正归一态出发，构造无限态与 GNS 表示 [9](#ref-omega)。

v91 处理的是两份边际是否存在规范 Markov 补全；它不把所有合法量子态都限制成 Markov 态。
该轮严格正的三角环反例留下一个明确缺口：每个两边窗口都可拼，全部边际却没有共同全态 [13](#ref-v91)。
本轮要补的是**还没有共同全态时，局部读出是否允许任何共同正归一态延拓**。

标准数学中，这属于量子边际问题的兼容见证与凸对偶。
Hall 的 Theorem 4、Proposition 3 已给其基础框架 [1](#ref-hall2007)。
本稿给出任意有限 patch 族的自足证明，并将它接到二元球、内部尺度、
精确椭圆及可数相容极限；不把已有基础数学重新认作物理新发现。

**白话图景。**上一轮问的是：两边能不能仅靠共享部分，按一种特定方式完整接起来。
这一轮先放开接法，允许整体保留额外量子关联，再问更基本的问题：
这些局部说法究竟能不能同时属于任何一个整体？
如果不能，必须指出一项具体的二元读出，说明矛盾落在哪里。

<a id="section-2"></a>

## 2. 同一合成关系的两种定义：唯一候选 C92

<a id="sec-c92-definition"></a>

### 定义 2.1（有限局部读出资料）

给定有限非空节点集 $V$，每个节点有非零有限维复载体 $\mathcal H_i$，
并沿用此前已声明的组合接口

$$
\mathcal H=\bigotimes_{i\in V}\mathcal H_i.
$$

取覆盖 $V$ 的非空有限 patch 族 $\mathscr C$，每个 $C\in\mathscr C$ 为非空子集。
局部资料是 Hermitian 表 $R_C\in\operatorname{Herm}(\mathcal H_C)$，表示实线性响应
$h_C\mapsto\operatorname{Tr}(R_Ch_C)$。暂不假定 $R_C$ 为正或迹一。
记 $\iota_C(h_C)=h_C\otimes I_{C^c}$，按节点次序嵌入整个载体。

取 Hermitian 表只是有限实线性读出的迹对偶表示，并未预先断言这些表已经是量子态。
共同复代数、伴随及张量嵌入是前序重构接口；本轮不把它们藏进“内生”一词。
也未假定存在与这些资料匹配的全态。

### 定义 2.2（合成算符与合成响应）

对任意局部 Hermitian 族 $h=(h_C)_{C\in\mathscr C}$，定义

<a id="eq-c92-composite"></a>

$$
W(h)=\sum_{C\in\mathscr C}\iota_C(h_C),\qquad
 b_R(h)=\sum_{C\in\mathscr C}\operatorname{Tr}(R_Ch_C).
\tag{2.1}
$$

$W(h)$ 是把局部关系放进共同载体后得到的同一个算符内容；
$b_R(h)$ 是从已给局部资料汇总出的同一关系的响应。
两者有各自独立的定义，因此可以检查是否相容。

### 定义 2.3（本轮唯一候选：内生谱界相容）

<a id="def-c92"></a>

一组局部读出资料可声明为同一量子整体的资料，当且仅当满足

<a id="eq-c92"></a>

$$
\boxed{\qquad
 b_R(h)\le\lambda_{\max}(W(h))
 \quad\text{对全部有限局部 Hermitian 族 }h.
 \qquad}
 \tag{C92}
$$

对 $-h$ 使用同一条件，自动得到

$$
\lambda_{\min}(W(h))\le b_R(h)\le\lambda_{\max}(W(h)).
$$

这不是另加一个公理，只是同一个条件在相反关系上的应用。
当 $W(h)=0$ 时，区间退化为 $\{0\}$，因此必须有 $b_R(h)=0$。
两种局部表达只要代表同一个算符内容，就必须给同一响应，
从而“内容即地址”的线性身份一致性将由 C92 推出。

本轮的二元对象可以明确取为

$$
F,\qquad I-F,
$$

其中 $F$ 是由某个合成关系的谱区间归一得到的效果。
若资料违反 C92，这两个互补结果中会出现推断的负值或大于一的值。
后文证明：任意不兼容都会被某个这样的二元报告检出；
报告只有三个实坐标，不意味着寻找它的整个问题只有三维。

**白话图景。**同一个关系有两种算法：把局部读数加起来，得到一个承诺值；
把局部关系放进同一个载体，得到它实际允许的读数范围。
如果承诺值跑到这个范围之外，就说明这些局部说法不能同时成立。
本轮只要求这两种内部定义相容，并证明这一要求恰好足以保证共同整体存在。

<a id="section-3"></a>

## 3. 一个谱区间条件怎样同时锁定归一、正性与地址一致

<a id="sec-c92-local-consequences"></a>

沿用唯一候选 [(C92)](#eq-c92)。将有限非空 patch 族记为
$\mathscr C$，总载体为 $\mathcal H$，局部载体为 $\mathcal H_C$。
输入 $R_C$ 此时只假定为 Hermitian 矩阵。
嵌入 $\iota_C(h_C)$ 在未显示因子上补单位；记

$$
W(h)=\sum_{C\in\mathscr C}\iota_C(h_C),
 \qquad b_R(h)=\sum_{C\in\mathscr C}\operatorname{Tr}(R_Ch_C).
$$

本节不再提出第二个公理，而是推导同一个全谱上界的后果。

### 命题 3.1（局部状态资格由 C92 自动给出）

<a id="prop-c92-local-states"></a>

若 C92 成立，则每个输入都满足

$$
R_C\ge0,\qquad \operatorname{Tr} R_C=1.
$$

**证明。**
仅令一个分量为 $h_C=I_C$，其余为零，则 $W=I$，C92 给出
$\operatorname{Tr} R_C\le1$。改取 $h_C=-I_C$，又得 $\operatorname{Tr} R_C\ge1$。
对任意单位向量 $v\in\mathcal H_C$，仅取
$h_C=-\lvert v\rangle\langle v\rvert$，则 $W\le0$，所以

$$
-\langle v\rvert R_C\lvert v\rangle\le\lambda_{\max}(W)\le0.
$$

故所有方向的二次型均非负，即 $R_C\ge0$。
这一论证也覆盖一维局部载体。

### 命题 3.2（零关系、代表无关与重叠一致）

<a id="prop-c92-address-identity"></a>

C92 蕴含：若 $W(h)=W(g)$，则 $b_R(h)=b_R(g)$。
特别地，任意两块在交叠部分的边际相同。

**证明。**
若 $W(k)=0$，对 $k$ 与 $-k$ 分别使用 C92，得到
$b_R(k)\le0$ 与 $-b_R(k)\le0$，故 $b_R(k)=0$。
将 $k=h-g$ 代入，得到代表无关。

若 $D=C\cap C'$，任取 $D$ 上的 Hermitian 算符 $Z$，
在 $C$ 分量使用 $Z\otimes I_{C\setminus D}$，
在 $C'$ 分量使用其负的同一嵌入，其他分量取零。
总算符恒为零，故两边对 $Z$ 的期望相等。
有限矩阵的迹配对非退化，遂有

$$
\operatorname{Tr}_{C\setminus D}R_C
 =\operatorname{Tr}_{C'\setminus D}R_{C'}.
$$

若交集为空，这只重复已经得到的归一条件。

取所有嵌入局部算符的实线性和空间

<a id="eq-c92-operator-system"></a>

$$
\mathcal S=\left\{W(h):h_C\in\operatorname{Herm}(\mathcal H_C)\right\}
 \subseteq\operatorname{Herm}(\mathcal H).
\tag{3.1}
$$

它包含 $I$。一般不对算符乘法封闭，不能直接称为子代数。
其复化 $\mathcal S+i\mathcal S$ 是一个有限维算符系统。
前一命题使

<a id="eq-c92-local-functional"></a>

$$
\ell_R(W(h)):=b_R(h)
\tag{3.2}
$$

成为与局部表达方式无关的实线性泛函。

### 命题 3.3（谱区间条件与归一正泛函等价）

<a id="prop-c92-positive-functional"></a>

C92 等价于以下整项声明：式 [(3.2)](#eq-c92-local-functional) 定义良好，且

$$
\ell_R(I)=1,\qquad
 \ell_R(W)\ge0\quad(W\in\mathcal S,\ W\ge0).
$$

此时对全部 $W\in\mathcal S$ 都有

<a id="eq-c92-two-sided-spectrum"></a>

$$
\lambda_{\min}(W)\le\ell_R(W)\le\lambda_{\max}(W).
\tag{3.3}
$$

**证明。**
在 C92 下，代表无关和归一已经证明。
对 $-h$ 使用同一上界，得到
$\ell_R(W)\ge\lambda_{\min}(W)$；若 $W\ge0$，这就给出正性。
反过来，若该泛函归一且为正，则
$\lambda_{\max}(W)I-W$ 属于 $\mathcal S$ 的正锥，故

$$
0\le\ell_R(\lambda_{\max}(W)I-W)
 =\lambda_{\max}(W)-\ell_R(W).
$$

这正是 C92；对负算符再用一次便得下界。

这里的零关系处理具有实质内容：同一个算符可由不同局部项相加得到，
这些表达可能沿不同重叠路径出现。C92 同时要求它们读出一致，
并要求所有整体正组合具有非负读数。
仅要求每一局部正项的读数非负，不能检查跨块相容；这点在兼容见证研究中已有明确说明
 [1](#ref-hall2007)。

**白话图景。**同一份完整关系可以从不同局部表达拼出来。
如果两种表达相减后什么都没有，读出的差也必须为零；
如果拼出的关系只能给非负读数，局部资料合起来就不能给负数。
这同一个要求，既固定归一，也固定局部正性，还把“同内容同地址”的表达一致锁住。

<a id="section-4"></a>

## 4. 完整扩张定理：通过全部二元见证，恰好存在同一个全态

<a id="sec-c92-extension"></a>

定义有限维实内积空间

$$
\mathfrak V=\bigoplus_{C\in\mathscr C}\operatorname{Herm}(\mathcal H_C),
 \qquad
 \langle h,r\rangle_{\mathfrak V}=\sum_C\operatorname{Tr}(h_Cr_C),
$$

以及边际映射和其迹伴随

<a id="eq-c92-marginal-adjoint"></a>

$$
A(X)=(\operatorname{Tr}_{C^c}X)_{C\in\mathscr C},
 \qquad A^*(h)=W(h).
\tag{4.1}
$$

伴随等式来自部分迹定义：
$\langle h,A(X)\rangle=\operatorname{Tr}(XW(h))$。
令

$$
\mathcal K=A(\mathcal D(\mathcal H)),\qquad
 \mathcal D(\mathcal H)=\{\sigma\ge0:\operatorname{Tr}\sigma=1\}.
$$

$\mathcal D(\mathcal H)$ 非空、紧且凸；有限线性映射连续，故 $\mathcal K$ 也紧且凸。
对任何 $h$，谱分解直接给出它的支撑函数

<a id="eq-c92-support-function"></a>

$$
\max_{k\in\mathcal K}\langle h,k\rangle
 =\max_{\sigma\in\mathcal D(\mathcal H)}\operatorname{Tr}(\sigma W(h))
 =\lambda_{\max}(W(h)).
\tag{4.2}
$$

最后的最大值由最大特征值的一条单位本征向量达到。

### 定理 4.1（有限重叠关系的完整正扩张）

<a id="thm-c92-extension"></a>

对任意有限非空 patch 族与 Hermitian 输入 $R=(R_C)_C$，以下条件等价：

1. 唯一候选 C92 成立；

2. $\ell_R$ 是式 [(3.1)](#eq-c92-operator-system) 上定义良好的归一正泛函；

3. 存在某个全态 $\sigma\in\mathcal D(\mathcal H)$，使
    $A(\sigma)=R$，即全部指定局部读出同时来自它。

原始局部输入与所求全态均不要求满秩；patch 可重叠、分叉或形成闭环。

**证明。**
第一、二项的等价已经证明。
若第三项成立，则

$$
b_R(h)=\operatorname{Tr}(\sigma W(h))\le\lambda_{\max}(W(h)),
$$

所以 C92 必要。

证明充分性时不调用数值算法或严格可行性。
若 $R\notin\mathcal K$，紧性保证存在到 $R$ 的 Hilbert–Schmidt 最近点
$k_*\in\mathcal K$。令 $z=R-k_*\ne0$。
对任意 $k\in\mathcal K$ 和 $0\le t\le1$，凸性给
$k_*+t(k-k_*)\in\mathcal K$。最优性于是给

$$
\left\lVert z-t(k-k_*)\right\rVert_2^2\ge\left\lVert z\right\rVert_2^2.
$$

展开、除以 $t>0$ 后令 $t\downarrow0$，得到

<a id="eq-c92-projection-normal"></a>

$$
\langle z,k-k_*\rangle\le0\quad(k\in\mathcal K).
\tag{4.3}
$$

因此式 [(4.2)](#eq-c92-support-function) 给出
$\lambda_{\max}(W(z))=\langle z,k_*\rangle$，但

$$
b_R(z)-\lambda_{\max}(W(z))
 =\langle z,R-k_*\rangle=\left\lVert z\right\rVert_2^2>0.
$$

这构造了一个违反 C92 的有限见证，矛盾。
故 $R\in\mathcal K$，也就是所需全态存在。

这是有限量子边际问题的凸见证表述。Hall 的兼容集、兼容见证定理及正算符判据
给出相同数学基础 [1](#ref-hall2007)；这里将其用于任意有限 patch 族，
并给出最近点的自足分离证明，不主张这一标准凸对偶的优先权。
本轮新增的项目接口，是把局部归一、零表达关系、闭环矛盾与完整扩张放在同一个条件中。

兼容全态的集合

$$
\mathcal E_R=\{\sigma\in\mathcal D(\mathcal H):A(\sigma)=R\}
$$

可以包含多份全态。若 $\mathcal S=\operatorname{Herm}(\mathcal H)$，全部矩阵读口已被指定，
迹配对保证扩张唯一；若 $\mathcal S$ 较小，唯一性须另外检查，
不能仅由空间维数或 C92 本身宣布。
这也保留了 v91 的边界：一般正扩张存在不要求全态具有 Markov 结构 [13](#ref-v91)。

### 推论 4.2（归一 Hilbert–Schmidt 见证的精确缺额）

<a id="cor-c92-hs-distance"></a>

令 $d_2(R,\mathcal K)=\min_{k\in\mathcal K}\left\lVert R-k\right\rVert_2$，则

<a id="eq-c92-hs-duality"></a>

$$
d_2(R,\mathcal K)
 =\max_{\left\lVert h\right\rVert_2\le1}
 \left[b_R(h)-\lambda_{\max}(W(h))\right].
\tag{4.4}
$$

若距离非零，$h=(R-k_*)/d_2$ 达到最大值；距离为零时 $h=0$ 达到。

**证明。**
对任意 $k\in\mathcal K$ 与 $\left\lVert h\right\rVert_2\le1$，

$$
b_R(h)-\lambda_{\max}(W(h))
 \le\langle h,R-k\rangle\le\left\lVert R-k\right\rVert_2.
$$

取最小值得上界。非零时将式 [(4.3)](#eq-c92-projection-normal) 的
$z$ 归一，恰好得到等号；零距离时各缺额非正，而 $h=0$ 给零。

这是一份有限见证存在定理，不承诺寻找见证所需的资源随系统数多项式增长。
“有限维”也不等于只需预先固定有限条线性不等式：
见证仍可来自连续的局部算符菜单。

**白话图景。**如果局部资料不能来自任何同一个整体，它们到所有合法整体读数之间就有一段距离。
朝着最近合法点的反方向比较，会得到一项明确的组合读口：
局部资料给出的值，超过了任何合法整体能给出的上限。
所以失败必能落到一个具体读口及其补读口，而不只停留在“可能还有全局问题”。

<a id="section-5"></a>

## 5. 固定二元读出菜单：同一候选的有界形式

<a id="sec-c92-binary-menu"></a>

从本节起，局部输入为密度态 $R_C$；它们可先由
命题 [3.1](#prop-c92-local-states) 认证，或由原有准备接口给出。
固定任意正权 $w_C>0$、$\sum_Cw_C=1$，例如对全部 patch 等权。
对每块选择二元效果 $0\le E_C\le I_C$，定义

<a id="eq-c92-binary-mixture"></a>

$$
F(E)=\sum_Cw_C\iota_C(E_C),
 \qquad b_R^w(E)=\sum_Cw_C\operatorname{Tr}(R_CE_C).
\tag{5.1}
$$

由于 $0\le F(E)\le I$，它与 $I-F(E)$ 构成总载体上的二元效果。
这可以理解为内部开关按 $w_C$ 选一个局部测量，最后只读出它的二元结果；
不要求同时测量所有可能不对易的局部效果。

### 命题 5.1（二元菜单与 C92 等价）

<a id="prop-c92-binary-equivalence"></a>

在局部输入为 Hermitian 且逐块满足 $\operatorname{Tr} R_C=1$ 的前提下，C92 等价于

<a id="eq-c92-binary-upper"></a>

$$
b_R^w(E)\le\lambda_{\max}(F(E))
 \quad\text{对全部 }(E_C)_C\in\prod_C[0,I_C].
\tag{5.2}
$$

同一条件也给出下界
$b_R^w(E)\ge\lambda_{\min}(F(E))$。

**证明。**
C92 蕴含式 [(5.2)](#eq-c92-binary-upper)，只需取 $h_C=w_CE_C$。
反过来，给任意 Hermitian 族 $h_C$，选择一个足够大的 $a>0$，使
$\left\lVert h_C\right\rVert_\infty\le aw_C/2$ 对全部 $C$ 成立。
于是

$$
E_C=\frac{h_C}{aw_C}+\frac12I_C\in[0,I_C],
 \qquad
 F(E)=\frac1aW(h)+\frac12I.
$$

由于每个 $R_C$ 迹为一，
$b_R^w(E)=b_R(h)/a+1/2$。
把这两式代入式 [(5.2)](#eq-c92-binary-upper)，便得 C92。
最后把全部 $E_C$ 同时换成 $I_C-E_C$：总效果变成 $I-F$，
读数变成 $1-b_R^w(E)$，上界就变成所需下界。

权重决定怎样量化不同 patch 的误差，但只要全部严格为正，
它不改变零缺额的兼容资格。
归一前件不能在本命题中省略：若所有 $R_C=0$，它们会通过仅对正效果的上界，
却没有概率总量一；C92 对 $h_C=\pm I_C$ 的测试已经排除了这种情况。

**白话图景。**每次只选一块、问一个是或否的问题，也能组织完整的相容检查。
任何组合读口在整体里都有自己的可达范围，局部资料汇总后必须落在这个范围里。
换成补问题就得到另一侧界限。选择各块的频率只改变误差怎样计分，不改变有没有共同整体。

<a id="section-6"></a>

## 6. 操作距离的精确对偶：缺额就是最少需要改动的局部读数

<a id="sec-c92-operational-distance"></a>

定义 $D(\rho,\sigma)=\tfrac12\left\lVert \rho-\sigma\right\rVert_1$，并令

<a id="eq-c92-operational-distance"></a>

$$
\Delta_w(R)
 :=\min_{\sigma\in\mathcal D(\mathcal H)}
       \sum_Cw_C D(R_C,\sigma_C).
\tag{6.1}
$$

它表示：为了让所有局部读数来自同一个全态，最少需要承担多少加权迹距离修正。
有限紧性保证最小值达到。

### 引理 6.1（有限凸集的距离与范数支撑）

<a id="lem-c92-norm-separation"></a>

设 $K$ 是有限维实内积空间中的非空紧凸集，$N$ 是任意范数，
$N^*$ 是其对偶范数。记 $s_K(h)=\max_{k\in K}\langle h,k\rangle$。
则对任意 $r$，

<a id="eq-c92-general-norm-duality"></a>

$$
\min_{k\in K}N(r-k)
 =\max_{N^*(h)\le1}\bigl[\langle h,r\rangle-s_K(h)\bigr].
\tag{6.2}
$$

两边均达到极值。

**证明。**
记左侧为 $d$。对任意允许的 $h$ 与 $k\in K$，

$$
\langle h,r\rangle-s_K(h)
 \le\langle h,r-k\rangle\le N(r-k),
$$

所以右侧不超过 $d$。若 $d=0$，取 $h=0$ 即给等号。

设 $d>0$。对 $0<\varepsilon<d$，两个紧凸集
$K$ 与 $B_\varepsilon=\{u:N(u-r)\le\varepsilon\}$ 不相交。
取它们的 Euclidean 最近点对 $k_\varepsilon,u_\varepsilon$，令
$z=u_\varepsilon-k_\varepsilon\ne0$。
分别沿两集合内的线段展开平方距离，得到

$$
\langle z,k-k_\varepsilon\rangle\le0\ (k\in K),
 \qquad
 \langle z,u-u_\varepsilon\rangle\ge0\ (u\in B_\varepsilon).
$$

故 $s_K(z)=\langle z,k_\varepsilon\rangle$，而

$$
\min_{u\in B_\varepsilon}\langle z,u\rangle
 =\langle z,r\rangle-\varepsilon N^*(z)
 =\langle z,u_\varepsilon\rangle.
$$

两式相减得

$$
\langle z,r\rangle-s_K(z)
 =\varepsilon N^*(z)+\left\lVert z\right\rVert_2^2.
$$

归一 $h_\varepsilon=z/N^*(z)$ 后，其对偶缺额严格大于 $\varepsilon$。
令 $\varepsilon\uparrow d$，对偶单位球的有限维紧性给收敛子列。
支撑函数连续，极限向量的缺额至少为 $d$。
结合已证上界，得到等号与右侧极值的达到。左侧由紧性达到。

### 定理 6.2（全部局部二元读出的精确操作缺额）

<a id="thm-c92-operational-duality"></a>

对归一局部态，有

<a id="eq-c92-operational-duality"></a>

$$
\boxed{\quad
 \Delta_w(R)
 =\max_{0\le E_C\le I_C}
 \left[
  \sum_Cw_C\operatorname{Tr}(R_CE_C)
  -\lambda_{\max}\!\left(\sum_Cw_C\iota_C(E_C)\right)
 \right].\quad}
\tag{6.3}
$$

因此 $\Delta_w(R)=0$ 当且仅当 C92 成立，也当且仅当存在兼容全态。
该等式不要求满秩、严格可行性或局部效果彼此对易。

**证明。**
在前文 $\mathfrak V$ 上取范数

$$
N(x)=\frac12\sum_Cw_C\left\lVert x_C\right\rVert_1.
$$

迹范数与算符范数的有限谱对偶给出

$$
N^*(h)=2\max_C\frac{\left\lVert h_C\right\rVert_\infty}{w_C}.
$$

其上界由逐块 Hölder 不等式得到。若 $h\ne0$，选择达到最大比值的块
$C_*$，再取 $h_{C_*}$ 的单位本征向量 $v$，使对应本征值 $\lambda$
满足 $|\lambda|=\left\lVert h_{C_*}\right\rVert_\infty$。令
$x_{C_*}=(2/w_{C_*})\operatorname{sgn}(\lambda)\lvert v\rangle\langle v\rvert$，其余块为零，
则 $N(x)=1$ 且 $\langle h,x\rangle=2|\lambda|/w_{C_*}$，给出反向等号；
$h=0$ 时等式显然成立。
所以对偶单位球恰为 $\left\lVert h_C\right\rVert_\infty\le w_C/2$。
应用引理 [6.1](#lem-c92-norm-separation)，并使用
式 [(4.2)](#eq-c92-support-function)，得到

$$
\Delta_w(R)=\max_{\left\lVert h_C\right\rVert_\infty\le w_C/2}
       \bigl[b_R(h)-\lambda_{\max}(W(h))\bigr].
$$

逐块写成 $h_C=w_C(E_C-I_C/2)$。
该变量替换与 $0\le E_C\le I_C$ 一一对应；归一性使两个标量偏移
$-1/2$ 恰好抵消，便得到式 [(6.3)](#eq-c92-operational-duality)。
零点资格由完整扩张定理或前一命题立即得到。

### 推论 6.3（稳定性、局部坐标协变与无关旁系统）

<a id="cor-c92-distance-stability"></a>

上述缺额为凸函数，且

<a id="eq-c92-distance-lipschitz"></a>

$$
|\Delta_w(R)-\Delta_w(R')|
 \le\sum_Cw_CD(R_C,R_C').
\tag{6.4}
$$

对同一子系统划分作局部酉基底改变，缺额不变。
若附加独立旁系统，且其全部局部态 $\tau_C$ 来自同一个合法旁系统全态，
将资料换成 $R_C\otimes\tau_C$ 后缺额也不变。

**证明。**
凸性由相容全态的凸混合与迹距离凸性得到；对任一候选全态使用三角不等式，
再取最小值并交换 $R,R'$，即得式 [(6.4)](#eq-c92-distance-lipschitz)。
局部酉共轭给候选全态的一一对应，并保持每项迹距离。
旁系统方向上，将任意旧候选与给定旁系统全态作乘积，
利用 $D(\rho\otimes\tau,\sigma\otimes\tau)=D(\rho,\sigma)$ 得新缺额不大于旧缺额；
反向对任意新候选丢弃旁系统，迹距离收缩给旧缺额不大于新缺额。

式 [(6.3)](#eq-c92-operational-duality) 比单纯的存在判据多给出一项精确含义：
最强二元见证超过全态可达上界多少，就至少需要改动这么多加权局部读数；
而这个下界可以由某个合法全态达到。
若最优全态为 $\sigma_*$，每块分别有
$D(R_C,(\sigma_*)_C)\le\Delta_w(R)/w_C$；
权重很小的块不会自动得到同样强的单块保证。
这仍是到相容集合的距离，不是到未知真实全态的距离。

**白话图景。**局部资料若互相冲突，最强的二元问题会把冲突量读出来。
这个量恰好等于把全部资料修正到某个共同整体所需的最小平均改动。
给各块换坐标，或在旁边加上完全独立的合法内容，都不会凭空消除冲突。
这样，闭合不只剩“是或否”，还带着由实际读出距离确定的误差尺度。

<a id="section-7"></a>

## 7. 每个失败怎样压成一个二元读出

<a id="sec-c92-binary-witness"></a>

沿用候选 C92 的局部关系族 $R=(R_C)_C$、局部自伴检验族 $h=(h_C)_C$，
以及由它们定义的整体检验算符 $W=W(h)$ 和资料赋值
$y=b_R(h)$。这里只对一个已选见证作有限提升，不把整个边际问题压缩成固定三个数。
先按前文的常数检验检查单位赋值为一；若原始 Hermitian 资料尚未归一，
它已在完整总量这一步失败。以下球内与球外编码针对已通过单位归一的资料。

设 $m=\lambda_{\min}(W)$、$M=\lambda_{\max}(W)$，先考虑 $M>m$。
定义

<a id="eq-c92-binary-normalization"></a>

$$
E=\frac{W-mI}{M-m},\qquad I-E=\frac{MI-W}{M-m},
 \qquad q=\frac{y-m}{M-m}.
\tag{7.1}
$$

因为 $mI\le W\le MI$，所以 $(E,I-E)$ 是完整的二元效果。
沿这一选定的局部表达，并在任一 patch 中用单位算符表示常数，
候选资料给它的两项赋值是 $(q,1-q)$。
若不同表达尚未相容，这只是该表达的推断值，并未预设存在全局良定义的响应泛函。
当这些资料确实来自某个整体态 $\rho$ 时，必有
$q=\operatorname{Tr}(\rho E)$。

### 命题 7.1（谱界与二元正性是同一个检查）

<a id="prop-c92-binary-ball"></a>

对 $M>m$，以下条件等价：

$$
m\le y\le M,
 \qquad 0\le q\le1,
 \qquad
 B(q):=\begin{pmatrix}q&0\\0&1-q\end{pmatrix}\ge0.
$$

写成 Bloch 形式，则

<a id="eq-c92-binary-bloch"></a>

$$
B(q)=\frac12(I+\mathbf r\cdot\boldsymbol\sigma),
 \qquad \mathbf r=(0,0,2q-1),
 \qquad B(q)\ge0\ \Longleftrightarrow\ \left\lVert \mathbf r\right\rVert\le1.
\tag{7.2}
$$

因此任何被这一 $W$ 识别的谱界失败，都成为一个球外二元赋值。

**证明。**
第一项与第二项由正的分母 $M-m$ 等价。
$B(q)$ 的特征值就是 $q,1-q$，给出其余等价；
$\left\lVert \mathbf r\right\rVert\le1$ 即 $|2q-1|\le1$。

若 $M=m$，则 $W=mI$，正确检查是 $y=m$，不能除以零。
若资料为同一个常数算符赋了另一数值，它还没有通过表示相容。
这种失败也能写成二元正性矛盾：对零算符的表达
$F=W-mI$ 或 $F=mI-W$，择使其资料赋值为负的一向，
就得到正效果 $F=0$ 被赋负值。必要时乘以任意正数只改变单位，不改变矛盾。

这里的 $B(q)$ 在失败时只是一个迹一 Hermitian *候选矩阵*，不是物理量子态。
$q<0$ 或 $q>1$ 表示局部资料无法同时成为这一共同读口的概率，
不表示某个真实实验产生了负概率。
项目 V78 已经使用过“迹一候选的球外点给二元正性见证”的接口 [7](#ref-v78)；
本轮的新接续在于定理 [4.1](#thm-c92-extension)：
即使尚未给出任何全态候选，失败的局部资料也必能被某个这样的二元检验识别。
已知有限维边际见证理论为这一判据提供数学背景 [1](#ref-hall2007)。

**白话图景。**把复杂的关系冲突集中到一个问题上：这个结果会不会发生，以及它的补会不会发生。
两项总和归一为一。如果局部资料迫使其中一项小于零，或者大于整个总量，
它们就不能同时属于同一个整体。这次三维提升保留的是一个矛盾见证；
整个问题还有多少其他关系，仍由原来的资料与检验族保留。

<a id="section-8"></a>

## 8. 二元效果的一量子比特实现，以及第三坐标从哪里来

<a id="sec-c92-effect-dilation"></a>

上节的球外点给出否定证书。对于一个合法二元效果，还可以在既有量子操作接口内
给出显式实现。这里已声明共同 Hilbert 载体、Born 读出与可用的内部辅助 qubit；
这个构造不把它们重新当作 C92 单独推出的结论。

### 命题 8.1（显式二元酉扩张）

<a id="prop-c92-effect-unitary"></a>

对任意 $0\le E\le I$，令 $A=\sqrt E$、$B=\sqrt{I-E}$。
在 $H\otimes\mathbb C^2$ 上，以辅助端口基底排列块矩阵，定义

<a id="eq-c92-effect-unitary"></a>

$$
U_E=\begin{pmatrix}A&-B\\ B&A\end{pmatrix}.
\tag{8.1}
$$

则 $U_E$ 为酉，且对初始化为 $\lvert 0\rangle$ 的辅助端口，

<a id="eq-c92-effect-isometry"></a>

$$
V_E\psi:=U_E(\psi\otimes\lvert 0\rangle)
 =\sqrt E\,\psi\otimes\lvert 0\rangle+
   \sqrt{I-E}\,\psi\otimes\lvert 1\rangle.
\tag{8.2}
$$

读取辅助端口的 $0,1$，恰好实现 $(E,I-E)$。

**证明。**
$A,B$ 同为 $E$ 的谱函数，因此相互对易，且 $A^2+B^2=I$。
直接作块矩阵乘法，$U_E^\dagger U_E=U_EU_E^\dagger=I$。
第一个块列给出式 [(8.2)](#eq-c92-effect-isometry)。
对输入态 $\rho$，两项概率分别为
$\operatorname{Tr}(A\rho A)=\operatorname{Tr}(\rho E)$ 与
$\operatorname{Tr}(B\rho B)=\operatorname{Tr}[\rho(I-E)]$。

在 $E$ 的每个本征方向上，式 [(8.1)](#eq-c92-effect-unitary) 都是一项普通二维旋转，
其两个幅度是 $\sqrt e$ 和 $\sqrt{1-e}$。
这解释了正效果怎样在既定平方读出下获得归一幅度实现；
不提供该整体算符的免费制备、门分解或资源代价。

### 命题 8.2（真实输出 qubit 的三轴条件）

<a id="prop-c92-actual-qubit"></a>

对任一实际输入态，辅助端口的约化态可以写成

<a id="eq-c92-actual-qubit"></a>

$$
\beta=\begin{pmatrix}q&\gamma\\\overline\gamma&1-q\end{pmatrix}
 =\frac12(I+x\sigma_x+y\sigma_y+z\sigma_z),
 \quad
 (x,y,z)=(2\operatorname{Re}\gamma,-2\operatorname{Im}\gamma,2q-1).
\tag{8.3}
$$

其正性等价于

<a id="eq-c92-actual-ball"></a>

$$
0\le q\le1,\qquad |\gamma|^2\le q(1-q),
 \quad\text{等价地}\quad x^2+y^2+z^2\le1.
\tag{8.4}
$$

对式 [(8.2)](#eq-c92-effect-isometry) 的规范实现，

$$
q=\operatorname{Tr}(\rho E),\qquad
 \gamma=\operatorname{Tr}\!\left[\rho\sqrt{E(I-E)}\right]\ge0.
$$

若采用另外声明的分支操作或相位，$\gamma$ 一般可以为复数。

**证明。**
对 $V_E\rho V_E^\dagger$ 取系统部分迹，其两个对角元给 $q,1-q$，
交叉元为 $\operatorname{Tr}(A\rho B)=\operatorname{Tr}(\rho BA)$。
对任意迹一 Hermitian $2\times2$ 矩阵，正性由对角非负与行列式非负等价刻画；
行列式为 $q(1-q)-|\gamma|^2$，直接代入得球内条件。
等价地，其特征值为 $(1\pm\sqrt{x^2+y^2+z^2})/2$。

$q$ 并不独自确定 $\gamma$。一个完全解析的例子是

$$
E=\operatorname{diag}(0,\tfrac12,1).
$$

输入中间本征向量的纯态，与输入两端本征向量的等权混合，都给 $q=1/2$；
规范扩张的 $\gamma$ 却分别是 $1/2$ 与 $0$。
前者辅助态为 $\lvert +\rangle\langle +\rvert$，后者为 $I_2/2$。
即使读出概率相同，关系的相干坐标仍可能不同。

若只保留二元经典记录，就对辅助端口去相干，得到上节的 $B(q)$，
其 Bloch 向量落在一条直径上。若要得到球面纯态，则必须额外指定满足
$|\gamma|^2=q(1-q)$ 的相干关系；不能仅从二项概率归一推出这一等号或相位。

**白话图景。**二元问题可以放进一个实际的内部量子比特：一个幅度对应结果，另一个幅度对应它的补。
两项平方加起来等于一。但两项之间还有相干关系，决定第三坐标怎样进入球中。
只知道两个概率，通常只确定一条轴上的位置；知道交叉关系，才确定更多方向。
归一、相位和相干各有自己的内容，不能互相代替。

<a id="section-9"></a>

## 9. 三角形闭环：精确可行区间、球外点与最小修复

<a id="sec-c92-triangle"></a>

v91 用三条经典对角边际说明：每个相邻窗口均可 Markov 拼接，
闭环仍可能没有共同全态 [13](#ref-v91)。
这里把同一反例展开成完整的参数分类，并求出精确修复量。
以下统一记迹距离为 $D(\rho,\sigma)=\tfrac12\left\lVert \rho-\sigma\right\rVert_1$。

对三个 qubit 的每条边指定

<a id="eq-c92-triangle-marginals"></a>

$$
\rho_{XY}(r)=\frac14(I+rZ_XZ_Y),
 \qquad XY\in\{AB,BC,CA\},\qquad -1\le r\le1.
\tag{9.1}
$$

每份边际都是合法状态，共有单点态 $I/2$。
任取两边，它们在计算基中同时对角，因此始终满足 v91 的双向 Markov 拼接条件。

### 定理 9.1（三条对称边际的完整可行区间）

<a id="thm-c92-triangle-range"></a>

式 [(9.1)](#eq-c92-triangle-marginals) 存在共同全态，当且仅当

<a id="eq-c92-triangle-range"></a>

$$
-\frac13\le r\le1.
\tag{9.2}
$$

在这个区间内，一个显式补全是

<a id="eq-c92-triangle-extension"></a>

$$
\omega_r=\frac18(I+rW_\triangle),
 \qquad W_\triangle=Z_AZ_B+Z_BZ_C+Z_CZ_A.
\tag{9.3}
$$

**证明。**
令

$$
E_\triangle=
 \frac{I+Z_AZ_B}{2}\frac{I+Z_BZ_C}{2}.
$$

两因子为相互对易的投影，因此乘积仍为投影，且

<a id="eq-c92-triangle-projector"></a>

$$
W_\triangle=4E_\triangle-I.
\tag{9.4}
$$

$E_\triangle$ 投影到 $\operatorname{span}\{\lvert 000\rangle,\lvert 111\rangle\}$，秩为二。
故 $W_\triangle$ 的谱为 $3,-1$，相应重数为二、六。
任意兼容全态都必须有
$\operatorname{Tr}(\rho W_\triangle)=3r\ge-1$，给出 $r\ge-1/3$。
上界 $r\le1$ 已是单边合法性所需。

反过来，式 [(9.3)](#eq-c92-triangle-extension) 的两个特征值为
$(1+3r)/8$、$(1-r)/8$，所以在所述区间内为正且迹一。
对任一端口取部分迹，其余两条含该端口 $Z$ 的项消失，
恰得到指定的另一条边际。因此补全成立。

对本例，式 [(7.1)](#eq-c92-binary-normalization) 给出

<a id="eq-c92-triangle-bloch"></a>

$$
E=\frac{W_\triangle+I}{4}=E_\triangle,
 \qquad q=\frac{1+3r}{4},
 \qquad z=2q-1=\frac{3r-1}{2}.
\tag{9.5}
$$

这个二元问题问“三位是否全部相同”。
v91 的反例 $r=-1/2$ 要求

$$
q=-\frac18,\qquad z=-\frac54.
$$

三张局部图合起来，竟要求一个正投影的概率为负，故其二元赋值落在球外。

### 定理 9.2（任意整体修复三条边的精确最坏误差）

<a id="thm-c92-triangle-repair"></a>

对 $-1\le r\le1$，定义

$$
\varepsilon_\triangle(r)=
 \inf_{\rho_{ABC}\ge0,\,\operatorname{Tr}\rho=1}
 \max_{XY\in\{AB,BC,CA\}}
 D(\rho_{XY},\rho_{XY}(r)).
$$

则

<a id="eq-c92-triangle-repair"></a>

$$
\boxed{\quad
 \varepsilon_\triangle(r)
 =\frac{\max\{0,-1-3r\}}6.
 \quad}
\tag{9.6}
$$

特别地，$r=-1/2$ 时精确最小误差为 $1/12$。

**证明。**
若某全态对三条边的误差均不超过 $\varepsilon$，则

$$
|\operatorname{Tr}(\rho_{XY}Z_XZ_Y)-r|
 \le\left\lVert \rho_{XY}-\rho_{XY}(r)\right\rVert_1
 \le2\varepsilon.
$$

谱下界又要求三个实际关联之和至少为 $-1$，故
$-1\le3r+6\varepsilon$。
得到 $\varepsilon\ge(-1-3r)/6$；误差当然也非负。

若 $r\ge-1/3$，使用 $\omega_r$ 达到零。
若 $r<-1/3$，使用边界全态 $\omega_{-1/3}$。
两份边态之差为 $(r+1/3)Z_XZ_Y/4$，而
$\left\lVert Z_XZ_Y\right\rVert_1=4$，所以每条边的误差恰为
$(-r-1/3)/2=(-1-3r)/6$。下界遂可达。

同一精确值也适用于三条边的等权平均迹距离。
因为各边关联变化至多为其迹距离的两倍，谱下界直接给
$2\sum_{XY}D(\rho_{XY},\rho_{XY}(r))\ge-1-3r$。
在 $r<-1/3$ 时，已构造的对称边界补全使三项误差相等并达到这个下界；
其余可行参数直接达到零误差。
特别地，$r=-1/2$ 时最小平均误差与最小最坏误差同为 $1/12$。

若限定沿共同白噪声方向修复，令
$\rho_{XY}^{(t)}=(1-t)\rho_{XY}(-1/2)+tI_4/4$。
新参数为 $r_t=-(1-t)/2$，由定理 [9.1](#thm-c92-triangle-range)，
可行当且仅当 $t\ge1/3$。
这个 $1/3$ 是指定混合方向上的最少白噪声比例；
式 [(9.6)](#eq-c92-triangle-repair) 的 $1/12$ 则是允许任意全态修复时的边际迹距离。
两者的定义和尺度不同。

**白话图景。**三条边都想让两端偏向相反，但三个二值方向无法同时过强地两两相反。
把冲突集中到“是否三位全部相同”，就出现负的推断概率。
需要改多少也能精确算清：指定的白噪声混合至少加三分之一，
或者按任意整体来修复，三条边中的最大迹距离至少十二分之一。
这些数来自同一个谱见证，不需要搜索候选状态。

<a id="section-10"></a>

## 10. 两份 Bell 关系：精确共享阈值与最小修复

<a id="sec-c92-bell"></a>

本节的相容阈值与后面的椭圆，属于已知的各向同性边际和非对称量子克隆结构。
Nechita–Pellegrini–Rochette 给出了包括负可见度在内的完整椭圆描述
 [2](#ref-npr2021)。这里给 qubit 情形的直接分块证明，
用来展示 C92 的二元见证、三轴提升和精确修复，不重新主张这些边界的数学优先权。

记 $\lvert \Phi\rangle=(\lvert 00\rangle+\lvert 11\rangle)/\sqrt2$、$\Phi=\lvert \Phi\rangle\langle \Phi\rvert$，
并定义两比特各向同性态

<a id="eq-c92-isotropic"></a>

$$
\sigma_v=v\Phi+(1-v)\frac{I_4}{4},
 \qquad -\frac13\le v\le1.
\tag{10.1}
$$

参数 $v$ 称为可见度；Bell 投影的实际概率是
$F_v=\operatorname{Tr}(\sigma_v\Phi)=(1+3v)/4$，两者不混同。
所给参数区间恰好使 Bell 方向与其三维正交补上的特征值均非负。

在 $ABC$ 上定义两个重叠投影

$$
\Pi_L=\Phi_{AB}\otimes I_C,\qquad
 \Pi_R=I_A\otimes\Phi_{BC},\qquad W_B=\Pi_L+\Pi_R.
$$

### 引理 10.1（两个 Bell 投影的精确二维分块）

<a id="lem-c92-bell-blocks"></a>

对 $b=0,1$，令

$$
g_b=\lvert \Phi\rangle_{AB}\otimes\lvert b\rangle_C,
 \qquad h_b=\lvert b\rangle_A\otimes\lvert \Phi\rangle_{BC},
 \qquad e_b=g_b,\quad f_b=\frac{2h_b-g_b}{\sqrt3}.
$$

则 $e_0,f_0,e_1,f_1$ 为正交单位组。
在每个平面 $\mathcal T_b=\operatorname{span}\{e_b,f_b\}$ 上，

<a id="eq-c92-bell-block-pauli"></a>

$$
\Pi_L=\frac{I+\sigma_z}{2},\qquad
 \Pi_R=\frac{I+\frac{\sqrt3}{2}\sigma_x-\frac12\sigma_z}{2}.
\tag{10.2}
$$

在两平面的共同正交补上，两投影均为零。
因此

<a id="eq-c92-bell-spectrum"></a>

$$
\operatorname{spec} W_B=\{0,\tfrac12,\tfrac32\},
 \quad\text{重数分别为 }4,2,2.
\tag{10.3}
$$

**证明。**
由 Bell 向量展开，
$\langle g_b,g_c\rangle=\langle h_b,h_c\rangle=\delta_{bc}$，
且 $\langle g_b,h_c\rangle=\delta_{bc}/2$。
这给出所述正交单位组。
在 $(e_b,f_b)$ 中，$g_b=e_b$、
$h_b=\tfrac12e_b+\tfrac{\sqrt3}{2}f_b$，
所以两个投影矩阵分别为

$$
\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
 \begin{pmatrix}1/4&\sqrt3/4\\\sqrt3/4&3/4\end{pmatrix},
$$

即式 [(10.2)](#eq-c92-bell-block-pauli)。
两者之和为 $I+(\sqrt3\sigma_x+\sigma_z)/4$，
无迹部分平方为 $I/4$，故每块特征值为 $1\pm1/2$。
余下四维空间为两投影的共同核。

### 定理 10.2（相同各向同性边际的完整阈值）

<a id="thm-c92-bell-threshold"></a>

两份边际 $\rho_{AB}=\sigma_v$、$\rho_{BC}=\sigma_v$ 存在共同全态，
当且仅当

<a id="eq-c92-bell-threshold"></a>

$$
-\frac13\le v\le\frac23.
\tag{10.4}
$$

**证明。**
必要性来自单一谱见证：任何兼容全态都必须有

$$
\operatorname{Tr}(\rho W_B)=2F_v=\frac{1+3v}{2}\le\frac32,
$$

即 $v\le2/3$。下界已由局部态正性给出。

为证明充分性，利用已知谱定义两个正交投影

<a id="eq-c92-bell-projectors"></a>

$$
\Pi_+=\frac{2W_B^2-W_B}{3},\qquad
 \Pi_0=I-\frac83W_B+\frac43W_B^2.
\tag{10.5}
$$

它们分别投影到 $W_B$ 的 $3/2$ 与零特征空间，秩为二、四。
令 $\tau_+=\Pi_+/2$、$\tau_0=\Pi_0/4$。
由

$$
\begin{aligned}
 \operatorname{Tr}_C\Pi_L&=2\Phi_{AB},&
 \operatorname{Tr}_C\Pi_R&=I_{AB}/2,\\
 \operatorname{Tr}_C(\Pi_L\Pi_R)&=\Phi_{AB}/2,&
 \operatorname{Tr}_C(\Pi_R\Pi_L)&=\Phi_{AB}/2
 \end{aligned}
$$

得到
$\operatorname{Tr}_C W_B^2=3\Phi_{AB}+I_{AB}/2$。
代回式 [(10.5)](#eq-c92-bell-projectors)，有

<a id="eq-c92-bell-endpoint-marginals"></a>

$$
(\tau_+)_{AB}=\frac23\Phi+\frac{I_4}{12}=\sigma_{2/3},
 \qquad
 (\tau_0)_{AB}=\frac{I_4-\Phi}{3}=\sigma_{-1/3}.
\tag{10.6}
$$

$A,C$ 交换对称性给出相同的 $BC$ 结论。
所以对整个区间，显式混合

<a id="eq-c92-bell-completion"></a>

$$
\tau_v=\left(v+\frac13\right)\tau_+
       +\left(\frac23-v\right)\tau_0
\tag{10.7}
$$

均为合法全态，且两边际恰为 $\sigma_v$。

本例的规范二元效果与推断概率是

<a id="eq-c92-bell-binary"></a>

$$
E_B=\frac23W_B,
 \qquad q=\frac{1+3v}{3}=v+\frac13,
 \qquad z=2v-\frac13.
\tag{10.8}
$$

两份完美 Bell 边际 $v=1$ 要求
$q=4/3$、$z=5/3$，落在二元球外。
边界 $v=2/3$ 则给 $q=1$，由 $\tau_+$ 精确达到。

这个可行边界仍然包含真正的量子关联。
当 $v>1/3$ 时，$\sigma_v$ 的部分转置在反对称方向上有特征值
$(1-3v)/4<0$，而可分态的部分转置必为正，因此它纠缠。
特别地，$v=2/3$ 时两条边都纠缠，但共同全态确实存在。
按 v91 对 qubit 共享端口的三种 Markov 分块分类，
Markov 扩张不可能同时具有这两份纠缠边际 [13](#ref-v91)。
所以 C92 的一般相容资格确实容纳了 C91 特定 Markov 拼接之外的关系。

### 定理 10.3（两份 Bell 边际的精确最坏修复）

<a id="thm-c92-bell-repair"></a>

对 $-1/3\le v\le1$，有

<a id="eq-c92-bell-repair"></a>

$$
\inf_{\rho_{ABC}\ge0,\,\operatorname{Tr}\rho=1}
 \max\{D(\rho_{AB},\sigma_v),D(\rho_{BC},\sigma_v)\}
 =\frac{\max\{0,3v-2\}}4.
\tag{10.9}
$$

因此完美 Bell–Bell 资料的精确最小最坏误差为 $1/4$。
若沿同一白噪声方向修复完美边际，最少混合比例为 $1/3$。

**证明。**
任一效果的概率差不超过迹距离。
若两个边际的误差均至多 $\varepsilon$，其实际 Bell 概率分别至少为
$F_v-\varepsilon$。谱上界给出
$2F_v-2\varepsilon\le3/2$，故
$\varepsilon\ge F_v-3/4=(3v-2)/4$。

若 $v\le2/3$，使用式 [(10.7)](#eq-c92-bell-completion) 达到零。
若 $v>2/3$，使用 $\tau_+$。
由 $\Phi-I_4/4$ 的特征值为 $3/4,-1/4,-1/4,-1/4$，得到

$$
D(\sigma_v,\sigma_w)=\frac34|v-w|.
$$

取 $w=2/3$ 恰达到下界。
对白噪声路径，修复后的可见度为 $v_t=1-t$，
阈值 $v_t\le2/3$ 等价于 $t\ge1/3$。

两条边的等权平均迹距离也有相同最优值。
实际两项 Bell 概率之和至多为 $3/2$，故
$D(\rho_{AB},\sigma_v)+D(\rho_{BC},\sigma_v)\ge2F_v-3/2$。
在 $v>2/3$ 时，前述对称边界补全使两项误差相等并达到下界；
其余可行参数直接达到零误差。
在 $v=1$ 时，最小平均误差因此同样为 $1/4$。

**白话图景。**一个中间量子比特不能同时把两份 Bell 关系都保持到满强度。
把两边的要求加起来，会要求一个合法二元效果的概率大于一。
允许两边各自降低到三分之二可见度，就有明确的整体承接它们，而且两边仍然纠缠。
这说明一般整体相容与无额外条件关联的 Markov 拼接，承担不同的定义资格。

<a id="section-11"></a>

## 11. 两条非正交读出怎样把球投影成椭圆

<a id="sec-c92-isotropic-ellipse"></a>

现在允许两边可见度不同：$\rho_{AB}=\sigma_v$、$\rho_{BC}=\sigma_w$。
在引理 [10.1](#lem-c92-bell-blocks) 的每个二维块中，两个投影的 Bloch 方向为

$$
\mathbf n_L=(0,0,1),\qquad
 \mathbf n_R=(\sqrt3/2,0,-1/2).
$$

它们的内积为 $-1/2$，夹角为 $120^\circ$。
第三轴由它们的交换子生成：

$$
i[\Pi_L,\Pi_R]= -\frac{\sqrt3}{4}\sigma_y
 \quad\text{（在每个二维块上）}.
$$

这三轴描述的是两个关系投影生成的有效矩阵代数。

<a id="fig-c92-bloch-readout-axes"></a>

```text
                           z
                           ↑ n_L
                    · · ·  ●  · · ·
                ·          │          ·
              ·            │            ·
             ·             │             ·
         ───·──────────────0───────────────·──→ x
             ·              ╲  120°      ·
              ·              ╲         ·
                ·             ╲      ·
                    · · · · ·  ● n_R

          单位圆盘位于 x–z 平面；y 轴垂直纸面。
          角度从向上的 n_L 转向右下方的 n_R。
```

字符图仅作示意；精确方向与交叉关系如下：

| 图示对象 | 精确坐标或关系 |
|---|---|
| 有效 Bloch 球的 x–z 截面 | x² + z² ≤ 1；原图填充单位圆盘。 |
| 左关系读出轴 n_L | 平面坐标 (0, 1)；三维坐标 (0, 0, 1)。 |
| 右关系读出轴 n_R | 平面坐标 (√3/2, −1/2)；三维坐标 (√3/2, 0, −1/2)。 |
| 两轴内积与夹角 | 内积 −1/2；夹角 120°。 |
| 垂直纸面的 y 轴 | 对应 i[Π_L, Π_R] 的交叉关系方向；在每个二维块上等于 −√3 σ_y/4。 |

**图 1。**有效 Bloch 球在 $x$–$z$ 平面的单位圆盘。
两条关系读出方向夹角为 $120^\circ$；
$y$ 轴垂直纸面，对应 $i[\Pi_L,\Pi_R]$ 的交叉关系方向。
沿这两条非正交方向同时读出，得到下述椭圆。

### 定理 11.1（两份各向同性边际的完整椭圆相容域）

<a id="thm-c92-isotropic-ellipse"></a>

令

<a id="eq-c92-isotropic-ellipse"></a>

$$
\mathcal E=\{(v,w)\in\mathbb R^2:
 v^2+w^2+vw\le v+w\},
 \qquad p_-=(-\tfrac13,-\tfrac13).
\tag{11.1}
$$

则所有存在共同全态的参数对，恰为

<a id="eq-c92-isotropic-full-region"></a>

$$
\boxed{\qquad
 \mathcal C_{\rm iso}
 =\operatorname{conv}\bigl(\{p_-\}\cup\mathcal E\bigr).
 \qquad}
\tag{11.2}
$$

尤其在通常的白噪声可见度范围 $v,w\ge0$ 内，判据恰为

<a id="eq-c92-isotropic-positive-region"></a>

$$
\boxed{\qquad v^2+w^2+vw\le v+w.\qquad}
\tag{11.3}
$$

这是已有一般椭圆分类在 qubit 上的特例 [2](#ref-npr2021)。

**证明。**
先只看两个有效二维块。对一个块上的逻辑 qubit 态

$$
\eta=\frac12(I+x\sigma_x+y\sigma_y+z\sigma_z),
 \qquad x^2+y^2+z^2\le1,
$$

两项投影期望为

<a id="eq-c92-ellipse-readouts"></a>

$$
F_L=\frac{1+z}{2},\qquad
 F_R=\frac{1-z/2+\sqrt3x/2}{2}.
\tag{11.4}
$$

令 $F_L=(1+3v)/4$、$F_R=(1+3w)/4$，得到

$$
z=\frac{3v-1}{2},\qquad
 x=\frac{\sqrt3}{2}(v+2w-1).
$$

存在某个 $y$ 使逻辑态合法，当且仅当 $x^2+z^2\le1$。
代入并展开，这恰为 $v^2+w^2+vw\le v+w$。

*必要性。*
记 $\mathcal T=\mathcal T_0\oplus\mathcal T_1$。
对任意全态 $\rho$，令 $t$ 为它在 $\mathcal T$ 上的权重。
两投影在 $\mathcal T^\perp$ 为零，跨支撑项也不贡献投影期望。
在 $t>0$ 时，把 $\mathcal T$ 上的归一压缩态在两个重复块上取部分迹，
便得到上述某个逻辑态 $\eta$。
所以 $(F_L,F_R)$ 是该椭圆读出与零点之间的凸组合。
零点 $F_L=F_R=0$ 对应可见度 $p_-$，从而所有兼容参数都位于
式 [(11.2)](#eq-c92-isotropic-full-region) 右侧。
$t=0$ 直接给出 $p_-$。

*充分性。*
不能仅凭两个投影期望就断言全部边际正确，下面给出明确构造。
对 $\eta=\begin{pmatrix}a&c\\\overline c&1-a\end{pmatrix}$，
定义

<a id="eq-c92-ellipse-completion"></a>

$$
\chi_\eta=\frac12\sum_{b=0}^1
 \left[
 a\lvert e_b\rangle\langle e_b\rvert+c\lvert e_b\rangle\langle f_b\rvert
 +\overline c\lvert f_b\rangle\langle e_b\rvert
 +(1-a)\lvert f_b\rangle\langle f_b\rvert
 \right].
\tag{11.5}
$$

它是两个相同逻辑块的等权混合，故为合法全态。
由 $e_b=g_b$、$f_b=(2h_b-g_b)/\sqrt3$ 直接取部分迹，有

$$
\begin{aligned}
 (\chi_\eta)_{AB}
 &=a\Phi+\frac{1-a}{3}(I_4-\Phi),\\
 (\chi_\eta)_{BC}
 &=\left[\frac23(1-a)+\frac{2\operatorname{Re} c}{\sqrt3}\right]\Phi
 +\left[\frac{1+2a}{12}-\frac{\operatorname{Re} c}{2\sqrt3}\right]I_4.
 \end{aligned}
$$

两份完整边际确实都是各向同性态。
取 $a=(1+z)/2$、$\operatorname{Re} c=x/2$，它们的 Bell 概率恰为
式 [(11.4)](#eq-c92-ellipse-readouts)。
故每个 $\mathcal E$ 点都被某个 $\chi_\eta$ 实现。
再与前节的 $\tau_0$ 混合，便实现它与 $p_-$ 的全部凸组合。

*非负象限。*
椭圆上每个坐标都在 $[-1/3,1]$ 内，因为它来自合法投影期望。
若从 $p_-$ 向某个椭圆点的线段进入非负象限，首次进入处必在一条坐标轴上，
另一坐标位于 $[0,1]$。两段轴线 $(s,0),(0,s)$、$0\le s\le1$ 均在
$\mathcal E$ 内。由椭圆盘的凸性，进入处至原椭圆点的整段仍在 $\mathcal E$。
所以凸包在非负象限中没有扩大椭圆，得到式 [(11.3)](#eq-c92-isotropic-positive-region)。

沿对角线 $v=w$，式 [(11.3)](#eq-c92-isotropic-positive-region) 退化为
$3v^2\le2v$，重新得到 $0\le v\le2/3$。
单边 $v=1$ 时，另一边只能有 $w=0$；
这也可直接从纯 Bell 边际迫使整体为乘积态得到。

这个椭圆来自三维球对两条*非正交读出方向*的线性投影。
未被两个读出固定的 $y$ 坐标，是它们交换子方向上的交叉关系；
在球面边界与球内之间如何选择，仍取决于实际相干内容。
这里证明的是静态相容域和读出几何。
若把椭圆进一步解释为时间轨道，仍须指定相应动力学，而不能仅凭形状推断。

**白话图景。**两条关系读出的方向不是直角，而是固定的夹角。
同一个三维球从这两个方向读出来，边界就成为椭圆。
越接近这个椭圆边界，能够留给第三方向的空间就越少；
在两项可见度非负的范围内，超出椭圆，就没有同一个正归一态能同时承接两份读数。
圆与椭圆在这里有精确来源：它们分别是同一逻辑关系的归一几何与投影几何。

<a id="section-12"></a>

## 12. 内部参照怎样统一不兼容、边界与忠实补全

<a id="sec-c92-internal-radius"></a>

前面的见证决定是否可拼接，迹距离决定最少须改多少局部读数。
现在再问一个不同但精确的问题：保持每个单点的内容不变，
把已有相关与其内部乘积参照混合，至少需要撤去多少相关强度，才能重新获得共同整体？

本节先要求各局部表已经是密度态 $\rho_C$，并通过全部*线性身份一致性*。
这比 C92 弱：允许正性相容失败，只要求同一个算符的不同局部表达给相同数值。
于是

$$
\mathcal S=\operatorname{ran} A^*,\qquad
 \ell\left(\sum_C\iota_C(h_C)\right)=\sum_C\operatorname{Tr}(\rho_Ch_C)
$$

良定义且 $\ell(I)=1$。这里 $A$ 是前文的边际映射。

### 引理 12.1（单点支撑与内部乘积参照）

线性身份一致性使每个节点 $i$ 的单点边际 $\rho_i$ 与读取它的 patch 无关。
把 $\mathcal H_i$ 限制到 $\operatorname{supp}\rho_i$ 后，所有 $\rho_C$ 仍完整保留，且

<a id="eq-c92-product-anchor"></a>

$$
\tau=\bigotimes_{i\in V}\rho_i>0,\qquad \operatorname{Tr}\tau=1.
\tag{12.1}
$$

**证明。**
对同一节点上的任意自伴读口，用两个 patch 的相反嵌入构成零算符，
身份一致性给两个约化响应相同。设 $P_i=\operatorname{supp}\rho_i$。
对包含 $i$ 的 $\rho_C$，有
$\operatorname{Tr}[\rho_C((I-P_i)\otimes I)]=0$，正性给出
$((I-P_i)\otimes I)\rho_C^{1/2}=0$。
对所有节点的对易支撑投影相乘，得到 $\rho_C$ 支撑于实际单点支撑之积。
限制后各 $\rho_i$ 严格正，故它们的张量积忠实。

$\tau$ 保留每个单点自身的读数，并撤去单点之间的相关。
它由当前资料定义；这是一项数学参照，并不自动供应实验中的额外副本或制备设备。
本节以下的忠实性与相容体，均相对于这个固定的支撑约简载体。
讨论其邻域扰动时保持载体不变，不随每份扰动资料再次改变维数。

### 定义 12.2（内部序半径）

定义正关系的归一截面与其最小响应

<a id="eq-c92-alpha"></a>

$$
\mathcal B_\tau=\{W\in\mathcal S:W\ge0,\ \operatorname{Tr}(\tau W)=1\},
 \qquad
 \alpha=\min_{W\in\mathcal B_\tau}\ell(W).
\tag{12.2}
$$

这个量不引入第二个资格公理。它量化 C92 在给定内部参照下的余量。
集合非空，因为 $I\in\mathcal B_\tau$。
若 $t=\lambda_{\min}(\tau)>0$，则其中每个 $W$ 都满足

$$
1=\operatorname{Tr}(\tau W)\ge t\operatorname{Tr} W\ge t\left\lVert W\right\rVert_{\mathrm{op}}.
$$

该集合闭且有界，有限维下紧；因此最小值有限且达到，并且 $\alpha\le1$。

### 定理 12.3（内生半径的正延拓与精确下界）

<a id="thm-c92-internal-radius"></a>

在以上前件下，

<a id="eq-c92-alpha-primal"></a>

$$
\alpha
 =\max\{t\in\mathbb R:\ \exists X=X^\dagger,
             \ A(X)=(\rho_C)_C,\ X\ge t\tau\}.
\tag{12.3}
$$

右侧最大值达到。进一步：

1. $\alpha<0$ 当且仅当局部资料没有共同密度态；

2. $\alpha=0$ 当且仅当资料兼容，但所有共同密度态补全均奇异；

3. $\alpha>0$ 当且仅当存在忠实共同密度态补全。

**证明。**
若 $X\ge t\tau$ 且满足给定边际，则对每个 $W\in\mathcal B_\tau$ 有
$\ell(W)=\operatorname{Tr}(XW)\ge t$。所以右侧不超过 $\alpha$。

若 $\alpha<1$，对每个非零 $W\in\mathcal S_+$ 按 $\operatorname{Tr}(\tau W)$ 归一，
得到 $\ell(W)\ge\alpha\operatorname{Tr}(\tau W)$。因此

$$
f(W)=\frac{\ell(W)-\alpha\operatorname{Tr}(\tau W)}{1-\alpha}
$$

是 $\mathcal S$ 上的正归一泛函。
前文的正延拓定理 [4.1](#thm-c92-extension) 给出某个密度态 $\sigma$，
使 $f(W)=\operatorname{Tr}(\sigma W)$。令

$$
X=\alpha\tau+(1-\alpha)\sigma.
$$

它满足原资料，且 $X\ge\alpha\tau$，证明达到。
这里 $\alpha<0$ 时 $X$ 只是迹一 Hermitian 延拓，不被称为密度态。

若 $\alpha=1$，则 $g=\ell-\operatorname{Tr}(\tau\,\cdot)$ 是正泛函，且 $g(I)=0$。
对任意自伴 $W\in\mathcal S$，由
$-\left\lVert W\right\rVert I\le W\le\left\lVert W\right\rVert I$，得到 $g(W)=0$。
故 $\ell=\operatorname{Tr}(\tau\,\cdot)$，取 $X=\tau$ 即得达到。

由 C92 正延拓等价，兼容当且仅当 $\ell$ 在 $\mathcal S_+$ 上非负，
也就是 $\alpha\ge0$。
若 $\alpha>0$，刚才达到的 $X\ge\alpha\tau>0$ 就是忠实补全。
反过来，任何忠实补全 $X>0$ 都有 $X\ge c\tau$ 对某个 $c>0$ 成立，
于是 $\alpha\ge c>0$。
剩下 $\alpha=0$ 的情形由这两个等价关系给出。

### 推论 12.4（相容体的内部与边界）

在局部迹一表的线性相容仿射空间内，存在忠实全态补全等价于资料属于
兼容集合的相对内部；$\alpha=0$ 的资料位于其相对边界。

**证明。**
若 $X>0$ 是补全，将有限维线性映射 $A$ 限制到迹零 Hermitian 空间，
它在自己的像上有有界线性右逆。
线性身份一致的扰动属于 $(\ker A^*)^\perp=\operatorname{ran} A$；
若每个局部迹的扰动为零，任一 Hermitian 前像的迹也为零。
因此任意充分小的相容边际扰动，都可提升成充分小的迹零 Hermitian 扰动，
仍使 $X$ 为正。故资料为相对内点。

反过来，若资料 $r$ 为相对内点，记 $r_0=A(\tau)$。
若 $r=r_0$ 已有忠实补全。否则，对充分小的 $\varepsilon>0$，
$r'=r+\varepsilon(r-r_0)$ 仍兼容。取其某个补全 $\sigma'$，则

$$
X=\frac{\sigma'+\varepsilon\tau}{1+\varepsilon}>0
$$

补全 $r$。最后由已证半径分类得到边界断言。

这给出了真正的“边界/体”含义：$\alpha$ 的符号认证是否越出相容体，
零点认证只剩奇异补全，正值认证存在完整支撑的补全。
其数值依赖已声明的内部参照，不能直接解释为能量、物理质量或时钟速率。

**白话图景。**用每个点自身的内容组成一份无额外相关的内部参照，
再问所有正关系里最薄弱的一项还剩多少余量。
余量为正，整体可以留在相容体内部；余量为零，所有补全都被压到某个低秩边界；
余量为负，当前局部说法已经越出任何整体能容纳的范围。

<a id="section-13"></a>

## 13. 最少撤去多少相关，才能重新成为共同整体

<a id="sec-c92-noise"></a>

令 $0\le\eta\le1$ 为原相关的保留比例，定义统一修订的资料

<a id="eq-c92-noise-family"></a>

$$
\rho_C^{(\eta)}=\eta\rho_C+(1-\eta)\tau_C.
\tag{13.1}
$$

每个单点边际保持不变。若原资料不兼容，这个式子描述对局部资料的共同修订，
不声称有一台通道正在作用于一份本来不存在的原全态。

### 定理 13.1（精确内部噪声阈值）

上述修订资料具有共同密度态，当且仅当

<a id="eq-c92-noise-criterion"></a>

$$
1-\eta+\eta\alpha\ge0.
\tag{13.2}
$$

因此最大保留比例及最小噪声比例分别为

<a id="eq-c92-noise-threshold"></a>

$$
\eta_*=
 \begin{cases}
 1,&\alpha\ge0,\\[2pt]
 \dfrac1{1-\alpha},&\alpha<0,
 \end{cases}
 \qquad
 \varepsilon_*=1-\eta_*=
 \begin{cases}
 0,&\alpha\ge0,\\[2pt]
 \dfrac{-\alpha}{1-\alpha},&\alpha<0.
 \end{cases}
\tag{13.3}
$$

**证明。**
修订后的响应为
$\ell_\eta=\eta\ell+(1-\eta)\operatorname{Tr}(\tau\,\cdot)$。
对任意非零 $W\in\mathcal S_+$，令
$\widehat W=W/\operatorname{Tr}(\tau W)\in\mathcal B_\tau$，则

$$
\ell_\eta(W)
 =\operatorname{Tr}(\tau W)\bigl[1-\eta+\eta\ell(\widehat W)\bigr].
$$

所以它对所有正关系非负，当且仅当式 [(13.2)](#eq-c92-noise-criterion) 成立。
调用 C92 正延拓定理，并解这一个线性不等式，得到阈值公式。
最优值的存在由 $\alpha$ 的极值达到与正延拓共同保证，未使用未经说明的强对偶假设。

### 命题 13.2（最优见证锁住阈值补全的支撑）

设 $\alpha<0$，且 $W_*\in\mathcal B_\tau$ 达到 $\ell(W_*)=\alpha$。
每个阈值补全 $\sigma_*$ 都满足

<a id="eq-c92-boundary-support"></a>

$$
\operatorname{supp}\sigma_*\subseteq\ker W_*.
\tag{13.4}
$$

当 $\alpha=0$ 时，同样结论对原资料的全部补全成立。

**证明。**
阈值处 $\operatorname{Tr}(\sigma_*W_*)=\ell_{\eta_*}(W_*)=0$。
两个算符均为正，所以
$\operatorname{Tr}(W_*^{1/2}\sigma_*W_*^{1/2})=0$ 迫使夹乘矩阵为零，
继而 $W_*^{1/2}\sigma_*^{1/2}=0$，得到支撑包含。
若 $\alpha=0$，直接对任意原资料补全使用同一个等式。

因此，达到边界时哪个方向被压成零，由失败关系自身决定。
若有多项最优见证，阈值补全必须同时支撑在它们零空间的交中。
前面的三角环与双 Bell 例子都给最小共同噪声 $1/3$，
但最小边际迹距离分别为 $1/12$ 与 $1/4$。
它们测量的是不同问题，不应混用常数或把噪声比例当作唯一误差尺度。

最后处理线性身份本身失败的情形。若 $A^*h=0$ 而
$b_R(h)\ne0$，与任意兼容资料 $r_0$ 混合后，残差变成

$$
b_{\eta R+(1-\eta)r_0}(h)=\eta b_R(h).
$$

任意 $\eta>0$ 仍有矛盾，最大保留率只能为零。
此时 $\ell$ 尚未在 $\mathcal S$ 上良定义，不能套用式 [(12.2)](#eq-c92-alpha)。
这把“同一地址给不同内容”与“地址一致但超出正性范围”两类失败准确分开。

**白话图景。**如果只是相关强度过大，可以沿着由原资料自己确定的参照方向逐步退回，
最少退多少有精确公式。退到边界时，失败见证恰好变成零，它的零空间就是允许整体落下来的位置。
但如果同一个关系被两份资料说成不同数值，保留任何正比例都会留下矛盾；
这种身份冲突不能靠一点共同噪声掩盖。

<a id="section-14"></a>

## 14. 有限窗口为何不能代替整圈：任意奇环的严格正反例

<a id="sec-c92-odd-cycles"></a>

v91 已给出三角形上的局部拼接与整体相容分离 [13](#ref-v91)。
这里把它推进成任意规模的解析族：每个真边子集都可严格正地补全，
全部边却共同失败。它证明有界大小的局部兼容检查不能覆盖任意规模网络。

### 定义 14.1（奇环上的共同边际资料）

取奇数 $n\ge3$，每个点为 qubit，按模 $n$ 记 $n+1=1$。
在每条边上指定

<a id="eq-c92-odd-cycle-data"></a>

$$
\rho_{i,i+1}=\frac14\left(I+rZ_iZ_{i+1}\right),
 \qquad r=-1+\frac1n,
 \qquad i=1,\ldots,n.
\tag{14.1}
$$

其中边算符嵌入整体时，未写的因子补单位。
各边的单点边际都是 $I/2$；因为 $-1<r<1$，每份边际严格正。

### 定理 14.2（所有真边子集可补全，完整奇环不相容）

<a id="thm-c92-odd-cycle-obstruction"></a>

式 [(14.1)](#eq-c92-odd-cycle-data) 的任意真边子集具有严格正的经典 Markov 补全；
但不存在同时实现全部 $n$ 条边际的量子全态。

**证明。**
任取真边子集 $F$，它是一个森林，允许孤立点。
对 $x_i\in\{+1,-1\}$ 定义

<a id="eq-c92-forest-distribution"></a>

$$
p_F(x_1,\ldots,x_n)
 =2^{-n}\prod_{(i,j)\in F}(1+rx_ix_j).
\tag{14.2}
$$

这可以按如下方式构造：在每个连通分量选一个根，根取均匀分布；
将树边向外定向，对每条边采用条件概率

$$
p(x_j\mid x_i)=\frac{1+rx_ix_j}{2}.
$$

若森林有 $c$ 个分量、$|F|$ 条边，则 $c+|F|=n$，
上述根概率与条件概率的乘积恰为式 [(14.2)](#eq-c92-forest-distribution)。
它归一且严格正。均匀单点边际沿边保持，边联合分布为
$p(x_i,x_j)=(1+rx_ix_j)/4$，正是指定边际。
树上的条件乘积分解还给出相应 Markov 性。
将此分布写成计算基对角密度矩阵，就得到量子空间中的合法扩张。

再看全部边。定义

$$
H_n=\sum_{i=1}^n Z_iZ_{i+1}.
$$

所有项对易。在每个共同本征配置上，
$\prod_i x_ix_{i+1}=1$，所以负边数为偶数。
因 $n$ 为奇数，最多有 $n-1$ 条负边，故

<a id="eq-c92-odd-cycle-bound"></a>

$$
H_n\ge(2-n)I.
\tag{14.3}
$$

任意量子全态都必须满足这个算符下界；不需要假定候选全态对角。
可是指定边际要求

$$
\langle H_n\rangle=nr=1-n<2-n,
$$

矛盾。因此全部资料不兼容。

### 推论 14.3（不存在统一固定的子资料大小上界）

<a id="cor-c92-no-fixed-window"></a>

对任意固定整数 $k\ge1$，存在有限量子边际资料，使每个至多含 $k$ 条边的子资料
都具有共同全态，但全部资料没有共同全态。

**证明。**
选择奇数 $n>\max\{k,2\}$，应用定理 [14.2](#thm-c92-odd-cycle-obstruction)。
所有至多 $k$ 条边的集合都是环的真边子集。

对至多含 $k<n$ 个顶点的诱导边窗口，同一个例子也成立。
这里否定的是*每个有界大小的子资料分别可扩张，就保证全部资料可扩张*。
它没有否定利用额外全局对称信息、网络长度或合成见证作判定的算法。
本例的统一参数 $r$ 与整个环结构本来就是可供全局推理的信息。

**白话图景。**任意切开一条边，剩下的链都能接好；每一小段也都没有矛盾。
但奇数个二值方向绕一圈，不能让每条边都过强地反向。
圈可以任意长，所以固定只看几条边，总可能漏掉更长的一圈。
本轮的完整条件必须允许把这些局部读出合成一个真正覆盖整圈的比较。

### 14.1 同一失败怎样归一成二元球外报告

先核定线性身份一致性。迹一 Hermitian 表

$$
X_n=2^{-n}(I+rH_n)
$$

逐边部分迹正好为指定的 $\rho_{i,i+1}$：
只有对应那条边的 Pauli 项在约化中保留，其余项含被迹去的单个 $Z$ 因子。
因此在边际算符系统上 $\ell(W)=\operatorname{Tr}(X_nW)$ 良定义。
$X_n$ 不必为正，这一步只保证地址身份一致，没有预设 C92 通过。

由式 [(14.3)](#eq-c92-odd-cycle-bound)，

<a id="eq-c92-odd-cycle-witness"></a>

$$
W_n=(n-2)I+H_n\ge0,
 \qquad \ell(W_n)=-1.
\tag{14.4}
$$

这就是定理 [4.1](#thm-c92-extension) 所要求的明确失败见证。
由于 $H_n\le nI$，效果

$$
E_n=\frac{W_n}{2(n-1)}
$$

满足 $0\le E_n\le I$，却得到候选推断

$$
p_n=\ell(E_n)=-\frac1{2(n-1)}.
$$

将事件与其补事件写成二元报告，便有

<a id="eq-c92-odd-cycle-bloch"></a>

$$
B_n=\begin{pmatrix}p_n&0\\0&1-p_n\end{pmatrix},
 \qquad \mathbf b_n=\left(0,0,-\frac n{n-1}\right).
\tag{14.5}
$$

它到 Bloch 球的欧氏距离恰为 $1/(n-1)$。
V77 的合成二元正性条件与 V78 的最小二元事件见证已有相应归一机制
 [6](#ref-v77)、[7](#ref-v78)；这里将其用于还不存在共同全态的边际资料。
负值指候选预测矛盾，不指某个合法实验实际产生负概率。
效果可以数学表示，也不自动获得实施它的联合测量装置。

**白话图景。**虽然矛盾绕着很长的一圈，它一旦被找出来，只需问一个合成事件及其补事件，
就会出现“一负、一大于一”的报告。
三维球负责把这个失败画清楚；寻找并组成这个事件，仍然用到了整圈的关系。

<a id="section-15"></a>

## 15. 奇环的精确噪声阈值与共同零支撑

<a id="sec-c92-odd-cycle-noise"></a>

这个反例还可以把前述内部噪声定理完全算成解析式。
由共同单点边际取内部乘积参照
$\tau_n=I/2^n$，保留率记为 $\eta\in[0,1]$。
混合资料的边相关为

$$
r_\eta=\eta r=-\eta\frac{n-1}{n}.
$$

### 定理 15.1（全部规模上的锐阈值）

<a id="thm-c92-odd-cycle-noise"></a>

上述混合边际存在共同全态，当且仅当

<a id="eq-c92-odd-cycle-noise-threshold"></a>

$$
0\le\eta\le\eta_*:=\frac{n-2}{n-1}.
\tag{15.1}
$$

所以最小参照噪声为 $1/(n-1)$。
相对于 $\tau_n$ 的内部最小值恰为

<a id="eq-c92-odd-cycle-alpha"></a>

$$
\alpha_n=-\frac1{n-2}.
\tag{15.2}
$$

任意阈值补全都支撑于 $\ker W_n$；这个零空间维数为 $2n$。

**证明。**
必要性由同一算符界给出：

$$
nr_\eta=-\eta(n-1)\ge2-n,
$$

即 $\eta\le(n-2)/(n-1)$。

为证明充分性，取所有恰有一条同向边、其余 $n-1$ 条反向边的配置。
每次指定唯一同向边及第一个自旋，就唯一决定整个配置；
$n-1$ 为偶数保证绕圈一致，因而共有 $2n$ 个不同配置。
在这些配置上取均匀对角态 $\sigma_*$。
每条边成为同向边的概率是 $1/n$，反向的概率是 $(n-1)/n$，所以其相关为

$$
r_*=-\frac{n-2}{n}=\eta_*r.
$$

全局自旋翻转将配置成对配平，故每个单点均匀。
一个二值对的两个单点均匀及相关 $r_*$，唯一给出
$(1+r_*x_ix_j)/4$ 的边分布。
因此 $\sigma_*$ 确实实现阈值处的每个完整边际，而不只实现一项期望。
对 $0\le\eta\le\eta_*$，取

$$
\sigma_\eta
 =\frac\eta{\eta_*}\sigma_*
  +\left(1-\frac\eta{\eta_*}\right)\tau_n.
$$

其边相关为 $\eta r$，单点仍均匀，给出所需补全。

接着核定内部最小值。由 $\operatorname{Tr}(\tau_nW_n)=n-2$，
$\widehat W_n=W_n/(n-2)$ 在其定义的归一正集合中可行，并给
$\ell(\widehat W_n)=-1/(n-2)$。
反过来，对任何归一正 $W$，阈值补全给

$$
0\le\operatorname{Tr}(\sigma_*W)
 =\eta_*\ell(W)+(1-\eta_*)\operatorname{Tr}(\tau_nW)
 =\eta_*\ell(W)+1-\eta_*.
$$

所以 $\ell(W)\ge-1/(n-2)$，证明式 [(15.2)](#eq-c92-odd-cycle-alpha)。
这与式 [(13.3)](#eq-c92-noise-threshold) 的
$\eta_*=1/(1-\alpha_n)$ 完全一致。

任意阈值补全都使正算符 $W_n$ 的期望为零，因而支撑于 $\ker W_n$。
共同本征基中 $W_n$ 为零恰好要求有 $n-1$ 条反向边，
故零空间恰由上述 $2n$ 个配置张成。
这里给出的是一份显式补全及全部阈值补全的支撑限制，不据此宣称全态唯一。

**白话图景。**这个闭环矛盾还能精确衡量需要撤回多少关系强度。
混入由各点自身读数构成的独立参照，恰好达到阈值时，整体只能落在同一份见证的零空间里。
在那里，每个配置都留下唯一一条同向边。
见证、三维球外距离、所需噪声和允许整体的支撑，于是属于同一个可核算结构。

<a id="section-16"></a>

## 16. 所有有限资料都相容，怎样得到同一个可数整体

<a id="sec-c92-countable-extension"></a>

前述奇环说明，不能把全部有限检查换成某个固定大小窗口。
下面证明真正的*每个有限资料集合都通过*足以得到可数整体。
它为项目 $\Omega$ 主稿中先假定相容局部态、再作无限延拓的步骤，
供应一个有限资料入口 [9](#ref-omega)。

### 定义 16.1（可数局部资料）

系统由可数个非零有限维 Hilbert 空间 $H_1,H_2,\ldots$ 组成。
对有限前缀记

$$
H_{1:n}=\bigotimes_{i=1}^nH_i,\qquad
 \mathfrak A_n=M(H_{1:n}),
$$

以 $X\mapsto X\otimes I_{H_{n+1}}$ 作为共享单位的嵌入。
给定由有限非空子集组成的任意族 $\mathcal F$，对每个 $S\in\mathcal F$ 指定一个密度态
$\rho_S$。每个子集只给一份指定态；同一子集上的重复而冲突的资料可先作为有限失败处理。

### 定理 16.2（有限 C92 与可数整体态存在等价）

<a id="thm-c92-countable-extension"></a>

以下条件等价：

1. 对每个有限 $\mathcal F_0\subseteq\mathcal F$，该有限边际资料满足 C92；

2. 存在一套相容的前缀密度态 $(\widehat\rho_n)_{n\ge1}$，使


   $$
   \operatorname{Tr}_{n+1}\widehat\rho_{n+1}=\widehat\rho_n,
   $$


    且其局部边际实现全部 $\rho_S$；

3. 拟局域 $C^*$ 代数


   $$
   \mathfrak A
     =\overline{\bigcup_n\mathfrak A_n}^{\|\cdot\|}
   $$


    上存在实现全部资料的正归一线性泛函 $\omega$。

**证明。**
先证 $1\Rightarrow2$。
固定前缀 $[n]=\{1,\ldots,n\}$，其中至多有 $2^n-1$ 个非空子集。
因此全部 $S\in\mathcal F$、$S\subseteq[n]$ 构成有限资料。
定理 [4.1](#thm-c92-extension) 给出共同态；对未被该资料覆盖的前缀点，
张量一个均匀态即可得到前缀上的状态 $\sigma_n$。
若前缀没有约束，也可直接取均匀态。
这些选择只证明数学存在，不要求不同 $n$ 的 $\sigma_n$ 预先一致。

对每个固定 $k$，$n\ge k$ 时定义

$$
\sigma_n^{(k)}=\operatorname{Tr}_{k+1:n}\sigma_n.
$$

它们位于有限维密度矩阵的紧集内。
先选使 $k=1$ 的边际收敛的子列，再在其内选使 $k=2$ 收敛的子列，依次进行。
取递增的对角子列 $n_j\ge j$，则对每个固定 $k$ 都存在

$$
\widehat\rho_k=\lim_{j\to\infty}\sigma_{n_j}^{(k)}.
$$

有限维中可用迹范数取极限。正性与迹一是闭条件，
部分迹连续则给
$\operatorname{Tr}_{k+1}\widehat\rho_{k+1}=\widehat\rho_k$。
任意给定 $S\in\mathcal F$ 包含于某个前缀；
所有充分大的 $\sigma_{n_j}$ 都实现 $\rho_S$，故极限也实现它。

再证 $2\Rightarrow3$。
在局部代数并集上，对 $X\in\mathfrak A_n$ 定义

<a id="eq-c92-local-state"></a>

$$
\omega(X)=\operatorname{Tr}(\widehat\rho_nX).
\tag{16.1}
$$

精确相容性保证该定义不依赖所选前缀。
它复线性、保伴随、归一且正；有限态的 Cauchy–Schwarz 不等式给

$$
|\omega(X)|^2\le\omega(X^\dagger X)\le\left\lVert X\right\rVert^2.
$$

所以它唯一连续延拓到范数闭包 $\mathfrak A$。
要验证闭包上的正性，给定 $a\in\mathfrak A$、$a\ge0$，
取局部 $b_m\to a^{1/2}$，则 $b_m^\dagger b_m\to a$。
由连续性和局部正性，
$\omega(a)=\lim_m\omega(b_m^\dagger b_m)\ge0$。
局部资料由式 [(16.1)](#eq-c92-local-state) 保留。

最后，$3\Rightarrow1$：把 $\omega$ 限制到包含任意给定有限资料的前缀代数。
有限矩阵迹对偶将该归一正泛函写成一个密度矩阵，它实现那些边际；
再由定理 [4.1](#thm-c92-extension) 得有限资料的 C92。

若一个前缀内允许无限多条单独读出约束，而不先合成一份边际态，
仍可使用同一结论：每条等式在前缀密度态紧集中定义闭集；
每个有限交非空，紧性使全部交非空，因而仍能先选择 $\sigma_n$。
这是对资料形式的补充，不减弱“每个有限集合都通过”的量词。

**白话图景。**局部窗口可以一层层扩大，但每次任意挑一个补全，它们未必自动接成同一个整体。
紧性允许在所有这些候选中选出一条逐层稳定的子列：先稳定第一层，再稳定第二层，继续下去。
最终每一层都保留旧层的全部读数，因而给同一套整体响应。
这一存在证明仍不保证当前资料唯一确定了整体。

<a id="section-17"></a>

## 17. 由整体正响应到 Hilbert 关系核：GNS 的完整接口

<a id="sec-c92-gns"></a>

上一节得到的是 $\mathfrak A$ 上的态 $\omega$。
它进一步给出一个共同的 Hilbert 表示。这里使用标准 GNS 构造
 [4](#ref-gns)、[9](#ref-omega)，把有限证书如何接到通常量子载体写清楚；
共同复代数与正序结构仍是本轮的声明前件。

### 定理 17.1（正响应的循环表示）

<a id="thm-c92-gns"></a>

定义

$$
k(a,b)=\omega(a^\dagger b),\qquad
 \mathcal N_\omega=\{a\in\mathfrak A:\omega(a^\dagger a)=0\}.
$$

则 $k$ 是正关系核，商空间 $\mathfrak A/\mathcal N_\omega$ 的内积为

$$
\langle[a],[b]\rangle=\omega(a^\dagger b).
$$

它的完备化 $H_\omega$ 上存在含幺 $*$ 表示 $\pi_\omega$ 与单位循环向量
$\Omega_\omega$，满足

<a id="eq-c92-gns-representation"></a>

$$
\omega(a)=\langle\Omega_\omega,\pi_\omega(a)\Omega_\omega\rangle,
 \qquad
 \overline{\pi_\omega(\mathfrak A)\Omega_\omega}=H_\omega.
\tag{17.1}
$$

对已经固定的同一个 $\omega$，这种循环表示唯一到保持循环向量的酉等价。

**证明。**
对任意有限 $a_i\in\mathfrak A$ 与复数 $c_i$，正性给

$$
\sum_{i,j}\overline{c_i}k(a_i,a_j)c_j
 =\omega\!\left[
   \left(\sum_i c_ia_i\right)^\dagger
   \left(\sum_j c_ja_j\right)\right]\ge0.
$$

通过考察 $\omega((a+zb)^\dagger(a+zb))\ge0$ 的复数二次式，得到

$$
|\omega(a^\dagger b)|^2
 \le\omega(a^\dagger a)\omega(b^\dagger b).
$$

因此零范数元与全部元正交，零元集合是线性空间，商上的内积良定义且正定。

对 $b\in\mathfrak A$，$C^*$ 正序给
$b^\dagger b\le\left\lVert b\right\rVert^2 I$，所以

<a id="eq-c92-gns-left-bound"></a>

$$
\omega(a^\dagger b^\dagger ba)
 \le\left\lVert b\right\rVert^2\omega(a^\dagger a).
\tag{17.2}
$$

若 $a\in\mathcal N_\omega$，右侧为零，故 $ba\in\mathcal N_\omega$；
这证明 $\mathcal N_\omega$ 是左理想。
于是左乘

$$
\pi_\omega(b)[a]=[ba]
$$

在商空间上良定义。
式 [(17.2)](#eq-c92-gns-left-bound) 给其范数不超过 $\left\lVert b\right\rVert$，
故它唯一有界延拓到 $H_\omega$。
乘法与单位性质由左乘直接成立，且

$$
\langle[x],\pi_\omega(b)[y]\rangle
 =\omega(x^\dagger by)
 =\langle\pi_\omega(b^\dagger)[x],[y]\rangle,
$$

所以该映射保持伴随。

取 $\Omega_\omega=[I]$，由 $\omega(I)=1$ 得其范数一，
且 $\pi_\omega(a)\Omega_\omega=[a]$，这些向量按定义稠密。
式 [(17.1)](#eq-c92-gns-representation) 随即成立。
若 $(H',\pi',\Omega')$ 是同一态的另一循环表示，
映射 $[a]\mapsto\pi'(a)\Omega'$ 保持全部内积，
由两边的循环性延拓为所需酉映射。

这里还得到精确的内容等价：

$$
[a]=[b]
 \iff
 \omega\bigl((a-b)^\dagger(a-b)\bigr)=0.
$$

左理想性质保证，零区别在任何相同的左续接后仍为零。
因此“同内容取同地址”在这个表示中是一个有明确比较范围的商定义。
所有有限 Gram 正性由同一个 $\omega$ 保证，而非逐对选取互不相容的局部实现。

### 17.1 存在、唯一与纯性各自的量词

从部分边际资料出发，上一节通常只保证*存在*至少一个 $\omega$。
对角子列可能选择不同的完整相容前缀族。
如果整个前缀族 $(\widehat\rho_n)$ 已经固定，它在拟局域代数上的连续延拓才唯一；
如果 $\omega$ 已固定，它的循环表示才具有上一定理的酉唯一性。
这三个层次不能合并成“部分资料决定唯一整体”。

也没有推出在预先指定的无限张量积 Hilbert 表示中存在迹类密度算符。
GNS 循环向量当然能在其自己的表示空间上构成秩一算符，
但这不识别它与另一预先选定表示，也不补出那一表示中的正规性。

最后，单位循环向量不意味着原代数态纯。
例如可数 qubit 的局部均匀态族
$\widehat\rho_n=I_{2^n}/2^n$ 给出一个整体态。
它是两份不同态的等权混合：第一份在首点为 $\lvert 0\rangle\langle 0\rvert$，
第二份为 $\lvert 1\rangle\langle 1\rvert$，其余点都保持均匀乘积。
这两份态分别具有相容前缀

$$
\lvert b\rangle\langle b\rvert\otimes\frac{I_{2^{n-1}}}{2^{n-1}},\qquad b=0,1.
$$

它们由上一节延拓，并在首点读出上不同，故均匀整体态非纯；
然而它仍有式 [(17.1)](#eq-c92-gns-representation) 的单位循环向量。
$\Omega_\omega$ 在这里是所选表示的根向量，不能仅凭记号就等同于项目全部内部结构的 $\Omega$。

**白话图景。**每个有限合成比较都合法，并且这些比较真正属于同一份资料，
就能得到一套共同的整体响应。用这套响应比较“先做哪段内容、再做哪段内容”，
自然形成一个正关系核；把完全没有区别的方向合并，再补齐极限，就得到 Hilbert 空间。
循环根向量把这份响应统一表示出来，但当前资料可能仍允许别的整体响应，
而根向量的存在也不会把混合态自动变成纯态。

<a id="section-18"></a>

## 18. 同一相容条件怎样成为量子通道与不可克隆的约束

<a id="sec-c92-channels"></a>

前面的边际问题也可以描述“同一个输入能否同时接上两个输出”。
关键是保留一个共同内部参考，将过程写成参考与输出之间的关系态。
这使用项目 V78、V80 已声明的参考复合接口；下面展开标准的有限 Choi–Kraus
论证 [7](#ref-v78)、[11](#ref-v80)、[3](#ref-watrous)，不另外提出一个 C93。

### 定义 18.1（过程的共同参考记录）

设输入空间 $H_Q$ 维数为 $d$，内部参考 $H_B$ 与它同维并有已对齐的基。
记

$$
\lvert \Gamma\rangle_{BQ}=\frac1{\sqrt d}\sum_{j=1}^d\lvert j\rangle_B\lvert j\rangle_Q.
$$

对复线性、保 Hermitian 的候选过程 $\Lambda:M(H_Q)\to M(H_O)$，
定义归一 Choi 表

<a id="eq-c92-choi"></a>

$$
J_\Lambda=(\operatorname{id}_B\otimes\Lambda)(\lvert \Gamma\rangle\langle \Gamma\rvert)
 =\frac1d\sum_{i,j}\lvert i\rangle\langle j\rvert\otimes\Lambda(\lvert i\rangle\langle j\rvert).
\tag{18.1}
$$

它起初只是候选关系表；没有先把它宣称为合法态。

### 定理 18.2（参考记录的正性与完整过程）

<a id="thm-c92-choi-channel"></a>

候选 $\Lambda$ 为完全正且保迹，当且仅当

<a id="eq-c92-channel-conditions"></a>

$$
J_\Lambda\ge0,\qquad \operatorname{Tr}_O J_\Lambda=I_B/d.
\tag{18.2}
$$

在保迹前件下，$J_\Lambda$ 的正性正是对完整参考记录使用 C92 的单 patch 情形。
若只给若干输出边际的 Choi 记录，它们满足 C92 当且仅当存在一份共同正记录；
只要共同参考边际已锁定为 $I_B/d$，它就对应一个共同 CPTP 过程。

**证明。**
若 $\Lambda$ 完全正，式 [(18.1)](#eq-c92-choi) 的输入为正，故 $J_\Lambda\ge0$。
保迹逐个矩阵单位给出
$\operatorname{Tr}\Lambda(\lvert i\rangle\langle j\rvert)=\delta_{ij}$，因此 $\operatorname{Tr}_OJ_\Lambda=I_B/d$。

反之，将正矩阵写为有限秩一和
$J_\Lambda=\sum_\alpha\lvert v_\alpha\rangle\langle v_\alpha\rvert$，
把本征值平方根吸收入 $v_\alpha$。
逐个定义 $M_\alpha:H_Q\to H_O$，使

$$
\lvert v_\alpha\rangle=\frac1{\sqrt d}\sum_j\lvert j\rangle_B\otimes M_\alpha\lvert j\rangle_Q.
$$

比较式 [(18.1)](#eq-c92-choi) 的全部 $B$ 端矩阵块，得到

$$
\Lambda(X)=\sum_\alpha M_\alpha X M_\alpha^\dagger.
$$

对任意额外有限参考 $R$，每项
$(I_R\otimes M_\alpha)Y(I_R\otimes M_\alpha^\dagger)$
都将 $Y\ge0$ 送至正矩阵，故 $\Lambda$ 完全正。
参考边际条件给
$(\sum_\alpha M_\alpha^\dagger M_\alpha)^{\mathsf T}=I$，
从而 $\sum_\alpha M_\alpha^\dagger M_\alpha=I$，证明保迹。
Choi 的逐块定义也证明该对应为一一对应。

对多份局部 Choi 记录使用定理 [4.1](#thm-c92-extension)。
共同记录的参考边际由任一给定记录固定，
故每个共同正归一态延拓都满足式 [(18.2)](#eq-c92-channel-conditions)。
再用刚证明的一一对应，即得共同过程。

数学表示中参考位于同一个整体，且其校准已经声明。
这不要求复制一个未知输入，也不从矩阵存在自动推出实验室已具有相应控制设备。

**白话图景。**要检查一扇门是否真能工作，可以保留一份它与内部参考的完整关系记录。
记录中任意合成事件都合法，就能把这份记录拆成一组线性分支，得到通常的量子通道。
若两个出口都声称来自同一个输入，它们的参考记录还必须接成同一份整体记录；
分别看起来合法，不足以保证两个承诺能一起实现。

### 18.1 双 Bell 椭圆就是通用 qubit 复制的精确边界

对 qubit，定义各向同性收缩通道

$$
\Lambda_v(X)=vX+(1-v)\operatorname{Tr}(X)I_2/2,
 \qquad -1/3\le v\le1.
$$

它的归一 Choi 态正是前文的
$\sigma_v=v\Phi+(1-v)I_4/4$。
这里“两个出口实现 $\Lambda_v,\Lambda_w$”指存在
$\mathcal C:M_2\to M_2\otimes M_2$，使其两个约化通道分别等于它们。

### 定理 18.3（同一个 C92 给出的通道椭圆与不可克隆）

<a id="thm-c92-cloning"></a>

当 $v,w\ge0$ 时，两个上述通道能够由一个共同 CPTP 过程实现，当且仅当

<a id="eq-c92-channel-ellipse"></a>

$$
\boxed{v^2+w^2+vw\le v+w.}
\tag{18.3}
$$

在对称情形 $v=w$，最大保留率为 $2/3$；
此时对任意纯输入的单个出口保真度
$\langle \psi\rvert\Lambda_v(\lvert \psi\rangle\langle \psi\rvert)\lvert \psi\rangle$
最多为 $5/6$，且该值能达到。
特别地，不存在对任意未知 qubit 态都给出两个完美副本的 CPTP 过程。

**证明。**
给输入加上同一个参考 $B$。共同过程的 Choi 态在 $AB$、$BC$ 上的边际
必须分别为 $\sigma_v$、$\sigma_w$。
反过来，任何这两份边际的共同正归一态都有 $B$ 边际 $I_B/2$，
由定理 [18.2](#thm-c92-choi-channel) 对应一个共同 CPTP 过程，
并由 Choi 对应的单射性得到指定的两个约化通道。
所以问题与定理 [11.1](#thm-c92-isotropic-ellipse) 完全等价。

代入 $w=v\ge0$，得到 $3v^2\le2v$，即 $v\le2/3$。
纯输入的单出口保真度为
$v+(1-v)/2=(1+v)/2$，从而上界为 $5/6$。
前文 $\tau_+$ 的参考边际为 $I_B/2$，
故其对应通道达到 $v=w=2/3$。
完美复制要求 $v=w=1$，违反式 [(18.3)](#eq-c92-channel-ellipse)。
更一般地，若两个约化通道对所有纯态均为恒等，由纯态张成 Hermitian 空间，
线性性使两个约化通道都等于恒等通道，仍归入该反例。

这些数值与椭圆属于已有通用非对称量子克隆理论 [2](#ref-npr2021)。
本轮把它们从同一个边际相容候选中接出，并给出有效 qubit 球的显式几何。
结论针对任意未知输入的通用过程；一组已经声明的相互正交状态可以被区分并复制。

**白话图景。**不能把未知量子内容随意复制成两个完整出口，因为每个出口都会向同一个参考承诺一份关系。
两份承诺都做到百分之百，就超过整体能容纳的谱界。
允许两边都退一点，正好出现椭圆边界；两边公平分配时，各保留三分之二的 Bloch 方向，
单个出口对原纯态的保真度就是六分之五。
这条限制来自两份关系必须属于同一个整体。

<a id="section-19"></a>

## 19. 如何接回现有量子力学：完整链条与每一步的前件

<a id="sec-c92-reconstruction"></a>

本轮延续项目已完成的条件式重构，不把既有结果再次改写成笼统待解问题。
V79 在既定正比较、总强度与共同复方向上，
由二元反向相容及有限相位校准得到复效果与二次读出；
V80 在共同相干接口上，由完整强度、有限定向锚和二元差分不增，
把实际完整后继锁为同一个复线性等距 [10](#ref-v79)、[11](#ref-v80)。
v90–v91 进一步处理共同恢复和 Markov 拼接。
本轮 C92 补上任意局部资料的共同正归一态存在条件，不要求 Markov 性。

### 19.1 由完整分支、正读出到标准有限理论

设前序条件已给实际等距
$V:H\to\bigoplus_e H_e$，记各结果分支为 $M_e=P_eV$。
于是

<a id="eq-c92-reconstruction-effects"></a>

$$
\sum_eM_e^\dagger M_e=V^\dagger V=I,\qquad
 E_e=M_e^\dagger M_e\ge0.
\tag{19.1}
$$

这同时给出完整效果菜单。
若分支输出已声明为 $H_e=K_e\otimes R_e$，而 $R_e$ 是未读出的细记录，
取其正交基 $\{\lvert \alpha\rangle\}$，定义
$M_{e\alpha}=(I_{K_e}\otimes\langle \alpha\rvert)M_e$，即得

$$
\mathcal I_e(\rho)=\sum_\alpha
       M_{e\alpha}\rho M_{e\alpha}^\dagger,\qquad
 p_e=\operatorname{Tr}\mathcal I_e(\rho)=\operatorname{Tr}(\rho E_e).
$$

当 $p_e>0$，条件态为 $\mathcal I_e(\rho)/p_e$；
保留结果标签时，总输出为 $\bigoplus_e\mathcal I_e(\rho)$；
若各 $K_e$ 已识别为同一个输出空间且丢弃标签，才写为
$\sum_e\mathcal I_e(\rho)$。
这里的测后态由已声明的实际分支决定，不能只凭一组效果反推出唯一仪器。

在有限完整效果空间上，非负、单位归一、合法细分可加且与菜单表达无关的响应，
延拓为 Hermitian 空间上的实线性泛函，再由迹对偶写成 $\operatorname{Tr}(\rho\,\cdot)$；
秩一正测试与单位测试分别给 $\rho\ge0$、$\operatorname{Tr}\rho=1$。
纯态是密度态集合的秩一极点：
秩大于一时可对两个正本征值作相反小扰动分解成两态；
秩一时任何正凸分解的支撑都被锁在同一条射线上，故无法非平凡分解。
因此纯态、锐投影情形给出熟悉的平方律

$$
p_\phi(\psi)=
 \operatorname{Tr}(\lvert \psi\rangle\langle \psi\rvert\lvert \phi\rangle\langle \phi\rvert)
 =|\langle\phi,\psi\rangle|^2
 \quad(\|\phi\|=\|\psi\|=1).
$$

在本轮从一般 Hermitian 局部资料出发时，
C92 自己给出局部正性、归一与共同密度态，随后全部局部概率由同一迹配对承接。
但线性响应的载体和共同复结构仍是明确的继承前件。

**白话图景。**先把所有实际结果保留下来，完整变化便是一扇保持总强度的线性门。
只看某个出口，就得到一个效果与一条条件更新；把所有出口相加，总概率仍为一。
当不同局部窗口都在描述这同一个整体，C92 再保证它们使用的是同一份量子状态，
而不是每个窗口各自选一份互相冲突的解释。

| 通常的规则 | 本项目中的推导接口 | v92 的准确角色 |
|---|---|---|
| 复 Hilbert 载体 | 共同复正核、零关系商与完备化；共同复方向保留其供应条件。 | 所有有限资料相容给整体正响应，再由 GNS 得共同表示；未从 C92 单独选择复数域。 |
| 密度态与纯态 | 完整效果响应的正性、归一、可加性，及密度态凸几何。 | 一般 Hermitian 局部表通过 C92，即具有共同密度态；部分资料通常不唯一决定它。 |
| Born 平方律与 POVM | V79 二元反向约束、共同相位校准；V80 完整等距的分支效果及同根读出。 | 全部局部 Born 读数可由同一个正响应承接；读出与状态资格不再逐窗口分裂。 |
| 组合与纠缠 | 声明的积核、产品张成及相应局部作用，给张量积表示。 | 在该组合接口内完整刻画边际存在性，允许非 Markov、纠缠的共同全态。 |
| 仪器与 CPTP | 实际细分支的 Kraus 形式；保留内部参考后仍为正。 | 局部 Choi 记录有共同正延拓且参考边际正确，当且仅当存在共同通道。 |
| 锐观测与投影更新 | 效果区间极点为投影；赋实标签给自伴可观测量。理想 Lüders 更新另需相应不扰动条件。 | 同一效果的不同局部表达必须相同；仅有效果不唯一决定测后态。 |
| 酉演化与薛定谔式 | 同维完整单分支等距为酉；实际可微历史给自伴生成元，自治还需群条件。 | 共同状态存在条件与这些过程规则相容；C92 本身不供应时钟或哈密顿量。 |
| 不确定性 | 同一个正响应的 Cauchy–Schwarz 与非对易关系。 | 在任何共同延拓中都成立；当前资料未固定的交叉项仍可随延拓而变。 |
| 可数整体 | 相容局部态、拟局域代数与 GNS。 | 将“预先有相容族”推进为“每个有限资料集合通过 C92”，给出存在性入口。 |

### 19.2 酉历史、生成元与不确定性怎样在同一个整体内出现

在同一有限维输入输出上，完整单分支满足 $U^\dagger U=I$；
有限维同维使它也满足 $UU^\dagger=I$。
若实际历史 $U(t)$ 为 $C^1$，定义

$$
H(t)=i\hbar\dot U(t)U(t)^\dagger.
$$

对 $U(t)U(t)^\dagger=I$ 求导给
$\dot U U^\dagger+U\dot U^\dagger=0$，所以 $H(t)=H(t)^\dagger$。
对 $\psi(t)=U(t)\psi(0)$，直接得到

$$
i\hbar\dot\psi(t)=H(t)\psi(t).
$$

若进一步 $U(t+s)=U(t)U(s)$，同维有限情形给固定生成元
$U(t)=\exp(-itH/\hbar)$。
这是在已有实际时间参数下的表示定理；没有从静态相容性算出 $\hbar$ 的物理标尺。

对同一个共同态 $\omega$ 和自伴 $A,B$，记
$\Delta A=A-\omega(A)I$、$\Delta B=B-\omega(B)I$。
GNS 正核的 Cauchy–Schwarz 给

$$
\operatorname{Var}_\omega(A)\operatorname{Var}_\omega(B)
 \ge|\omega(\Delta A\Delta B)|^2
 \ge\frac14|\omega([A,B])|^2.
$$

因此不确定性界来自同一个正关系核及其非对易方向。
某个具体态上交换子的期望可能为零，乘积下界也可能为零；
不能仅凭“关系总有关系”就声称每个量都有普遍严格正的最小误差。

**白话图景。**同一套正比较先保证状态和读数能放在一起；
保持完整关系的同维单出口变化就是酉门。
再用内部时钟连续地给这些门编号，切向变化才写成哈密顿量与薛定谔方程。
两个读出方向若不能对易，它们的共同正关系会限制可同时达到的精度。
时间标尺、实际相互作用和具体场仍需要各自的关系定义。

<a id="section-20"></a>

## 20. 反向审计：撤去哪里，就在哪一对关系上失败

<a id="sec-c92-audit"></a>

本轮的反向逻辑是一个充要定理，强于只列举若干坏例子。
在已声明的有限复组合背景下，任意局部资料若没有共同全态，
最近点分离必定给出某个 $h$ 违反 C92。
单位归一与同一算符表达的一致性须先通过常数及零关系检查。
通过后，非退化谱见证可归一为二元对象 $E$ 与 $I-E$，
其失败成为一个球外报告；退化谱见证仍按前文的常数情形处理。
更大的承接结构依次是算符系统上的正泛函、全矩阵代数上的密度态、
以及可数相容情况下的拟局域态与 GNS 表示。

| 删去或混淆的条件 | 可以准确指出的后果 |
|---|---|
| 单位与正负关系都须校验 | 若只用未归一的二元效果上界，零表也能通过，故不能代表完整概率读出。 |
| 同一算符表达给同一响应 | $W(h)=0$ 却 $b_R(h)\ne0$；同一零关系取得两个数值。 任何正保留率的共同噪声仍留下冲突。 |
| 允许全部有限合成比较 | 任意奇环例子中，每个真边子集都合法，而完整环违反谱界； 固定大小窗口不能普遍取代整体比较。 |
| 只要求重叠处边际相同 | 双 Bell 在共享点均为 $I/2$，仍不能同时完美； 共同正性比重叠一致更强。 |
| 把 C91 当作所有量子态的资格 | 双 $\sigma_{2/3}$ 有共同纠缠延拓，却没有以中间 qubit 为条件的 Markov 延拓； 会误删合法量子资料。 |
| 把一个二元概率当作完整相干态 | 相同 $q$ 可配不同 $\gamma$；第三轴与相干读口不能从概率总量凭空推出。 |
| 把三维报告当作固定三维整体 | 见证可能涉及任意长的环；输出三个坐标不消除组成该见证所需的全部关系。 |

### 20.1 内容地址、平方闭合与参照变化的精确含义

在已固定的 $\omega$ 中，GNS 地址等价为

$$
a\sim_\omega b
 \quad\Longleftrightarrow\quad
 \omega((a-b)^\dagger(a-b))=0.
$$

同一个左续接 $c$ 保持这种等价，因为零元形成左理想。
这是一个相对于已声明来源和比较范围的内容商。
它不自动对所有右侧换源操作封闭：
例如取 $P_1=\lvert 1\rangle\langle 1\rvert$，在 $\lvert 0\rangle$ 来源下，$P_1\lvert 0\rangle=0$；
先从右边加入翻转 $X$ 后，$P_1X\lvert 0\rangle=\lvert 1\rangle$。
因此当前内容地址可以在同一延续中可靠使用，而换了输入上下文须重新比较。

平方律使读出落在正二次形式及其稳定归一结构中。
它不意味着所有关系检查会在某个统一有限递归深度停止。
任意奇环已经给出反例：每个较小层都闭合，新增一整圈仍可出现更高层约束。
本轮证明的是*每个有限矛盾均有有限合成二元见证*，
而不是一个固定球同时保存全部递归内容。

若各站点换酉坐标，且所有重叠窗口使用同一套变换，
即 $U=\bigotimes_iU_i$、$U_C=\bigotimes_{i\in C}U_i$，令
$\rho_C\mapsto U_C\rho_CU_C^\dagger$、
$h_C\mapsto U_Ch_CU_C^\dagger$，
则合成读数和谱界不变；前文精确误差也不变。
单点乘积参照随资料协变，序半径亦保持。
这给“参照改写不影响关系资格”一个明确版本。
任意改变物理状态、动力学或把不同参照强行保持同一数值，不属于单纯坐标改写。
空间各向同性还涉及旋转如何作用于实际空间关系，不能仅由名称相同代替其证明。

**白话图景。**内容地址必须带着它所比较的内部上下文。
在同一来源下已经完全相同的两段内容，再接同一段后继仍然相同；
换了来源，就要重新比较。
平方律让每一次合法比较有稳定的归一方式，而全部关系能否共存，
仍由任意有限合成后的相容性把关。改变描述坐标不会改变答案。

<a id="section-21"></a>

## 21. 与当前量子研究的接点及本轮完成的范围

<a id="sec-c92-frontier"></a>

2026 年的 *Fully Quantum Inflation* 将量子边际问题的限制用于量子因果推断，
研究给定因果网络能否产生指定量子态 [5](#ref-inflation2026)。
这为“关系的关系”提供一个具体的当代问题入口：
局部量子对象不仅各自要合法，还须共同服从产生它们的结构。
但因果网络中的独立源等条件比普通边际共同延拓更强；
该文的 triangle 因果场景也不等同于本文的三条边际构成一个三角环。
C92 精确解决的是这里已声明的普通共同态存在性。

本轮的可数延拓与 GNS 把这一存在性接到代数量子理论，
对应 AQFT 的标准状态–表示接口 [4](#ref-gns)。
相对论量子场还需要局域代数网、因果相容、对称作用、谱条件以及动力学。
这些不是仅由正性与紧性自动得到的结果。
因此本稿没有据此宣称统一场论已经完成，
也没有据此宣称解决 Yang–Mills 存在性与质量间隙问题。

本轮实质上完成三项闭合。
第一，单一 C92 与共同全态存在之间有完整充要证明。
第二，失败可同时量化为二元读出超额、边际最小改动与内部参照噪声，
并在三角环、双 Bell 与任意奇环上给出锐值。
第三，双 Bell 的关系球投影产生精确椭圆，接出通道兼容及通用复制界；
所有有限资料相容则进一步接成可数整体及 Hilbert 表示。
这些定理让前序量子重构的局部接口真正拥有共同的整体实现。

### 21.1 本轮完整白话

**白话图景。**量子可以先理解为一套必须共同成立的内部关系。
每个局部窗口都给出一部分内容，也给出一些能回答的是非问题；
门把内容继续接下去，测量把它与某个内部参考比较。
如果不同窗口确实来自同一个整体，
那么把它们的问题合成同一个问题以后，它们承诺的答案就必须落在这个问题自身允许的范围里。

这就是本轮的新条件。
它失败时，不必泛泛地说整体不协调：
单位与表达没有对齐时，矛盾先在单位或零事件上出现；
通过这些检查后，一定能找出一个具体事件及其补事件，
让候选答案变成一负、一大于一，在三维球上落到外面。
它对全部有限合成都成立时，则确实存在一份共同量子状态，
不是每个窗口各选一个互相矛盾的替身。

在本轮双 Bell 模型中，两条共享同一部分的量子关系，
成为同一个有效球上的两条读出轴。
轴之间带固定夹角，球的读出影子就成为椭圆；
在非负保留率范围内，两条关系不能越过这个椭圆还声称同时属于一个整体。
未知内容不能完美复制到两个出口，就是这种共同承诺超过边界的一个例子。
如果原资料稍微越界，需要退多少关系强度、修改多少读数，也能精确计算。

沿着已有项目的重构链，正比较形成 Hilbert 载体，
完整分支形成效果和量子仪器，平方读出形成 Born 规则，
同维完整单出口形成酉门，可微门历史形成薛定谔方程。
本轮再让这些局部结构真正接成同一份整体响应，并能逐层接到可数系统。
公理于是具有明确的内部含义：同一内容的不同定义必须相容。
它选择并刻画一种可以共同成立的关系结构，
其实际物理范围仍由已声明的载体、比较、组合与实验关系负责。

<a id="references"></a>

## 来源、版本与核读范围

<a id="ref-hall2007"></a>

### [1]

William Hall, *Compatibility of subsystem states and convex geometry*,
Physical Review A **75**, 032102 (2007).
[doi:10.1103/PhysRevA.75.032102](https://doi.org/10.1103/PhysRevA.75.032102)；
[作者全文](https://arxiv.org/pdf/quant-ph/0610031)。
本轮核读 Theorem 4、Proposition 3 的凸相容体、分离见证、
局部算符合成及表达非唯一性。C92 使用这一标准数学基础，
正文另给任意有限 patch 族的最近点证明，不主张兼容见证定理的新颖性。

<a id="ref-npr2021"></a>

### [2]

Ion Nechita, Clément Pellegrini and Denis Rochette,
*A geometrical description of the universal $1\to2$ asymmetric quantum cloning region*,
Quantum Information Processing **20**, 333 (2021).
[doi:10.1007/s11128-021-03258-y](https://doi.org/10.1007/s11128-021-03258-y)；
[arXiv 记录](https://arxiv.org/abs/2106.09655)；
[全文](https://arxiv.org/pdf/2106.09655)。
本轮核读 Theorem 1 的一般椭圆区域与后续两份 isotropic 边际、通用克隆接口。
正文对 $d=2$ 给显式重复二维块、完整边际构造及负参数凸包证明。
$2/3$、$5/6$ 与椭圆均按既有结果引用。

<a id="ref-watrous"></a>

### [3]

John Watrous, *The Theory of Quantum Information*,
Cambridge University Press, 2018.
[作者公开预出版稿](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)。
本轮核读第 2 章 Theorem 2.22、Theorem 2.26、Corollary 2.27，
用于 Choi 正性、Kraus 形式、完全正与保迹的标准等价。
正文采用迹为一的 Choi 约定，故参考边际为 $I/d$。

<a id="ref-gns"></a>

### [4]

Christopher J. Fewster and Kasia Rejzner,
*Algebraic Quantum Field Theory—an Introduction*,
arXiv:1904.04051v2, 2019.
[版本记录](https://arxiv.org/abs/1904.04051v2)；
[全文](https://arxiv.org/pdf/1904.04051v2)。
本轮核读 §2.3、Theorem 10 的 GNS 构造、循环表示及酉唯一性，
并参考其代数态与预选 Hilbert 表示的区分。
本文没有把 GNS 的存在替代 AQFT 的全部局域、对称与谱条件。

<a id="ref-inflation2026"></a>

### [5]

Isaac D. Smith, Elie Wolfe and Robert W. Spekkens,
*Fully Quantum Inflation: Quantum Marginal Problem Constraints in the Service of Causal Inference*,
PRX Quantum **7**, 010351, 13 March 2026.
[doi:10.1103/244y-nh5n](https://doi.org/10.1103/244y-nh5n)；
[出版社原文与摘要](https://journals.aps.org/prxquantum/abstract/10.1103/244y-nh5n)。
本轮仅以已核读摘要中的量子边际–因果推断联系作为当代背景；
不声称重建该文的整个方法，也不把其 triangle 因果场景与本文边际三角环混同。

<a id="ref-v77"></a>

### [6]

trureturing 项目，V77：
*反向定位量子公理：二元见证、三维比较与内部整体相容*。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/9bf2db5e96b1e6b9c96fdf9665ff9ec3ae0cf252/docs/develop/theory/AURIC_REVERSE_LOCATION_OF_QUANTUM_AXIOMS_BINARY_WITNESSES_AND_INTERNAL_COMPATIBILITY_V77.md)。
本轮核读 §3 的全部合成二元 Gram 正性、原始两两检查反例，
并保留其“表达正性不等于从无前件取得正性”的边界。

<a id="ref-v78"></a>

### [7]

trureturing 项目，V78 continuation：
*二元失败见证与整体量子关系*。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/9bf2db5e96b1e6b9c96fdf9665ff9ec3ae0cf252/docs/develop/theory/AURIC_BINARY_FAILURE_WITNESSES_AND_GLOBAL_QUANTUM_RELATIONS_V78_CONTINUATION.md)。
本轮核读 §6.1 定理 6.1 的迹一候选最小二元正性见证，
及相邻内部参考的完整正性说明。
本文复用其二元球外编码，不将它重复算作 v92 新定理来源。

<a id="ref-atlas"></a>

### [8]

trureturing 项目，
*Quantum Origin: Endogenous Cut Atlas and Discrete Reconstruction Boundaries III*。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_III.md)。
本轮核读 §10 的有限响应纤维宽度与缺失预测量范数对偶，
作为已有凸对偶接口；未据此认证整篇后续内容或程序证明。

<a id="ref-omega"></a>

### [9]

trureturing 项目，
*AURIC Omega Static Compatibility Fiber Theory*。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)。
本轮核读 §12 的假设 12.2、精确相容局部态、范数延拓与 GNS。
v92 的可数定理为该接口补入“所有有限资料相容”的存在性入口，
不声称原稿缺少 GNS 论证。

<a id="ref-v79"></a>

### [10]

trureturing 项目，V79：
*二元反向相容、有限相位证书与量子读出重构*。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_BINARY_REVERSAL_COMPATIBILITY_FINITE_PHASE_CERTIFICATES_AND_QUANTUM_READOUT_RECONSTRUCTION_V79.md)。
本轮核读定义 5.1、定理 5.2 及概率来源段；
沿用共同正比较、总强度、实际复方向与同根标定的声明前件。

<a id="ref-v80"></a>

### [11]

trureturing 项目，V80：
*全结果二元差分不增、有限有向锚与内生量子过程*。
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_ALL_OUTCOME_BINARY_DIFFERENCE_NONEXPANSION_FINITE_ORIENTED_ANCHORS_AND_ENDOGENOUS_QUANTUM_PROCESSES_V80.md)。
本轮核读定理 5.1 的完整后继等距证明与 §16 的有限量子理论重构表；
过程、效果、仪器、张量接口、酉性与光滑历史仍按该处各自前件使用。

<a id="ref-v90"></a>

### [12]

本对话研究稿，*AURIC v90: Intrinsic Binary Recovery and Shared Quantum Structure*，2026。
沿用共同参考恢复、内生中点缺额及全输入可逆接口；
本轮没有把部分资料可恢复与整个载体可逆混为一谈。

<a id="ref-v91"></a>

### [13]

本对话研究稿，*AURIC v91: Overlap Gluing, Three-Axis Relations and Quantum Markov Closure*，2026。
本轮直接接续 C91 的 Markov 充要判据、规范 Markov 补全唯一性、
严格正三角闭环反例与双 Bell 共享点例子。
C92 保留 C91 所刻画的特殊结构，同时允许一般非 Markov 共同全态。

**原稿核查记录。**
数学部分采用解析推导与独立解析复核；没有运行数学程序、CAS、数值求值、枚举或测试。
文档编译与页面渲染只用于排版检查。
本轮未修改、提交或推送项目仓库。
实时 HEAD 未能读取，所有仓库论断仅限正文注明的固定提交与已核读片段。
