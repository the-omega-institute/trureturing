# 有限内部约束、唯一整体源与稳定量子读出

二元有限夹逼、正零关系闭合与无限量子链

**AURIC v97：一个完整候选的定义、定理与反向审计**

项目连续研究稿

2026 年 11 月 3 日（新加坡）

## 摘要

本轮承接 v96 的唯一纯共同根，将问题向前推进一步：不先给定整体态，
而从同一整体代数中的正关系族出发，问这些关系何时自己选出唯一来源。
在每份有限关系均相容的明确前件下，提出本轮唯一候选 C97：
任意二元读口、任意正精度，都可由有限内部关系给出一个正序夹逼证书。
证明该条件等价于每个固定读口的候选差异趋零，也等价于全部关系只有一个共同态。
正零约束形成面的性质进一步迫使该唯一态为纯态，接回 v96 的不可约 GNS 与同扇区酉可达。

给出三项具体接续。第一，每个由全部关系强制的正零结论，都有任意精度的有限正序证书；
每个正约束又可改写为两个酉门的返回比较，精确零解不变。
第二，在有限矩阵窗口中，二态直径等于效果在可行核上的压缩谱宽度，
并能用一个规范化的二元三维球表示剩余区别。
第三，固定一块有限内部关系即可控制任意更大截口的局域误差，不需要统一外层谱隙。

完整构造双向无限 cluster 链：每个有限约束核始终四维，
但所有固定窗口的歧义最终精确消失，故全局共同零约束态唯一且纯，单点读出却完全混合。
同时给出整体范数不收敛、平均缺额掩盖局部错误、严格局域忠实态不能用非零正零约束选出等边界。
将结果连接到标准量子公理的条件式重建，明确已有复正代数、复合和实际过程接口的作用。

态空间紧致性、纯态结构、纠错和图态按既有文献归属；本轮贡献是项目内的结构接续与完整证明组织。
全文为解析推理和独立解析复核，未运行数学程序、CAS、数值求值、枚举或测试。

## 目录

- [1. 从“有一个纯根”推进到“内部关系怎样选根”](#section-1)
- [2. 一致的内部关系族与本轮唯一候选 C97](#section-2)
- [3. 有限一致性怎样给出整体：使用有向紧致性](#section-3)
- [4. C97 的充要定理：正序证书、二态收紧与唯一纯根](#section-4)
- [5. 反向审计：失败保留两个纯来源，零容差会误删相干关系](#section-5)
- [6. 有限矩阵窗口：从可行候选到唯一整体的精确判据](#section-6)
- [7. 二态差异属于哪个算符结构：压缩后是否只剩常数](#section-7)
- [8. 二元关系的有限三维提升：把剩余区别放进 Bloch 球](#section-8)
- [9. 有限关系块的鲁棒性：小缺额怎样控制读出误差](#section-9)
- [10. 固定内层证书控制任意更大观察截口](#section-10)
- [11. 双向无限 cluster 链：有限核始终退化，整体来源仍唯一](#section-11)
- [12. 把正约束还原为两个关系的有限三维比较](#section-12)
- [13. 关系的关系：全部零后果都是有限正序后果](#section-13)
- [14. 任意正约束都可改写为两个酉门的返回关系](#section-14)
- [15. 继续反着推：哪些更大结构不能被省略](#section-15)
- [16. 从 C97 接回 Hilbert 空间、平方律与量子过程](#section-16)
- [17. 标准量子公理的依赖总表](#section-17)
- [18. 完整白话：这一轮究竟怎样理解量子](#section-18)
- [19. v97 的完成范围与下一步的确定问题](#section-19)
- [来源、版本与核读范围](#references)

<a id="section-1"></a>

## 1. 从“有一个纯根”推进到“内部关系怎样选根”

<a id="sec-c97-position"></a>

版本由 v96 递增到 v97。本轮保留用户已经修正的整体观：
一个模型中只有一份共同来源，观察者、环境、程序、门参数、记录和计算都在同一整体内。
但“这些对象都在整体内”还需要一个数学接头：
为什么所声明的内部关系恰好共同确定一份来源，而非两份或完全没有来源？

v96 已证明，给定整体态 $\omega$ 后，其正二元不可分解条件 C96
等价于纯性、GNS 不可约性和标量交换子；
还证明全部零约束可唯一确定这样的纯根 [7](#ref-v96)。
本轮改变起点：先给正关系 $q_j$，不先给 $\omega$，
用有限正序不等式刻画这些关系何时共同选出唯一纯态。

$$
\boxed{\begin{gathered}
\text{有限内部关系相容，且每个二元读口都可任意夹紧}\\
\Downarrow\\
\text{唯一共同态，自动纯；其全部零关系都有有限近似证书}.
\end{gathered}}
$$

这里“任意夹紧”是逐个固定读口、逐个精度的量词。
它与整个无限系统在一个统一范数中收敛有实质区别，后文给出明确反例。

本轮核读了项目当前公开首页及默认 `dev` 信息，
但没有取得一个可固定的更新提交 SHA。
精确引用仍落在已取得的
`c63ab162315fddd0801cbe9f47dbf3eda6e13360`
理论快照；不能将此写成已验证更晚提交的全部进展 [1](#ref-currentrepo)。
本轮只读仓库。此次接续使用的已有结构包括：

- $\Omega$ 静态纤维稿第 5 节的有限逆系统与紧交思想、第 12 节的相容态延拓和 GNS，
  以及第 62.2、63.2 节的有限实际菜单与置信纤维直径 [2](#ref-omega)。

- 同稿第 8 节的精确量子恢复：编码内容在被擦除端口上的共同读数，
  与内部补端口上的可恢复性相连 [2](#ref-omega)。

- V78 对每个模型选定一份纯态与全部模型唯一解的量词区分，
  以及全部相干聚合二元窗口与共同正核的闭合关系 [4](#ref-v78pure)、[5](#ref-v78closure)。

- V74 的内部参考、时钟与采样区别，以及 V80 的条件式量子重建接口 [3](#ref-v74)、[6](#ref-v80)。

因此本轮的新增问题并非重新证明“有限一致性可以有整体”，
而是把*任意精度的有限正序证书、二态区别消失、唯一整体源、纯性与误差稳定*
放到一组明示量词下。
数学等价关系将全部证明；物理上是否采用 C97，仍是一个可用反见证审查的候选。
把它写成内部对象间的关系，不会凭空使所有相容模型都服从它。

**白话图景。**可以把整体想成一张不断被内部读口查看的关系网。
每看一小块，往往还有多种补全方法；新候选要求的是：
对一个已经选定的问题，继续补足内部关系，就能让所有允许补全给出越来越一致的答案。
如果每个问题都能如此，而且有限关系从不互相打架，
整张网便只有一份共同来源。纯性随后由这些不能正负抵消的零关系推出。

<a id="section-2"></a>

## 2. 一致的内部关系族与本轮唯一候选 C97

<a id="sec-c97-candidate"></a>

本轮承接共同复正关系接口，令 $\mathcal A$ 为非零含单位复 $C^*$ 代数，
$S(\mathcal A)$ 为其态空间。整体中的过程比较、效果及复合范围仍按已有接口解释
 [2](#ref-omega)、[5](#ref-v78closure)、[4](#ref-v78pure)。
本节不先指定待选出的整体态 $\omega$，而从一族关系约束开始。

### 定义 2.1（内部正约束族与有限一致性）

<a id="def-c97-constraint-family"></a>

给定 $q_j\in\mathcal A_+$，$j\in J$。
它们可由两段内部关系的差构成，如
$q_j=(a_j-b_j)^*(a_j-b_j)$。
对有限 $F\subset J$，记

<a id="eq-c97-finite-constraint-face"></a>

$$
Q_F=\sum_{j\in F}q_j,\qquad
K_F=\{\varphi\in S(\mathcal A):\varphi(Q_F)=0\}.
\tag{2.1}
$$

本轮的*一致约束族*是指

<a id="eq-c97-finite-feasibility"></a>

$$
K_F\ne\varnothing\qquad\text{对每个有限 }F\subset J.
\tag{2.2}
$$

由于各项非负，$\varphi(Q_F)=0$ 等价于
$\varphi(q_j)=0$ 对所有 $j\in F$ 成立。
定义全部约束的共同解集

$$
K_\infty=\bigcap_{F\Subset J}K_F.
$$

符号 $F\Subset J$ 表示 $F$ 有限；有限集合按包含关系构成有向集。

式 [(2.2)](#eq-c97-finite-feasibility) 是明确的可行性前件。
它不能用“全部对象都在内部”替代，也不能从空可行集上的二态陈述推得。
对非零 $q_j$ 乘以任意正常数不改变共同零态集合；
但改变了误差数值的标尺，使用误差界时须保留实际标定。

### 定义 2.2（候选 C97：有限内部关系给出任意精度的二元读出证书）

<a id="def-c97-axiom"></a>

对每个二元效果 $0\le B\le1$ 及每个 $\varepsilon>0$，要求存在有限
$F\Subset J$、$b\in[0,1]$ 和有限常数 $\lambda\ge0$，使

<a id="eq-c97-order-certificate"></a>

$$
\boxed{\quad
-\varepsilon1-\lambda Q_F
\ \le\ B-b1\ \le\
\varepsilon1+\lambda Q_F.
\quad}
\tag{2.3}
$$

称此条件为 C97。有限可行性是其适用的约束族定义；
式 [(2.3)](#eq-c97-order-certificate) 是本轮唯一新增候选。

候选只使用同一代数中的效果、有限个正关系、归一化标量和正序。
它没有把未知根的完整读数表放在前件中。
证书中的 $b$ 是这一读口的有限精度中心值，$\lambda$ 则控制约束误差怎样传入读出。
不同 $B$ 和不同精度可以使用不同的 $F,b,\lambda$；
候选没有声称一个固定有限证书能同时决定整个无限整体。

### 命题 2.3（证书控制近似候选的二态差异）

<a id="prop-c97-certificate-error"></a>

若式 [(2.3)](#eq-c97-order-certificate) 成立，且态 $\varphi$ 满足
$\varphi(Q_F)\le\delta$，则

<a id="eq-c97-one-state-error"></a>

$$
|\varphi(B)-b|\le\varepsilon+\lambda\delta.
\tag{2.4}
$$

若 $\varphi,\psi$ 都满足该缺额界，则

<a id="eq-c97-two-state-error"></a>

$$
|\varphi(B)-\psi(B)|\le2\varepsilon+2\lambda\delta.
\tag{2.5}
$$

**证明。**
对两个正序不等式分别施加正归一泛函 $\varphi$，即得第一式。
对 $\varphi,\psi$ 使用同一个中心 $b$，由三角不等式得到第二式。

**白话图景。**先不把最终答案写进去，只拿若干条内部关系来约束一个是非问题。
证书说：只要这些关系的缺额足够小，任何两个候选来源给出的答案就只能相差这么多。
继续要求更高精度，可以换用更充分的一组有限关系。
因此公理已经成为“关系缺额怎样约束读出差异”的具体不等式。

<a id="section-3"></a>

## 3. 有限一致性怎样给出整体：使用有向紧致性

<a id="sec-c97-global-compactness"></a>

本节使用两个标准 $C^*$ 态空间事实：$S(\mathcal A)$ 弱星紧致；
一个自伴元素为正，当且仅当全部态在其上的评价非负 [8](#ref-landsman1998)。
前者由 Banach–Alaoglu 定理及正归一条件的弱星闭性得到。
后者说明正序确实可以由全部正归一比较判定。
一般代数可以不可分，故以下使用有限交性质和有向集合，不把紧致性误写成序列紧致性。

### 引理 3.1（共同解是非空紧致面）

<a id="lem-c97-nonempty-face"></a>

在有限可行性下，每个 $K_F$ 是非空弱星紧致面，
$K_\infty$ 也是非空弱星紧致面。

**证明。**
评价 $\varphi\mapsto\varphi(Q_F)$ 弱星连续，所以 $K_F$ 弱星闭。
若 $0<t<1$ 且 $t\alpha+(1-t)\beta\in K_F$，则

$$
0=t\alpha(Q_F)+(1-t)\beta(Q_F).
$$

两项非负，故 $\alpha,\beta\in K_F$，这正是面的性质。
任意有限多个 $K_{F_i}$ 的交包含 $K_{\cup_iF_i}$，后者非空。
于是态空间的紧致性给 $K_\infty\ne\varnothing$。
闭性与面的性质均在交运算下保持。

### 定义 3.2（固定二元读口的剩余区间）

<a id="def-c97-readout-width"></a>

对效果 $B$，定义

$$
I_F(B)=\{\varphi(B):\varphi\in K_F\}
       =[m_F(B),M_F(B)],
\tag{3.1}
$$

<a id="eq-c97-width"></a>

$$
w_F(B)=M_F(B)-m_F(B)
       =\sup_{\varphi,\psi\in K_F}|\varphi(B)-\psi(B)|.
\tag{3.2}
$$

紧致性保证两端达到；凸性保证评价像为整个闭区间。
当 $F\subseteq G$ 时，$K_G\subseteq K_F$，所以这些区间嵌套，宽度不增。

### 定理 3.3（有限读出区间的精确整体极限）

<a id="thm-c97-interval-limit"></a>

对每个效果 $B$，有

<a id="eq-c97-interval-intersection"></a>

$$
\boxed{\quad
\bigcap_{F\Subset J}I_F(B)
=\{\omega(B):\omega\in K_\infty\}.
\quad}
\tag{3.3}
$$

从而

$$
\lim_F m_F(B)=\min_{\omega\in K_\infty}\omega(B),
$$

$$
\lim_F M_F(B)=\max_{\omega\in K_\infty}\omega(B),
$$

<a id="eq-c97-width-limit"></a>

$$
\boxed{\lim_F w_F(B)}
=\boxed{\sup_{\omega,\eta\in K_\infty}|\omega(B)-\eta(B)|}.
\tag{3.4}
$$

**证明。**
右侧包含于左侧，因为共同解满足每份有限约束。
反向，取 $t\in\bigcap_FI_F(B)$，定义

$$
L_F=K_F\cap\{\varphi:\varphi(B)=t\}.
$$

每个 $L_F$ 非空且弱星紧致。
对有限多个 $F_1,\ldots,F_k$，令 $G=\bigcup_iF_i$，则
$L_G\subseteq\bigcap_iL_{F_i}$，故这些集合有有限交性质。
紧致性给出 $\omega\in\bigcap_FL_F$；它属于 $K_\infty$ 且 $\omega(B)=t$。
这证明式 [(3.3)](#eq-c97-interval-intersection)。
嵌套闭区间的下端单调上升、上端单调下降，
交区间两端分别为下端的上确界与上端的下确界，故其余公式成立。

**白话图景。**一份有限关系允许一个答案区间，补充关系后，这个区间只会缩小。
如果某个数始终没有被任何有限关系排除，它就确实属于某份完整相容来源的读数。
这里没有把“每一层看起来能继续”偷偷改成“已经指定了全局来源”；
紧致性承担的正是从全部有限相容到整体相容的那一步。

<a id="section-4"></a>

## 4. C97 的充要定理：正序证书、二态收紧与唯一纯根

<a id="sec-c97-equivalence"></a>

### 定理 4.1（C97 的完整结构等价）

<a id="thm-c97-main-equivalence"></a>

对定义 [2.1](#def-c97-constraint-family) 的一致约束族，下列条件等价：

1. 候选 C97 的有限正序证书成立。

2. 对每个效果 $B$ 及每个 $\varepsilon>0$，存在有限 $F$ 使 $w_F(B)<\varepsilon$。

3. $K_\infty=\{\omega\}$ 为单点。

4. 对每个效果 $B$ 及每个 $\varepsilon>0$，存在有限 $F$ 和 $\delta>0$，使


   $$
   \sup_{\varphi,\psi\in K_{F,\delta}}
   |\varphi(B)-\psi(B)|<\varepsilon,
   \qquad
   K_{F,\delta}=\{\varphi\in S(\mathcal A):\varphi(Q_F)\le\delta\}.
   $$

当这些条件成立时，唯一态 $\omega$ 自动为纯态，故满足 v96 的 C96，
其 GNS 表示不可约。

**证明。**
**条件 1 推出条件 2。**
给定目标精度 $\eta>0$，用 C97 取证书精度 $\varepsilon<\eta/2$。
对 $\varphi,\psi\in K_F$ 使用式 [(2.5)](#eq-c97-two-state-error) 的 $\delta=0$ 情形，
得到 $w_F(B)\le2\varepsilon<\eta$。

**条件 2 与条件 3 等价。**
由引理 [3.1](#lem-c97-nonempty-face)，共同解集非空。
条件 2 及式 [(3.4)](#eq-c97-width-limit) 说明任何两个共同解在每个效果上相同。
对非零自伴 $h$，

$$
B_h=\tfrac12(1+h/\left\lVert h\right\rVert)
$$

是效果，所以两态在所有自伴元素上相同，再由复线性在全部 $\mathcal A$ 上相同。
因此共同解唯一。反向，共同解唯一使式 [(3.4)](#eq-c97-width-limit) 的右侧为零，
于是有限区间宽度可以任意缩小。

**条件 2 推出条件 1：有限正序证书的存在。**
固定 $B$ 与证书精度 $\varepsilon>0$。
选有限 $F$ 使 $w_F(B)<2\varepsilon$，并置

$$
b=\frac{m_F(B)+M_F(B)}2\in[0,1],
\qquad X=B-b1.
$$

对所有 $\varphi\in K_F$，有 $|\varphi(X)|<\varepsilon$。
考虑弱星紧致集合

$$
C=\{\varphi\in S(\mathcal A):|\varphi(X)|\ge\varepsilon\}.
$$

若 $C=\varnothing$，全部态在 $\varepsilon1\pm X$ 上非负，
由态分离正序可取 $\lambda=0$。
若 $C\ne\varnothing$，它与 $K_F$ 不交；因此

$$
\delta_0=\min_{\varphi\in C}\varphi(Q_F)>0.
$$

取 $\lambda=\left\lVert X\right\rVert/\delta_0$。
对 $\varphi\in C$，有
$|\varphi(X)|\le\left\lVert X\right\rVert\le\lambda\varphi(Q_F)$；
对 $\varphi\notin C$，有 $|\varphi(X)|<\varepsilon$。
于是对全部态均有

$$
|\varphi(X)|\le\varepsilon+\lambda\varphi(Q_F).
$$

再由态分离正序，得到式 [(2.3)](#eq-c97-order-certificate)。
此步骤不需要有限维或谱隙。

**条件 1 推出条件 4。**
给定目标 $\eta>0$，取证书精度 $\varepsilon<\eta/4$。
若 $\lambda>0$，再取 $\delta>0$ 满足
$2\lambda\delta<\eta-2\varepsilon$；若 $\lambda=0$，任取 $\delta>0$。
式 [(2.5)](#eq-c97-two-state-error) 便给条件 4。
反向，$K_F\subseteq K_{F,\delta}$，所以条件 4 立即推出条件 2。

**唯一共同解自动纯。**
若 $\omega=t\alpha+(1-t)\beta$，其中 $0<t<1$，
则每个正约束上均有

$$
0=t\alpha(q_j)+(1-t)\beta(q_j).
$$

非负性迫使 $\alpha(q_j)=\beta(q_j)=0$ 对每个 $j$ 成立。
所以 $\alpha,\beta\in K_\infty=\{\omega\}$。
这正是纯态定义；纯态与 C96、不可约 GNS 的等价由 v96 已证结果给出 [7](#ref-v96)。

这里证出的量词是：每个固定效果、每个所需精度，都有一份有限证书。
没有假设统一谱隙，也没有导出统一的证书长度、获得证书的算法或计算成本。
若只测试一个能够分离全部共同候选的效果族，条件仍足够；
例如范数稠密局域子代数中的全部效果。
如果读口族未能分离候选，则只得到该观察范围内的唯一性。

**白话图景。**现在三件事连成一个定理：有限关系能给任意精度的读出界，
每个问题上的两个候选答案最终无法保持区别，整体共同解只有一份。
由于约束都是正零关系，两份不同来源不能靠正负抵消偷偷拼成这一份解，
所以得到的共同源自动纯。
本轮不再先假定全局纯性，而是让它由一致性和二态收紧共同推出。

<a id="section-5"></a>

## 5. 反向审计：失败保留两个纯来源，零容差会误删相干关系

<a id="sec-c97-reverse-audit"></a>

### 命题 5.1（C97 失败必留下两个纯来源和一个二元区分）

<a id="prop-c97-two-pure-witnesses"></a>

若一致约束族不满足 C97，则存在两个不同纯态
$\omega_-,\omega_+\in K_\infty$ 和效果 $B$，使

$$
\omega_-(B)<\omega_+(B).
$$

它们均满足全部内部约束，故其区别不能由继续加入这同一族约束消除。

**证明。**
由定理 [4.1](#thm-c97-main-equivalence)，$K_\infty$ 非单点。
两个不同态被某个自伴元素区分，经归一化可选为效果 $B$。
因此 $B$ 在 $K_\infty$ 上的最小值 $m$ 与最大值 $M$ 满足 $m<M$。
取

$$
F_- =\{\varphi\in K_\infty:\varphi(B)=m\},\qquad
F_+ =\{\varphi\in K_\infty:\varphi(B)=M\}.
$$

它们均为非空弱星紧致面，而且作为面的面，也是整个态空间的面。

每个非空紧致面都含纯态。为说明这一步，可将其中非空闭面按反向包含排序。
链的交由紧致性非空，且仍为闭面，所以 Zorn 引理给一个按包含关系最小的非空闭面。
若它含两个不同态，某自伴元素在其上的最大值集合就是一个更小的非空闭面，矛盾。
所以最小面为单点；单点面的态为纯态。
分别在 $F_-,F_+$ 中取这样的纯态，即得所需见证。

若效果来自范数稠密的有限观察代数链，区分效果还可选在某个有限层。
因为两个态的差连续，足够好的自伴局域逼近仍保留非零差异，
再在该有限代数内归一化即可。

**白话图景。**反过来看，若某个固定问题上的歧义永远压不下去，
就不是仅仅还没挑好一个坐标：确实有两份不同的完整纯来源同时服从全部已给关系。
一个是非读口已经能区分它们。
这准确指出需要补充哪类关系，而不会把现有约束不足写成已经证明了唯一宇宙。

### 命题 5.2（正容差不可一般地改成零容差）

<a id="prop-c97-zero-tolerance-obstruction"></a>

即使正约束已经选出唯一纯态，也未必存在有限 $\lambda$ 使
$-\lambda Q\le B-bI\le\lambda Q$。

**证明。**
在 $M_2$ 中取

$$
Q=\lvert 1\rangle\langle 1\rvert,\qquad
B=\lvert +\rangle\langle +\rvert,
\qquad \lvert +\rangle=(\lvert 0\rangle+\lvert 1\rangle)/\sqrt2.
$$

唯一满足 $\operatorname{Tr}(\rho Q)=0$ 的态为 $\lvert 0\rangle\langle 0\rvert$，其 $B$ 读数为 $b=1/2$。
但

$$
B-\tfrac12I=\tfrac12X,\qquad
\lambda Q-\tfrac12X
=\begin{pmatrix}0&-1/2\\-1/2&\lambda\end{pmatrix}
$$

行列式为 $-1/4$，不可能为正。
若加入 $\varepsilon I$，两个所需正矩阵的对角元分别为
$\varepsilon,\varepsilon+\lambda$，行列式为

$$
\varepsilon(\varepsilon+\lambda)-\tfrac14.
$$

对每个 $\varepsilon>0$，选取足够大的有限 $\lambda\ge0$ 就可使其非负。

这个反例也说明：约束在根上选定读数，不等于把效果在整个 Hilbert 空间中的作用消去。
离开根方向的相干矩阵元仍然可以存在。
若把 $Q$ 直接当成全代数中等于零的算符关系，则改变了本轮的态约束问题。

**白话图景。**共同源已经确定，并不表示每个读口在其他方向上都没有作用。
一个读口仍可把根方向与别的方向相干地连接起来。
任意小的正容差让有限正序证书保留这种连接；强行要求零容差，会把合法的量子关系也排除掉。

### 5.1 一致性与正零结构的必要位置

如果省掉有限可行性，取 $q=I$ 就没有任何归一零态；
但对任意效果取 $b=1/2$、足够大的 $\lambda$，式 [(2.3)](#eq-c97-order-certificate) 仍成立。
所以证书不能在空解集上冒充选出了来源。

如果把正零关系换成任意线性读数条件，在 $M_2$ 中要求

$$
\varphi(X)=\varphi(Y)=\varphi(Z)=0
$$

确实只留下 $I/2$，却是混合态。
因此“唯一解自动纯”实质使用了正零条件形成面的性质。

如果只看不足以分离整体态的端口，例如只固定二端口系统的第一端口为 $\lvert 0\rangle$，
第二端口仍可处在不同态；第一端口的全部答案相同不能推出整体唯一。
这些反例逐一说明本轮条件承担的作用，不把它们隐藏在“内生”一词里。

<a id="section-6"></a>

## 6. 有限矩阵窗口：从可行候选到唯一整体的精确判据

<a id="sec-c97-matrix-windows"></a>

以下是一般候选的一个有限矩阵实现范围。
令

$$
\mathcal A_1\subseteq\mathcal A_2\subseteq\cdots,
\qquad \mathcal A_n\simeq M_{d_n}(\mathbb C),
\qquad
\mathcal A=\overline{\bigcup_n\mathcal A_n}^{\left\lVert \cdot\right\rVert},
$$

各嵌入保留同一个单位。
指定

<a id="eq-c97-matrix-constraints"></a>

$$
0\le Q_n\in\mathcal A_n,
\qquad Q_{n+1}\ge Q_n,
\qquad K_n=\ker Q_n\ne0,
\qquad P_n=\text{到 }K_n\text{ 的投影}.
\tag{6.1}
$$

这里 $Q_n$ 在比较时按嵌入理解。
例如可令 $Q_n$ 为前 $n$ 层全部正关系的和。
这些关系在有限层可行，并不预设每个有限候选都能通过以后全部约束。

### 定义 6.1（有限候选与窗口二态直径）

<a id="def-c97-window-diameter"></a>

记

$$
C_n=\{\rho\ge0:\operatorname{Tr}\rho=1,\ \operatorname{supp}\rho\subseteq K_n\}.
$$

对固定 $r\le n$，将态限制到 $\mathcal A_r$，记所得密度矩阵为 $\rho_r$，并定义

<a id="eq-c97-window-diameter"></a>

$$
C_{r,n}=\{\rho_r:\rho\in C_n\},\qquad
D_{r,n}=\sup_{\rho,\sigma\in C_n}
\frac12\left\lVert \rho_r-\sigma_r\right\rVert_1.
\tag{6.2}
$$

普通矩阵迹用于各层的密度矩阵表示。

这里 $\operatorname{Tr}(\rho Q_n)=\left\lVert Q_n^{1/2}\rho^{1/2}\right\rVert_2^2$，
所以零期望恰好等价于 $\operatorname{supp}\rho\subseteq K_n$。

含幺嵌入 $M_d\to M_D$ 可以在一个酉坐标中写成 $a\mapsto a\otimes I_k$，
其中 $D=dk$：其矩阵单位的对角投影等秩，非对角矩阵单位给对应子空间之间的等距，
据此选择共同基即可得到该形式。
因此限制映射可用相应的偏迹表示，且与所选酉坐标无关。
这也证明每个有限层态都有到任意更高层的态延拓：
在重数因子上选择任意归一态即可。
该延拓只用于存在性论证，没有断言其满足尚未施加的后续约束。

### 引理 6.2（有限候选的嵌套与整体存在）

<a id="lem-c97-window-compactness"></a>

$C_n$ 非空紧致凸，$C_{r,n+1}\subseteq C_{r,n}$。
存在 $\omega\in S(\mathcal A)$ 满足 $\omega(Q_n)=0$ 对每个 $n$ 成立。

**证明。**
有限维正性、迹一与支撑条件给非空紧致凸性。
若 $\rho\in C_{n+1}$，由 $0\le Q_n\le Q_{n+1}$ 得

$$
0\le\rho(Q_n)\le\rho(Q_{n+1})=0.
$$

所以限制到第 $n$ 层的态属于 $C_n$，再限制到第 $r$ 层便得嵌套。

现在对每个 $n$ 任取 $\rho^{(n)}\in C_n$。
逐层利用有限维态空间的紧致性，先抽取使第 1 层限制收敛的子列，
再抽取使第 2 层限制收敛的子列，依次进行，最后取对角子列。
得到每个固定层 $r$ 的极限态 $\omega_r\in C_r$。
限制映射连续，所以这些极限相容。
在代数并集上定义 $\omega(a)=\omega_r(a)$，其中 $a\in\mathcal A_r$。
相容性使其良定义，正性、归一化及 $|\omega(a)|\le\left\lVert a\right\rVert$ 使其唯一连续延拓到
$\mathcal A$；对 $a^*a$ 的局域逼近保证延拓仍为正归一态。
每个 $Q_r$ 的期望为零，故得到所需整体态。

本证明在这条可数有限矩阵链中使用序列紧致性；
前文一般 $C^*$ 版本仍使用有向有限交性质。
相容有限态到整体态的连续延拓，也与项目已有构造一致 [2](#ref-omega)（第 12 节）。

### 定理 6.3（窗口直径的精确极限）

<a id="thm-c97-window-limit"></a>

令

$$
K_\infty=\{\omega\in S(\mathcal A):\omega(Q_n)=0\ \forall n\}.
$$

则对每个固定 $r$，

<a id="eq-c97-window-intersection"></a>

$$
\bigcap_{n\ge r}C_{r,n}
=\{\omega|_{\mathcal A_r}:\omega\in K_\infty\},
\tag{6.3}
$$

<a id="eq-c97-window-limit"></a>

$$
\boxed{\lim_{n\to\infty}D_{r,n}}
=\boxed{\operatorname{diam}_{D_{\rm tr}}
\{\omega|_{\mathcal A_r}:\omega\in K_\infty\}}.
\tag{6.4}
$$

特别地，$K_\infty$ 为单点，当且仅当

<a id="eq-c97-window-criterion"></a>

$$
\boxed{D_{r,n}\longrightarrow0\quad\text{对每个固定 }r.}
\tag{6.5}
$$

此时唯一整体态自动纯，并满足一般形式的 C97。

**证明。**
整体解的有限限制显然属于每个 $C_{r,n}$。
反向，若 $\tau_r\in\bigcap_{n\ge r}C_{r,n}$，
对每个 $n\ge r$ 选择 $\rho^{(n)}\in C_n$，其第 $r$ 层限制恰为 $\tau_r$。
沿引理 [6.2](#lem-c97-window-compactness) 的对角抽取，得到共同整体解，
第 $r$ 层限制仍为 $\tau_r$。这证明式 [(6.3)](#eq-c97-window-intersection)。

非空紧致集合 $C_{r,n}$ 递减，故其直径 $D_{r,n}$ 递减并有极限 $d$。
在每个 $C_{r,n}$ 中取达到直径的一对 $\alpha_n,\beta_n$。
由有限维紧致性，取一共同子列使两者分别收敛到 $\alpha,\beta$。
对每个固定 $m$，子列充分后都属于闭集 $C_{r,m}$，
所以两个极限属于全部 $C_{r,m}$ 的交。
迹距离连续，给 $D_{\rm tr}(\alpha,\beta)=d$。
反向，交集的直径不超过任何 $D_{r,n}$，因此得到式 [(6.4)](#eq-c97-window-limit)。

若全部固定窗口直径趋零，任何两个共同解都在每个 $\mathcal A_r$ 上相同，
由稠密性在 $\mathcal A$ 上相同。
反向由极限直径公式立即成立。
纯性和一般 C97 使用定理 [4.1](#thm-c97-main-equivalence)；
若取 $q_1=Q_1$、$q_n=Q_n-Q_{n-1}$，它们是正约束，且前 $n$ 项之和恰为 $Q_n$。

**白话图景。**每一层允许保留多个候选，包括以后会被淘汰的候选。
只要对任何固定窗口，足够多的内部约束能把所有候选的读出压到一起，
完整关系网就只剩一份来源。
自由度仍可出现在越来越远、越来越细的地方；这里要求的是每个固定窗口最终被确定，
没有要求某一有限层已经把整个无限世界一口气确定。

<a id="section-7"></a>

## 7. 二态差异属于哪个算符结构：压缩后是否只剩常数

<a id="sec-c97-compression"></a>

把 $B\in\mathcal A_r$ 按嵌入视为第 $n$ 层算符。
在可行子空间上定义自伴压缩

$$
T_{n,B}=P_nBP_n|_{K_n}.
$$

### 定理 7.1（窗口直径的压缩算符刻画）

<a id="thm-c97-compression-diameter"></a>

对每个 $r\le n$，

<a id="eq-c97-compression-width"></a>

$$
\boxed{
D_{r,n}
=\max_{\substack{B\in\mathcal A_r\\0\le B\le I}}
\bigl(\lambda_{\max}(T_{n,B})-\lambda_{\min}(T_{n,B})\bigr).
}
\tag{7.1}
$$

并且

<a id="eq-c97-distance-to-scalars"></a>

$$
D_{r,n}
=2\max_{\substack{B\in\mathcal A_r\\0\le B\le I}}
\inf_{b\in\mathbb R}\left\lVert P_nBP_n-bP_n\right\rVert.
\tag{7.2}
$$

若 $D_{r,n}>0$，达到这个二态差异的可行态可以选成两个正交纯态。

**证明。**
对两个第 $r$ 层密度矩阵，Hermitian 差的 Jordan 分解给

$$
\tfrac12\left\lVert \rho_r-\sigma_r\right\rVert_1
=\max_{0\le B\le I}\operatorname{Tr}((\rho_r-\sigma_r)B).
$$

因为正部与负部的迹相等，右侧由正部的支撑投影达到。
把有限维紧致集合上的最大化次序交换，得到

$$
\begin{aligned}
D_{r,n}
&=\max_{0\le B\le I}
\left(\max_{\rho\in C_n}\operatorname{Tr}(\rho B)
-\min_{\sigma\in C_n}\operatorname{Tr}(\sigma B)\right)\\
&=\max_{0\le B\le I}
\bigl(\lambda_{\max}(T_{n,B})-\lambda_{\min}(T_{n,B})\bigr).
\end{aligned}
$$

最后一步是有限维自伴谱定理。
对任意自伴 $T$，

$$
\inf_{b\in\mathbb R}\left\lVert T-bI\right\rVert
=\tfrac12(\lambda_{\max}(T)-\lambda_{\min}(T)),
$$

最优中心为两端点的均值，所以得到第二式。
若最大宽度非零，对达到最大值的 $B$ 取 $T_{n,B}$ 的最大、最小本征向量。
它们位于 $K_n$ 且正交；其局部迹距离至少为该 $B$ 的期望差，又不超过定义中的最大值，
故达到 $D_{r,n}$。

若 C97 选出唯一整体态 $\omega$，其第 $n$ 层限制属于 $C_n$，
所以 $\omega(B)$ 位于 $T_{n,B}$ 的谱端点之间，从而

<a id="eq-c97-selected-scalar"></a>

$$
\left\lVert P_nBP_n-\omega(B)P_n\right\rVert\le D_{r,n}
\quad(0\le B\le I,\ B\in\mathcal A_r).
\tag{7.3}
$$

因此内部约束不断增加时，每个固定窗口的效果在剩余可行子空间上逐渐只剩一个标量读数。
它并不说明 $B$ 在整个 Hilbert 空间上成为标量，也不说明完整关系代数变成可交换代数。

**白话图景。**观察者尚未排除的来源构成一个可行子空间。
一个固定问题若还能在这空间里区分不同方向，它的压缩算符就有不同本征值。
把所有这样的差异压到零，恰好就是压缩后只剩常数。
原来的量子门仍可作用在其他方向上；被确定的是共同源的读数。

<a id="section-8"></a>

## 8. 二元关系的有限三维提升：把剩余区别放进 Bloch 球

<a id="sec-c97-bloch-lift"></a>

### 定义 8.1（二态平面的归一化区别矩阵）

<a id="def-c97-comparison-state"></a>

取正交单位向量 $\xi,\eta\in K_n$，对局部效果 $B$ 定义

$$
M=\begin{pmatrix}a&c\\\overline c&d\end{pmatrix},
\quad
a=\langle\xi,B\xi\rangle,
\quad d=\langle\eta,B\eta\rangle,
\quad c=\langle\xi,B\eta\rangle.
$$

这是 $B$ 在该二态平面的压缩，故 $0\le M\le I_2$。
定义

<a id="eq-c97-comparison-state"></a>

$$
\boxed{
\Gamma=\frac12I_2+M-\frac{\operatorname{Tr} M}{2}I_2.
}
\tag{8.1}
$$

实际共同均值 $\bar b=(a+d)/2$ 另外保留。

### 定理 8.2（三维球半径恰为二元剩余区别）

<a id="thm-c97-bloch-diameter"></a>

$\Gamma$ 为正迹一矩阵，且

<a id="eq-c97-comparison-bloch"></a>

$$
\Gamma=\tfrac12(I+\mathbf r\cdot\boldsymbol\sigma),
\qquad
\mathbf r=(2\operatorname{Re} c,-2\operatorname{Im} c,a-d),
\tag{8.2}
$$

满足

<a id="eq-c97-bloch-width"></a>

$$
\left\lVert \mathbf r\right\rVert_{\mathbb R^3}
=\lambda_{\max}(M)-\lambda_{\min}(M)\le1.
\tag{8.3}
$$

并且

<a id="eq-c97-bloch-window-diameter"></a>

$$
\boxed{
D_{r,n}
=\sup_{\substack{B\in\mathcal A_r, 0\le B\le I\\
\xi,\eta\in K_n, \left\lVert \xi\right\rVert=\left\lVert \eta\right\rVert=1, \xi\perp\eta}}
\left\lVert \mathbf r(B;\xi,\eta)\right\rVert_{\mathbb R^3}.
}
\tag{8.4}
$$

若 $\dim K_n=1$，最后一个空上确界按 $0$ 定义。

**证明。**
设 $M$ 的本征值为 $\mu_-\le\mu_+$。
由 $0\le M\le I$，二者属于 $[0,1]$。
$\Gamma$ 的本征值为

$$
\frac{1-(\mu_+-\mu_-)}2,\qquad
\frac{1+(\mu_+-\mu_-)}2,
$$

所以 $\Gamma\ge0$ 且迹为一。
展开 Pauli 矩阵得到式 [(8.2)](#eq-c97-comparison-bloch)；
两个本征值之差等于 Bloch 向量长度，即得式 [(8.3)](#eq-c97-bloch-width)。

任何二态平面压缩的最小、最大 Rayleigh 商，都位于
$T_{n,B}$ 的最小与最大本征值之间。
所以其谱宽度不超过 $T_{n,B}$ 的谱宽度。
当 $T_{n,B}$ 非标量时，选择最大、最小本征向量作为 $\xi,\eta$ 就达到该宽度。
若它是标量，每个二态平面的半径均为零。
再用定理 [7.1](#thm-c97-compression-diameter) 对效果取最大值，得到最后公式。
若 $\dim K_n=1$，可行态本来就只有一个，$D_{r,n}=0$，约定与原定义相容。

这个归一化没有除以可能趋零的 $\operatorname{Tr} M$，因而不会把一个消失的小概率块
放大为虚假的固定区别。
它编码的是去掉共同均值后的区别与相干项。
例如 $B=0$ 与 $B=I$ 都给 $\Gamma=I/2$，但其均值分别为 $0$ 与 $1$。
因此不应丢掉 $\bar b$，也不能把这个三维区别球称为整个高维效果的无损编码。
均值与球坐标也不能独立任取：$M$ 的两个本征值为
$\bar b\pm\left\lVert \mathbf r\right\rVert_{\mathbb R^3}/2$，它们都必须属于 $[0,1]$，故

$$
\left\lVert \mathbf r\right\rVert_{\mathbb R^3}\le2\min\{\bar b,1-\bar b\}.
$$

这是保留均值后的准确可实现域。

**白话图景。**在任意两个剩余方向之间，取一个问题来看，就得到一个二乘二比较块。
把两者共同的答案中心留下，剩余的对角差和相干差恰好成为三维球里的三个坐标。
球半径越小，这个问题越无法区分两种候选。
C97 的有限窗口形式，就是每个固定窗口里所有这样的半径最终都缩到零。

### 命题 8.3（只比较两个对角答案会漏掉最大相干区别）

<a id="prop-c97-coherent-counterexample"></a>

取 $B=\lvert +\rangle\langle +\rvert$、$\xi=\lvert 0\rangle$、$\eta=\lvert 1\rangle$。
则 $a=d=1/2$，两个对角答案相同，但 $c=1/2$，
故 $\mathbf r=(1,0,0)$、$\left\lVert \mathbf r\right\rVert=1$。

**证明。**
在 $\lvert 0\rangle,\lvert 1\rangle$ 基中，

$$
B=\frac12\begin{pmatrix}1&1\\1&1\end{pmatrix}.
$$

代入定义即得所列值。
在相干方向 $\lvert +\rangle$ 与 $\lvert -\rangle=(\lvert 0\rangle-\lvert 1\rangle)/\sqrt2$ 上，
这个效果的概率分别为 $1$ 与 $0$，实现最大区别。

因此候选需要对全部相容二态比较成立，包含它们的相干重组。
这与项目先前“原始词对的测试不足以替代全部相干聚合测试”的量词边界相接
 [5](#ref-v78closure)。
如果只固定某一基的一对对角读数，就可能漏掉球的另外两个方向。

**白话图景。**两个方向分别回答相同，不等于它们之间已经没有信息。
把它们相干地合起来，原来隐藏的区别可以变成完全不同的答案。
三维提升在这里承担明确工作：同时保留概率差、相干实部和相干虚部，
不让只看某个截面的观察误判为整体已经唯一。

<a id="section-9"></a>

## 9. 有限关系块的鲁棒性：小缺额怎样控制读出误差

<a id="sec-c97-finite-robustness"></a>

前文的一般 C97 条件通过有限正序证书约束一个固定读口。
本节在有限矩阵关系块上给出显式误差界，再构造一个满足该条件的无限量子模型。
正算符 $Q$ 表示约束缺额；其谱尺度在这里不自动具有物理能量或质量的单位。
所有限制和补端口仍属于共同模型内部。

### 定义 9.1（零约束支撑与有限缺额隙）

<a id="def-c97-finite-gap"></a>

设 $H$ 有限维，$Q\ge0$，且 $K=\ker Q\ne\{0\}$。
令 $P$ 为 $K$ 上的正交投影。
若 $Q\ne0$，记其最小正本征值为 $\Delta>0$，则

$$
Q\ge\Delta(I-P).
$$

对密度态采用迹距离
$D(\rho,\sigma)=\tfrac12\left\lVert \rho-\sigma\right\rVert_1$，并对 $\delta\ge0$ 定义

<a id="eq-c97-finite-error-function"></a>

$$
g_Q(\delta)=
\begin{cases}
0,&Q=0,\\[2pt]
\min\{1,\sqrt{\delta/\Delta}\},&Q\ne0.
\end{cases}
\tag{9.1}
$$

### 定理 9.2（低缺额态靠近一份零约束态）

<a id="thm-c97-low-defect"></a>

若密度态 $\rho$ 满足 $\operatorname{Tr}(\rho Q)\le\delta$，则存在归一态
$\sigma$，支撑在 $\ker Q$ 中，并满足

<a id="eq-c97-low-defect-distance"></a>

$$
\boxed{D(\rho,\sigma)\le g_Q(\delta).}
\tag{9.2}
$$

当 $p=\operatorname{Tr}(P\rho)>0$ 时，可以取
$\sigma=P\rho P/p$。

**证明。**
若 $Q=0$，取 $\sigma=\rho$。
以下设 $Q\ne0$。由正序关系得到

$$
1-p=\operatorname{Tr}(\rho(I-P))
\le\frac{\operatorname{Tr}(\rho Q)}{\Delta}
\le\frac{\delta}{\Delta}.
$$

若 $p>0$，所写 $\sigma$ 显然归一且支撑在 $\ker Q$。
下面证明 $D(\rho,\sigma)\le\sqrt{1-p}$。

取 $\rho$ 的 GNS 表示 $(H_\rho,\pi,\Omega)$，令

$$
x=\Omega,\qquad y=\frac{\pi(P)\Omega}{\sqrt p}.
$$

则 $x,y$ 均归一且 $\langle y,x\rangle=\sqrt p$。
$y$ 的向量态在原矩阵代数上的限制为

$$
\langle y,\pi(a)y\rangle
=\frac{\operatorname{Tr}(\rho PaP)}p
=\operatorname{Tr}(\sigma a).
$$

若 $p=1$，二向量相同，所需结论成立。
若 $0<p<1$，可写成
$x=\sqrt p\,y+\sqrt{1-p}\,z$，其中 $z\perp y$、$\left\lVert z\right\rVert=1$。
两个秩一投影之差在 $\operatorname{span}\{y,z\}$ 上的矩阵为

$$
\begin{pmatrix}
-(1-p)&\sqrt{p(1-p)}\\
\sqrt{p(1-p)}&1-p
\end{pmatrix}.
$$

其迹为零、行列式为 $-(1-p)$，故本征值为
$\pm\sqrt{1-p}$。
两个完整向量态的迹距离因而等于 $\sqrt{1-p}$。
限制到原代数只减少允许的二元效果，故不能增加可区分性。
于是

$$
D(\rho,\sigma)\le\sqrt{1-p}\le\sqrt{\delta/\Delta}.
$$

迹距离还始终不超过一，所以得到式 [(9.2)](#eq-c97-low-defect-distance)。

若 $p=0$，则 $\delta\ge\Delta$。
任选支撑在非零空间 $\ker Q$ 中的归一态 $\sigma$，
已有 $D(\rho,\sigma)\le1=g_Q(\delta)$。

这里的 GNS 向量仅用于表示和比较同一份读数；没有假设新增一个物理外部纯化端口。
该表示及其与原读数的对应，沿用项目已有构造和 v96 的内外范围说明
 [2](#ref-omega)、[7](#ref-v96)。

**白话图景。**若离开某个有限关系块的零解必须付出正缺额，那么总缺额很小的内容，
就必定靠近一份真正满足这块关系的内容。
所用的隙属于这一块有限关系，不要求无限整体具有统一的最小隙。
零权重和零算符也被单独处理，所以归一化没有隐藏除零。

<a id="section-10"></a>

## 10. 固定内层证书控制任意更大观察截口

<a id="sec-c97-inner-certificate"></a>

考虑具有共同单位的递增有限矩阵代数
$\mathcal A_r\subseteq\mathcal A_m\subseteq\mathcal A_M$，
以及按单位嵌入理解的正约束

$$
Q_M\ge Q_m\ge0,\qquad K_m=\ker Q_m\ne\{0\}.
$$

令

$$
\mathcal C_m=\{\sigma_m:\sigma_m\text{ 为态， }\operatorname{Tr}(\sigma_mQ_m)=0\}.
$$

给定已经存在的全局共同零约束态 $\omega$，
它的有限限制 $\omega_m$ 属于 $\mathcal C_m$。
对固定读口 $\mathcal A_r$，定义

<a id="eq-c97-local-root-diameter"></a>

$$
D_{r,m}
=\sup_{\sigma,\tau\in\mathcal C_m}
D(\sigma|_{\mathcal A_r},\tau|_{\mathcal A_r}).
\tag{10.1}
$$

这是前文一般读口宽度在完整有限矩阵端口上的统一形式。
有限维效果集紧致，故逐个效果的宽度收紧与这里的迹距离直径收紧相容；
一般等价关系已经在前文给出。

### 定理 10.1（固定内层的定量证书）

<a id="thm-c97-inner-certificate"></a>

对任意 $M\ge m\ge r$，若态 $\rho_M$ 满足
$\rho_M(Q_M)\le\delta$，则

<a id="eq-c97-inner-certificate-bound"></a>

$$
\boxed{
D(\rho_M|_{\mathcal A_r},\omega|_{\mathcal A_r})
\le D_{r,m}+g_{Q_m}(\delta).
}
\tag{10.2}
$$

右侧可再与一取最小值。
若两份外层态的总缺额均不超过 $\delta$，则其局域距离不超过
$D_{r,m}+2g_{Q_m}(\delta)$。

**证明。**
限制态 $\rho_m=\rho_M|_{\mathcal A_m}$ 满足

$$
\rho_m(Q_m)\le\rho_M(Q_M)\le\delta.
$$

由定理 [9.2](#thm-c97-low-defect)，存在
$\sigma_m\in\mathcal C_m$，使
$D(\rho_m,\sigma_m)\le g_{Q_m}(\delta)$。
迹距离在限制下不增；这可由二元效果的对偶表达直接看出：
小端口的每个效果仍是大端口的效果。
于是

$$
\begin{aligned}
D(\rho_M|_{\mathcal A_r},\omega|_{\mathcal A_r})
&\le D(\rho_m|_{\mathcal A_r},\sigma_m|_{\mathcal A_r})
 +D(\sigma_m|_{\mathcal A_r},\omega_m|_{\mathcal A_r})\\
&\le g_{Q_m}(\delta)+D_{r,m}.
\end{aligned}
$$

对两份外层态分别选取零约束近邻，再使用同一个直径界，即得最后一项。

### 推论 10.2（局域稳定性不需要统一外层隙）

<a id="cor-c97-local-stability-without-global-gap"></a>

若对每个固定 $r$ 都有 $D_{r,m}\to0$，
且一列外层态满足 $\rho_M(Q_M)\to0$，则

<a id="eq-c97-local-approximation-limit"></a>

$$
\rho_M|_{\mathcal A_r}\longrightarrow\omega|_{\mathcal A_r}
\quad\text{按迹范数，对每个固定 }r.
\tag{10.3}
$$

不需要 $\rho_M(Q_M)/\Delta_M\to0$。

**证明。**
给定 $\varepsilon>0$，先固定 $m\ge r$，使
$D_{r,m}<\varepsilon/2$。
此后 $m$ 不再变化。
若 $Q_m\ne0$，其 $\Delta_m$ 是固定正数，
所以对足够大的 $M$ 有
$g_{Q_m}(\rho_M(Q_M))<\varepsilon/2$；
若 $Q_m=0$，该误差项直接为零。
代入式 [(10.2)](#eq-c97-inner-certificate-bound) 即得结论。

还可只要求每条固定约束的缺额趋零。
若 $Q_m$ 是有限个已声明正约束之和，
且 $\rho_M(q_j)\to0$ 对每个固定 $j$ 成立，
则 $\rho_M(Q_m)\to0$ 对每个固定 $m$ 成立，
同一证明继续适用。

**白话图景。**要确定一个固定窗口的答案，不必先控制无限世界的最小隙。
先找到一块已经把这个窗口解释清楚的有限关系，然后要求这块关系的误差足够小。
后面继续增加多少内容，都受这份已有证书约束。
这是先固定所问的问题，再扩大内部关系；不是让问题跟着截口不断逃向远处。

### 10.1 反例：隙趋零、局域稳定，但整体范数不收敛

取双向无限 qubit 链，位置为 $j\in\mathbb Z$。
以下 $\lvert \pm\rangle=(\lvert 0\rangle\pm\lvert 1\rangle)/\sqrt2$ 为 Pauli $X$ 的两个本征态。
令

$$
P_j^-=\frac{I-X_j}{2},\qquad
q_j=2^{-|j|}P_j^-,
\qquad
Q_m=\sum_{|j|\le m}q_j.
$$

这些约束对易。有限共同零空间只有
$\lvert +\rangle^{\otimes(2m+1)}$ 一条射线，
因此 $D_{r,m}=0$ 对 $m\ge r$ 成立。
同时，张量积 $X$ 本征基给

$$
\Delta_m=2^{-m}\longrightarrow0.
$$

相容的全 $\lvert +\rangle$ 乘积态记为 $\omega_+$。
任意共同零约束态的每个有限限制都只能是这个乘积态，
所以 $\omega_+$ 是唯一的全局共同零约束态。

令 $\sigma_n$ 只把第 $n$ 个位置从 $\lvert +\rangle$ 翻为 $\lvert -\rangle$，
其余位置保持 $\lvert +\rangle$。
在外层 $M=2n$ 上，

<a id="eq-c97-gap-ratio-counterexample"></a>

$$
\sigma_n(Q_{2n})=2^{-n},
\qquad
\frac{\sigma_n(Q_{2n})}{\Delta_{2n}}=2^n\longrightarrow\infty.
\tag{10.4}
$$

然而对每个固定窗口 $[-r,r]$，
当 $n>r$ 时，其限制与 $\omega_+$ 完全相同。
局域收敛因此最终精确成立。

在完整代数上，效果 $P_n^-$ 却给出

$$
\sigma_n(P_n^-)=1,\qquad\omega_+(P_n^-)=0.
$$

故

<a id="eq-c97-global-norm-obstruction"></a>

$$
D_{\mathcal A}(\sigma_n,\omega_+)=1,
\qquad
\left\lVert \sigma_n-\omega_+\right\rVert=2
\quad\text{对每个 }n.
\tag{10.5}
$$

这里 $D_{\mathcal A}=\tfrac12\left\lVert \cdot\right\rVert$ 使用态泛函的对偶范数。
因为 $\sum_j2^{-|j|}<\infty$，
还可以在代数内定义范数收敛的正元素
$Q_\infty=\sum_j2^{-|j|}P_j^-$。
其唯一零读数态仍为 $\omega_+$，
且 $\sigma_n(Q_\infty)\to0$，而式 [(10.5)](#eq-c97-global-norm-obstruction) 不变。

**白话图景。**误差可以移到越来越远的内部位置。
每个固定窗口最终都正确，但完整状态始终保留一个能被相应远处读口完全辨认的区别。
所以固定读口的稳定可以成立，外层隙比值可以发散，整体态范数也可以一直相距最大。
三件事描述的是不同量词，不能互相替代。

<a id="section-11"></a>

## 11. 双向无限 cluster 链：有限核始终退化，整体来源仍唯一

<a id="sec-c97-cluster"></a>

下面给出一个有非平凡量子关联的模型。
Cluster 态与图态的基本构造属于既有研究
 [10](#ref-hein2004)；
本节完整证明这里所需的有限核、无限相容、唯一零约束态和局域稳定结论。
它不把唯一共同零约束态扩大为关于所有代数量子基态的分类结论。

### 定义 11.1（双向链的有限关系截口）

<a id="def-c97-cluster-cut"></a>

令

$$
I_m=\{-m,\ldots,m\},\qquad
H_m=(\mathbb C^2)^{\otimes(2m+1)},\qquad
\mathcal A_m=B(H_m),
$$

通过两端补单位嵌入
$\mathcal A_m\subseteq\mathcal A_{m+1}$，
并令 $\mathcal A=\overline{\bigcup_m\mathcal A_m}^{\left\lVert \cdot\right\rVert}$。
对 $-m<j<m$，定义

<a id="eq-c97-cluster-constraints"></a>

$$
S_j=Z_{j-1}X_jZ_{j+1},\qquad
q_j=\frac{I-S_j}{2},\qquad
Q_m=\sum_{-m<j<m}q_j.
\tag{11.1}
$$

其中 $X,Z$ 是 Pauli 算符。
各 $S_j$ 自伴且平方为单位，所以每个 $q_j$ 都是正投影。
而且

<a id="eq-c97-cluster-binary-word"></a>

$$
\boxed{
q_j=
\frac14
(X_j-Z_{j-1}Z_{j+1})^*(X_j-Z_{j-1}Z_{j+1}).
}
\tag{11.2}
$$

因此每条零约束比较的是两个门词作用到同一内容后的结果：

$$
X_j\Psi=Z_{j-1}Z_{j+1}\Psi.
$$

这是一项二元关系，其物理支持含三个 qubit。
“比较两个关系词”并不等于“只允许二体相互作用”。
同时，$Q_{m+1}$ 包含 $Q_m$ 的全部项并增加两个正项，故 $Q_{m+1}\ge Q_m$。

### 引理 11.2（有限 CZ 共轭）

<a id="lem-c97-cluster-conjugation"></a>

令

$$
U_m=\prod_{j=-m}^{m-1}\operatorname{CZ}_{j,j+1}.
$$

则 $U_m=U_m^*=U_m^{-1}$，并且对内部位置 $-m<j<m$，

$$
U_mX_jU_m=Z_{j-1}X_jZ_{j+1},
\qquad U_mZ_jU_m=Z_j.
$$

**证明。**
CZ 在计算基上给相位 $(-1)^{ab}$，因此它是对角自伴酉，
所有边上的 CZ 彼此对易。
翻转第一个输入位所改变的相位因子为 $(-1)^b$，
所以
$\operatorname{CZ}(X\otimes I)\operatorname{CZ}=X\otimes Z$；
同理
$\operatorname{CZ}(I\otimes X)\operatorname{CZ}=Z\otimes X$。
对角的 $Z$ 与 CZ 对易。
一个内部位置恰有两条相邻边，故得到所列共轭公式；
其他边与该位置的算符对易。

### 定理 11.3（所有有限共同核均为四维）

<a id="thm-c97-cluster-finite-kernel"></a>

对 $m\ge1$，有

$$
U_mQ_mU_m
=\sum_{-m<j<m}\frac{I-X_j}{2}.
$$

所以零空间为

<a id="eq-c97-cluster-code-space"></a>

$$
K_m=
U_m\left(
H_{\{-m,m\}}\otimes
\bigotimes_{-m<j<m}\mathbb C\lvert +\rangle_j
\right),
\qquad \dim K_m=4,
\tag{11.3}
$$

其中张量因子按对应位置排列。
此外，$Q_m$ 的最小正本征值为 $\Delta_m=1$。

**证明。**
第一式由引理 [11.2](#lem-c97-cluster-conjugation) 逐项得到。
共轭后的每项投影只作用于一个内部位置。
其和为零当且仅当每个内部 qubit 都处于 $X$ 的 $+1$ 本征方向 $\lvert +\rangle$；
两个端点不受约束，合计留下四维空间。
共同的张量积 $X$ 本征基将投影和对角化。
非零本征值为至少一个内部位置取 $\lvert -\rangle$ 时的投影数，
最小值一可由恰有一个内部位置取 $\lvert -\rangle$ 实现。

**白话图景。**每个有限截口都还有四维自由度，因此它从来没有单独选出唯一态。
这些自由度留在截口的两个端点，而内部关系已经固定。
下一步要证明的是：截口向外增长时，端点留下的区别能否继续影响一个事先固定的窗口。

### 11.1 无限自同构与唯一共同零约束态

对局域算符 $B$，取足够大的 $m$，使其支持及相邻一格均落在 $I_m$ 内，定义

<a id="eq-c97-cluster-automorphism"></a>

$$
\alpha(B)=U_mBU_m.
\tag{11.4}
$$

此定义与更大的 $m$ 无关：新增 CZ 边与 $B$ 对易，
且与全部原 CZ 对易，故在共轭中成对消去。
对任意两个局域算符选同一个足够大的 $m$，便得

$$
\alpha(AB)=\alpha(A)\alpha(B),\qquad
\alpha(A^*)=\alpha(A)^*,\qquad
\left\lVert \alpha(A)\right\rVert=\left\lVert A\right\rVert.
$$

再次选足够大的共同截口，还得 $\alpha^2=\operatorname{id}$。
于是 $\alpha$ 唯一连续延拓为完整 $\mathcal A$ 的自同构。
这里没有假定无穷 CZ 乘积在 $\mathcal A$ 中按范数收敛成一个酉元。

令 $\omega_+$ 为全 $\lvert +\rangle$ 的相容无限乘积态，定义

<a id="eq-c97-infinite-cluster-state"></a>

$$
\boxed{\omega_{\rm cl}=\omega_+\circ\alpha.}
\tag{11.5}
$$

相容有限态的连续延拓采用项目既有构造 [2](#ref-omega)。

### 定理 11.4（唯一全局共同零约束态）

<a id="thm-c97-cluster-unique"></a>

$\omega_{\rm cl}$ 是唯一满足
$\omega(q_j)=0$ 对所有 $j\in\mathbb Z$ 成立的全局态。
它是纯态，因而满足 v96 的 C96。

**证明。**
由共轭关系和 $\alpha^2=\operatorname{id}$，

$$
\alpha(q_j)=\frac{I-X_j}{2}=:P_j^-.
$$

所以 $\omega_{\rm cl}(q_j)=\omega_+(P_j^-)=0$，存在性成立。

反向，设 $\omega(q_j)=0$ 对全部 $j$ 成立，并令
$\varphi=\omega\circ\alpha$。
则 $\varphi(P_j^-)=\omega(q_j)=0$。
对任何有限窗口 $I_r$，正算符
$\sum_{j\in I_r}P_j^-$ 的共同零空间只有
$\lvert +\rangle^{\otimes|I_r|}$ 一条射线。
正归一态在该和上的期望为零，迫使其支撑落入这个一维核。
所以 $\varphi$ 的每个有限限制都等于相应的全 $\lvert +\rangle$ 乘积态。
由局域代数的范数稠密性，$\varphi=\omega_+$。
再次复合 $\alpha$，便得 $\omega=\omega_{\rm cl}$。

最后，$\omega_+$ 的每个有限限制均纯。
若它有非平凡全局凸分解，将分解限制到每个有限层，有限纯性迫使各支限制都相同；
再由稠密性，整个分解只能平凡。
因此 $\omega_+$ 纯。
自同构在态空间上给仿射双射，保持纯态，所以 $\omega_{\rm cl}$ 纯。
这也可由前文“正零约束的唯一共同解为纯态”直接推出。

这里的纯性由明确的结构证明；没有使用“每层纯，所以任意弱星极限仍纯”。
v96 已给出后一说法的反例 [7](#ref-v96)。

### 命题 11.5（全局纯，单点读出完全混合）

<a id="prop-c97-cluster-one-site"></a>

任一单点的限制态都是 $I/2$。

**证明。**
有

$$
\omega_{\rm cl}(X_j)
=\omega_+(Z_{j-1}X_jZ_{j+1})=0.
$$

CZ 共轭同样将 $Y_j$ 送为 $Z_{j-1}Y_jZ_{j+1}$，
故 $\omega_{\rm cl}(Y_j)=0$。
又因 $\alpha(Z_j)=Z_j$，有 $\omega_{\rm cl}(Z_j)=0$。
三个 Pauli 读数全为零，归一化给单点密度态 $I/2$。

**白话图景。**整个无限关系网只允许一份共同零约束态，而且这份态是纯的。
单独看任何一个位置，却得到完全混合的读数。
纯性保存在全体关联中，局部混合不要求增加第二份整体来源。
有限截口的端点属于观察截断；双向无限模型没有在宇宙之外另设初态端点。

### 11.2 多看两格：固定窗口的来源歧义精确消失

### 定理 11.6（局域压缩最终为标量）

<a id="thm-c97-cluster-local-scalar"></a>

对固定窗口 $I_r$，若 $m\ge r+2$，则对全部 $B\in\mathcal A_r$，

<a id="eq-c97-cluster-local-scalar"></a>

$$
\boxed{P_mBP_m=\omega_{\rm cl}(B)P_m.}
\tag{11.6}
$$

因此 $D_{r,m}=0$。

**证明。**
CZ 共轭使局域支持至多扩大一格，故 $U_mBU_m$ 支撑在 $I_{r+1}$ 内。
当 $m\ge r+2$ 时，这些位置都属于已经固定为 $\lvert +\rangle$ 的内部位置，
不包含自由端点。
令

$$
P_m^0=
I_{\{-m,m\}}\otimes
\bigotimes_{-m<j<m}\lvert +\rangle\langle +\rvert_j,
\qquad P_m=U_mP_m^0U_m.
$$

于是

$$
P_m^0(U_mBU_m)P_m^0
=c_B P_m^0,
\qquad
c_B=\omega_+(\alpha(B))=\omega_{\rm cl}(B).
$$

再共轭 $U_m$ 就得到式 [(11.6)](#eq-c97-cluster-local-scalar)。
每个支撑在 $K_m$ 的归一态都对所有 $B\in\mathcal A_r$ 给出同一读数，
故窗口限制完全相同，$D_{r,m}=0$。

### 推论 11.7（固定窗口的显式鲁棒界）

<a id="cor-c97-cluster-robust"></a>

若 $M\ge r+2$ 且 $\rho_M(Q_M)\le\delta$，则

<a id="eq-c97-cluster-robust"></a>

$$
\boxed{
D(\rho_M|_{\mathcal A_r},\omega_{\rm cl}|_{\mathcal A_r})
\le\min\{1,\sqrt\delta\}.
}
\tag{11.7}
$$

**证明。**
在定理 [10.1](#thm-c97-inner-certificate) 中固定 $m=r+2$。
此时 $D_{r,m}=0$ 且 $\Delta_m=1$，直接代入即可。

**白话图景。**每个有限截口虽然都有多份允许内容，但对一个固定窗口，多加入两格相容关系后，
这些内容已经无法在窗口里给出不同答案。
剩下的自由度继续留在更远的截口处。
约束若有小缺额，窗口读数的误差仍有明确上界，而且不随后来增加的外层大小恶化。

### 11.3 二元归一几何与既有恢复接口

对归一向量 $\Psi$，比较两个门词
$u=X_j$、$v=Z_{j-1}Z_{j+1}$。
它们的 Gram 块为

$$
G_j=
\begin{pmatrix}
1&z\\
\overline z&1
\end{pmatrix},
\qquad
z=\langle u\Psi,v\Psi\rangle
=\langle\Psi,S_j\Psi\rangle\in\mathbb R.
$$

归一化后
$G_j/2=(I+zX)/2$，
对应 Bloch 坐标 $(z,0,0)$。
而

$$
\langle\Psi,q_j\Psi\rangle=\frac{1-z}{2}.
$$

所以零缺额把这一二元关系点固定到球的 $+X$ 端点。
它给出一般二元 Gram 归一化的一个具体截面；
没有将整个无限链无损压成一个三维球。

式 [(11.6)](#eq-c97-cluster-local-scalar) 也接到项目已经建立的恢复接口：
编码子空间上的全部逻辑态在窗口 $I_r$ 上具有同一限制，
等价于擦除该窗口后，逻辑信息仍能由其内部补端口恢复。
这是精确的 Knill–Laflamme 条件及其互补接口表达，
本轮按 $\Omega$ 静态稿第 8 节承接，而不计为新发现
 [2](#ref-omega)、[9](#ref-knill1997)。
所得到的数学恢复过程存在性，也不自动供应任意指定观察者的实际控制资源。

若压缩仅近似为标量，不能直接宣称维数无关的近似恢复。
无参考输入的迹距离控制，尚未自动给出统一的完全有界或 diamond 范数控制；
还需参考稳定条件或相应维数估计。
本节的定量结论因此限定为局域读口和局域迹距离稳定，
而精确压缩模型连接精确恢复。

**白话图景。**同一项局域压缩关系有两种读法：
从观察窗口看，剩余来源已经没有可见区别；
从其余内部端口看，那些逻辑区别仍可被保存和恢复。
区别没有被宇宙抹掉，只是当前窗口已经不再承载它们。
二元读出、整体唯一性与内部信息保存，因此可以放在同一套约束中比较。

<a id="section-12"></a>

## 12. 把正约束还原为两个关系的有限三维比较

<a id="sec-c97-two-relation-gram"></a>

### 定义 12.1（两个内部关系的 Gram 读出）

给定态 $\varphi$ 与 $a,b\in\mathcal A$，记

$$
G_\varphi(a,b)=
\begin{pmatrix}
\varphi(a^*a)&\varphi(a^*b)\\
\varphi(b^*a)&\varphi(b^*b)
\end{pmatrix},\qquad
T=\varphi(a^*a)+\varphi(b^*b).
$$

对任意 $s,t\in\mathbb C$，

$$
(\overline s,\overline t)G_\varphi(a,b)\binom{s}{t}
=\varphi((sa+tb)^*(sa+tb))\ge0,
$$

故 $G_\varphi(a,b)\ge0$。

若 $T>0$，令 $z=\varphi(a^*b)$，则

<a id="eq-c97-general-gram-ball"></a>

$$
\frac{G_\varphi(a,b)}T=\frac{I+\mathbf r\cdot\boldsymbol\sigma}{2},
\qquad
\mathbf r=
\left(\frac{2\operatorname{Re} z}T,-\frac{2\operatorname{Im} z}T,
\frac{\varphi(a^*a)-\varphi(b^*b)}T\right),
\qquad \left\lVert \mathbf r\right\rVert\le1.
\tag{12.1}
$$

其中 $\boldsymbol\sigma=(X,Y,Z)$ 为 Pauli 矩阵。
正性等价于两个本征值 $(1\pm\left\lVert \mathbf r\right\rVert)/2$ 均非负。

### 命题 12.2（零关系是这一球中的确定方向）

令 $q=(a-b)^*(a-b)$。
若 $T>0$，则

<a id="eq-c97-gram-defect"></a>

$$
\boxed{\varphi(q)=T(1-r_x).}
\tag{12.2}
$$

因此 $\varphi(q)=0$ 当且仅当 $\mathbf r=(1,0,0)$。
若 $T=0$，则 $G_\varphi(a,b)=0$ 且 $\varphi(q)=0$，不作除零归一化。

**证明。**
展开平方得
$\varphi(q)=T-z-\overline z=T-2\operatorname{Re} z$，即所需公式。
在单位球内 $r_x=1$ 强制另外两个坐标为零。
若 $T=0$，正矩阵的两个对角元均为零，其行列式非负迫使非对角元也为零，
所以缺额同样为零。

这是项目二元正核归一化的一个直接应用 [5](#ref-v78closure)、[3](#ref-v74)。
它与前文的 $\Gamma$ 球各有明确对象：
这里编码两个关系词在同一内容上的吻合程度，零关系落在球面的一端；
前文编码一个读口在两个允许内容之间留下的区别，唯一性使区别球缩向中心。
两个构造都保留其所需的尺度或共同均值。
没有从“每个二元块有三维表示”推出整个无限关系网只有三个自由度。

**白话图景。**拿两条内部路径去作用于同一份内容，把它们的长度和相互吻合程度放进一个二乘二表。
这个表归一后可以画成球里的一个点。
若两条路径在这份内容上完全重合，点就到达一个确定端点；
若考察的是两个候选来源还剩多少区别，则对应的另一个球向中心缩小。
三维图景使二元关系看得见，完整网络仍由全部这样的比较及其相容关系组成。

<a id="section-13"></a>

## 13. 关系的关系：全部零后果都是有限正序后果

<a id="sec-c97-internal-consequences"></a>

本节仅要求正约束族有限可行，暂不要求 C97。
于是共同解集 $K_\infty$ 非空。

### 定理 13.1（正零后果的有限证书）

<a id="thm-c97-zero-consequence"></a>

对任意 $q\in\mathcal A_+$，以下两项等价：

1. 每个 $\varphi\in K_\infty$ 都满足 $\varphi(q)=0$。

2. 对每个 $\varepsilon>0$，存在有限 $F\Subset J$ 与 $\lambda\ge0$，使


   <a id="eq-c97-zero-consequence-certificate"></a>

   $$
   \boxed{q\le\varepsilon1+\lambda Q_F.}
   \tag{13.1}
   $$

**证明。**
第二项推出第一项：对共同解施加证书，得
$0\le\varphi(q)\le\varepsilon$ 对所有正 $\varepsilon$ 成立。

反向，固定 $\varepsilon>0$，考虑紧集

$$
C=\{\varphi\in S(\mathcal A):\varphi(q)\ge\varepsilon\}.
$$

若它为空，则 $q\le\varepsilon1$，取 $F=\varnothing,\lambda=0$。
若它非空，由第一项知 $C\cap K_\infty=\varnothing$。
若每个 $C\cap K_F$ 都非空，这族紧集有有限交性质，
便会产生一个属于 $C\cap K_\infty$ 的态，矛盾。
故某个有限 $F$ 满足 $C\cap K_F=\varnothing$。
此时

$$
\delta_0=\min_{\varphi\in C}\varphi(Q_F)>0.
$$

取 $\lambda=\left\lVert q\right\rVert/\delta_0$。
对 $\varphi\in C$ 有 $\varphi(q)\le\lambda\varphi(Q_F)$；
对 $\varphi\notin C$ 有 $\varphi(q)<\varepsilon$。
因此全部态均满足
$\varphi(q)\le\varepsilon+\lambda\varphi(Q_F)$。
态分离正序，得到式 [(13.1)](#eq-c97-zero-consequence-certificate)。

于是可以在同一代数内定义关系族的零后果闭合：

$$
\operatorname{Cl}_0(\{q_j\})
=\{q\ge0:\varphi(q)=0\ \forall\varphi\in K_\infty\}.
$$

定理将“由整体强制”与“每个精度有有限正序证书”锁在一起。
这是数学存在性命题；有限证书的搜索算法、长度界、正序判定成本与实际可测菜单，
都不由紧致性自动提供。

**白话图景。**一条新的零关系如果真是整张关系网的后果，就不必把无限网一次塞进观察者。
对任何指定精度，都有一小组内部关系足以把这条新关系的缺额压住。
这给“关系还有关系”一个明确含义：新约束由已有约束的有限证书支持，
继续生成后果也不需要增加网外的物理来源。能证明证书存在，仍与能迅速找到证书不同。

### 定义 13.2（由内部关系确定的零读数空间）

<a id="def-c97-ordered-null-space"></a>

定义自伴实向量空间中的子集

<a id="eq-c97-ordered-null-space"></a>

$$
\begin{split}
J_Q=\{h=h^*:\ &\forall\varepsilon>0\ \exists F\Subset J,\lambda\ge0,\\[-2pt]
&-\varepsilon1-\lambda Q_F\le h\le\varepsilon1+\lambda Q_F\}.
\end{split}
\tag{13.2}
$$

### 命题 13.3（候选 C97 是有序读数空间的一维确定性）

<a id="prop-c97-ordered-quotient"></a>

有

<a id="eq-c97-null-evaluation"></a>

$$
J_Q=\{h=h^*:\varphi(h)=0\ \forall\varphi\in K_\infty\}.
\tag{13.3}
$$

因此 $J_Q$ 是闭实线性子空间，且

<a id="eq-c97-one-dimensional-readout-quotient"></a>

$$
\boxed{\text{C97}\quad\Longleftrightarrow\quad
\dim_{\mathbb R}(\mathcal A_{\rm sa}/J_Q)=1.}
\tag{13.4}
$$

**证明。**
证书推出零评价的方向直接对共同解取值。
反向，对 $h$ 使用紧集
$C=\{\varphi\in S(\mathcal A):|\varphi(h)|\ge\varepsilon\}$，
重复定理 [13.1](#thm-c97-zero-consequence) 的有限交论证和
$\lambda=\left\lVert h\right\rVert/\delta_0$ 的构造，即得两个方向的正序界。
这证明式 [(13.3)](#eq-c97-null-evaluation)，其右侧显然为闭实线性子空间。

若 C97 成立，则共同解只有 $\omega$，因而
$J_Q=\ker\omega\cap\mathcal A_{\rm sa}$；
每个 $h=h^*$ 都满足 $h-\omega(h)1\in J_Q$。
又因共同解非空且其单位读数为一，$1\notin J_Q$，故商空间恰好一维。

反向，若该商空间一维，$[1]\ne0$ 因而张成它。
于是每个自伴 $h$ 都有唯一实数 $c_h$ 使 $h-c_h1\in J_Q$。
由式 [(13.3)](#eq-c97-null-evaluation)，所有共同解都对 $h$ 给出 $c_h$。
它们因而在所有自伴元素、进而全部元素上相同，故由主定理得到 C97。

在 C97 下，系数 $c_h$ 本身就定义唯一整体读数 $\omega(h)$。
正性、归一化和线性由任一已经存在的共同解保证。
这个*实向量空间商*描述“根对每个问题只有一个答案”。
它不是把全部过程合并为一个标量的 $C^*$ 代数商；
更不是 GNS 中的振幅地址空间 $\mathcal A/N_\omega$。

例如在 $M_2$ 中取 $q=\lvert 1\rangle\langle 1\rvert$，唯一根为 $\lvert 0\rangle\langle 0\rvert$。
若将 $q$ 强行视为全代数中的零元并取双边理想商，
由于 $XqX=\lvert 0\rangle\langle 0\rvert$，该双边理想已经包含 $I$，整个商代数变成零。
而正确的根约束仅是 $q\Omega=0$；它没有消去 $q$ 对其他输入的作用。
在纯根情形，v96 的 $\ker\omega=N_\omega+N_\omega^*$
给出与本节零读数空间的另一种标准表达 [7](#ref-v96)、[14](#ref-kadison1957)。

**白话图景。**每个问题的答案被唯一确定，并不表示所有问题是同一个问题，
也不表示所有门成为同一个门。
根上的零关系只描述这些门怎样作用于这份共同内容。
如果把它误写成对所有输入都成立的算符恒等式，
一个最简单的 qubit 例子就会把整个理论一并抹掉。

<a id="section-14"></a>

## 14. 任意正约束都可改写为两个酉门的返回关系

<a id="sec-c97-unitary-return"></a>

### 定理 14.1（保留精确零解的酉返回编码）

<a id="thm-c97-unitary-encoding"></a>

对任意 $q\in\mathcal A_+$，先将其视为已标定的无量纲关系缺额，令

<a id="eq-c97-return-encoding"></a>

$$
p=\frac{q}{1+\left\lVert q\right\rVert},\qquad
u=e^{ip},\qquad
r=\frac14(1-u)^*(1-u)=\sin^2(p/2).
\tag{14.1}
$$

则 $u$ 为代数内酉元，$0\le p\le1$，$0\le r\le1$，而对任意态 $\varphi$，

<a id="eq-c97-return-zero-equivalence"></a>

$$
\boxed{\varphi(q)=0\quad\Longleftrightarrow\quad\varphi(r)=0.}
\tag{14.2}
$$

还具有误差换算界

<a id="eq-c97-return-error-rescaling"></a>

$$
\varphi(r)\le\frac{\varphi(q)}{4(1+\left\lVert q\right\rVert)},\qquad
\varphi(q)\le\pi(1+\left\lVert q\right\rVert)\sqrt{\varphi(r)}.
\tag{14.3}
$$

**证明。**
连续函数演算保证 $u=e^{ip}$ 属于同一含幺代数且酉。
对 $0\le t\le1$，由 $\sin(t/2)\le t/2$，以及正弦在
$[0,\pi/2]$ 上位于其端点弦之上，得到

$$
\frac{t^2}{\pi^2}\le\sin^2(t/2)\le\frac{t^2}{4}\le\frac t4.
$$

函数演算给

$$
\frac{p^2}{\pi^2}\le r\le\frac{p^2}{4}\le\frac p4.
$$

态的 Cauchy–Schwarz 不等式给
$\varphi(p)^2\le\varphi(p^2)$。
所以 $\varphi(p)=0$ 迫使 $\varphi(r)=0$；
而 $\varphi(r)=0$ 迫使 $\varphi(p^2)=0$，进而 $\varphi(p)=0$。
$p$ 与 $q$ 只差正标尺，零解等价成立。
同样由这些不等式，得到
$\varphi(r)\le\varphi(p)/4$ 与
$\varphi(p)\le\pi\sqrt{\varphi(r)}$，即所列误差界。

若原始缺额带有物理单位，应先除以一份固定正标尺，再使用上述归一化；
不能把带单位的范数直接与数字一相加。
因此一般正约束族可以逐条写成

$$
(1-u_j)\Omega=0,
$$

即比较单位门与一段内部酉门的作用结果。
共同精确零态集合不变，故 C97 的成立与否也不变。
近似缺额则必须按式 [(14.3)](#eq-c97-return-error-rescaling) 换算，不能直接使用同一个数值容差。

归一化 $0\le p\le1$ 阻止整周相位混叠。
若跳过这一步，取 $p=2\pi P$、$P$ 为非零投影，
则 $e^{ip}=I$，返回约束对所有态都成立，却完全没有强制 $\varphi(P)=0$。
这与 V74 已指出的离散门采样不足以唯一确定连续生成元相呼应 [3](#ref-v74)。
代数酉元的存在亦不等于某个观察者已经具备实现它的实际门菜单。

### 推论 14.2（每个纯根都有一套这种返回关系表示）

<a id="cor-c97-every-pure-root-return"></a>

给定纯态 $\omega$，令
$N_\omega=\{a:\omega(a^*a)=0\}$。
将所有 $q_a=a^*a$，$a\in N_\omega$，按定理 [14.1](#thm-c97-unitary-encoding) 改写为返回关系。
所得一致约束族满足 C97，唯一共同态恰为 $\omega$。

**证明。**
$\omega$ 满足全部原零关系，故有限可行性成立。
v96 已证纯态由其全部零关系唯一确定 [7](#ref-v96)、[14](#ref-kadison1957)。
返回编码保持共同零态集合，因而新关系族也只留下 $\omega$。
由本轮主定理得到 C97。

此推论说明表达形式具有足够覆盖性，不是从空关系族凭空产生任意指定宇宙。
若先用一个已知 $\omega$ 反构全部 $N_\omega$，那是表示定理；
真正的选源应用仍应先独立声明关系族，再检查有限可行性和 C97。

**白话图景。**每条“这两个内容必须吻合”的正约束，都能改写成一项内部返回实验：
绕一段归一化的酉变化之后，这份内容必须与原来吻合。
归一化使一次整周绕行不能冒充零变化。
因此关系可以始终用两个门的比较来表达；
但实际有哪些门、能否构造它们以及构造要花多少资源，仍须由内部过程给出。

<a id="section-15"></a>

## 15. 继续反着推：哪些更大结构不能被省略

<a id="sec-c97-scope"></a>

前文已经用明确反例说明有限可行性、正零面的性质、完整读口分离性和正容差的作用。
以下补上无穷极限与量子场范围中的三个边界。

### 15.1 关系递增不能换成每层各自唯一

在同一个 $M_2$ 中，若奇数层只要求
$\varphi(\lvert 1\rangle\langle 1\rvert)=0$，偶数层只要求
$\varphi(\lvert 0\rangle\langle 0\rvert)=0$，则每一层都只有一份纯态，
但这些态交替变化，两类约束的共同解为空。
这不是本轮的递增一致约束族。
$Q_{n+1}\ge Q_n$ 或一般有限子集的联合约束，负责保证旧关系不会在下一层被悄悄撤掉。

### 15.2 平均缺额趋零，可以把固定位置的错误藏起来

在双向 qubit 链上取
$Q_m=\sum_{|j|\le m}(I-X_j)/2$。
唯一共同零态为全 $\lvert +\rangle$ 乘积态。
令 $\sigma$ 仅在第零个位置取 $\lvert -\rangle$，其余取 $\lvert +\rangle$。
则对全部 $m\ge1$，

$$
\sigma(Q_m)=1,\qquad
\frac{\sigma(Q_m)}{2m+1}\longrightarrow0.
$$

但固定读口 $(I-X_0)/2$ 在 $\sigma$ 与共同零态上的答案一直相差一。
所以总缺额控制或每条固定关系的缺额趋零，不能任意改成“单位体积平均缺额趋零”。
归一化若同时把待检查的局部错误稀释掉，就改变了证书的意义。

**白话图景。**关系可以越来越多，错误却始终留在眼前同一个位置。
用新增关系的总数去平均，它看起来越来越小；当前读口却一次也没有变对。
因此每次归一化都必须说明保留了哪一个实际问题和误差标尺。

### 15.3 严格局域忠实态的阻碍：不能把本模型直接宣布为任意量子场论

### 命题 15.1（忠实读出中没有非零正零约束）

<a id="prop-c97-faithful-local-obstruction"></a>

设 $\omega$ 在某个子代数 $\mathcal B$ 上忠实，即
$\omega(b^*b)=0$ 蕴涵 $b=0$。
则 $q\in\mathcal B_+$ 且 $\omega(q)=0$ 必有 $q=0$。

**证明。**
在同一 $C^*$ 子代数内取 $b=q^{1/2}$，由忠实性得 $b=0$，故 $q=0$。

在满足谱条件、弱可加性及局域因果性等标准前件的相对论局域网中，
对有界因果凸区域，且其因果补含有非空开区域时，
Reeh–Schlieder 的循环性配合局域性使真空向量对该区域的被表示局域代数分离 [13](#ref-fewster2019)。
若 $q\ge0$ 属于这样的局域代数且
$\langle\Omega,q\Omega\rangle=0$，则 $q^{1/2}\Omega=0$，分离性给 $q=0$。
若起点是抽象局域代数，先得到的是表示像为零；推出抽象 $q=0$ 还要表示忠实。

所以若目标真空在所有这些严格局域代数上忠实，
完全由非零严格局域正零项构成的无挫折选择方案便不适用。
一般 C97 允许完整代数中的有界关系，不要求每条都严格局域；
有限矩阵链和本轮 cluster 例子则有明确的较窄范围。
它们并未由自身推出一般连续量子场论或引力场方程。

**白话图景。**有些整体态在任何有限局部里都保留所有允许方向的非零权重。
这时想在该局部找一个非零的“必须完全为零”的正关系，就会失败。
反着推得到的不是整体观失效，而是关系的选取范围过窄：
必须重新说明哪些整体关系、哪些极限或哪些近似结构能选出目标态。

### 15.4 代数态紧致，不等于固定表示中的正态密度集紧致

令 $\mathcal A=B(\ell^2(\mathbb N))$，取标准正交基 $e_j$，
并设 $q_j=\lvert e_j\rangle\langle e_j\rvert$。
任意有限组零约束都有正态向量解：选一个未被这组约束包含的基方向即可。
但若正态密度矩阵 $\rho$ 满足全部约束，则

$$
\operatorname{Tr}\rho=\sum_j\langle e_j,\rho e_j\rangle=0,
$$

与归一化矛盾。
全体代数态的弱星紧致性仍给共同零态；这些态必不属于该固定表示的正态密度类。
所以若额外要求目标在预选 Hilbert 表示中正态，须另外保证该态类的紧致性或相应紧性条件。
GNS 为每个态提供自己的循环向量表示，不会把它自动变成原固定表示中的正态密度矩阵。

**白话图景。**有限观察每次都能找到候选，不代表这些候选留在你预先选好的同一类密度矩阵中。
它们可能一直往未被固定有限读口看到的方向移动。
整体存在性定理必须写清楚允许哪一类态，才能知道极限究竟落在哪里。

### 15.5 与近期量子多体结果的准确接点

本轮的局域压缩与不可区分性，直接连接无挫折多体理论中的既有结构。
Michalakis–Zwolak 的谱隙稳定工作使用带有空间尺度与统一衰减条件的 Local-TQO，
并另有谱隙、Local-Gap 和扰动衰减前件 [11](#ref-michalakis2013)。
本轮“每个固定读口都有某份有限证书”的定性命题，没有自动给出这些统一估计。

2026 年 10 月 28 日发表的 Jackson–Nachtergaele–Young 论文，
研究六角与 Lieb 等相应 AKLT 格点模型的局域拓扑量子序和谱隙稳定。
作者明确区分两层结论：已知共同零态唯一时，固定局域读数的共同极限是定性后果；
其进一步工作给出依赖边界距离的统一指数速率与支撑控制 [12](#ref-aklt2026)。
这恰好标明本轮之后真正需要补的内容：
从有限证书存在，推进到证书的距离尺度、收缩速度和扰动稳定性。
唯一共同零约束态也不等于已分类所有可能的动力学基态。
本文没有将定性紧致性接续宣称为已解决质量间隙、引力统一或该论文的全部定量问题。

<a id="section-16"></a>

## 16. 从 C97 接回 Hilbert 空间、平方律与量子过程

<a id="sec-c97-reconstruction"></a>

本节直接承接项目已经建立的共同复正比较、效果、复合和实际过程接口，
不把这些接口再次列为本轮尚未讨论过的问题 [2](#ref-omega)、[5](#ref-v78closure)、[6](#ref-v80)。
C97 新承担的是：给定内部关系族后，唯一共同源与纯性不必另行指定。
下面明确每一步使用什么，以及所得结论是什么。

### 16.1 Hilbert 空间是内部关系的表示

### 命题 16.1（由选出的共同态构造振幅地址空间）

<a id="prop-c97-gns-reconstruction"></a>

在有限可行性和 C97 下，设唯一共同态为 $\omega$。
定义

$$
N_\omega=\{a\in\mathcal A:\omega(a^*a)=0\},
\qquad
\langle[a],[b]\rangle=\omega(a^*b).
$$

则商空间 $\mathcal A/N_\omega$ 的完备化为 Hilbert 空间 $H_\omega$。
左乘给出有界表示

$$
\pi_\omega(c)[a]=[ca],\qquad
\Omega=[1],\qquad
\omega(a)=\langle\Omega,\pi_\omega(a)\Omega\rangle.
$$

$\Omega$ 循环，且 $\pi_\omega$ 不可约；此处 $\Omega$ 专指所选共同态的循环向量。

**证明。**
正性使 $\omega(a^*b)$ 为半正内积。
由 Cauchy–Schwarz，不同代表元只要相差 $N_\omega$ 中元素，就有相同内积；
商掉零范数后得到正定内积，完备化给 $H_\omega$。

对任意 $c$ 有 $c^*c\le\left\lVert c\right\rVert^2 1$，故

$$
\omega(a^*c^*ca)\le\left\lVert c\right\rVert^2\omega(a^*a).
$$

因此 $N_\omega$ 为左理想，左乘在商上良定义且
$\left\lVert \pi_\omega(c)\right\rVert\le\left\lVert c\right\rVert$，可以延拓到完备化。
乘法、伴随和单位关系由定义直接保持。
$[a]=\pi_\omega(a)\Omega$ 的线性张成稠密，所以 $\Omega$ 循环。
最后，本轮主定理已证 $\omega$ 纯；v96 的纯态与不可约表示等价给出不可约性。
这是标准 GNS 构造在本轮所选共同态上的应用 [2](#ref-omega)、[8](#ref-landsman1998)、[7](#ref-v96)。

在这个表示中，“内容即地址”可以准确写成

$$
[a]=[b]\quad\Longleftrightarrow\quad
\omega((a-b)^*(a-b))=0
\quad\Longleftrightarrow\quad
\pi_\omega(a)\Omega=\pi_\omega(b)\Omega.
$$

若讨论完整过程相同，还要比较它们在所有前缀 $x$ 后的作用，
即要求 $\pi_\omega(a-b)\pi_\omega(x)\Omega=0$ 对全部 $x$ 成立，
由循环性才等价于 $\pi_\omega(a)=\pi_\omega(b)$。
因此一个根上的地址相同，不会自动删掉它们在其他输入上的差别 [7](#ref-v96)。

**白话图景。**先有共同关系和它们唯一允许的读数，再把所有作用到根上的路径按“得到同一内容”合并。
这些路径之间的重合程度给出内积，补齐极限就得到 Hilbert 空间。
空间不是网外新增的容器，而是内部路径关系的一种表示。
同一内容可以有多个写法；完整门是否相同，还必须检查它对其他内容的作用。

### 16.2 Born 平方律与效果测量

### 命题 16.2（正归一读出在表示中成为 Born 形式）

<a id="prop-c97-born"></a>

对效果 $0\le E\le1$，继承的二元读出概率为 $p(E)=\omega(E)$，则

<a id="eq-c97-born-effect"></a>

$$
p(E)=\left\lVert \pi_\omega(E)^{1/2}\Omega\right\rVert^2.
\tag{16.1}
$$

若 $P$ 为投影，则 $p(P)=\left\lVert \pi_\omega(P)\Omega\right\rVert^2$。
若一个有限端口为完整矩阵代数，则存在唯一密度矩阵 $\rho$，使

<a id="eq-c97-finite-born"></a>

$$
p(E)=\operatorname{Tr}(\rho E),\qquad \rho\ge0,\quad\operatorname{Tr}\rho=1.
\tag{16.2}
$$

对实际完整的有限结果族 $\{E_i\}$，若 $\sum_iE_i=I$，则 $\sum_ip(E_i)=1$。

**证明。**
正元有正平方根，且 $E=(E^{1/2})^*E^{1/2}$，
代入 GNS 公式即得式 [(16.1)](#eq-c97-born-effect)。
投影满足 $P^{1/2}=P$。
有限矩阵代数中的每个线性泛函都可唯一写成 $E\mapsto\operatorname{Tr}(\rho E)$；
对所有秩一正投影的非负评价保证 $\rho\ge0$，单位读数一给 $\operatorname{Tr}\rho=1$。
最后，结果归一化由共同态的线性与单位读数得到。
若 $\rho=\lvert \psi\rangle\langle \psi\rvert$、$E=\lvert e\rangle\langle e\rvert$，则
$p(E)=|\langle e,\psi\rangle|^2$。

因此平方律是已建立的共同复正读出在振幅表示中的必然形式。
本轮没有从一句“唯一整体”单独推出数域必须为复数，也没有把正线性读出藏进 C97 的结论。
此前的共同复正核及其效果接口在这里继续承担原来的作用 [5](#ref-v78closure)、[6](#ref-v80)。

**白话图景。**只要不同内部读口确实共用同一套正归一比较，
在路径振幅表示里，某个结果的权重就是对应分量的长度平方。
整个来源可以纯，而一个局部端口仍可以混合，因为该端口没有保留全体关联。
本轮的 cluster 例子已经把这一点直接做出来了。

### 16.3 独立复合端口给张量积

设两个已经声明的有限完整端口分别为 $M_d$ 和 $M_e$，
其含幺嵌入像在整体内彼此对易。
则乘法映射

$$
\Phi:M_d\otimes M_e\longrightarrow C^*(M_d,M_e),
\qquad a\otimes b\longmapsto ab
$$

是含幺 $*$ 同态。
由于 $M_d\otimes M_e\simeq M_{de}$ 为单代数，非零含幺同态无核；
目标由两端口生成，故该映射满射。
因此联合作用代数就是这两个端口的张量积。
一般无穷代数与非独立端口须另行声明复合范围，不能由这段有限证明直接跳过 [6](#ref-v80)。

**白话图景。**两个端口能独立完整操作且彼此兼容，合起来就有标准张量积结构。
“环境”和“系统”只是整体内部的端口划分，
这种划分可以解释局部混合与关联，不要求在共同来源之外再加一个物理世界。

### 16.4 实际等距过程给完全正操作，特定记录耦合给投影更新

本小节取 $H,H',K$ 为有限维 Hilbert 空间，$\rho$ 为密度矩阵，求和均为有限和。
给定实际实现的等距耦合
$V:H\to H'\otimes K$，$V^*V=I$。
取记录端口正交基 $\lvert i\rangle$，定义
$K_i=(I\otimes\langle i\rvert)V$，则

$$
V\psi=\sum_iK_i\psi\otimes\lvert i\rangle,
\qquad \sum_iK_i^*K_i=I.
$$

忽略记录结果后，系统态变为

<a id="eq-c97-kraus-from-isometry"></a>

$$
\mathcal E(\rho)=\sum_iK_i\rho K_i^*.
\tag{16.3}
$$

该映射保迹；对任意有限参考端口 $R$ 和正矩阵 $X$，

$$
(\mathcal E\otimes\operatorname{id}_R)(X)
=\sum_i(K_i\otimes I_R)X(K_i^*\otimes I_R)\ge0,
$$

故完全正。
若读取结果 $i$，其效果为 $E_i=K_i^*K_i$，
概率 $p_i=\operatorname{Tr}(\rho E_i)$；当 $p_i>0$ 时条件态为
$K_i\rho K_i^*/p_i$。

若实际无扰动记录耦合特取
$V\psi=\sum_iP_i\psi\otimes\lvert i\rangle$，
其中 $P_i$ 为互相正交且完备的投影，便得到

$$
\rho\longmapsto\frac{P_i\rho P_i}{\operatorname{Tr}(\rho P_i)}.
$$

所以 Lüders 更新来自这种记录结构；仅有 Born 概率并不能唯一确定测后扰动。
该区分与项目已有的效果、全结果过程和实际仪器接口一致 [6](#ref-v80)、[7](#ref-v96)。

**白话图景。**一个门怎样改变读数，取决于它怎样把内容与内部记录联系起来。
保留哪个结果、忽略哪个结果，给出条件变化或平均变化。
标准量子操作和投影更新可以由明确耦合推出；
同一组结果概率却未必意味着同一种测后过程。

### 16.5 酉演化、薛定谔方程和不确定性各自的位置

v96 已借助标准 Kadison 插值证明：在同一不可约 GNS 扇区内，
任意两个单位向量可由某个代数酉门 $e^{ih}$ 精确相连 [7](#ref-v96)、[14](#ref-kadison1957)、[15](#ref-spiegel2022)。
这是代数可达性。实际菜单能否合成该门、需要多少记录增长，属于实际过程问题。

若某个内部校准时钟给出的有限维闭合演化是可微的一参数酉群 $U(t)$，则

$$
\dot U(0)^*=-\dot U(0),\qquad H=i\hbar\dot U(0)=H^*.
$$

由群性质有 $\dot U(t)=\dot U(0)U(t)$，因而

<a id="eq-c97-schrodinger"></a>

$$
i\hbar\frac{d}{dt}\psi(t)=H\psi(t),
\qquad \psi(t)=U(t)\psi(0).
\tag{16.4}
$$

时间相关酉路径则有
$H(t)=i\hbar\dot U(t)U(t)^*$。
无穷维情形还须连续性与生成元定义域等条件。
C97 决定共同源；它没有指定实际酉路径、钟速、$\hbar$ 的标定或具体 Hamiltonian。

对任意 $A=A^*,B=B^*\in\mathcal A$，令
$\widetilde A=A-\omega(A)I$、$\widetilde B=B-\omega(B)I$。
定义 $\operatorname{Var}_\omega(A)=\omega(\widetilde A^2)$，$B$ 的方差同理。
共同正核的二元 Cauchy–Schwarz 给

$$
\operatorname{Var}_\omega(A)\operatorname{Var}_\omega(B)
\ge|\omega(\widetilde A\widetilde B)|^2
$$

<a id="eq-c97-robertson"></a>

$$
\ge\left|\frac{\omega([A,B])}{2i}\right|^2.
\tag{16.5}
$$

非对易读口的关系因而限制联合精度。
这种不确定性在有限维也存在，并不需要把无限维本体作为唯一成因 [3](#ref-v74)、[7](#ref-v96)。
实际的重复结果是否每次变化，也取决于态、读口及测量过程；
本征态上的相应投影读出可以确定，不能断言所有读数每次必变。

**白话图景。**共同源提供所有内部变化的共同约束；
选定真实的时钟与门过程后，才谈沿哪条轨迹、以多快的速度变化。
闭合酉变化用该时钟微分，就得到薛定谔方程。
两个读口互不兼容时，精度受同一个二元正关系限制；
稳定的是这套约束，具体结果是否随机还要看当下读口。

<a id="section-17"></a>

## 17. 标准量子公理的依赖总表

<a id="sec-c97-postulate-table"></a>

| 标准结构 | 本轮与此前项目中的推导接口 | 仍须明确的条件 |
|---|---|---|
| 唯一纯整体源 | 有限可行性与 C97 $\Rightarrow$ 唯一正零态 $\Rightarrow$ 纯性。 | 必须给出关系族并证明证书条件；内生一词不自动保证唯一。 |
| Hilbert 空间与态向量 | 选出的 $\omega$ 给半正内积，商零范数并完备化得到 GNS。 | 共同复 $C^*$ 正结构承接此前版本。 |
| 密度矩阵与 Born 规则 | 有限端口正归一泛函等于 $\operatorname{Tr}(\rho\,\cdot)$；投影权重等于振幅平方。 | 继承正线性读出及效果解释。 |
| 可观测量与结果族 | 有限矩阵端口中，自伴元素的谱分解给投影结果；一般正效果和为单位给 POVM。 | 代数允许的效果是否实际可测仍由菜单规定。 |
| 复合与纠缠 | 对易完整有限矩阵端口的生成代数为张量积；整体态限制可混合。 | 一般复合范围及实际独立性按已有接口声明。 |
| 完全正过程与仪器 | 实际等距耦合及内部记录给 Kraus 分解、完全正性和条件更新。 | 实现耦合与记录可用性不由根的唯一性提供。 |
| 投影测后更新 | 特定无扰动投影记录耦合给 Lüders 形式。 | 概率本身不唯一决定测后态。 |
| 酉动力学与薛定谔方程 | 同扇区代数酉可达；可微酉群加内部时钟给生成元方程。 | 实际轨迹、时钟标定、连续性和定义域另有前件。 |
| 不确定性 | 二元 Gram 正性推出协方差及对易子下界。 | 适用于所声明读口；不等同于所有结果必然变化。 |
| 时空与引力 | 本轮提供共同源和局域稳定的结构条件。 | 尚未由 C97 推出时空度规、Einstein 方程或全部场耦合。 |

表中已完成的接口直接继承，不将每个版本都重新开启为相同的未解问题。
本轮也没有把其他接口的前件包装成 C97 的推论。
一个简单检验是：在交换代数 $C(X)$ 中，一组正函数也可能只在某点同时为零，
从而满足 C97 并选出点评价纯态。
所以 C97 是共同源的选择条件；单靠它并不能排除所有经典关系模型。
复量子结构的工作仍由项目此前共同复正核、复合和过程条件承担。

**白话图景。**这一门理论现在有一条清楚的主干：
内部关系先确定唯一来源，共同正比较把它表示为量子态，
内部端口给局部系统和纠缠，内部记录耦合给量子操作，
内部时钟把酉变化写成运动方程。
每个环节都有对应定义和证明，不能把选出来源这一步当成已经自动选出了所有物理规律。

<a id="section-18"></a>

## 18. 完整白话：这一轮究竟怎样理解量子

<a id="sec-c97-plain-whole"></a>

宇宙在这个候选模型中是一份共同内容 $\Omega$。
观察者、环境、他者、尺子、钟、程序和所谓参数，全部属于这份内容内部的关系。
观察者每次得到的，是这些关系在一个具体读口上的答案。
稳定对象是某些内部读法持续相容所形成的结构；
把它称作“对象”并不要求在共同来源之外另立一种本体。

观察者手里的关系总是有限的，因此眼前可能有许多完整补全。
新候选要求：先固定一个问题，再把相关内部关系补得充分一些，
所有允许补全对此问题的答案就可以被夹到任意一致。
每个问题都能这样确定，并且有限关系始终相容，
便证明整体只有一份共同来源。
约束都是正零关系，因此无法让两份不同来源靠正负抵消伪装成它；纯性也随之得到。

两条路径若作用于根后得到同一内容，它们就是这个内容的两个写法。
比较两条路径的长度和相互吻合程度，给出一个正的二元表；
归一化后，它能画成三维球里的一个点。
所有二元表相互兼容时，形成共同的振幅空间。
对某结果的读数，便是相应振幅分量的长度平方。
局部读口看不到全部关联，所以一份纯的整体可以在局部显得混合。

关系可以继续谈关系：某条新关系若由整体强制，就能在任意精度下找到有限的内部证书。
一个门的参数也可以作为其他内部过程的读出；
但这种递归必须保持同样的相容性、精度和实际实现要求。
写下一个门的数学表达，与观察者已经构造出它并不相同。
发生真实记录变化的门过程，可以用来校准局域时钟；
把同一个门拆成更多语法步骤，不会凭空让物理时间变长。

本轮的无限 cluster 链给出具体图景：每个有限截口都有四维未决自由度，
但它们随着截口增长留在更远的位置，无法继续改变一个固定窗口的读数。
整体因此唯一，局部却仍有量子混合和关联。
关系略有缺额时，固定窗口的误差仍被一块有限证书控制。
这表明“无限整体、有限观察、唯一来源、局部不确定”能够同时成立，
而且每一步都有可以检查的数学对象。

$\Omega$ 在这里是共同来源，不额外定义为任意动力学必然到达的时间终点。
如果要证明某条实际历史最终趋近它，还需要明确更新过程并证明相应收敛。
同理，源的唯一性没有指定轨道必须是圆或椭圆；
轨道形状由实际生成元、读口和几何度量共同决定。
这些区别使“全部内生”能够保持精确，而不会把静态相容、动态选择和观察几何混成一个断言。

<a id="section-19"></a>

## 19. v97 的完成范围与下一步的确定问题

<a id="sec-c97-completion"></a>

本轮给出一个候选 C97，并完成其两种主要表达的严格等价：

$$
\text{有限正序夹逼}
\quad\Longleftrightarrow\quad
\text{任意固定二元读口的候选区别趋零}.
$$

在有限可行性下，它们又恰好等价于唯一共同纯源。
正零后果闭合、二元酉返回表达、三维差异球、固定内层误差证书和无限 cluster 模型，
说明这不只是对已指定纯态换一个名字：可以先写关系，再证明关系足以选源。

下一步有一个具体而非泛泛的目标：
对与实际空间、时钟和资源对应的关系族，求出有限证书的长度、位置范围与误差放大常数，
并证明这些量在允许扰动下的统一控制。
本轮的紧致性保证存在性，cluster 例子给出一种精确可解析的特殊情形；
它们没有自动给任意模型的有效算法或物理时间界。
近期 AKLT 的指数不可区分估计，提示了这一方向需要达到的定量层级 [12](#ref-aklt2026)。

**白话图景。**新候选可以完整说成一句话：
只要内部关系没有有限矛盾，而且对每一个已经选定的问题，都能用更多有限内部关系
把所有候选答案夹到任意一致，那么这张关系网就自己确定唯一的纯来源。
量子读数来自同一来源中的正比较，变化来自其中实际发生的过程，
观察者与他的钟也属于这些过程。
下一步要算清的，是为了把一个具体问题确定到某个精度，内部究竟需要多少关系和多少实际资源。

<a id="references"></a>

## 来源、版本与核读范围

<a id="ref-currentrepo"></a>

### [1]

the-omega-institute，*trureturing* 项目，
[当前公开首页](https://github.com/the-omega-institute/trureturing)。
本轮读到公开首页及其默认 `dev` 分支信息，
但提交历史、提交 API 与只读远端引用查询未能提供可固定的更新 SHA。
仓库证明的核读继续采用提交
`c63ab162315fddd0801cbe9f47dbf3eda6e13360`
的既存选择性快照，不能写成已核查一个更新的 `dev` 提交。
快照中的关键词检索不等于对整个当前仓库的穷尽审计；
公开标题、摘要或开放 PR 也不作为已合并、已逐段验证的数学证明。
本轮未修改仓库、运行仓库构建或数学测试。

<a id="ref-omega"></a>

### [2]

trureturing，*AURIC Omega Static Compatibility Fiber Theory*，
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)。
沿用 v96 已核读的第 1–5 节与第 12 节；本轮补读第 5 节有限逆系统、
第 8 节定义 8.1 及量子恢复的完整证明，
并连续核读定理 62.2 的有限实际菜单证明与命题 63.2 的置信纤维及记录距离证明。
相容有限态延拓与 GNS、有限逆极限、互补环境恒定的恢复判据、
紧致性给有限菜单及有限维态纤维直径均有既有前件。
本文的正零约束面使用另一组量词；不将上述已有内容改称新发现。
共同单位下递增有限维代数的范数完成也不自动覆盖任意量子场论代数。

<a id="ref-v74"></a>

### [3]

trureturing，*AURIC v74：平滑量子历史、余切动力学与内生运动*，
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_SMOOTH_QUANTUM_HISTORIES_COTANGENT_DYNAMICS_AND_ENDOGENOUS_MOTION_V74.md)。
沿用 v96 对第 9–10 节及“时钟重标和离散采样”小节的核读，
包括协方差 Gram 行列式、相对生成元
$H_{\rm rel}=R^*HR-i\hbar R^*\dot R$ 的证明，
以及同一离散门采样不能唯一确定连续生成元的反例。
本轮没有重新审计全文，亦不把静态共同根、移动内部读口或时钟重标计作新增定理。

<a id="ref-v78pure"></a>

### [4]

trureturing，*单一纯整体中的设置—源关系：V78 共同态量词的定量接口*，
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_SINGLE_PURE_WHOLE_SETTING_SOURCE_RELATIONS_V78_CONTINUATION.md)。
沿用 v96 对第 1–2 节的核读；本轮重读定义 1.1 及假设 1.2 的对象和前提说明。
原文区分整体结构、校准根向量与所选纯态泛函，
明确“每个模型固定一个纯态”不等于“全部候选模型只有唯一解”。
本轮把指定关系族的共同态唯一性与纯性连接，不删除关系族本身的选择和实现义务。

<a id="ref-v78closure"></a>

### [5]

trureturing，*已证结构的内生闭合：有限根证书与结果核递归*，
[V78 固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_ENDOGENOUS_CLOSURE_FINITE_ROOT_CERTIFICATES_AND_OUTCOME_KERNEL_RECURSION_V78_CONTINUATION.md)。
沿用 v96 对第 1.1–1.2 节、定义 2.1、命题 2.2、
定理 5.1 及反例、定理 9.1–9.2 完整证明的核读。
全部保尺度复合二元球测试与整体正性的等价，以及结果核树的有限递归相容，
均保留原文的共同复结构、复合域与实际后继前件；本轮未重审全文。

<a id="ref-v80"></a>

### [6]

trureturing，*AURIC v80：全结果二元差分不增与内生量子过程*，
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_ALL_OUTCOME_BINARY_DIFFERENCE_NONEXPANSION_FINITE_ORIENTED_ANCHORS_AND_ENDOGENOUS_QUANTUM_PROCESSES_V80.md)。
沿用 v96 对第 16.1–16.2 节条件式重建总表及内生性范围的核读。
共同复比较、概率效果、实际仪器、独立复合与光滑时钟仍各有前件；
把这些对象置于同一整体并不使相容条件自动成立。

<a id="ref-v96"></a>

### [7]

本对话研究稿，*唯一共同根、内部零约束与递归量子读出：
二元不可分解、同扇区酉可达与无外部初始边界的闭环历史*，
AURIC v96，已交付 29 页 PDF，标题页日期为 2026 年 11 月 3 日（新加坡）。
承接 C96 的正二元不可分解、纯态、GNS 不可约与标量交换子的等价，
全部零约束唯一选态、同一扇区内的代数酉可达，
以及有限闭环历史、内部程序与条件式重建。
v97 的增量是先给关系约束，再用有限比较直径和有限证书刻画其共同态唯一性；
不把本轮重述或标准工具计作新的起源推导。

<a id="ref-landsman1998"></a>

### [8]

N. P. Landsman，
*Lecture Notes on $C^*$-Algebras, Hilbert $C^*$-modules, and Quantum Mechanics*，
arXiv:math-ph/9807030v1，1998 年 7 月 24 日。
[作者预印本](https://arxiv.org/pdf/math-ph/9807030)。
本轮核读第 2.8 节印刷第 37 页引理 2.8.8 的谱值与态实现证明、
其后的态空间弱星紧致性论证，
以及第 2.12 节定义 2.12.1 的纯态极点定义。
有单位代数的态空间在对偶单位球中弱星闭，故由 Banach–Alaoglu 紧；
本文的正零约束闭面、紧交性质及单点面纯性由此逐步证明。
一般非可分情形采用有限子集定向网，不默认序列紧致。

<a id="ref-knill1997"></a>

### [9]

Emanuel Knill、Raymond Laflamme，
*Theory of Quantum Error-Correcting Codes*，
Physical Review A **55**，900–911，1997。
[DOI: 10.1103/PhysRevA.55.900](https://doi.org/10.1103/PhysRevA.55.900)；
[作者预印本](https://arxiv.org/pdf/quant-ph/9604034)。
本轮连续核读预印本定理 3.2 的必要性及恢复构造证明，
另读定理 3.3 声明与定理 3.5 的综合征分解证明，未通读全部 34 页。
精确纠错条件为 $P A_a^*A_bP=\alpha_{ab}P$；
已知区域的擦除使错误乘积张成该区域的全部矩阵代数，
因而得到相应局域标量压缩判据。全部逻辑态与同一个恢复通道的量词不可省略。

<a id="ref-hein2004"></a>

### [10]

M. Hein、J. Eisert、H. J. Briegel，
*Multiparty Entanglement in Graph States*，
Physical Review A **69**，062311，2004。
[DOI: 10.1103/PhysRevA.69.062311](https://doi.org/10.1103/PhysRevA.69.062311)；
[作者预印本](https://arxiv.org/pdf/quant-ph/0307130)。
本轮核读第 II.B 节的图态稳定子、独立可交换生成元与受控 $Z$ 制备，
特别是式 (5)–(10) 及其说明。
有限图态和稳定子码属于标准构造；
本文对双向无穷链、有限区间四维核及固定内部读口的唯一性另给证明，
不声称该论文已经证明本文的全部无穷约束命题。

<a id="ref-michalakis2013"></a>

### [11]

Spyridon Michalakis、Justyna P. Zwolak，
*Stability of Frustration-Free Hamiltonians*，
Communications in Mathematical Physics **322**，277–302，2013。
[DOI: 10.1007/s00220-013-1762-6](https://doi.org/10.1007/s00220-013-1762-6)；
[作者预印本](https://arxiv.org/pdf/1109.1588)。
本轮核读定义 3–5、定理 1 的前提与结论，以及相关局域不可区分性讨论；
未逐项复核全部辅助估计。
Local-TQO 具有空间尺度和统一衰减的量词；谱隙稳定定理还使用整体谱隙、
Local-Gap 及扰动衰减条件。
本文逐个固定读口的定性收缩，不直接供应这些统一估计或谱隙稳定性。

<a id="ref-aklt2026"></a>

### [12]

Thomas Jackson、Bruno Nachtergaele、Amanda Young，
*Local Topological Quantum Order and Spectral Gap Stability for the AKLT Models
on the Hexagonal and Lieb Lattices*，
Communications in Mathematical Physics **407**，文章 261，2026 年 10 月 28 日。
[DOI: 10.1007/s00220-026-05752-9](https://doi.org/10.1007/s00220-026-05752-9)。
作者、日期与卷号以出版全文为准。
本轮核读摘要、第 1 节相关说明、定理 1.1、推论 1.2 及后者的完整压缩范数证明；
未重审聚合物展开或作者的辅助计数证明。
原文明言唯一全零约束态已知时，固定局域期望的共同极限是直接后果；
其新内容包括边界距离的均匀指数速率及显式支撑前因子。
唯一 frustration-free 态亦须与可能存在的其他动力学基态区分。

<a id="ref-fewster2019"></a>

### [13]

Christopher J. Fewster、Kasia Rejzner，
*Algebraic Quantum Field Theory—an Introduction*，
arXiv:1904.04051v2，2019 年 11 月 18 日。
[作者预印本](https://arxiv.org/pdf/1904.04051v2)。
沿用 v96 对第 2.2–2.3 节 GNS 构造和表示唯一性的核读；
本轮补读第 5.1 节谱条件、第 5.2 节弱可加性，
以及定理 26 的完整 Reeh–Schlieder 证明和推论 27。
在原文前提下，真空对被表示的有界因果凸局域代数循环且分离，
因此该代数中的正元若有零真空期望便为零。
若从抽象局域代数出发，首先得到的是其表示像为零；
推出抽象元为零还须表示忠实。本文不把有限矩阵约束层级视为任意 AQFT 的通用模型。

<a id="ref-kadison1957"></a>

### [14]

Richard V. Kadison，*Irreducible Operator Algebras*，
Proceedings of the National Academy of Sciences of the United States of America
**43**(3)，273–276，1957。
[DOI: 10.1073/pnas.43.3.273](https://doi.org/10.1073/pnas.43.3.273)；
[原始论文扫描件](https://www.isibang.ac.in/~soumyashant/misc/collected-works-of-kadison/1950s/1957_IrreducibleOperatorAlgebras.pdf)。
沿用 v96 对第 273–276 页原文的核读，
尤其定理 1 的有限自伴插值证明及推论 2 的零约束结构。
本轮将其作为标准工具，未重新审计原文；
不可约表示与代数内插值的前提不授予未声明的实际门菜单。

<a id="ref-spiegel2022"></a>

### [15]

Daniel Spiegel、Juan Moreno、Marvin Qi、Michael Hermele、
Agnès Beaudry、Markus J. Pflaum，
*Continuous Dependence on the Initial Data in the Kadison Transitivity
Theorem and GNS Construction*，arXiv:2112.13315v2，2022。
[作者预印本](https://arxiv.org/pdf/2112.13315v2)；
[期刊 DOI: 10.1142/S0129055X22500313](https://doi.org/10.1142/S0129055X22500313)。
沿用 v96 对定理 1.14 与定理 3.4 完整证明的核读，未重审全文。
前者刻画同一纯态扇区、共同不可约向量表示与酉变换的关系；
后者给有限插值、自伴插值及目标范数控制，并调用基础 Kadison 定理。
本轮不把同扇区的代数可达性扩成全部扇区或任意实际控制权限。
