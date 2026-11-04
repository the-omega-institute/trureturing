# 唯一共同根、内部零约束与递归量子读出

二元不可分解、同扇区酉可达与无外部初始边界的闭环历史

**AURIC v96：一个完整候选的定义、定理与反向审计**

项目连续研究稿

2026 年 11 月 3 日（新加坡）

## 摘要

本轮承接用户的新修正：一个模型中的本体来源只有一份 $\Omega$，
观察者、环境、程序、记录、思考和计算全部属于同一整体；
不同量子态是内部关系给出的不同读出。
在项目已经建立的复正关系代数及相容读出接口上，提出唯一新候选 C96：
若共同态可正地分成两份而全部非选择读出不变，则两份只能按同一比例回答所有问题。
这一二元约束等价于整体态纯、GNS 表示不可约及其交换子仅含标量。

进一步证明：C96 恰好等价于整体的全部零约束唯一确定其共同态；
其零约束组成左理想，完整过程等价则由一个双边理想确定。
这给“约束不变、内容即地址”提供可检验的数学含义。
借助标准的 Kadison 有限插值定理，同一不可约表示扇区内的每个单位态向量，
都可由共同根经一个代数酉门精确取得。
无限系统中的不同扇区、实际门菜单与无限历史极限必须分别声明。

给出一个完全有限的闭环约束模型：整圈运输的一个一维不动空间，
在没有外部初始状态边界的条件下选出唯一静态纯源；
内部时钟的不同读口却给出不同的系统态。
门参数通过内部程序实现，其精确全输入功能受二程序正交性限制。
不确定性来自二元 Gram 关系；无限维本体不是这一不等式的必要条件。
局域时钟由实际记录校准；门的语法细分不产生新的物理时长。

本文给出定义、完整解析证明、反向见证、有限三维编码及标准量子公理的依赖表。
纯态、不可约及酉传递等经典结果按文献归属；新版本的贡献是项目中的统一接续。
全部数学采用解析推理与独立解析复核，未运行数学程序、CAS、数值求值、枚举或测试。

## 目录

- [1. 这一轮固定什么：一份共同本体，全部内部读出](#section-1)
- [2. 本轮唯一候选 C96：共同根的二元不可分解](#section-2)
- [3. 二元分解为何等价于全体内部操作的交换子](#section-3)
- [4. C96、纯态和不可约性的完整等价](#section-4)
- [5. 反向推理：违反 C96 会留下哪个二元见证](#section-5)
- [6. 为什么 C96 不禁止测量、局部混合及多种合法纯态](#section-6)
- [7. 全部零约束何时唯一确定共同根](#section-7)
- [8. 内容即地址：共同根上的幅度地址与完整门功能](#section-8)
- [9. 共同纯根的酉轨道：同一表示内的精确可达性](#section-9)
- [10. 无限整体的边界：纯乘积态、尾部读口与无限历史](#section-10)
- [11. 正约束的共同零空间：怎样由内部关系选出一份源](#section-11)
- [12. 静态整体中的闭环时钟与变动读出](#section-12)
- [13. 门参数作为内部程序：递归控制的明确形式](#section-13)
- [14. 二程序关系锁定精确门容量：全输入编程定理](#section-14)
- [15. 固定源的态地址，不等于全输入门地址](#section-15)
- [16. 约束固定，读口变化：不确定性的二元几何](#section-16)
- [17. 门的切向、实际局域时钟与关系曲率](#section-17)
- [18. 怎样接回现有量子力学公理](#section-18)
- [19. v96 的完整白话及下一项可证明问题](#section-19)
- [来源、版本与核读范围](#references)

<a id="section-1"></a>

## 1. 这一轮固定什么：一份共同本体，全部内部读出

<a id="sec-c96-position"></a>

本轮由 v95 递增到 v96。v95 研究给定观察更新如何产生极限态；
本轮转向用户现在强调的*整体共同来源*：
完整模型中的所有读出、门参数和观察记录，均属于同一份关系结构。
以下让这两种用途各有精确符号，避免把存在共同来源的结论直接代入动力学极限问题。

### 定义 1.1（整体、共同根与观察截口）

<a id="def-c96-whole-root"></a>

沿用项目已经声明的含单位复 $C^*$ 代数 $\mathcal A$，
以及其上的正归一线性泛函 $\omega$：

$$
\omega(a^*a)\ge0,\qquad \omega(1)=1.
$$

$\mathcal A$ 表示所声明的完整内部关系代数；
系统、程序、时钟和环境等名称标记其中的端口、子代数或复合结构。
共同根的 GNS 表示记为
$(H_\omega,\pi_\omega,\Omega_\omega)$，满足

$$
\omega(a)=\langle\Omega_\omega,\pi_\omega(a)\Omega_\omega\rangle.
$$

一个观察截口通过所用效果、条件记录及允许过程确定；
它们均在这套结构内声明。

这里“完整”说明模型的量化范围；不等于一个有限观察者已经测完所有元素。
GNS 空间是同一份关系的数学表示，没有为本体再增添一个外部物理环境。
使用子代数或张量端口也只规定哪些关系被比较；它本身没有指定宇宙有空间边界。

本轮核读了当前公开 `dev` 页面，但没有取得可固定的更晚提交 SHA。
精确引用继续使用已取得的
`c63ab162315fddd0801cbe9f47dbf3eda6e13360`
理论快照；未把当前开放工作当成已合并定理 [1](#ref-currentrepo)。
仓库仅作只读核对。已有结论直接承接如下：

- $\Omega$ 静态纤维稿第 12 节已给相容有限读出到整体态、再到 GNS 表示的延拓。
  若使用有限维子代数的范数稠密递增链，该构造属于其明确声明的 AF 型范围，
  并不囊括任意量子场代数 [2](#ref-omega)。

- V78 已证明：允许全部相干聚合的二元窗口时，窗口正性可以刻画共同核正性；
  只检查未经聚合的原始词对不足够 [4](#ref-v78closure)。

- V78 的单一纯整体稿已区分“一个模型选择一份纯整体”
  与“所有允许模型只存在一个解”；设置、源和观察关系都可置于整体内 [5](#ref-v78pure)。

- V74 已给二元 Gram 不确定性、移动内部参考与时钟重参数化；
  V80 给全结果差分、复合端口及过程接口 [3](#ref-v74)、[6](#ref-v80)。

所以这一轮直接进入新的接续：

$$
\boxed{\begin{gathered}
\text{共同来源的二元不可分解}\\
\Updownarrow\\
\text{全部零约束唯一锁定共同根}\\
\Downarrow\\
\text{同一表示扇区内的精确酉可达}.
\end{gathered}}
$$

中间的充要关系尤其对应用户的直觉：“不变的是约束。”
后文还给出有限闭环实例，展示具体关系怎样真正选出唯一共同根。

**白话图景。**把宇宙看成一张完整的关系网，观察者、尺子、钟、程序以及他所见的对象，
都在网里。读出某个部分，不需要在网外再放一个观察者。
接下来要精确回答的是：怎样保证这张网的共同来源不能偷偷分成两个不同来源？
哪些内部约束足以把这一份来源完全锁定？
把这两件事证明清楚，才有一个可继续发展的“唯一本体”理论。

<a id="section-2"></a>

## 2. 本轮唯一候选 C96：共同根的二元不可分解

<a id="sec-c96-binary-root"></a>

本节沿用项目已经建立的共同复比较结构，而不把它重新列为本轮结论。
具体地，令 $\mathcal A$ 为含单位 $1$ 的复 $C^*$ 代数；
乘法表示已声明的续接，星运算表示相应的伴随比较。
令 $\omega:\mathcal A\to\mathbb C$ 为一份给定的正归一化读数：

$$
\omega(a^*a)\ge0,\qquad \omega(1)=1.
$$

相容读数的拼合、复正核与循环表示属于此前的接口
 [2](#ref-omega)、[4](#ref-v78closure)、[5](#ref-v78pure)。
本节简写 $\pi=\pi_\omega$、$\Omega=\Omega_\omega$。取其 GNS 三元组 $(H_\omega,\pi,\Omega)$，其中

<a id="eq-c96-gns-interface"></a>

$$
\omega(a)=\langle\Omega,\pi(a)\Omega\rangle,\qquad
 \overline{\pi(\mathcal A)\Omega}=H_\omega,\qquad
 \left\lVert \Omega\right\rVert=1.
\tag{2.1}
$$

内积在第二个变量上线性，记 $[a]=\pi(a)\Omega$。
这里的归一化不等于预先指定表示中的正规性：
任意 $C^*$ 态都具有自己的 GNS 向量表示，但不因此在任意其他表示中正规。

### 定义 2.1（受共同根支配的二元分解）

<a id="def-c96-dominated-split"></a>

正线性泛函 $\nu$ 满足 $0\le\nu\le\omega$，是指 $\nu$ 与
$\omega-\nu$ 均为正泛函。等价地，对每个 $a\in\mathcal A$，

$$
0\le\nu(a^*a)\le\omega(a^*a).
$$

此时 $(\nu,\omega-\nu)$ 是一对相加恢复全部原读数的非归一化分支。
支配必须在同一个完整的 $\mathcal A$ 上成立，不能仅在某个选定的
可交换子代数或一组当前可见的效果上成立。

### 定义 2.2（候选 C96：共同根的二元不可分解）

<a id="def-c96-axiom"></a>

要求上述给定读数 $\omega$ 满足

<a id="eq-c96-axiom"></a>

$$
\boxed{\qquad
 \forall\,\nu\in\mathcal A^*_+,\quad
 0\le\nu\le\omega
 \quad\Longrightarrow\quad
 \nu=\nu(1)\,\omega .
 \qquad}
\tag{2.2}
$$

称此条件为 C96。它要求任何保持全体原读数的正二分，只能改变两支的权重，
不能生成两份不同的归一化根读数。

C96 是本轮对既有量子读数结构增加的一个选择条件。
“一切都在内部”本身没有排除混合态，故不能单凭这句话推出 C96。
本轮要证明的是：这个只涉及一对正分支的条件，
精确等价于共同根的纯性及其循环表示的不可约性。
这些等价关系是标准算子代数结果；本节给出完整证明，
本轮的理论选择是把它们用于约束共同根的含义 [13](#ref-putnam2019)。

**白话图景。**先把整个内部世界已经给出的答案固定下来，再问：能不能把这些答案拆成两套不同的来源，
使两套按权重加起来，恰好恢复所有原答案？
C96 要求，凡是真正保持全部关系的拆法，两套归一化答案都仍是同一套答案。
它由一对分支约束整体；这不意味着观察者不能测量，也不意味着局部不能出现混合。

### 2.1 归一化端点与二元效果表达

称 $B\in\mathcal A$ 为效果，若 $0\le B\le1$；
它对应一个具有“是、否”两个结果的读口。
对 $0\le\nu\le\omega$，记

$$
c=\nu(1),\qquad p=\omega(B),\qquad u=\nu(B).
$$

### 引理 2.3（正泛函的界与零权重端点）

<a id="lem-c96-positive-bound"></a>

正泛函 $\lambda$ 满足

<a id="eq-c96-positive-cs"></a>

$$
|\lambda(a^*b)|^2\le\lambda(a^*a)\lambda(b^*b),
 \qquad \left\lVert \lambda\right\rVert=\lambda(1).
\tag{2.3}
$$

因此 $0\le\nu\le\omega$ 时 $0\le c\le1$；
若 $c=0$，则 $\nu=0$；若 $c=1$，则 $\nu=\omega$。

**证明。**
每个自伴元都是两个正元之差，故其 $\lambda$ 读数为实数；
再将任意元分成自伴实部和虚部，得到
$\lambda(x^*)=\overline{\lambda(x)}$。
展开 $\lambda((a+zb)^*(a+zb))\ge0$ 并对 $z\in\mathbb C$ 完成平方，
得到式 [(2.3)](#eq-c96-positive-cs) 的第一式；
若 $\lambda(b^*b)=0$，则任意大的线性项仍须保持非负，
所以 $\lambda(a^*b)=0$，退化情形亦成立。
又因为 $a^*a\le\left\lVert a\right\rVert^2 1$，

$$
|\lambda(a)|^2\le\lambda(1)\lambda(a^*a)
 \le\lambda(1)^2\left\lVert a\right\rVert^2.
$$

在 $a=1$ 处取等号，得到 $\left\lVert \lambda\right\rVert=\lambda(1)$。
将此结论分别用于 $\nu$ 与 $\omega-\nu$，即得两个端点。

### 命题 2.4（C96 的二元效果零协方差表达）

<a id="prop-c96-zero-covariance"></a>

C96 等价于下述完全二元的条件：

<a id="eq-c96-zero-covariance"></a>

$$
\boxed{\quad
 0\le\nu\le\omega,\quad 0\le B\le1
 \quad\Longrightarrow\quad
 \nu(B)=\nu(1)\omega(B).
 \quad}
\tag{2.4}
$$

也就是任一相容二分的分支标签，与任一二元效果读数之间的协方差均为零。
这里的标签首先是正分解的数学标签，不预设存在额外物理装置能实施它。

**证明。**
C96 直接推出式 [(2.4)](#eq-c96-zero-covariance)。
反向，令 $\delta=\nu-c\omega$，则 $\delta(1)=0$。
对任意非零自伴 $h$，

$$
B_h=\frac12\left(1+\frac h{\left\lVert h\right\rVert}\right)
$$

是效果，所以 $\delta(B_h)=0$ 给 $\delta(h)=0$。
任意 $a$ 可写为两个自伴元的复线性组合，故 $\delta(a)=0$。

**白话图景。**这里的最小问题是一对一对地问：
“如果根真的含有两个不同的正来源，那么选择哪一个来源，会不会影响某个是非问题的答案？”
C96 说不会；若对全部是非问题都不会，所谓两个来源就只剩权重不同。
权重为零或一只是空分支，不能冒充真正的拆分。

<a id="section-3"></a>

## 3. 二元分解为何等价于全体内部操作的交换子

<a id="sec-c96-radon-nikodym"></a>

定义完整交换子代数

$$
\pi(\mathcal A)'=
 \{T\in B(H_\omega):T\pi(a)=\pi(a)T
 \text{ 对每个 }a\in\mathcal A\}.
$$

它要求与每个已声明的内部操作相容。
下面把正分解和这一更大结构逐一对应起来。

### 定理 3.1（受支配正泛函的 Radon–Nikodym 对应）

<a id="thm-c96-rn"></a>

映射

<a id="eq-c96-rn-map"></a>

$$
T\longmapsto\nu_T,\qquad
 \nu_T(a)=\langle\Omega,T\pi(a)\Omega\rangle
\tag{3.1}
$$

在下列两个有序区间之间构成一一、保序且反向亦保序的对应：

<a id="eq-c96-rn-intervals"></a>

$$
\{T\in\pi(\mathcal A)':0\le T\le I\}
 \quad\longleftrightarrow\quad
 \{\nu\in\mathcal A^*:0\le\nu\le\omega\}.
\tag{3.2}
$$

无需假设 $\omega$ 忠实，也无需有限维。

**证明。**
**第一步：由分支构造有界形式。**
给定 $0\le\nu\le\omega$，在稠密空间 $\pi(\mathcal A)\Omega$ 上定义

$$
q_\nu([a],[b])=\nu(a^*b).
$$

由引理 [2.3](#lem-c96-positive-bound)，

<a id="eq-c96-form-bound"></a>

$$
|q_\nu([a],[b])|^2
 \le\nu(a^*a)\nu(b^*b)
 \le\omega(a^*a)\omega(b^*b)
 =\left\lVert [a]\right\rVert^2\left\lVert [b]\right\rVert^2.
\tag{3.3}
$$

若 $[a]=0$，则 $\nu(a^*a)=0$，所有相关交叉项也为零。
故 $q_\nu$ 与代表元选择无关，并唯一连续延拓到
$H_\omega\times H_\omega$。
其满足

$$
0\le q_\nu(x,x)\le\left\lVert x\right\rVert^2.
$$

由 Hilbert 空间有界形式的 Riesz 表示，存在唯一有界算符 $T$，
使 $q_\nu(x,y)=\langle x,Ty\rangle$。
上述二次型不等式给 $T=T^*$ 及 $0\le T\le I$。

**第二步：续接相容迫使 $T$ 落在交换子中。**
对任意 $a,b,d\in\mathcal A$，

$$
\begin{aligned}
\langle[a],T\pi(d)[b]\rangle
 &=\nu(a^*db)\\
 &=\langle\pi(d^*)[a],T[b]\rangle\\
 &=\langle[a],\pi(d)T[b]\rangle.
\end{aligned}
$$

由稠密性和有界性，$T\pi(d)=\pi(d)T$。
在形式的表示式中取 $a=1$、$b=d$，得到
$\nu(d)=\langle\Omega,T\pi(d)\Omega\rangle$。

**第三步：每个正收缩交换子都给合法分支。**
反过来，若 $T\in\pi(\mathcal A)'$ 且 $0\le T\le I$，
则 $T^{1/2}$ 也与 $\pi(\mathcal A)$ 交换，因而

$$
\nu_T(a)=
 \langle T^{1/2}\Omega,\pi(a)T^{1/2}\Omega\rangle
$$

是正泛函。
同理由 $(I-T)^{1/2}$ 得到正泛函 $\omega-\nu_T$。
所以 $0\le\nu_T\le\omega$。

**第四步：唯一性与序。**
对任意 $a,b$，

$$
\langle[a],T[b]\rangle=\nu_T(a^*b).
$$

因此 $\nu_T$ 决定 $T$ 在稠密空间上的全部矩阵元，进而唯一决定 $T$。
若 $T\le S$，同样的向量形式给 $\nu_T\le\nu_S$。
若 $\nu_T\le\nu_S$，则

$$
\langle[a],(S-T)[a]\rangle
 =(\nu_S-\nu_T)(a^*a)\ge0;
$$

密度给 $S-T\ge0$。

这一定理把原来只谈两份读数的条件，提升成对全部续接操作的约束。
$T$ 是保持全体读数比较方式相容的一个分支权重算符。
一般而言，$T$ 位于交换子中，并不自动属于 $\pi(\mathcal A)$，
也不自动成为观察者实际可调用的量子门。
交换子在此是判定给定根能否被正分解的数学结构，
不表示额外添加了一个外部物理对象。

**白话图景。**如果一种拆分真的在整个内部世界都成立，那么先做任意内部操作再看拆分，
与先看拆分再做操作，必须给出同一套比较结果。
这个“处处兼容”恰好就是交换。
于是问题变得很具体：有没有一个非平凡的权重开关，能与所有内部操作同时兼容？
有，就能把根拆开；没有，根就是二元不可分解的。

<a id="section-4"></a>

## 4. C96、纯态和不可约性的完整等价

<a id="sec-c96-pure-irreducible"></a>

### 定义 4.1（纯态与不可约表示）

态 $\omega$ 称为纯态，若

$$
\omega=t\alpha+(1-t)\beta,\qquad
 0<t<1,\qquad \alpha,\beta\text{ 为态}
$$

只能发生在 $\alpha=\beta=\omega$ 时。
表示 $\pi$ 称为不可约，若不存在既非零又非全空间的闭子空间，
对全部 $\pi(a)$ 保持不变。

### 定理 4.2（C96 的结构等价）

<a id="thm-c96-pure-equivalences"></a>

对给定的含单位 $C^*$ 代数态 $\omega$ 及其 GNS 表示，
下列条件等价：

1. C96 成立；

2. $\omega$ 是纯态；

3. $\pi(\mathcal A)'=\mathbb C I$；

4. $\pi$ 不可约。

**证明。**
**条件 1 与条件 2。**
若 $\omega=t\alpha+(1-t)\beta$，则 $\nu=t\alpha$ 满足
$0\le\nu\le\omega$。C96 给 $\nu=t\omega$，从而
$\alpha=\beta=\omega$。
反向，若 $0\le\nu\le\omega$，记 $c=\nu(1)$。
$c=0,1$ 已由引理 [2.3](#lem-c96-positive-bound) 处理。
若 $0<c<1$，则

<a id="eq-c96-convex-split"></a>

$$
\omega
 =c\,\frac{\nu}{c}
 +(1-c)\,\frac{\omega-\nu}{1-c}
\tag{4.1}
$$

是两个态的凸分解。
纯性给 $\nu/c=\omega$，即 C96。

**条件 1 与条件 3。**
由定理 [3.1](#thm-c96-rn)，$\nu=c\omega$ 的唯一对应算符是 $cI$。
所以 C96 等价于交换子中的每个正收缩均为标量。
若所有正收缩都是标量，对任意自伴
$S\in\pi(\mathcal A)'$，选 $r>\left\lVert S\right\rVert$，则

$$
\frac{S+rI}{2r}
$$

是正收缩，故 $S$ 为标量。
将任意交换子分成自伴实部和自伴虚部，得到
$\pi(\mathcal A)'=\mathbb C I$。反向立即成立。

**条件 3 与条件 4。**
若闭子空间 $M$ 对全部 $\pi(a)$ 不变，
由于 $\mathcal A$ 对星运算闭合，$M^\perp$ 也不变。
故其正交投影 $P_M$ 与全部 $\pi(a)$ 交换。
条件 3 迫使 $P_M=0$ 或 $I$，所以 $\pi$ 不可约。
反过来，若交换子包含一个非标量算符，
其自伴实部或虚部至少有一个非标量自伴元 $S$。
自伴谱定理给 $S$ 的某个非零、非单位谱投影 $P$；
所有 $\pi(a)$ 与 $S$ 交换，也与它的谱投影交换。
于是 $PH_\omega$ 是非平凡闭不变子空间，
与不可约性矛盾。

**白话图景。**“根不能拆成两套不同的正答案”“根是纯态”“所有内部操作共同允许的权重开关只有常数”，
说的是同一个条件。
它没有消除叠加：纯态本来就能叠加。
它排除的是一种更具体的情况——在保留全部读口后，根仍只是两套不同状态按经典权重混在一起。

### 4.1 不能把完整交换子偷换成中心

### 命题 4.3（单一因子仍可能有混合根）

<a id="prop-c96-center-counterexample"></a>

“$\pi(\mathcal A)$ 的中心只有标量”不足以推出 C96。

**证明。**
取 $\mathcal A=M_2(\mathbb C)$，
$\omega(a)=\operatorname{Tr}(a)/2$。
它的 GNS 空间可写为 $M_2(\mathbb C)$ 上的 Hilbert–Schmidt 空间，

$$
\Omega=I/\sqrt2,\qquad \pi(a)x=ax.
$$

左乘代数的中心只有标量，但全部右乘算符 $x\mapsto xb$
都属于其交换子。
令 $P_0=\lvert 0\rangle\langle 0\rvert$，取右乘正投影 $T:x\mapsto xP_0$。
对应分支为

$$
\nu(a)=\frac12\langle0|a|0\rangle,\qquad
 (\omega-\nu)(a)=\frac12\langle1|a|1\rangle.
$$

两者均正，而 $\nu$ 不是 $\omega$ 的比例副本。
故 C96 失败，尽管左乘代数是中心平凡的因子。

**白话图景。**“整体没有一个经典中心标签”还不够。
一个因子内部仍然可以承载混合读数。
必须检查所有与内部操作相容的分解方向，也就是完整交换子，
才能排除两套不同正来源被混在同一根里的情况。

<a id="section-5"></a>

## 5. 反向推理：违反 C96 会留下哪个二元见证

<a id="sec-c96-failure-witness"></a>

### 定理 5.1（非平凡分解必被一个效果分开）

<a id="thm-c96-binary-witness"></a>

若 C96 失败，则存在 $0\le\nu\le\omega$，
$0<c:=\nu(1)<1$，以及一个效果 $B$，使

<a id="eq-c96-witness"></a>

$$
\nu(B)-c\omega(B)\ne0.
\tag{5.1}
$$

对应的两个归一化态

$$
\omega_+=\nu/c,\qquad
 \omega_-=(\omega-\nu)/(1-c)
$$

在同一个二元读口 $B$ 上给出不同概率。

**证明。**
选择非比例分支 $\nu$，两个端点不可能发生。
令 $\delta=\nu-c\omega\ne0$。
因 $\delta$ 保持星运算，任意非零见证的自伴实部或虚部中，
至少存在一个自伴 $h$ 使 $\delta(h)\ne0$。
取

$$
B=\frac12\left(1+\frac h{\left\lVert h\right\rVert}\right),
$$

则

$$
\delta(B)=\frac{\delta(h)}{2\left\lVert h\right\rVert}\ne0.
$$

并且

<a id="eq-c96-conditional-separation"></a>

$$
\omega_+(B)-\omega_-(B)
 =\frac{\nu(B)-c\omega(B)}{c(1-c)}\ne0.
\tag{5.2}
$$

若另有一族含同一单位 $1$ 的有向有限观察子代数 $\mathcal A_i$，
且 $\bigcup_i\mathcal A_i$ 在 $\mathcal A$ 中范数稠密，
则上述 $h$ 还可选在某一个 $\mathcal A_i$ 中。
理由是 $\delta$ 连续；先足够逼近一个 $\delta(h)\ne0$ 的自伴元，
仍有非零读数差，再于该有限代数内归一化成效果。
这证明的是：*一个已经存在的全局分解，必有一个有限区分见证*。
它没有说有限次实验可以穷尽检查全部全局分解。

**白话图景。**现在按“假如不满足会怎样”反推：
如果根确实可以拆成两套不同的正答案，就一定能找到一个具体的是非问题，
两套答案的概率不同。
所以失败不会只是一个遥远的抽象标签；它必会落到一对分支与一个二元读口之间的可区分关系上。
但要断言全局没有任何这种拆分，仍需要对完整内部结构的论证。

### 5.1 归一化的三维概率报告

对定理中的 $(\nu,B)$，记 $p=\omega(B)$、$u=\nu(B)$。
分支标签与二元读数形成归一化表

<a id="eq-c96-binary-table"></a>

$$
P=
 \begin{pmatrix}
 u & c-u\\
 p-u & 1-c-p+u
 \end{pmatrix}.
\tag{5.3}
$$

第一行是分支 $+$，第二行是分支 $-$；两列分别是读数“是”和“否”。
四项由正泛函直接给出，均非负，总和为一。其行列式为

<a id="eq-c96-table-determinant"></a>

$$
\boxed{\det P=u-cp.}
\tag{5.4}
$$

所以 C96 正好要求任一相容分解与任一效果给出的这张表都为独立分布。

把两个标签记成 $x,y\in\{-1,+1\}$，定义三个实数

<a id="eq-c96-tetrahedron-coordinates"></a>

$$
r=2c-1,\qquad s=2p-1,\qquad
 t=1-2c-2p+4u.
\tag{5.5}
$$

则四项概率统一为

$$
P(x,y)=\frac14(1+xr+ys+xyt),
 \qquad t-rs=4(u-cp).
$$

这给出一个完整的三维有限报告。
仅施加四个概率非负与归一化时，其几何区域是顶点

$$
(1,1,1),\quad(1,-1,-1),\quad(-1,1,-1),\quad(-1,-1,1)
$$

组成的四面体；它不是 Bloch 球。
对给定的 $\omega$，实际可实现的表还可能只占其中一部分；
C96 进一步要求每张相容表都满足 $t=rs$。
这一层报告只有两个经典二元标签的联合概率，
不能凭维数同为三就加入未给出的相干相位。

若希望把每一支的二元答案写进既有 Bloch 表达，
可另定义

$$
q_+=u/c,\qquad q_-=(p-u)/(1-c),\qquad
 \Gamma_\pm=
 \begin{pmatrix}q_\pm&0\\0&1-q_\pm\end{pmatrix}.
$$

令 $Z=\operatorname{diag}(1,-1)$，则

<a id="eq-c96-conditional-bloch"></a>

$$
\Gamma_\pm=\frac12\bigl(I+(2q_\pm-1)Z\bigr),
 \qquad
 \boldsymbol b_\pm=(0,0,2q_\pm-1).
\tag{5.6}
$$

两点都在 Bloch 球的同一条直径上，
式 [(5.1)](#eq-c96-witness) 恰好意味着
$\boldsymbol b_+\ne\boldsymbol b_-$。
这是二元条件读数的几何编码，不声称原来的整个无限维系统就是一个量子比特。

**白话图景。**把拆分和回答都写成“是、否”，四个概率加起来等于一，所以只剩三个独立数。
这三个数首先组成一个四面体。
若单独画每一支对同一问题的回答，两支就在 Bloch 球的一条直径上：
根能被非平凡拆开时，总有一次比较把这两个点分开。
三维图景因此来自明确的二元读数，几何形状由实际关系决定。

<a id="section-6"></a>

## 6. 为什么 C96 不禁止测量、局部混合及多种合法纯态

<a id="sec-c96-scope"></a>

### 6.1 只在一个局部读口成立的支配不能冒充全局支配

令

$$
\lvert \pm\rangle=\frac{\lvert 0\rangle\pm\lvert 1\rangle}{\sqrt2},\qquad
 P_\pm=\lvert \pm\rangle\langle \pm\rvert,\qquad
 P_0=\lvert 0\rangle\langle 0\rvert.
$$

在 $\mathcal A=M_2(\mathbb C)$ 上取

$$
\omega(a)=\operatorname{Tr}(P_+a),\qquad
 \nu(a)=\frac12\operatorname{Tr}(P_0a).
$$

两者均为正泛函，$\nu(1)=1/2$。
在 $Z$ 对角子代数上，若 $a=\operatorname{diag}(a_0,a_1)\ge0$，
则

$$
\nu(a)=a_0/2,\qquad
 \omega(a)-\nu(a)=a_1/2\ge0.
$$

于是只看这个局部读口，确实有 $0\le\nu\le\omega$。
但在全代数效果 $P_-$ 上，

<a id="eq-c96-local-false-domination"></a>

$$
\omega(P_-)=0,\qquad
 \nu(P_-)=\frac14,
\tag{6.1}
$$

所以全局支配不成立。

特别地，这个 $\nu$ 正是测量 Kraus 算符 $K=P_0$ 的分支

$$
\nu(a)=\omega(K^*aK).
$$

因此一般测量分支虽然正，却不一定受测量前的 $\omega$ 全局支配。
各分支之和通常是测量后的读数，并不等于全部测量前读数。
C96 只禁止保持全部原读数的非平凡正分解，
因而并未排除测量过程中的结果分支。

**白话图景。**只问“零还是一”，叠加态看起来可以拆成两半；
再问一个相干方向的问题，这种拆法就不再保留原答案。
测量当然可以产生分支，但它也可能改变后续问题的答案。
C96 针对的是全体答案丝毫未变时仍能否拆出两个不同来源，
所以它和正常的量子测量没有冲突。

### 6.2 整体纯态可以有混合的局部读数

在 $\mathbb C^2\otimes\mathbb C^2$ 中，取 Bell 向量

$$
\lvert \Phi_+\rangle=\frac{\lvert 00\rangle+\lvert 11\rangle}{\sqrt2},
 \qquad
 \omega_{\Phi_+}(A)=\langle\Phi_+|A|\Phi_+\rangle.
$$

全矩阵代数能将任意非零向量送到任意向量，
故对全代数 $M_4(\mathbb C)$，上述向量表示不可约且循环，
故由定理 [4.2](#thm-c96-pure-equivalences)，它是纯态并满足 C96。
限制到 $M_2(\mathbb C)\otimes I$ 后却有

$$
\omega_{\Phi_+}(a\otimes I)=\frac12\operatorname{Tr}(a).
$$

这一局部态可分成 $\lvert 0\rangle$ 与 $\lvert 1\rangle$ 的等权混合。
这些局部分解不能延伸为受原 Bell 态支配的非比例全局分解，
否则就与已证的 C96 矛盾。
因此根的纯性和观察者某个局部接口的混合性可以同时成立；
本节的“完整”始终相对于已声明的 $\mathcal A$。

**白话图景。**同一整幅关系图可以不可分解，而只看其中一块时，答案呈现混合。
遗漏的关联仍在整体读口中。
观察者不知道某些关系，并不证明全局根由多个不同根混成；
反过来，把一个接口称为“整体”，也需要说明它包含哪些关系。

### 6.3 给定全读数的表示唯一性，与只准有一个合法态不同

### 命题 6.1（共同根的循环表示只至酉等价唯一）

<a id="prop-c96-gns-uniqueness"></a>

若 $(\mathcal H,\pi,\Omega)$ 与
$(\mathcal H',\pi',\Omega')$ 均为同一份全读数 $\omega$ 的循环表示，
则存在唯一酉算符 $W:\mathcal H\to\mathcal H'$，使

$$
W\Omega=\Omega',\qquad W\pi(a)=\pi'(a)W
 \quad(a\in\mathcal A).
$$

该结论对混合态也成立，不需要 C96。

**证明。**
在稠密空间 $\pi(\mathcal A)\Omega$ 上定义

$$
W\pi(a)\Omega=\pi'(a)\Omega'.
$$

两边内积都由同一个 $\omega(a^*b)$ 给出，因此映射良定义且等距。
循环性使它的值域稠密，延拓后为酉算符。
续接关系在稠密空间上直接给出交织式，连续延拓到全空间。
任何满足所列条件的算符在循环稠密空间上均被此公式确定，故唯一。

此唯一性没有选出 $\omega$ 本身。
例如 $M_2(\mathbb C)$ 上由 $\lvert 0\rangle$ 与 $\lvert 1\rangle$ 给出的两个态都满足 C96，
但它们是不同的合法读数。
“实际整体采用一份 $\omega$”是对模型实际状态的指定；
“一份已给全读数的循环实现至酉等价唯一”是表示定理；
“C96 排除该读数的非平凡正分解”是纯性约束。
这三句话须分别成立。

此外，任意 GNS 根 $\Omega$ 都是表示空间中的一个向量。
若改为允许全部 $B(H_\omega)$，其秩一向量态当然纯；
但这不会自动证明原先 $\mathcal A$ 上的 $\omega$ 纯。
命题 [4.3](#prop-c96-center-counterexample) 已给出反例：
四维 Hilbert–Schmidt 空间中的向量 $\Omega=I/\sqrt2$，
限制在左乘 $M_2$ 后给出的正是混合态。
把所有 $B(H_\omega)$ 操作加入读口，可能增添了模型尚未给出的操作。

最后，本节没有选择任何实际时间过程。
共同根、纯根及循环表示唯一性均不推出所有轨道朝向同一终点。
这种收敛需要像 v95 那样对实际过程作另外的动力学判定 [7](#ref-v95)。

**白话图景。**同一整套答案可以换坐标表示，换完仍是同一个根；
这叫表示唯一。
不同整套答案也可能各自完全合法，这不与表示唯一冲突。
本轮新增的是根内部的不可分解性。
它使“只有一份不可再混合的共同来源”有了精确含义，
而“所有运动最后都到这里”仍需由具体运动规律证明。

<a id="section-7"></a>

## 7. 全部零约束何时唯一确定共同根

<a id="sec-c96-zero-constraints"></a>

前节的 C96 已等价于纯态及不可约 GNS 表示。
这一节把它接到用户要求的“把公理锁成定义之间的约束”。

### 定义 7.1（根的零关系）

<a id="def-c96-null-relations"></a>

定义

<a id="eq-c96-null-leftideal"></a>

$$
\mathcal N_\omega=\{a\in\mathcal A:\omega(a^*a)=0\}.
\tag{7.1}
$$

这些是对共同根作用后幅度为零的关系。
满足其全部零约束的归一态集合为

<a id="eq-c96-zero-state-set"></a>

$$
Z(\omega)=\{\varphi\in S(\mathcal A):
\varphi(n^*n)=0\ \text{对每个 }n\in\mathcal N_\omega\}.
\tag{7.2}
$$

由正泛函的 Cauchy–Schwarz 不等式，
$\mathcal N_\omega$ 是闭线性空间。对 $c\in\mathcal A$，

$$
0\le\omega((cn)^*(cn))
\le\left\lVert c\right\rVert^2\omega(n^*n)=0,
$$

所以它是左理想。
GNS 构造正是将这些零关系商掉：

$$
\langle[a],[b]\rangle=\omega(a^*b),\qquad
\Omega_\omega=[1],\qquad \pi_\omega(c)[a]=[ca],
$$

再取完备化。
$\left\lVert \pi_\omega(c)\right\rVert\le\left\lVert c\right\rVert$ 保证门的代数作用成为有界作用。
这是项目已有 GNS 构造在本节所需的部分 [2](#ref-omega)、[12](#ref-fewster2019)。

### 引理 7.2（标准的有限自伴插值）

<a id="lem-c96-kadison"></a>

设 $\pi$ 是含单位 $C^*$ 代数 $\mathcal A$ 的不可约表示，
$K\subset H$ 有限维，$T\in B(H)$ 自伴。
存在 $a=a^*\in\mathcal A$，使

$$
\pi(a)\xi=T\xi\quad(\xi\in K),
\qquad \left\lVert a\right\rVert\le\left\lVert T\right\rVert.
$$

非自伴版本允许对有限组线性独立向量指定任意目标。

这是 Kadison 传递定理的标准形式；有限插值及自伴选择见原始定理，
所写范数控制见 Spiegel 等的定理 3.4 [8](#ref-kadison1957)、[10](#ref-spiegel2022)。
本节显式使用这一已证明的数学定理，后续推导给出完整步骤。

### 定理 7.3（C96 的零约束刻画）

<a id="thm-c96-null-unique"></a>

对任意含单位复 $C^*$ 代数上的态 $\omega$，以下条件等价：

$$
\boxed{\quad
\mathrm{C96}
\quad\Longleftrightarrow\quad
\omega\text{ 纯}
\quad\Longleftrightarrow\quad
Z(\omega)=\{\omega\}.
\quad}
$$

在这些条件下还有

<a id="eq-c96-kernel-null-sum"></a>

$$
\ker\omega=\mathcal N_\omega+\mathcal N_\omega^*.
\tag{7.3}
$$

这里的和是代数和，无须在等式右侧额外取闭包。

**证明。**
前两个条件的等价已经在前节证明。
设 $\omega$ 纯，则 $\pi_\omega$ 不可约。
取 $h=h^*$ 且 $\omega(h)=0$，置
$\xi=\pi_\omega(h)\Omega_\omega$。
它与 $\Omega_\omega$ 正交。
若 $\xi=0$，已有 $h\in\mathcal N_\omega$。
若 $\xi\ne0$，在
$K=\operatorname{span}\{\Omega_\omega,\xi\}$ 上指定自伴算符

$$
T\Omega_\omega=0,\qquad T\xi=\xi,
$$

并在 $K^\perp$ 上取零。
由引理 [7.2](#lem-c96-kadison) 取 $a=a^*\in\mathcal A$ 实现此作用。
于是

$$
a\in\mathcal N_\omega,\qquad
c:=h-ah\in\mathcal N_\omega,\qquad
h=ha+c^*.
$$

因 $\mathcal N_\omega$ 是左理想，$ha\in\mathcal N_\omega$。
所以每个自伴零期望元素属于 $\mathcal N_\omega+\mathcal N_\omega^*$。
把一般 $x\in\ker\omega$ 分解为实部与虚部，得到同一结论。
反向包含由 Cauchy–Schwarz 给出
$\omega(n)=\omega(n^*)=0$，故式 [(7.3)](#eq-c96-kernel-null-sum) 成立。

现在取 $\varphi\in Z(\omega)$。
正性及 Cauchy–Schwarz 给 $\varphi(n)=\varphi(n^*)=0$，
故上式意味着 $\varphi$ 在 $\ker\omega$ 上恒零。
对任何 $b\in\mathcal A$，$b-\omega(b)1\in\ker\omega$，于是

$$
\varphi(b)=\omega(b)\varphi(1)=\omega(b).
$$

因此 $Z(\omega)=\{\omega\}$。

反向，假设 $Z(\omega)$ 只有 $\omega$。
若 $\omega=t\varphi_1+(1-t)\varphi_2$，其中 $0<t<1$、$\varphi_i$ 为态，
则对 $n\in\mathcal N_\omega$，

$$
0=t\varphi_1(n^*n)+(1-t)\varphi_2(n^*n).
$$

两项非负，故都为零。
于是 $\varphi_1,\varphi_2\in Z(\omega)$，只能同为 $\omega$；所以 $\omega$ 纯。

零核分解与纯态的对应来自 Kadison 的经典结论；上面的解析证明把它用于本轮的内部约束表述
 [8](#ref-kadison1957)。
这里没有用“给态换一个名字”的方式省掉证明：
真正结论是，*所有归一正读出中，共同零约束的解空间是否只剩一份*，
恰好决定共同根能否非平凡正分解。

**白话图景。**一张完整的网不只记录哪些关系会出现，还记录哪些组合绝不可能出现。
当共同来源不可分解时，把全部这些“零关系”固定下来，任何给出不同读数的另一个来源
都会违反其中至少一条。
所以同一份完整零约束就把共同根锁住了。
这个“全部”有实质作用；只知道几条局部规则，还需要另证它们足以锁定整体。

### 命题 7.4（零关系在更大结构中的位置）

<a id="prop-c96-maximal-leftideal"></a>

若 C96 成立，$\mathcal N_\omega$ 是最大真左理想。

**证明。**
它是真左理想，因为 $\omega(1)=1$。
设左理想 $J$ 严格包含 $\mathcal N_\omega$，取
$a\in J\setminus\mathcal N_\omega$。
则 $\pi_\omega(a)\Omega_\omega\ne0$。
由有限插值定理的单向量版本，存在 $b\in\mathcal A$，使

$$
\pi_\omega(b)\pi_\omega(a)\Omega_\omega=\Omega_\omega.
$$

故 $ba-1\in\mathcal N_\omega\subseteq J$，而 $ba\in J$；于是 $1\in J$，
从而 $J=\mathcal A$。

### 命题 7.5（给定正约束族：唯一共同解自动为纯态）

<a id="prop-c96-constraint-face"></a>

给定 $q_\alpha\in\mathcal A_+$，令

$$
F_Q=\{\varphi\in S(\mathcal A):\varphi(q_\alpha)=0\ \forall\alpha\}.
$$

$F_Q$ 是态空间的弱星闭面。
若 $F_Q$ 恰有一个元素 $\omega$，则 $\omega$ 满足 C96。

**证明。**
各评价条件弱星连续，且保持凸组合，故集合弱星闭且凸。
若 $t\varphi_1+(1-t)\varphi_2\in F_Q$ 且 $0<t<1$，
每个 $q_\alpha$ 上的两个非负值之和为零，迫使两个值分别为零。
所以 $\varphi_1,\varphi_2\in F_Q$；这是面的定义。
单点面是极点，故其唯一态为纯态，再由前节等价得到 C96。

这也说明理论中的逻辑输入在哪里。
从给定 $\omega$ 构造全部 $\mathcal N_\omega$，获得的是完整等价刻画。
若从一小组可陈述的内部关系出发，则必须另外证明这些关系的共同解存在且唯一。
第 [12](#sec-c96-closed-history) 节将给出一个这样的闭环构造。
仅说所有对象均在整体内，尚未指定哪一组关系选出实际的整体。

**白话图景。**内部约束可以选出源，选源不需要一只来自网外的手。
数学工作是证明这些约束合得上，而且合起来只允许一个方向。
如果还允许多个方向，就继续寻找区分它们的关系；如果完全合不上，就修正那组关系。
这正是从“不遵守会怎样”反推约束位置的做法。

<a id="section-8"></a>

## 8. 内容即地址：共同根上的幅度地址与完整门功能

<a id="sec-c96-content-address"></a>

### 定义 8.1（两种内部等价）

<a id="def-c96-two-addresses"></a>

共同根上的*相干幅度地址*定义为

$$
a\sim_\Omega b
\quad\Longleftrightarrow\quad
\omega((a-b)^*(a-b))=0.
$$

完整过程等价定义为

$$
a\equiv b
\quad\Longleftrightarrow\quad
\omega\bigl(x^*(a-b)^*(a-b)x\bigr)=0
\quad\text{对每个 }x\in\mathcal A.
$$

这里 $x$ 表示同一共同根内的不同前序准备；并未增加另一份外部来源。

### 定理 8.2（两种地址分别对应左理想商与表示核）

<a id="thm-c96-address-kernels"></a>

有

<a id="eq-c96-root-address"></a>

$$
a\sim_\Omega b
\Longleftrightarrow a-b\in\mathcal N_\omega
\Longleftrightarrow \pi_\omega(a)\Omega_\omega=\pi_\omega(b)\Omega_\omega,
\tag{8.1}
$$

<a id="eq-c96-process-address"></a>

$$
a\equiv b
\Longleftrightarrow \pi_\omega(a)=\pi_\omega(b).
\tag{8.2}
$$

根地址在任何共同后续作用下保持：$a\sim_\Omega b\Rightarrow ca\sim_\Omega cb$。
完整过程的零类为双边理想

<a id="eq-c96-two-sided-kernel"></a>

$$
\ker\pi_\omega=\{a\in\mathcal A:a\mathcal A\subseteq\mathcal N_\omega\}.
\tag{8.3}
$$

**证明。**
第一行由 GNS 范数定义得到，左乘保持来自 $\mathcal N_\omega$ 的左理想性质。
第二种条件等价于

$$
\pi_\omega(a-b)\pi_\omega(x)\Omega_\omega=0\quad\forall x.
$$

$\pi_\omega(\mathcal A)\Omega_\omega$ 稠密，且 $\pi_\omega(a-b)$ 有界，
所以它等价于 $\pi_\omega(a-b)=0$。
取 $b=0$ 即得式 [(8.3)](#eq-c96-two-sided-kernel)。
表示核作为 $*$ 同态的核自动是闭双边 $*$ 理想。

相干幅度地址保留相位和未归一范数，以便随后进行相干组合。
若只读孤立纯态，可以进一步商去整体相位；
将这一步提前用于不同相干分支，则会丢掉干涉所需要的相对相位。
因此“同一读出态”“同一相干内容”“同一全输入门功能”需要按实际比较任务声明。

取 $\mathcal A=M_2$、$\Omega=\lvert 0\rangle$。
$I$ 与 $Z$ 满足
$I\lvert 0\rangle=Z\lvert 0\rangle=\lvert 0\rangle$，所以根地址相同。
令 $\mathsf H=(X+Z)/\sqrt2$ 为 Hadamard 门，
$\lvert \pm\rangle=(\lvert 0\rangle\pm\lvert 1\rangle)/\sqrt2$。
在它们之前放内部准备 $x=\mathsf H$，就有

$$
I\mathsf H\lvert 0\rangle=\lvert +\rangle,
\qquad Z\mathsf H\lvert 0\rangle=\lvert -\rangle.
$$

这两个结果正交，完整门功能因而不同。
同一共同根已经足以暴露这种区别。

**白话图景。**内容确实能定义地址：凡是作用到共同根后给出同一相干内容的写法，
都指向同一个根地址。
但描述一扇门，还要知道它对其他内部准备会怎样作用。
两扇门此刻把你带到同一点，前面换一段准备之后，可能把你带到两个完全不同的点。
把地址按比较任务定义清楚，递归、回溯和共享子结构才不会误合并。

<a id="section-9"></a>

## 9. 共同纯根的酉轨道：同一表示内的精确可达性

<a id="sec-c96-unitary-orbits"></a>

本节沿用 C96 已得到的纯态 $\omega$ 及其不可约 GNS 表示
$(H_\omega,\pi_\omega,\Omega_\omega)$，并保留有单位元的复 $C^*$ 代数
$\mathcal A$。整体结构 $\Omega$、循环根向量 $\Omega_\omega$ 与态泛函
$\omega$ 的类型仍不同；项目已有的区分见
 [2](#ref-omega)、[4](#ref-v78closure)、[5](#ref-v78pure)。
下面调用的有限自伴插值是标准 Kadison 定理的内容，
不是把循环性直接改称为全部实际门供应
 [8](#ref-kadison1957)、[10](#ref-spiegel2022)。

### 定理 9.1（同一 GNS 空间内的单指数可达性）

<a id="thm-c96-exponential-reachability"></a>

对任意单位向量 $\xi,\eta\in H_\omega$，存在
$h=h^*\in\mathcal A$，使

<a id="eq-c96-exponential-reachability"></a>

$$
\pi_\omega(e^{ih})\xi=\eta.
\tag{9.1}
$$

特别地，每个单位向量 $\psi\in H_\omega$ 均可写成
$\psi=\pi_\omega(e^{ih})\Omega_\omega$。
采用带范数控制的有限自伴插值形式时，还可令 $\left\lVert h\right\rVert\le\pi$。

**证明。**
令 $E=\operatorname{span}_{\mathbb C}\{\xi,\eta\}$。这是至多二维的子空间。
因为两个向量的范数相同，可以在 $E$ 上选取酉算子 $V_E$，
使 $V_E\xi=\eta$。有限维谱定理给出

$$
V_E=e^{ik_E},\qquad k_E=k_E^*,\qquad \left\lVert k_E\right\rVert\le\pi.
$$

把 $k_E$ 在 $E^\perp$ 上延拓为零，记所得自伴算子为 $T$。
对 $E$ 的一组基应用引理 [7.2](#lem-c96-kadison)，得到
$h=h^*\in\mathcal A$，满足

$$
\pi_\omega(h)|_E=k_E.
$$

因此 $E$ 对 $\pi_\omega(h)$ 不变；自伴性还使 $E$ 成为约化子空间。
由函数演算与表示相容，

$$
\pi_\omega(e^{ih})|_E
 =e^{i\pi_\omega(h)}|_E
 =e^{ik_E}=V_E.
$$

这证明式 [(9.1)](#eq-c96-exponential-reachability)。
若同时要求范数上界，应用  [10](#ref-spiegel2022) 定理 3.4 的加强形式，
可在上述有限插值中选取 $\left\lVert h\right\rVert\le\left\lVert T\right\rVert\le\pi$。

这里选出一个具有所需作用的指数酉元；并未断言
$U(\mathcal A)$ 中每个酉元都具有 $\mathcal A$ 内的单一自伴对数。
插值只约束 $h$ 在有限空间 $E$ 上的作用，也不要求
$\pi_\omega(h)$ 在 $E^\perp$ 上为零。

**白话图景。**共同根不能拆成互不相干的来源时，在它所生成的同一个表示世界里，
每个纯态方向都能由一个内部酉变换到达。
要连接两个方向，只需先处理它们张成的那一小块平面，再把这个动作延拓到整体。
这里证明了所需内部算子的存在，还没有把它编译成观察者手中某套有限基础门。

### 定义 9.2（共同根所在的纯态扇区）

<a id="def-c96-pure-sector"></a>

记 $\mathcal P(\mathcal A)$ 为 $\mathcal A$ 的纯态集合，定义

$$
\mathcal P_\omega(\mathcal A)
 =\{\varphi\in\mathcal P(\mathcal A):
             \pi_\varphi\simeq\pi_\omega\}.
$$

其中 $\simeq$ 表示存在酉交织算子使两个表示等价。
对 $u\in U(\mathcal A)$，定义门后的态
$\omega_u(a)=\omega(u^*au)$。

### 推论 9.3（单根酉轨道的准确范围）

<a id="cor-c96-sector-orbit"></a>

有

$$
\mathcal P_\omega(\mathcal A)
 =\{a\mapsto\langle \psi,\pi_\omega(a)\psi\rangle:
                      \psi\in H_\omega,\ \left\lVert \psi\right\rVert=1\}
$$

$$
=\{\omega_u:u\in U(\mathcal A)\}
$$

<a id="eq-c96-sector-orbit"></a>

$$
=\{\omega_{e^{ih}}:h=h^*\in\mathcal A\}.
\tag{9.2}
$$

**证明。**
在不可约表示中，任一非零向量的循环闭包是非零约化子空间，
所以等于 $H_\omega$。该向量态的 GNS 表示于是与
$\pi_\omega$ 等价，且该态为纯态。
反过来，若 $\pi_\varphi\simeq\pi_\omega$，把 $\varphi$ 的 GNS 根向量
经酉交织算子搬到 $H_\omega$，便得到表示 $\varphi$ 的单位向量。
这证明第一行。
定理 [9.1](#thm-c96-exponential-reachability) 把该向量写成
$\pi_\omega(e^{ih})\Omega_\omega$，给出最后一行。
指数酉元也是酉元，而每个 $\pi_\omega(u)\Omega_\omega$ 都是单位向量，
其余包含关系随即成立。

这也复现了标准的同扇区酉传递结论
 [10](#ref-spiegel2022)（定理 1.14）。
式 [(9.2)](#eq-c96-sector-orbit) 中的量词不能直接扩成
$\mathcal P(\mathcal A)$，更不能扩成全部态 $\mathcal S(\mathcal A)$。
同一表示中的一般 $\pi_\omega$-正规态可以写为

$$
a\longmapsto\operatorname{Tr}\!\bigl(D\pi_\omega(a)\bigr),
 \qquad D\ge0,\quad D\text{ 为迹类算子},\quad\operatorname{Tr} D=1.
$$

其中混合态一般不在纯根的酉轨道中。
“同一扇区的全部纯态方向”“同一表示中的一般正规态”
与“整个代数的全部态”因而是三个不同的范围
 [12](#ref-fewster2019)、[10](#ref-spiegel2022)。

若声明的实际有限门字组成 $G_{\rm fin}\subseteq U(\mathcal A)$，直接得到的是

$$
\{\omega_g:g\in G_{\rm fin}\}
 \subseteq\mathcal P_\omega(\mathcal A).
$$

即使基础门生成的 $C^*$ 代数恰为 $\mathcal A$，
这一代数生成陈述也包含线性组合、取伴随和范数完成；
它本身不等于有限门字的精确编译定理。
实际供应、参数控制与所选收敛方式仍须由已经声明的过程接口负责。
例如，若某些实际门 $g_n$ 在算子范数下逼近 $u$，则对 $\left\lVert a\right\rVert\le1$，

$$
|\omega(g_n^*ag_n)-\omega(u^*au)|
 \le2\left\lVert g_n-u\right\rVert,
$$

从而得到态范数意义的近似可达，而不是自动得到一个精确的有限门字。

**白话图景。**“所有状态来自同一个根”可以有一个准确而有力的含义：
在这个根所属的纯态扇区里，每个方向都在它的内部酉轨道上。
如果把范围换成整个无限代数的所有态，或者要求每个变换都用有限基础门精确做完，
就增加了新的量词；这些量词不能由原来那句话悄悄带进来。

<a id="section-10"></a>

## 10. 无限整体的边界：纯乘积态、尾部读口与无限历史

<a id="sec-c96-infinite-sectors"></a>

下面完全解析地构造一个无限模型，检查 C96 能否把全部纯态压进单一根轨道。
逐级矩阵代数的范数完成是一个 UHF 代数模型；
相关的表示与纯态轨道框架见  [9](#ref-glimm1960)、[10](#ref-spiegel2022)。
本节用到的纯性、不可达性和极限结论均在下文直接证明。

### 定义 10.1（无限量子比特链）

<a id="def-c96-quasilocal-chain"></a>

令

$$
\mathcal A_N=M_2(\mathbb C)^{\otimes N},\qquad
 a\in\mathcal A_N\longmapsto a\otimes I\in\mathcal A_{N+1},
 \qquad
 \mathcal A=\overline{\bigcup_{N\ge1}\mathcal A_N}^{\left\lVert \cdot\right\rVert}.
$$

令 $e_0=(1,0)^{\mathsf T}$、$e_1=(0,1)^{\mathsf T}$。
对 $b=0,1$，在有限层定义

$$
\omega_b(a)=
 \langle e_b^{\otimes N},a\,e_b^{\otimes N}\rangle,
 \qquad a\in\mathcal A_N.
$$

这些归一正泛函相容，故各自唯一连续延拓为
$\mathcal A$ 上的态，仍记为 $\omega_0,\omega_1$。
项目已有的相容有限态延拓与 GNS 构造见  [2](#ref-omega)（第 12 节）。

### 命题 10.2（两个整体都纯）

<a id="prop-c96-product-purity"></a>

$\omega_0$ 与 $\omega_1$ 均为纯态，因而都满足 C96 的二元不可分解条件。

**证明。**
若 $\omega_b=t\varphi+(1-t)\psi$，其中 $0<t<1$，
限制到每个 $\mathcal A_N$ 后，左边是有限矩阵代数上的秩一向量态。
有限纯态的极端性迫使
$\varphi|_{\mathcal A_N}=\psi|_{\mathcal A_N}=\omega_b|_{\mathcal A_N}$。
因此三个泛函在稠密子代数上相同，由连续性在整个 $\mathcal A$ 上相同。
这证明 $\omega_b$ 纯。与 C96 的等价性使用前节已证结论。

### 命题 10.3（任意固定准局域酉门不能翻转无限尾部）

<a id="prop-c96-tail-obstruction"></a>

记

$$
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
 Z_n=I^{\otimes(n-1)}\otimes Z.
$$

对每个固定 $a\in\mathcal A$，均有

<a id="eq-c96-tail-commutator"></a>

$$
\lim_{n\to\infty}\left\lVert [a,Z_n]\right\rVert=0.
\tag{10.1}
$$

不存在 $U\in U(\mathcal A)$ 使 $\omega_1=\omega_U$，
其中 $\omega_U(a)=\omega_0(U^*aU)$。
事实上，对每个这样的 $U$，

<a id="eq-c96-orbit-distance-two"></a>

$$
\left\lVert \omega_U-\omega_1\right\rVert=2.
\tag{10.2}
$$

**证明。**
给定 $\varepsilon>0$，取 $b\in\mathcal A_N$ 满足
$\left\lVert a-b\right\rVert<\varepsilon$。当 $n>N$ 时，$[b,Z_n]=0$，所以

$$
\left\lVert [a,Z_n]\right\rVert
 =\left\lVert [a-b,Z_n]\right\rVert
 \le2\left\lVert a-b\right\rVert<2\varepsilon.
$$

这证明式 [(10.1)](#eq-c96-tail-commutator)。
由于 $\omega_0(Z_n)=1$、$\omega_1(Z_n)=-1$，

$$
\bigl|\omega_0(U^*Z_nU)-1\bigr|
 \le\left\lVert U^*Z_nU-Z_n\right\rVert
 =\left\lVert [Z_n,U]\right\rVert\longrightarrow0.
$$

因此 $\omega_U$ 不可能等于 $\omega_1$。
又因 $\left\lVert Z_n\right\rVert=1$，两态在这些读口上的差趋于 $2$，
而两归一正泛函的范数距离至多为 $2$，
故式 [(10.2)](#eq-c96-orbit-distance-two) 成立。

**白话图景。**两个整体都不能拆成混合来源，并不表示它们必能由同一扇门互相变换。
这里一个整体的无限尾部始终朝上，另一个始终朝下。
任何固定的准局域门，在足够远的尾部上都越来越接近不作改变，
所以它无法一次把这两个整体互换。

### 10.1 有限激发表示：直接看见另一个纯态不在根的 Hilbert 空间中

令 $\mathfrak F$ 为 $\mathbb N$ 的全部有限子集，取

$$
H_0=\ell^2(\mathfrak F),\qquad
 \Omega_0=\lvert \varnothing\rangle.
$$

基向量 $\lvert F\rangle$ 表示恰在有限集合 $F$ 中的比特为 $1$。
$\mathcal A_N$ 改变前 $N$ 个比特，并保持 $N$ 以后的有限激发不变。
这一作用与嵌入相容，且在分解

$$
H_0\simeq(\mathbb C^2)^{\otimes N}
       \otimes\ell^2\bigl(\{F\subseteq\{N+1,N+2,\ldots\}:F\text{ 有限}\}\bigr)
$$

上是 $a\otimes I$，故连续延拓成 $\mathcal A$ 的表示 $\pi_0$。
真空期望等于 $\omega_0$，而有限个翻转门从
$\Omega_0$ 生成全部基向量，所以这是 $\omega_0$ 的循环 GNS 表示。

### 命题 10.4（所有有限激发向量的尾部概率趋零）

<a id="prop-c96-tail-vector-boundary"></a>

令 $P_n=(I-Z_n)/2$。对任意单位向量 $\psi\in H_0$，

$$
\langle \psi,\pi_0(P_n)\psi\rangle\longrightarrow0.
$$

由于 $\omega_1(P_n)=1$，$\omega_1$ 不能由 $H_0$ 中任何单位向量表示。
因此 $\omega_0$ 与 $\omega_1$ 的 GNS 表示不等价。

**证明。**
写 $\psi=\sum_{F\in\mathfrak F}c_F\lvert F\rangle$，其中
$\sum_F|c_F|^2=1$。则

$$
\langle \psi,\pi_0(P_n)\psi\rangle
 =\sum_{\substack{F\in\mathfrak F\\n\in F}}|c_F|^2.
$$

给定 $\varepsilon>0$，取有限个集合
$F_1,\ldots,F_m$，使其余系数平方和小于 $\varepsilon$。
当 $n$ 超过 $\bigcup_{j=1}^mF_j$ 中的所有编号时，
上式至多为这份余项平方和，故小于 $\varepsilon$。
于是尾部概率趋零，不可能对每个 $n$ 都等于 $1$。
若两个 GNS 表示酉等价，把 $\omega_1$ 的循环根向量搬到 $H_0$，
便会产生这样的单位向量，矛盾。

**白话图景。**这个根的 Hilbert 空间允许有限激发的任意平方可和叠加，
不只允许某一条有限门历史。
即使允许这些叠加，越往无限远处看，读到激发的概率仍趋于零。
全链处处激发的纯态因而在另一个表示扇区；障碍不是少写了几个有限门。

### 10.2 无限门历史的弱星边界确实可以跨出原扇区

### 命题 10.5（逐步翻转的读出极限与向量不收敛）

<a id="prop-c96-prefix-flip-limit"></a>

令

$$
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
 U_N=X^{\otimes N}\in\mathcal A_N,\qquad
 \psi_N=\pi_0(U_N)\Omega_0=\lvert \{1,\ldots,N\}\rangle,
$$

并记 $\sigma_N(a)=\omega_0(U_N^*aU_N)$。
则 $\psi_N$ 两两正交，因而无范数收敛子列；$U_N$ 也无算子范数收敛子列。
然而

<a id="eq-c96-weakstar-boundary"></a>

$$
\sigma_N\xrightarrow{\,w^*\,}\omega_1,
 \qquad
 \left\lVert \sigma_N-\omega_1\right\rVert=2\quad\text{对每个 }N.
\tag{10.3}
$$

**证明。**
不同有限集合对应不同正交基向量，所以当 $M\ne N$ 时，
$\left\lVert \psi_M-\psi_N\right\rVert=\sqrt2$。
若 $M>N$，则 $U_N^*U_M$ 只翻转第 $N+1,\ldots,M$ 个比特，
其谱含 $1$ 与 $-1$，故

$$
\left\lVert U_M-U_N\right\rVert=\left\lVert U_N^*U_M-I\right\rVert=2.
$$

对于固定的 $a\in\mathcal A_m$，当 $N\ge m$ 时，
前 $m$ 个比特已经全部翻转，因而 $\sigma_N(a)=\omega_1(a)$。
对于一般 $a\in\mathcal A$，先取局域 $b$ 满足
$\left\lVert a-b\right\rVert<\varepsilon$，再取足够大的 $N$，得到

$$
|\sigma_N(a)-\omega_1(a)|
 \le|\sigma_N(a-b)|+|\omega_1(a-b)|<2\varepsilon.
$$

这证明弱星收敛，即每个固定代数读口的期望收敛。
但 $P_{N+1}$ 在 $\sigma_N$ 下的期望为 $0$，在 $\omega_1$ 下为 $1$；
等价地，$Z_{N+1}$ 的两个期望为 $1$ 与 $-1$。
因此两态的范数距离仍为 $2$。

这不是定理 [9.1](#thm-c96-exponential-reachability) 的反例。
该定理连接同一个 $H_\omega$ 内的单位向量；
这里的无限历史只有态的弱星读出极限，没有一个相应的极限单位向量，
也没有 $\mathcal A$ 内的范数极限酉门。
因此，若把弱星无限历史的边界也纳入“可达”，可达范围可以超出单根的精确酉轨道。
必须声明所用的完成方式，不能用向量范数收敛、门的算子范数收敛和态的弱星收敛互相替代。

此外，纯态性本身也不能不加条件地传到弱星极限。
在同一个 $H_0$ 中取

$$
\chi_N=2^{-1/2}
       \bigl(\Omega_0+\lvert \{1,\ldots,N\}\rangle\bigr),\qquad N\ge1.
$$

这些是不可约表示中的纯向量态。
对支撑在前 $m$ 个比特的 $a$，当 $N>m$ 时，两项在未被 $a$ 作用的尾部正交，
故交叉矩阵元为零，其期望恰为
$\tfrac12\omega_0(a)+\tfrac12\omega_1(a)$。
由同一稠密性论证，这些纯态弱星收敛到
$\tfrac12(\omega_0+\omega_1)$，一个非平凡混合态。
所以 C96 是对所选全局态的条件，不能仅由一列纯态的弱星收敛自动继承。
这里的猫态近似并非逐层限制相容且每层皆纯的有限态族，
因此与前文“全部有限限制纯且相容则整体纯”的证明相容。

**白话图景。**门可以一扇接一扇加下去：对任何事先固定的有限读口，最终都会看到全链朝下。
但这不表示所有有限历史在原来的 Hilbert 空间里收敛成同一个向量。
“每个固定窗口都收敛”与“整个状态按同一范数收敛”是两种不同的完成。
无限历史能走到原扇区的读出边界，甚至把一列纯态的读出极限变成混合态；
因此，唯一纯根与无限极限如何接合，必须由清楚的整体相容条件锁定。

<a id="section-11"></a>

## 11. 正约束的共同零空间：怎样由内部关系选出一份源

<a id="sec-c96-positive-constraints"></a>

C96 规定共同根在整个指定代数上的不可分解性。
它仍允许很多不同的纯态；要进一步由一套具体关系选出唯一源，
必须证明这些关系的共同解确实只有一个。
下面给出一个完全有限、没有外部初始边界的闭环模型。
本节的正算符用作关系缺额，不因被写成正算符就自动取得物理能量单位。

### 引理 11.1（正约束的共同零空间）

<a id="lem-c96-common-zero-space"></a>

在有限维 $H$ 上给定正算符 $Q_1,\ldots,Q_m$，令
$Q=\sum_jQ_j$、$K=\bigcap_j\ker Q_j$。
对密度态 $\rho$，以下条件等价：

$$
\operatorname{Tr}(\rho Q)=0
 \quad\Longleftrightarrow\quad
 \operatorname{Tr}(\rho Q_j)=0\ \text{对全部 }j
 \quad\Longleftrightarrow\quad
 \operatorname{supp}\rho\subseteq K.
$$

特别地，$\ker Q=K$。
若 $K$ 一维，满足全部约束的归一态唯一，且为纯态；
若 $K=0$，没有满足条件的归一态。

**证明。**
每个 $\operatorname{Tr}(\rho Q_j)$ 非负，故其和为零当且仅当每项为零。
又有

$$
\operatorname{Tr}(\rho Q_j)=\left\lVert Q_j^{1/2}\rho^{1/2}\right\rVert_2^2.
$$

因此零期望等价于 $\rho$ 的支撑包含在 $\ker Q_j$ 中。
对秩一态使用同一论证即得 $\ker Q=K$。
一维支撑上的正迹一算符只能是该方向的秩一投影，余下结论随之成立。

**白话图景。**唯一源可以由关系选出，但要真的看这些关系是否只剩一个共同方向。
每项正缺额都为零，表示每条内部约束同时满足。
如果它们交会后只留一条射线，归一化便选出唯一纯源；如果仍留多个方向，
就不能因为已经把全部对象放进整体而宣称源已经唯一。

<a id="section-12"></a>

## 12. 静态整体中的闭环时钟与变动读出

<a id="sec-c96-closed-history"></a>

给定有限系统空间 $H_S$ 与 $T\ge2$ 个内部时钟标签，
$H_C=\mathbb C^T$，指标按模 $T$ 解释。
在每条有向边上给定酉关系 $U_t:H_S\to H_S$。
时钟、系统、边和门均为这个模型内部的对象；
张量端口及其比较关系按项目既有独立接口声明 [6](#ref-v80)。

### 定义 12.1（闭环传播缺额）

<a id="def-c96-cyclic-propagation"></a>

对
$\Psi=\sum_{t=0}^{T-1}\lvert t\rangle\otimes\psi_t$，定义

<a id="eq-c96-cyclic-constraint"></a>

$$
\begin{split}
 L_t&=\langle t+1\rvert\otimes I-\langle t\rvert\otimes U_t,
       \qquad L_t:H_C\otimes H_S\to H_S,\\
 Q&=\sum_{t=0}^{T-1}L_t^\dagger L_t\ge0.
 \end{split}
\tag{12.1}
$$

于是有精确恒等式

<a id="eq-c96-history-defect"></a>

$$
\boxed{\quad
 \langle\Psi,Q\Psi\rangle
 =\sum_{t=0}^{T-1}\left\lVert \psi_{t+1}-U_t\psi_t\right\rVert^2.
 \quad}
\tag{12.2}
$$

因此 $Q\Psi=0$ 当且仅当全部边关系
$\psi_{t+1}=U_t\psi_t$ 同时成立。

### 定理 12.2（闭环源由整体回路运输决定）

<a id="thm-c96-holonomy-source"></a>

令

$$
F=U_{T-1}\cdots U_0,
 \qquad V_0=I,
 \qquad V_t=U_{t-1}\cdots U_0\quad(1\le t<T).
$$

则

<a id="eq-c96-holonomy-dimension"></a>

$$
\boxed{\dim\ker Q=\dim\ker(F-I).}
\tag{12.3}
$$

对应的等距为

<a id="eq-c96-history-isometry"></a>

$$
W\psi=\frac1{\sqrt T}
 \sum_{t=0}^{T-1}\lvert t\rangle\otimes V_t\psi,
 \qquad \psi\in\ker(F-I),
\tag{12.4}
$$

其像正好是 $\ker Q$。
闭环存在非零零缺额向量，当且仅当 $F$ 有本征值 $1$；
归一源至整体相位唯一，当且仅当这个本征空间一维。

**证明。**
从 $\psi_0$ 出发，前 $T-1$ 条边唯一给出 $\psi_t=V_t\psi_0$。
最后一条边给 $\psi_0=U_{T-1}\psi_{T-1}=F\psi_0$。
反向，任何 $F\psi_0=\psi_0$ 都给一份满足全部边的向量。
这建立两个核之间的线性双射。
各 $V_t$ 酉，时钟标签正交，故

$$
\langle W\phi,W\psi\rangle
 =\frac1T\sum_t\langle V_t\phi,V_t\psi\rangle
 =\langle\phi,\psi\rangle.
$$

所以所写对应是等距，维数、存在性与唯一性结论均成立。

若把最后一条边改成含指定相位扭转的关系，闭环条件相应变成
$F\psi=e^{i\alpha}\psi$。
相位扭转必须明写在共同约束中；不能在固定零缺额问题里悄悄改掉闭环条件。
同样，“闭合”本身既不保证存在共同解，也不保证共同解唯一。

**白话图景。**沿着闭环从任一点走一圈，返回时必须与出发处相容。
每条边都对了，还要整圈合得上。
整圈运输的不动方向就是允许的共同源；只有一个不动方向时才得到唯一源。
这个结论由整个闭环共同决定，没有在环外额外摆放一个初始状态。

### 12.1 两格时钟：唯一纯源，两个不同条件读出

取系统为 qubit，令

$$
Z=\lvert 0\rangle\langle 0\rvert-\lvert 1\rangle\langle 1\rvert,
 \qquad X=\lvert 0\rangle\langle 1\rvert+\lvert 1\rangle\langle 0\rvert,
 \qquad \mathsf H=\frac{X+Z}{\sqrt2}.
$$

$\mathsf H$ 是 Hadamard 酉，$\mathsf H^2=I$。
给定两条边

$$
U_0=\mathsf H,\qquad U_1=Z\mathsf H.
$$

其闭环运输为 $F=U_1U_0=Z$。

### 定理 12.3（一个由闭环约束唯一选出的静态纯源）

<a id="thm-c96-two-clock-source"></a>

令

$$
\begin{aligned}
L_0&=\langle 1\rvert\otimes I-\langle 0\rvert\otimes\mathsf H,\\
 L_1&=\langle 0\rvert\otimes I-\langle 1\rvert\otimes Z\mathsf H,\\
 Q&=L_0^\dagger L_0+L_1^\dagger L_1.
\end{aligned}
$$

则满足 $\operatorname{Tr}(\rho Q)=0$ 的归一态唯一，等于

<a id="eq-c96-two-clock-omega"></a>

$$
\boxed{\quad
 \rho_{\rm hist}=\lvert \Omega_{\rm hist}\rangle\langle \Omega_{\rm hist}\rvert,
 \qquad
 \lvert \Omega_{\rm hist}\rangle
 =\frac{\lvert 0\rangle_C\lvert 0\rangle_S+\lvert 1\rangle_C\lvert +\rangle_S}{\sqrt2},
 \quad}
\tag{12.5}
$$

其中 $\lvert +\rangle=(\lvert 0\rangle+\lvert 1\rangle)/\sqrt2$。
它在完整代数 $B(H_C\otimes H_S)=M_4$ 上为纯态，满足 C96。
读取内部时钟 $0$ 与 $1$，系统条件态分别为 $\lvert 0\rangle\langle 0\rvert$ 与 $\lvert +\rangle\langle +\rvert$。

**证明。**
零缺额给

$$
\psi_1=\mathsf H\psi_0,
 \qquad
 \psi_0=Z\mathsf H\psi_1=Z\psi_0.
$$

所以 $\psi_0$ 只能是 $\lvert 0\rangle$ 的倍数，$\psi_1$ 则是 $\lvert +\rangle$ 的同一倍数。
共同零空间因此一维；归一后即得式 [(12.5)](#eq-c96-two-clock-omega)。
由引理 [11.1](#lem-c96-common-zero-space)，任意零缺额密度态也只能是这个秩一投影。
完整矩阵代数上的秩一态是纯态，故由前文 C96 的等价定理满足候选。

对任意系统效果 $0\le A\le I$，令
$\psi_0=\lvert 0\rangle$、$\psi_1=\lvert +\rangle$，有

$$
\langle\Omega_{\rm hist},(\lvert t\rangle\langle t\rvert\otimes A)\Omega_{\rm hist}\rangle
 =\frac12\langle\psi_t,A\psi_t\rangle,
 \qquad \Pr(C=t)=\frac12.
$$

除以时钟结果的概率，即得相应条件态。
整个 $\rho_{\rm hist}$ 在这个描述中固定；改变的是内部条件读口。

固定整体与内部时钟条件演化的思想，与 Page–Wootters 的工作相接
 [15](#ref-page1983)。
这里仅以其摘要作思想归属，上述有限闭环及唯一性证明由本文完整给出。
整体的向量表示与无限均匀历史的归一化边界，继续按项目既有论证使用 [2](#ref-omega)。

**白话图景。**这个小模型里，整体只有一份由闭环关系选出的纯源。
观察者读取内部时钟的不同位置，分别看到两个不同系统态。
整体不需要从第一个态变成第二个态；两个条件读出和它们之间的门关系，已经同时存在于同一源中。
约束不变而读出变化，在这里是一个精确的有限模型。

### 12.2 选起点只重标闭环，周期相位不等于完整历史长度

从第 $k$ 格给闭环编号时，整圈运输为
$F_k=V_kFV_k^\dagger$。
因此不动空间的维数和共同源是否唯一不变。
同时重标时钟、边与状态分量，只改变这份闭环关系的坐标，
并不允许保持原门关系不动却任意改选源。

时钟标签属于 $\mathbb Z/T\mathbb Z$，它只记录周期相位，
不记录已经绕行了多少圈。
若观察者还保存轮次、思考或计算的追加记录，就须在整体内保留相应的记录自由度。
不能因为周期相位相同，就把所有不同长度的完整历史合并。
这与项目关于正历史追加及完整记录的区别一致 [2](#ref-omega)、[3](#ref-v74)、[7](#ref-v95)。

**白话图景。**闭环没有指定必须从哪里开始讲述；换一个节点作为第一格，整体关系仍是同一个。
但钟面回到同一格，并不表示新增记忆也回到原样。
周期位置与累计历史是两个内部读数，完整记录不能被一个有限钟面替代。

<a id="section-13"></a>

## 13. 门参数作为内部程序：递归控制的明确形式

<a id="sec-c96-endogenous-programs"></a>

在明确声明系统端口、程序端口及其乘积准备的任务中，
取程序空间的正交标签 $\lvert j\rangle$，并给定系统酉门 $U_j$。
先设标签有限，定义同一个处理器

<a id="eq-c96-controlled-program"></a>

$$
G=\sum_jU_j\otimes\lvert j\rangle\langle j\rvert.
\tag{13.1}
$$

各标签投影正交且穷尽，故 $G^\dagger G=GG^\dagger=I$，并有

$$
G(\psi\otimes\lvert j\rangle)=U_j\psi\otimes\lvert j\rangle.
$$

参数标签因此可以作为整体内部的实际量子内容，不需要摆在模型之外。

若归一程序处于叠加 $p=\sum_jc_j\lvert j\rangle$，则

$$
G(\psi\otimes p)=\sum_jc_jU_j\psi\otimes\lvert j\rangle.
$$

完整输出保留不同参数与不同变化之间的相干关系。
忽略程序端口时，系统过程为

<a id="eq-c96-program-mixture"></a>

$$
\Phi_p(\rho)=\sum_j|c_j|^2U_j\rho U_j^\dagger.
\tag{13.2}
$$

它通常不能用“参数平均值所对应的一扇酉门”替代。

**白话图景。**把参数放进整体以后，它也能叠加，也能与结果关联。
程序的不同分支带着系统走不同的变化；保留程序，就保留完整关系；
只看系统，便可能看到混合过程。
参数的内生化因而有明确的量子实现，不只是一种语言上的改名。

还可以给处理器的控制再加一层内部程序。
对任意有限层，只要端口、复合及参考关系相容，就得到更大整体中的普通复合过程。
无限递归则仍需各有限截口相容及所声明极限的存在性，不能由“递归”自动保证。
自引用或反复出现同一种定义，也不自动证明几何缩放对称或分形维数。
“分形”若要作为严格结论，必须另给作用于尺度的映射及其保持关系。

所有程序和记录都可作为整体的内部对象；
这一数学表示本身不自动供应它们的准备资源，也不证明任意指定程序均已可取得
 [6](#ref-v80)。

<a id="section-14"></a>

## 14. 二程序关系锁定精确门容量：全输入编程定理

<a id="sec-c96-no-programming"></a>

参数能够内生，不表示不同精确门功能可以随意共用不可区分的程序。
以下采用 Nielsen–Chuang 精确编程定理的标准机制，并给出本轮所需的完整证明
 [14](#ref-nielsen1997)。

### 定义 14.1（精确、确定的全输入酉门编程）

<a id="def-c96-exact-programming"></a>

给定同一个等距处理器
$G:H_S\otimes H_P\to H_S\otimes H_E$。
归一程序 $p_U\in H_P$ 实现系统酉门 $U$，指对*全部*数据密度态 $\rho$，

<a id="eq-c96-exact-programming"></a>

$$
\operatorname{Tr}_EG(\rho\otimes\lvert p_U\rangle\langle p_U\rvert)G^\dagger
 =U\rho U^\dagger.
\tag{14.1}
$$

同一程序须在所有这些输入上工作；系统与程序的乘积准备属于此任务的明确前件。
$H_E$ 可以是整体内部的输出程序与记录端口。

### 引理 14.2（精确酉分支的最终记录不依赖数据输入）

<a id="lem-c96-program-environment"></a>

满足定义 [14.1](#def-c96-exact-programming) 时，存在同一个归一向量 $e_U\in H_E$，使

$$
G(\psi\otimes p_U)=U\psi\otimes e_U
 \qquad(\psi\in H_S).
$$

**证明。**
对纯输入，系统边缘输出为纯态 $\lvert U\psi\rangle\langle U\psi\rvert$，
所以完整向量只能是 $U\psi\otimes e_{U,\psi}$。
取一组数据正交基 $f_j$，写相应环境向量为 $e_j$。
再输入 $(f_j+f_k)/\sqrt2$。
线性给完整输出的两项叠加；它的系统约化必须精确等于
$U(f_j+f_k)/\sqrt2$ 的秩一投影。
比较两个不同基方向之间的交叉矩阵元，得到 $\langle e_k,e_j\rangle=1$。
归一性迫使 $e_j=e_k$。
因此所有基向量具有同一环境输出；线性延拓即得结论。

### 定理 14.3（非相位等价的酉门要求正交程序）

<a id="thm-c96-no-programming"></a>

若同一处理器分别用 $p_U,p_V$ 精确、确定地实现 $U,V$，则

<a id="eq-c96-two-program-identity"></a>

$$
\boxed{
 \langle p_U,p_V\rangle I
 =\langle e_U,e_V\rangle U^\dagger V.
 }
\tag{14.2}
$$

若 $U^\dagger V$ 不是标量，则 $\langle p_U,p_V\rangle=0$。
因此一族模全局相位互不相同的精确门，必须使用两两正交的程序。

**证明。**
等距保持任意两输入的内积。由上个引理，对全部 $\psi,\phi$，

$$
\langle\psi,\phi\rangle\langle p_U,p_V\rangle
 =\langle U\psi,V\phi\rangle\langle e_U,e_V\rangle
 =\langle\psi,U^\dagger V\phi\rangle\langle e_U,e_V\rangle.
$$

矩阵元分离算符，故得到式 [(14.2)](#eq-c96-two-program-identity)。
若 $\langle e_U,e_V\rangle\ne0$，该式迫使 $U^\dagger V$ 为标量。
在定理的非相位等价前件下，只能有 $\langle e_U,e_V\rangle=0$，
继而 $\langle p_U,p_V\rangle=0$。

**白话图景。**两份程序如果代表真正不同的门，而且同一台处理器必须对所有数据精确执行，
这两份程序就必须完全可区分。
这个限制只比较两个程序，却约束整个门族能使用多大的内部内容空间。
把参数也当作量子内容，可以使它内生；它仍须服从相干比较的约束。

### 14.1 有限、可分无限与非可分程序空间的界线

若程序空间维数为 $d_P<\infty$，最多精确实现 $d_P$ 个模相位不同的酉门。
若程序空间可分，其任意正交归一族至多可数，所以只能容纳可数个这样的精确程序。
若目标是系统维数至少为二时的全部酉门（模全局相位），目标族不可数，
故可分程序空间仍不足以精确覆盖。
这不是对近似编程、概率成功编程或增长资源的否定；这些任务改变了所声明的前件。

若明确允许非可分程序空间，数学上可取 $H_P=\ell^2(J)$，
并在 $H_S\otimes\ell^2(J)\simeq\bigoplus_{j\in J}H_S$ 上定义

$$
G((\psi_j)_{j\in J})=(U_j\psi_j)_{j\in J}.
$$

它逐项保持范数，逆为逐项 $U_j^\dagger$，故为酉算符。
每个基程序 $\lvert j\rangle$ 精确实现 $U_j$。
因此“无限维”必须继续区分可分性与所需程序族；不能把所有无限维情形一概判为不可能。
这份直和表示也不自动证明如此大的程序资源已实际供应。

<a id="section-15"></a>

## 15. 固定源的态地址，不等于全输入门地址

<a id="sec-c96-state-versus-process-address"></a>

前节的全输入量词不可省略。
若任务只要求把一个固定系统源 $\Omega_S$ 送到目标态 $\psi$，
取程序端口为 $H_S$ 的另一个副本，便有一个直接的内部实现：

<a id="eq-c96-swap-state-program"></a>

$$
\boxed{
 \operatorname{SWAP}(\Omega_S\otimes\psi)
 =\psi\otimes\Omega_S.
 }
\tag{15.1}
$$

不同目标 $\psi,\phi$ 不必正交，相应程序也不必正交。
这没有违反定理 [14.3](#thm-c96-no-programming)，因为程序编码的是目标态，
而不是一扇在全部可能数据上都按指定酉规则工作的门。
它把已经位于程序端口的内容移到数据端口；
任意目标程序是否已经由共同源实际供应，仍是另一项需要证明的关系。

**白话图景。**内容可以直接成为态的地址：把程序里已有的那份态换到当前端口，就得到了它。
但同一个目标态可以由许多不同的门得到；只知道这一次从源到哪里，还不能确定门对所有其他内容怎样作用。
因此“态地址”和“过程地址”都可以在整体内，却需要分别给出完整的关系含义。
这个区分保留了共同源图景，也使递归参数与实际门功能的约束能够被逐项证明。

<a id="section-16"></a>

## 16. 约束固定，读口变化：不确定性的二元几何

<a id="sec-c96-readout-uncertainty"></a>

固定同一整体态 $\omega$。对效果 $0\le E\le1$ 与内部酉关系 $U$，
变化后的读口及其概率写成

<a id="eq-c96-moving-readout"></a>

$$
E_U=U^*EU,\qquad p_U(E)=\omega(U^*EU).
\tag{16.1}
$$

也可以把同一个数记为 $\omega_U(E)$。
在静态整体的表述中，$U$ 指定怎样在整体内关联准备与读口；
这份重新标记的态泛函并未另外增加一份本体来源。

对已声明量子仪器中一条结果历史的门乘积 $K_w$，
有 $K_w^*K_w\le I$，其条件读出为

<a id="eq-c96-history-conditioning"></a>

$$
p_w=\omega(K_w^*K_w),\qquad
\omega_w(a)=\frac{\omega(K_w^*aK_w)}{p_w}\quad(p_w>0).
\tag{16.2}
$$

从 $\omega$、门到记录的整套接口都在模型内；每一项独立准备或门可用性仍按所声明任务核对。
概率为零的分支不能用除法定义其条件态。

### 命题 16.1（小门变化的读出稳定性）

<a id="prop-c96-stability"></a>

对态 $\omega$、$a,a'\in\mathcal A$ 及酉 $U,V$，有

$$
|\omega(a')-\omega(a)|\le\left\lVert a'-a\right\rVert,
\tag{16.3}
$$

<a id="eq-c96-readout-lipschitz"></a>

$$
|\omega(U^*aU)-\omega(V^*aV)|\le2\left\lVert a\right\rVert\,\left\lVert U-V\right\rVert.
\tag{16.4}
$$

**证明。**
正归一泛函的范数为一。
第二式使用分解

$$
U^*aU-V^*aV=(U^*-V^*)aU+V^*a(U-V)
$$

以及酉的范数为一。

因此有界读口对算符范数意义下的小门变化保持定量稳定。
条件化还包含除以 $p_w$：若成功概率没有共同正下界，
很小的绝对概率变化也可能给出很大的条件态变化。
这项归一化效应需要在递归读出中保留。

**白话图景。**同一张网可以固定，而你沿不同关系读到不同内容。
门只变一点时，有界读数的变化有明确上界；若只挑一个极少发生的分支，
再把它放大成全部条件世界，变化就可能被放大。
所以“约束保持、读口变化”可以精确计算；它不要求每次结果都一定换成另一个。

### 定理 16.2（二元 Gram 约束与三维归一化）

<a id="thm-c96-uncertainty-bloch"></a>

令 $A=A^*,B=B^*\in\mathcal A$，并置

$$
a=A-\omega(A)1,\quad b=B-\omega(B)1,\quad
v_A=\omega(a^2),\quad v_B=\omega(b^2),\quad z=\omega(ab).
$$

则

<a id="eq-c96-gram-uncertainty"></a>

$$
G=\begin{pmatrix}v_A&z\\\overline z&v_B\end{pmatrix}\ge0,
\qquad
v_Av_B\ge(\operatorname{Re} z)^2+\tfrac14|\omega([A,B])|^2.
\tag{16.5}
$$

若 $s=v_A+v_B>0$，归一矩阵 $G/s$ 的 Bloch 坐标为

<a id="eq-c96-gram-bloch"></a>

$$
\mathbf r=
\left(\frac{2\operatorname{Re} z}{s},\frac{-2\operatorname{Im} z}{s},\frac{v_A-v_B}{s}\right),
\qquad
\left\lVert \mathbf r\right\rVert_{\mathbb R^3}^2
=1-\frac{4\det G}{s^2}\le1.
\tag{16.6}
$$

若 $s=0$，则两个方差及 $z$ 均为零，直接保留零关系，不进行除法。

**证明。**
对任意 $\alpha,\beta\in\mathbb C$，

$$
(\overline\alpha,\overline\beta)G
\binom\alpha\beta
=\omega((\alpha a+\beta b)^*(\alpha a+\beta b))\ge0.
$$

所以 $\det G=v_Av_B-|z|^2\ge0$。
因 $a,b$ 自伴，$z-\overline z=\omega([A,B])$，
故 $|z|^2=(\operatorname{Re} z)^2+\tfrac14|\omega([A,B])|^2$。
将 $G/s$ 展开为 $(I+\mathbf r\cdot\boldsymbol\sigma)/2$ 得所写坐标。
平方展开或直接计算其行列式，即得最后的恒等式。
若 $s=0$，非负对角元均为零，正性迫使非对角元也为零。

这是项目 V74 已有的 Robertson–Schrödinger 关系在本轮整体读出语言中的接续
 [3](#ref-v74)。
三维球是这一次二元比较的归一化容器：
$\det G=0$ 对应球面，严格正行列式对应球内。
不同二元窗口之间仍需共享同一正泛函及其重叠相容关系，
因此每次能作三维编码，并不把任意高维整体变成一个无损的三维全局坐标。

无限维不是这项不确定性的必要条件。
在 qubit 的 $\lvert 0\rangle$ 态上取 $A=X,B=Y$，有
$v_A=v_B=1$、$\omega([X,Y])=2i$，不等式已饱和。
反之，在无限维 $\ell^2(\mathbb N)$ 上取根 $e_0$ 与投影
$P_0=\lvert e_0\rangle\langle e_0\rvert$，其读数恒为一、方差为零。
这两个解析例子直接检查“维数导致每次变化”的说法。

**白话图景。**拿两种读法比较，它们各自的波动和彼此的相位不能随意拼接；
必须合成一个正的二乘二关系块。
归一化以后，这个块可以放进三维球中，球的边界就是某种关系恰好锁紧的位置。
量子测不准已经出现在最小的非平凡系统中；无限整体会带来更多读口和极限问题，
但波动约束本身来自读口之间的相容关系。

### 16.1 稳定他者作为保持的内部关系

给定一族实际内部更新的 Heisenberg 映射 $\Phi_g^*$，
一个可用的稳定读口集合是

$$
\mathcal S=\{a=a^*: \Phi_g^*(a)=a\ \text{对所有声明的 }g\}.
$$

这给“他者作为稳定读出”一种数学入口：
不同观察过程仍可在同一批关系上取得一致读数。
是否形成普通乘法代数、是否需要先限制到支撑、是否具有调和延拓，
沿用 v94–v95 的精确条件，不能只从“不动”二字推得 [7](#ref-v95)。
这个构造讨论共同模型里的稳定结构；它不把其他观察者的经验存在问题当作已经解决。

<a id="section-17"></a>

## 17. 门的切向、实际局域时钟与关系曲率

<a id="sec-c96-time-curvature"></a>

在已声明的可微酉轨迹上，令
$i\hbar\dot\psi=H\psi$，$\left\lVert \psi\right\rVert=1$。
去掉整体相位方向后，射线的水平切向为

<a id="eq-c96-horizontal-tangent"></a>

$$
v_\psi=-\frac{i}{\hbar}\bigl(H-\langle\psi,H\psi\rangle I\bigr)\psi,
\qquad \langle\psi,v_\psi\rangle=0.
\tag{17.1}
$$

因此一扇连续门在给定态上的局部作用可读为切向关系。
同一切向没有确定门对所有其他态的作用；
完整门功能仍按第 [8](#sec-c96-content-address) 节的全输入关系比较。
若 $v_\psi=0$，它是静止射线，不能强行归一化为单位切向。

唯一共同源也没有使任意酉轨迹都以它为时间终点。
若两个态的整体演化使用同一酉，二者距离保持；
实际局部极限需要 v95 已证明的守恒纤维与衰减条件 [7](#ref-v95)。
本轮闭环中的“最终一致”指全部关系同时满足的共同解。

**白话图景。**一个态和它的变化方向确实构成最直接的二元关系。
但同一个方向只描述这一次、这个位置的局部变化。
整扇门还包含它在其他位置会怎样作用，而整个共同根要满足所有位置的关系。
这样，切向、门和整体都能放进同一张网，同时保留它们各自携带的信息。

### 17.1 为什么必须用实际记录校准门增速

令内部时钟读数为 $t$，同一条轨迹改用局部 $C^1$ 重参数化
$\tau=f(t)$，其中 $f'(t)>0$。
链式法则给

<a id="eq-c96-clock-reparam"></a>

$$
i\hbar\frac{d\psi}{d\tau}=H_\tau\psi,
\qquad H_\tau=\frac{dt}{d\tau}H_t.
\tag{17.2}
$$

这与项目 V74 的内部时钟变换一致 [3](#ref-v74)。
实际可比较的是钟与记录的联合关系，例如在钟 $C$ 的某些读数之间，
观察者记录端口 $R$ 出现了哪些可区分追加。

纯语法门数不足以给出不变时长，因为对固定生成元有精确恒等式

<a id="eq-c96-gate-refinement"></a>

$$
e^{-iH\Delta t/\hbar}
=\left(e^{-iH\Delta t/(m\hbar)}\right)^m
\qquad(m\in\mathbb N_{>0}).
\tag{17.3}
$$

同一变换可以写成一个门，也可以写成 $m$ 个门。
若每一步确实新增了可读取的物理记录，完整过程便包含这些记录；
若只是把同一个公式切细，钟并未因此多走。
所谓原子 tick，须以实际记录的可区分性、允许门菜单和比较精度定义。

**白话图景。**你说的“增长就是时钟”，可以落实为记忆和记录真正增加了多少。
把一个动作的数学写法拆成十段，不会凭空让时间变成十倍。
要比较两个局域时钟，就比较两套内部记录之间的对应；
实际新增记录、分辨率和门的写法因此都有清楚的位置。

### 17.2 从关系变化到场：一个必须满足的曲率检验

假定模型进一步给出可微参数空间 $M$，并在其某区域存在光滑酉参考 $R(x)$。
全空间参考变换的联络一形式为

$$
\mathcal A_R=R^*dR.
$$

微分 $R^*R=I$ 得
$dR^*=-R^*(dR)R^*$，于是

<a id="eq-c96-pure-frame-flat"></a>

$$
d\mathcal A_R=-\mathcal A_R\wedge\mathcal A_R,
\qquad \mathcal F_R=d\mathcal A_R+\mathcal A_R\wedge\mathcal A_R=0.
\tag{17.4}
$$

所以在这样的区域，单纯光滑改变完整参考并不会产生非零联络曲率。

保留一个内部子空间或一个态射线，则可以出现不同几何。
例如在 qubit 上取局部态

$$
\psi(\theta,\phi)=\cos\frac\theta2\lvert 0\rangle+
e^{i\phi}\sin\frac\theta2\lvert 1\rangle.
$$

其射线参考的一形式及曲率为

<a id="eq-c96-berry-curvature"></a>

$$
\alpha=-i\langle\psi,d\psi\rangle
=\sin^2\frac\theta2\,d\phi,
\qquad d\alpha=\frac12\sin\theta\,d\theta\wedge d\phi.
\tag{17.5}
$$

这由所写态直接求微分得到，也是 V74 相位面积关系的一个实例 [3](#ref-v74)。
完整参考的纯规范联络与投影后的 Berry 曲率，作用对象不同，因而相容。

这些结果给关系场研究一个具体方向：比较不同内部截口怎样拼接，
以及投影后留下怎样的相位和曲率。
若要得到引力，还须从模型构造时空的因果与度量关系、实际钟与自由落体的对应，
再证明相应场方程。C96 与时钟重参数化尚未提供这些结论。
本轮不把量子程序的递归或参考变换直接称为已经完成的引力统一。

**白话图景。**关系的变化当然还能被继续比较，比较绕一圈可能留下相位。
但把整套坐标一起换掉时，不能仅凭坐标变化就说产生了引力。
先找出哪些内部比较绕一圈留下不可消去的差别，
再证明这些差别怎样控制钟、距离和运动，统一关系场才有可验证的内容。

<a id="section-18"></a>

## 18. 怎样接回现有量子力学公理

<a id="sec-c96-reconstruction"></a>

C96 是本轮新增的一项选择条件：它在共同复正关系接口中选择不可分解的整体来源。
下面把完整理论的依赖写清楚，说明哪些是已有重建，哪些是本轮定理，哪些还需实际接口。

### 18.1 态、效果与平方律

共同正泛函经 GNS 给 Hilbert 空间与根向量；这个构造已在项目证明 [2](#ref-omega)、[4](#ref-v78closure)。
若所声明有限端口的代数是 $M_d$，矩阵单位的评价唯一决定一个矩阵 $\rho$，满足

$$
\omega(a)=\operatorname{Tr}(\rho a),\qquad \rho\ge0,\qquad \operatorname{Tr}\rho=1.
$$

其中正性来自对每个 $v$ 的
$\operatorname{Tr}(\rho\lvert v\rangle\langle v\rvert)=\omega(\lvert v\rangle\langle v\rvert)\ge0$；
归一化来自 $\omega(I)=1$。
纯态在完整 $M_d$ 上对应秩一密度矩阵，故
$\omega(a)=\langle\psi,a\psi\rangle$。

声明效果 $0\le E\le I$ 后，$\omega(E)$ 自动在 $[0,1]$ 内。
一个实际 POVM $\{E_j\}$ 满足 $\sum_jE_j=I$，其概率和因此为一。
对投影 $P$ 及归一化的 $\phi$，

<a id="eq-c96-born"></a>

$$
p(P)=\langle\psi,P\psi\rangle=\left\lVert P\psi\right\rVert^2;
\qquad
p(\lvert \phi\rangle\langle \phi\rvert)=|\langle\phi,\psi\rangle|^2.
\tag{18.1}
$$

平方律在这一结构内是同一正关系的投影表达。
它已使用共同复正结构；C96 单独并没有从任意关系模型选择复数域或所有可实施效果。

### 18.2 过程、复合与连续演化

对实际实现的等距过程
$V\psi=\sum_jK_j\psi\otimes\lvert j\rangle$，
$V^*V=I$ 等价于 $\sum_jK_j^*K_j=I$。
读结果 $j$ 给

$$
p_j=\omega(K_j^*K_j),\qquad
\rho\longmapsto K_j\rho K_j^*,
$$

忽略该记录则为 $\sum_jK_j\rho K_j^*$。
对任何内部参考空间，此映射与恒等过程的张量扩张仍保持正性，
所以得到完全正性。等距实现是否已实际可用，是过程接口的内容 [6](#ref-v80)。

当两个矩阵端口通过具有共同单位的相互对易嵌入，且共同生成复合代数时，
乘法给出 $M_m\otimes M_n$ 到复合代数的满含幺 $*$ 同态；
矩阵代数 $M_{mn}$ 的单性使其单射，从而得到通常的张量乘积端口。
独立准备和独立控制仍属于实际接口；全局态在复合端口上的读出可以纠缠。
把端口全部放进 $\Omega$ 并不自动使它们独立，独立性须用实际的组合关系定义。

对一参数、可微、满足群法则的有限维酉过程 $U(t)$，定义

$$
H=i\hbar\dot U(0).
$$

微分 $U(t)^*U(t)=I$ 得 $H=H^*$；
群法则再给 $\dot U(t)=\dot U(0)U(t)$，于是

<a id="eq-c96-schrodinger"></a>

$$
i\hbar\dot\psi(t)=H\psi(t),\qquad \psi(t)=U(t)\psi(0).
\tag{18.2}
$$

这是有限维连续酉接口到薛定谔方程的推导。
一般无限维生成元还须指定强连续性和算符定义域；本轮不省略这些条件。

| 通常量子公理 | 所用内部条件 | 本轮中的地位 |
|---|---|---|
| Hilbert 空间与态 | 共同复正核、归一化、零关系商与完备化 | 承接 V78 与 $\Omega$ 静态稿的 GNS 证明 |
| 全局纯源 | 全局受支配二元分解只能等比例 | C96；等价于纯态、不可约、零约束唯一性 |
| 密度态与效果 | 矩阵端口；正归一泛函；实际效果接口 | 得到 $\operatorname{Tr}\rho E$；全效果可实施性另由接口供应 |
| Born 平方律 | 投影读出作用于同一正内积 | $p=\left\lVert P\psi\right\rVert^2$，相容二元窗口沿用既有闭合 |
| 酉门 | 不可约扇区；或已实现的闭合可逆量子过程 | C96 给代数酉轨道；实际编译须核对门菜单 |
| 张量复合 | 独立矩阵端口、共同参考与组合规则 | 承接 V80；全局纯性不替代独立性 |
| 一般测量与 CP | 实际等距及结果记录；所有内部参考的正性 | Kraus 形式与条件态；忽略记录给 CPTP |
| Lüders 更新 | CP 投影结果，且保持该投影角内全部关系 | 沿用既有额外非扰动条件；Born 概率本身未固定更新 |
| 薛定谔方程 | 可微酉群、实际时钟及 $\hbar$ 的尺度标定 | 由群法则得到自伴生成元与一阶演化 |
| 不确定性 | 两个中心化读口的共同 Gram 正性 | 本文给完整证明；有限三维归一编码 |

可以由 C96 立即得到的反向检查是：
交换代数 $C(X)$ 上的点评价 $\omega(f)=f(x_0)$ 也为纯态，满足 C96。
其 GNS 空间只有一维。
所以 C96 的任务是约束*整体来源如何不可分解*；
多方向的量子运动还依赖项目已经声明和重建的非交换复关系结构。
这项可见依赖保证理论不会把预先使用的结构隐藏在“内生”一词里面。

**白话图景。**现有量子规则可以在同一套关系结构里接起来：
相容的正关系给内积和态空间，投影读出给平方律，
保留全部记录的已声明纯过程给等距；同一有限维载体上的闭合可逆情形给酉门，
忽略某些内部记录给一般量子通道，
可微的内部时钟关系给薛定谔方程。
这一轮加上的 C96 把共同来源锁成纯的一份，并证明其零约束和同扇区酉轨道。
每一环用到了什么，都写在明处，才能继续用反向检验压缩它们。

<a id="section-19"></a>

## 19. v96 的完整白话及下一项可证明问题

<a id="sec-c96-synthesis"></a>

把整个宇宙模型想成一张完整的关系网。网中的观察者、钟、程序、环境和他者都由同一份
共同来源给出。观察者沿一段门历史读取内容，又把结果写成新的内部记录；
思考、计算、程序修改也属于这样的内部过程。
同一静态关系网因此能够同时容纳不同条件下的变化。

要把“只有一份来源”说得足够强，就要求：若有人想在保留所有整体读数的情况下，
把它分成两份来源，这两份必须对每个问题给出完全相同的比例答案。
只要两份真的不同，总能找到一个二元问题把区别显出来。
这个要求就是 C96；它严格等价于全局纯态及不可约表示。

共同根的全部零约束也能表达同一件事：所有不可能的组合固定后，
只剩一份正归一读出。一个有限闭环已经示范了怎样通过整圈相容关系选出唯一根，
同时让内部时钟读出不同系统态。
把这个原理推广到实际宇宙，需要找到足够明确的内部关系并证明其共同解性质。

内容可以决定相干地址。门序列只要对共同根产生相同相干内容，就共享这一根地址；
如果要说两扇门完全相同，还须比较它们对所有内部准备的作用。
纯共同根所在的表示扇区内，每个单位向量都能经一个代数酉门取得。
实际能调用哪些门，以及无限历史用哪种极限完成，是这张关系网还必须明示的结构。

门的参数可以作为程序内容内生，程序又可以受其他程序控制。
相干关系和内积保持会约束这种递归：不同精确全输入门的程序，必须有足够的可区分空间。
这既允许递归，也使递归受到同一套量子关系约束。

每次读数可以变，跨读数的相容关系保持。
两种读法的波动和相位能归一编码在一个三维球内；
许多这样的窗口靠共同来源和重叠条件拼成整体。
内部记录的实际增长给局域时钟，关系的闭环比较给相位和曲率候选。
要把它们发展为引力及统一关系场，接下来必须证明时空、钟、运动与场方程之间的具体关系。

**本轮新增的精确结论。**
在已声明的复正关系代数内，

$$
\boxed{\begin{gathered}
\text{二元来源不可分解}
\ \Longleftrightarrow\
\text{纯共同根}
\ \Longleftrightarrow\
\text{零约束唯一性}\\
\Longleftrightarrow\ \text{GNS 不可约及标量交换子},\\[2pt]
\text{并推出同扇区的精确代数酉可达。}
\end{gathered}}
$$

这给出一个闭合、可反驳、可接回现有量子形式的候选。
从局部短约束恢复无限整体时，下一项具体任务是：
给出可陈述的约束族，证明存在性、唯一性和相容极限，并检验纯性是否随该极限保持。
本文的无限链例子已表明，最后一步需要证明，不能仅凭每一层纯就自动成立。

<a id="references"></a>

## 来源、版本与核读范围

<a id="ref-currentrepo"></a>

### [1]

the-omega-institute，*trureturing* 项目，
[当前公开首页](https://github.com/the-omega-institute/trureturing)。
本轮读取当前公开默认 `dev` 分支页面及进展列表，
但未取得可固定的更新提交 SHA。
下列仓库证明的核读均针对已存提交
`c63ab162315fddd0801cbe9f47dbf3eda6e13360`
的固定快照；不能把它写成已核对一个更新的 `dev` 提交。
公开开放 PR 的标题与状态仅用于定位进展，不作为已合并或已逐段验证的数学证明。
本轮未修改仓库，也未执行仓库构建或数学测试。

<a id="ref-omega"></a>

### [2]

trureturing，*AURIC Omega Static Compatibility Fiber Theory*，
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)。
本轮连续核读第 1–5 节的整体、正历史、内部观察者、响应商、未来等价与相容粘合，
以及第 12 节的有限量子关系图、相容有限态延拓与 GNS 构造。
第 12 节已经给出共同单位下递增有限维 $C^*$ 子代数的范数完成，
相容态的唯一连续延拓及循环根表示；本文沿用这些结果。
该递增有限维接口有其范围，不能不加说明地视为任意量子场论代数的构造。

<a id="ref-v74"></a>

### [3]

trureturing，*AURIC v74：平滑量子历史、余切动力学与内生运动*，
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_SMOOTH_QUANTUM_HISTORIES_COTANGENT_DYNAMICS_AND_ENDOGENOUS_MOTION_V74.md)。
本轮连续核读第 9–10 节及“时钟重标和离散采样”小节，
包括协方差 Gram 行列式、相对运动生成元
$H_{\rm rel}=R^*HR-i\hbar R^*\dot R$ 的完整证明，
以及相同离散门采样不能唯一确定连续生成元的反例。
静态共同根与移动内部读口的表示已经在项目中建立，
不将其重述计作本轮新发现。

<a id="ref-v78closure"></a>

### [4]

trureturing，*已证结构的内生闭合：有限根证书与结果核递归*，
[V78 固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_ENDOGENOUS_CLOSURE_FINITE_ROOT_CERTIFICATES_AND_OUTCOME_KERNEL_RECURSION_V78_CONTINUATION.md)。
本轮核读第 1.1–1.2 节、第 2 节定义 2.1 与命题 2.2，
第 5 节定理 5.1 的完整证明及反例，
以及第 9 节定理 9.1–9.2 的完整证明。
全部保尺度复合二元球测试与整体正性的等价已经在此承接 V77；
结果核树的有限递归相容也已经有条件式定理。
本文保留共同复结构、复合范围和实际后继供应的既有前件。

<a id="ref-v78pure"></a>

### [5]

trureturing，*单一纯整体中的设置—源关系：V78 共同态量词的定量接口*，
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_SINGLE_PURE_WHOLE_SETTING_SOURCE_RELATIONS_V78_CONTINUATION.md)。
本轮核读第 1–2 节，包括定义 1.1、假设 1.2、共同源缺陷及定理 2.3 的证明。
原文明确区分整体结构、校准根向量和所选纯态泛函；
每个模型固定一个纯态不等于所有候选模型只有唯一解。
共同整体归属或全局纯性也不自动推出设置与源的独立性。

<a id="ref-v80"></a>

### [6]

trureturing，*AURIC v80：全结果二元差分不增与内生量子过程*，
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_ALL_OUTCOME_BINARY_DIFFERENCE_NONEXPANSION_FINITE_ORIENTED_ANCHORS_AND_ENDOGENOUS_QUANTUM_PROCESSES_V80.md)。
本轮连续核读第 16.1–16.2 节的条件式重建总表与内生性范围说明。
内部归属、共同复比较、概率效果、实际仪器、独立复合和光滑时钟各自保留其明确前件；
把所有对象放入整体并不使这些相容条件在逻辑上自行成立。

<a id="ref-v95"></a>

### [7]

本对话研究稿，*AURIC v95：一个完整候选的定义、定理与反向审计*，
标题页日期为 2026 年 11 月 3 日（新加坡）。
承接有限维 C95 的二元终态判据、实际幂收敛、
守恒资料纤维内的唯一终态及内生最大不动支撑。
这些是上一轮的动力学接口；本轮的共同纯根与不可约表示
不把可逆酉轨道重新解释为全初态的吸引收敛。

<a id="ref-kadison1957"></a>

### [8]

Richard V. Kadison，
*Irreducible Operator Algebras*，
Proceedings of the National Academy of Sciences of the United States of America
**43**(3)，273–276，1957。
[DOI: 10.1073/pnas.43.3.273](https://doi.org/10.1073/pnas.43.3.273)；
[原始论文扫描件](https://www.isibang.ac.in/~soumyashant/misc/collected-works-of-kadison/1950s/1957_IrreducibleOperatorAlgebras.pdf)。
本轮核读原论文正文第 273–276 页，
尤其第 274 页定理 1 的有限自伴插值证明与第 275 页推论 2 的零约束结构。
原定理的误差修正使用 Kaplansky 密度与范数可和级数；
本稿把它作为标准定理调用，不声称为本轮新结果。

<a id="ref-glimm1960"></a>

### [9]

James G. Glimm、Richard V. Kadison，
*Unitary Operators in $C^*$-Algebras*，
Pacific Journal of Mathematics **10**(2)，547–556，1960。
[DOI: 10.2140/pjm.1960.10.547](https://doi.org/10.2140/pjm.1960.10.547)。
本轮核读第 547–553 页中定理 1 与推论 8 的相关证明。
同一不可约表示内的酉连接与相应纯态等价属于既有算子代数结构；
不将其量词扩成一个固定表示覆盖代数上的全部纯态。

<a id="ref-spiegel2022"></a>

### [10]

Daniel Spiegel、Juan Moreno、Marvin Qi、Michael Hermele、
Agnès Beaudry、Markus J. Pflaum，
*Continuous Dependence on the Initial Data in the Kadison Transitivity
Theorem and GNS Construction*，arXiv:2112.13315v2，2022。
[作者预印本](https://arxiv.org/pdf/2112.13315v2)；
[期刊 DOI: 10.1142/S0129055X22500313](https://doi.org/10.1142/S0129055X22500313)。
本轮连续核读定理 1.14 及其证明（预印本印刷第 15–16 页），
以及定理 3.4 的全部证明（第 31–32 页）。
后者给出不可约表示中的有限插值和自伴插值，并保留目标算子的范数上界；
前者明确同扇区、共同不可约向量表示与酉变换的等价。
该文的定理 3.4 调用基础 Kadison 定理，不是从无前提推出酉供应。

<a id="ref-mueger2022"></a>

### [11]

Michael Müger，
*Pure States and the Irreducibility of GNS Representations*，
2022 年 5 月 17 日，4 页。
[作者原文](https://www.math.ru.nl/~mueger/PDF/pure.pdf)。
本轮通读全文，包括纯态与不可约性的等价证明、
简化传递定理 2.1 及推论 2.3。
定理 2.1 直接证明一般元素 $a\xi=\eta$；
自伴与酉加强形式在说明 2.4 中提及而未在该短文重证，
因此正文的有限自伴插值引用前两项原始来源。

<a id="ref-fewster2019"></a>

### [12]

Christopher J. Fewster、Kasia Rejzner，
*Algebraic Quantum Field Theory—an Introduction*，
arXiv:1904.04051v2，2019。
[作者预印本](https://arxiv.org/pdf/1904.04051v2)。
本轮核读第 2.2–2.3 节中的态、GNS 定理 10、
构造及循环表示的酉唯一性证明（印刷第 8–9 页），
以及纯态、不可约表示与混合态向量表示的范围说明。
一般 $*$ 代数表示可能涉及共同稠密定义域；
本文使用的 $C^*$ 代数分支则给出有界表示。

<a id="ref-putnam2019"></a>

### [13]

Ian F. Putnam，*Lecture Notes on $C^*$-Algebras*，
2019 年 1 月 3 日。
[作者讲义原文](https://web.uvic.ca/~ifputnam/ln/C*-algebras.pdf)。
本轮核读第 1.12 节定理 1.12.4、1.12.6、1.12.7 及相关证明，
印刷第 54–58 页，涉及零左理想、GNS 构造、循环表示唯一性与纯态的不可约刻画。
正文给出本轮所需的受支配正泛函对应及纯性等价的完整证明；
讲义使用第一变量线性的内积约定，本文统一使用第二变量线性的约定。

<a id="ref-nielsen1997"></a>

### [14]

Michael A. Nielsen、Isaac L. Chuang，
*Programmable Quantum Gate Arrays*，
Physical Review Letters **79**，321–324，1997。
[DOI: 10.1103/PhysRevLett.79.321](https://doi.org/10.1103/PhysRevLett.79.321)；
[作者预印本](https://arxiv.org/pdf/quant-ph/9703032)。
本轮核读预印本第 2 页的关键无编程证明，
即不同酉操作的确定性精确实现对程序态可区分性的要求。
使用时保留固定处理器、精确性和确定性等范围；
不把该定理扩成近似、概率性或任意资源模型的统一禁止结论。

<a id="ref-page1983"></a>

### [15]

Don N. Page、William K. Wootters，
*Evolution without Evolution: Dynamics Described by Stationary Observables*，
Physical Review D **27**，2885–2892，1983。
[DOI: 10.1103/PhysRevD.27.2885](https://doi.org/10.1103/PhysRevD.27.2885)。
本轮核对出版信息与作者摘要；完整正文入口未成功取得，
因此不声称已核读原文全部证明。
该来源仅用于标明静态整体与内部时钟相关描述的既有研究背景；
本文实际使用的条件模型与时钟公式在正文独立给出。
