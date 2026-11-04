# 手性定向、守恒关系与内生量子终态

从正交二态的有限衰减到不动代数与调和边界

**AURIC v95：一个完整候选的定义、定理与反向审计**

项目连续研究稿

2026 年 11 月 3 日（新加坡）

## 摘要

用户提出新的约束：若 $\Omega$ 是相对于观察者手性的最终量子态，它就不能任意选取。
本轮把这句话推进为有限维的充要定理。
先声明与观察者手性相容的实际正向更新 $\Phi$；守恒读口由 $\operatorname{Fix}\Phi^*$ 内生定义。
唯一新候选 C95 要求：具有相同守恒资料、起初支持正交的两态，
必在某段有限正向历史后失去完全可区分性。
不预先指定最终态，也不要求每一步都严格收缩。

证明 C95 当且仅当全部实际迭代 $\Phi^n$ 收敛到唯一的 CPTP 幂等过程 $R$。
每个守恒资料纤维内都有唯一终态 $\omega_\rho=R\rho$；
全初态共享一个终态，当且仅当守恒读口只有标量。
紧致性把逐对存在的有限时刻提升为共同有限步与严格收缩系数，给出几何收敛界。

在忠实稳态载体上，所有永不损失的关系形成可逆代数。
真正终态存在，恰好要求其上不再保留非平凡旋转。
这一判据通过有限次平方缺额与 v94 衔接；极限过程正是 v94 的规范约化。
参照也由动力学产生；非忠实情形先确定最大不动支撑，
再将原空间守恒关系解释为终端代数在瞬态空间上的完全正调和延拓。

双跃迁 qubit 模型给出手性盘旋、内生平衡终态和纯态边界。
反例严格区分手性、唯一不动态、平均收敛、实际收敛与有限步结束，
并说明完整记录如何保留局部衰减的区别。
本文继承有限复量子过程接口；混合理论和乘法域结构按既有文献归属，
新增内容指项目内的关系接续，不宣称从一个方向符号推出全部量子公理。
全部数学为解析证明与独立解析复核，未运行数学程序、CAS、数值求值、枚举或测试。

## 目录

- [1. 项目接续：最终态必须由什么关系决定](#section-1)
- [2. 方向、固定点与最终收敛的反向边界](#section-2)
- [3. 先给有向过程，再由它定义守恒读口](#section-3)
- [4. 本轮唯一候选 C95：同资料正交二态最终出现重叠](#section-4)
- [5. 从逐对有限延伸到统一有限窗口](#section-5)
- [6. 最终态的唯一性范围与二元三维报告](#section-6)
- [7. 忠实稳态下，平方缺额给出同一终态判据](#section-7)
- [8. 所有永不损失的关系形成一个可逆代数](#section-8)
- [9. C95 正好排除可逆代数中的非固定运动](#section-9)
- [10. 参照由动力学产生：最大不动支撑与终态族](#section-10)
- [11. 终端载体恢复 v94：普通代数、块重置与参照等价](#section-11)
- [12. 瞬态关系如何延伸终端读数：完全正的调和边界](#section-12)
- [13. 由两个内部跃迁率锁定终态：有向量子位的解析模型](#section-13)
- [14. 保留完整内部记录时，局部吸引子不成为整体内容的融合](#section-14)
- [15. 门序列条件：每扇门有终态，仍不保证整条历史有终态](#section-15)
- [16. 实际极限、时间平均与单位圆上的残留运动](#section-16)
- [17. 参照可以换坐标，实际终点不能任意换](#section-17)
- [18. 怎样接到现有量子力学公理：本轮所在的完整依赖链](#section-18)
- [19. 本轮候选的完整白话表述与理论边界](#section-19)
- [来源、版本与核读范围](#references)

<a id="section-1"></a>

## 1. 项目接续：最终态必须由什么关系决定

<a id="sec-c95-position"></a>

本轮由 v94 递增到 v95，研究用户提出的收紧：
*如果 $\Omega$ 表示相对于观察者手性的最终量子态，它就不能随意选。*
这个方向可以被准确表达为：给定实际观察更新及其允许的正向历史，
终态必须是这套更新所确定的极限。
但“有方向”“有不动点”“沿方向真正收敛”是需要分别证明的关系。

本轮核读当前公开 `dev` 页面，尚未取得可固定的更晚提交 SHA；
精确理论来源仍采用已取得的
`c63ab162315fddd0801cbe9f47dbf3eda6e13360`
快照（2026 年 11 月 2 日） [1](#ref-currentrepo)。
当前开放的候选工作没有被当作已合并、已核验的数学前件。
所引理论原文仅作只读核对，没有执行仓库构建或测试。

项目 V74 已把局部手性写成接触关系

$$
\alpha=-i\langle\psi,d\psi\rangle,
\qquad
d\alpha(u,v)=2\operatorname{Im}\langle u,v\rangle.
$$

绕行方向改变会改变留下的相位；这个结论描述有向面积与历史相位，
尚未给吸引子 [3](#ref-v74)。
$\Omega$ 静态纤维稿也已明确：正历史追加不会被系统读出的逆门抵消；
安全且持续有后继仍不等于最终完成；相位门的非负幂甚至可以逼近逆门
 [2](#ref-omega)。
重复内部记录模型已有不动代数与无衰减相位模式的明确区别 [4](#ref-records)。

因此本轮推进到更具体的二态约束：

$$
\boxed{
\begin{gathered}
\text{同一守恒资料中的正交二态}\\
\text{不能沿正向历史永远保持完全可区分}
\end{gathered}
\quad\Longleftrightarrow\quad
\begin{gathered}
\text{每份守恒资料}\\
\text{具有唯一实际极限态}.
\end{gathered}}
$$

这里的守恒读口由更新 $\Phi$ 自己定义，最终态则由极限推出。
它们没有在候选之前被外部指定。

标准的广义 Lyapunov 理论已经用态对的渐近距离刻画混合，
有限量子通道文献也已区分唯一不动态与实际迭代收敛
 [7](#ref-bg2007)、[8](#ref-bcgpy2013)。
本轮给守恒纤维中的自足证明，连接正交二态、有限收缩、平方缺额、v94 物理约化、
最大不动支撑与手性模型；不把标准混合定理重新认领为首次发现。

**白话图景。**如果最终态只是任意挑一份参照，确实没有解释它为什么是终点。
这一轮先固定实际怎样向前变化，再由这个变化找出永远保留的读数。
在这些读数相同的内容之间，若没有一对完全分离的状态能永远保持完全分离，
它们就会趋向同一个代表。
最终态因此由正向过程和守恒资料共同决定，手性负责的方向也有了明确的位置。

<a id="section-2"></a>

## 2. 方向、固定点与最终收敛的反向边界

<a id="sec-c95-basic-obstructions"></a>

以下反例先回答：如果只保留用户直觉中的“有手性、有方向”，还会允许什么？
它们不是证明该直觉没有用途，而是精确找出需要被下一项内部关系约束的自由度。

### 命题 2.1（有向酉轨迹的极限只能来自原本不动的态）

<a id="prop-c95-unitary-no-attractor"></a>

对有限维酉 $U$，若 $\rho_n=U^n\rho U^{-n}$ 在迹范数中收敛到 $\omega$，
则 $U\omega U^\dagger=\omega$ 且 $\rho=\omega$。
因此非平凡闭系统酉轨迹没有不同于其初态的吸引终点。

**证明。**
由连续性，$U\omega U^\dagger=\lim_n\rho_{n+1}=\omega$。
迹距离的酉不变性给

$$
D_{\rm tr}(\rho_n,\omega)=D_{\rm tr}(\rho,\omega),
\qquad D_{\rm tr}(\rho,\sigma)=\tfrac12\left\lVert \rho-\sigma\right\rVert_1.
$$

左侧趋零，故 $\rho=\omega$。
同理，两个不同初态的完整酉输出不能收敛到同一状态，因为其相互距离始终保持。

取 $U_\chi=e^{-i\chi\theta Z/2}$，其中 $\chi=\pm1$，
就得到一个有明确旋向的 qubit 例子。
非轴上态可以周期回返，也可以在圆上无周期地继续旋转；旋向本身没有吸引性。
这与项目既有“正向门调用不排除回返”的结论相容 [2](#ref-omega)。

### 命题 2.2（唯一不动态也不保证实际迭代有终点）

<a id="prop-c95-flip"></a>

令

$$
\Phi_{\rm flip}(\rho)
=\rho_{00}\lvert 1\rangle\langle 1\rvert+\rho_{11}\lvert 0\rangle\langle 0\rvert.
$$

这是 CPTP 映射，唯一不动态为 $I/2$，但 $\lvert 0\rangle\langle 0\rvert$ 与 $\lvert 1\rangle\langle 1\rvert$
永远交替，实际迭代不收敛。

**证明。**
Kraus 算符为 $\lvert 1\rangle\langle 0\rvert$、$\lvert 0\rangle\langle 1\rvert$，其伴随乘积之和为单位。
Bloch 作用是 $(x,y,z)\mapsto(0,0,-z)$。
不动要求 $x=y=z=0$，故仅有 $I/2$。
但正反 $Z$ 纯态始终交换，二态迹距离始终为一。
其时间平均趋于 $I/2$，原始状态序列却没有极限。

这个经典二周期已经出现在量子混合文献中 [8](#ref-bcgpy2013)。
它表明不能用 Cesàro 平均收敛替换实际迭代收敛，
也不能把一个稳定平均值称为每一步都趋近的最终态。

### 命题 2.3（可以每份资料有终点，却没有全初态共同终点）

<a id="prop-c95-dephasing-terminal-family"></a>

对 $\Delta_Z(\rho)=P_0\rho P_0+P_1\rho P_1$，每条轨迹一步后固定。
但 $Z$ 读数保持，故不同 $Z$ 资料具有不同终态。

**证明。**
Bloch 作用为 $(x,y,z)\mapsto(0,0,z)$，所以 $\Delta_Z^2=\Delta_Z$。
$P_0,P_1$ 是不同不动态；同一 $z$ 的全部初态则都被送到 $(I+zZ)/2$。

**白话图景。**顺着一个方向走，可以一直绕圈；只有一个不动点，也可以始终在它两边交换。
即使每条轨迹都稳定下来，保留下来的资料不同，终态仍可以不同。
所以真正要约束的是：哪些区别允许永久保留，哪些区别在同一份守恒资料中必须逐渐失去完全可区分性。
下一节把这句话写成唯一候选。

<a id="section-3"></a>

## 3. 先给有向过程，再由它定义守恒读口

<a id="sec-c95-directed-interface"></a>

令 $\mathcal H$ 为 $d\ge1$ 维复 Hilbert 空间。
本轮继承此前的有限量子过程接口 [5](#ref-v80)、[6](#ref-v94)，
给定一项实际声明的完全正、保迹映射

$$
\Phi:B(\mathcal H)\longrightarrow B(\mathcal H).
$$

它表示观察者采用的同一个正向步长或固定观察周期。
若手性 $\chi$ 选择不同过程，可以写成 $\Phi_\chi$；
以下证明在选定该过程后进行。
时间有向性在此表现为 $\Phi^n$ 的 $n=0,1,2,\ldots$，
没有据此假设反向过程不存在，也没有预先指定最终态。

记 $E=\Phi^*$ 为迹对偶。它保持单位且完全正。
由实际过程定义当前的守恒读口

<a id="eq-c95-conserved-readout"></a>

$$
\mathcal S=\{s=s^\dagger:E(s)=s\},\qquad
 \mathcal A=\operatorname{Fix} E=\mathcal S+i\mathcal S.
\tag{3.1}
$$

此时 $I\in\mathcal S$；在未有忠实稳态前，
不预设 $\mathcal A$ 对普通矩阵乘法闭合。

### 定义 3.1（守恒资料纤维与未读差异）

<a id="def-c95-conservation-fiber"></a>

对密度态 $\rho,\sigma$，定义

$$
\rho\sim_{\mathcal S}\sigma
 \quad\Longleftrightarrow\quad
 \operatorname{Tr}(\rho s)=\operatorname{Tr}(\sigma s)\quad(s\in\mathcal S).
$$

令

<a id="eq-c95-unread-differences"></a>

$$
\Delta=\{X=X^\dagger:\operatorname{Tr}(Xs)=0\text{ 对全部 }s\in\mathcal S\}.
\tag{3.2}
$$

于是 $\rho\sim_{\mathcal S}\sigma$ 当且仅当 $\rho-\sigma\in\Delta$。
因为 $I\in\mathcal S$，$\Delta$ 中每个算符迹为零；
又因为 $E(s)=s$，有 $\Phi(\Delta)\subseteq\Delta$。

任意守恒关系满足

$$
\operatorname{Tr}(\Phi^n(\rho)s)=\operatorname{Tr}(\rho s)\qquad(n\ge0,s\in\mathcal S).
$$

因此不同的守恒资料不能在这个实际过程中被随意改写。
本轮先由 $\Phi$ 决定这些资料，再询问它们是否足以唯一确定一份最终代表。

以下使用迹距离

$$
D_{\rm tr}(\rho,\sigma)=\frac12\left\lVert \rho-\sigma\right\rVert_1,
 \qquad\left\lVert X\right\rVert_1=\operatorname{Tr}\sqrt{X^\dagger X}.
$$

它由全部二元效果的最大概率差给出，而不是额外选择的一种坐标距离。

**白话图景。**先说明观察者沿哪个实际过程向前，再看哪些问题在这个过程中始终给同一个答案。
这些不变答案构成当前的守恒资料。
最终态若存在，必须保留它们；因此最终态不能先任意挑选，再要求过程替它补出理由。

<a id="section-4"></a>

## 4. 本轮唯一候选 C95：同资料正交二态最终出现重叠

<a id="sec-c95-candidate"></a>

### 定义 4.1（候选 C95）

<a id="def-c95-candidate"></a>

对上述同一正向过程 $\Phi$ 及其内生读口 $\mathcal S$，要求：
对每一对具有相同守恒资料、支撑正交的密度态，
总有一个有限正向延伸使其输出支撑不再正交。
即

<a id="eq-c95-orthogonal-criterion"></a>

$$
\boxed{\quad
 \begin{gathered}
 \rho\sim_{\mathcal S}\sigma,\qquad \rho\sigma=0
 \\
 \Longrightarrow\quad
 \exists n\ge1:\ \operatorname{Tr}\bigl[\Phi^n(\rho)\Phi^n(\sigma)\bigr]>0.
 \end{gathered}\quad}
\tag{4.1}
$$

该条件称为 C95。此时没有给定参照态 $\tau$，也没有给定候选终态 $\Omega$。

这项条件只检查*当前守恒资料相同而一开始完全可区分*的两态。
它不要求一步后立刻合并，不要求不同守恒资料的状态相互合并，
也不把每一个合法量子过程都宣称为具有终态的过程。
它是本轮赋予观察切分“正向最终代表”含义的候选条件。
下文以 $\Omega_\rho$ 记该观察切分中由输入 $\rho$ 得到的归一化终态；
作为全部内部关系结构的整体 $\Omega$ 仍保持项目的既有含义。
二者通过观察者的读口联系，不能把一个有限状态矩阵直接等同于全部历史记录。

### 引理 4.2（迹距离收缩与正交支撑）

<a id="lem-c95-trace-contractivity"></a>

对任意自伴 $X$，

$$
\left\lVert \Phi(X)\right\rVert_1\le\left\lVert X\right\rVert_1.
$$

对密度态 $\rho,\sigma$，有

<a id="eq-c95-orthogonal-trace-distance"></a>

$$
D_{\rm tr}(\rho,\sigma)=1
 \quad\Longleftrightarrow\quad
 \rho\sigma=0
 \quad\Longleftrightarrow\quad
 \operatorname{Tr}(\rho\sigma)=0.
\tag{4.2}
$$

**证明。**
写 $X=X_+-X_-$ 为正负部分。正性、保迹和三角不等式给

$$
\left\lVert \Phi(X)\right\rVert_1
 \le\operatorname{Tr}\Phi(X_+)+\operatorname{Tr}\Phi(X_-)
 =\operatorname{Tr} X_++\operatorname{Tr} X_-=\left\lVert X\right\rVert_1.
$$

令 $P$ 为 $\rho-\sigma$ 的正谱投影。
迹零性给 $D_{\rm tr}(\rho,\sigma)=\operatorname{Tr} P(\rho-\sigma)\le1$。
若等于一，则必有 $\operatorname{Tr}(P\rho)=1$、$\operatorname{Tr}(P\sigma)=0$。
正性因此迫使 $\rho$ 支撑在 $P$ 中，$\sigma$ 支撑在 $I-P$ 中。
反向，支撑正交时正负部分就是 $\rho,\sigma$，迹距离为一。
最后，$\operatorname{Tr}(\rho\sigma)=\left\lVert \rho^{1/2}\sigma^{1/2}\right\rVert_2^2$，
其为零当且仅当两个支撑正交。

### 引理 4.3（所有未读差异都由一个正交同资料态对承载）

<a id="lem-c95-jordan-pair"></a>

任意 $0\ne X\in\Delta$ 都可以写成

<a id="eq-c95-jordan-pair"></a>

$$
X=a(\rho_+-\rho_-),\qquad a>0,
 \quad\rho_+\rho_-=0,
 \quad\rho_+\sim_{\mathcal S}\rho_-.
\tag{4.3}
$$

因此 C95 等价于

<a id="eq-c95-individual-strict-contraction"></a>

$$
\forall\,0\ne X\in\Delta,\quad
 \exists n\ge1:\ \left\lVert \Phi^n(X)\right\rVert_1<\left\lVert X\right\rVert_1.
\tag{4.4}
$$

**证明。**
$X$ 迹零，故其 Jordan 正负部分满足
$a:=\operatorname{Tr} X_+=\operatorname{Tr} X_->0$。
取 $\rho_\pm=X_\pm/a$，即得正交密度态。
对每个 $s\in\mathcal S$，$\operatorname{Tr}(Xs)=0$，所以两态具有相同资料。
并且 $\left\lVert X\right\rVert_1=2a$。
由引理 [4.2](#lem-c95-trace-contractivity)，
式 [(4.1)](#eq-c95-orthogonal-criterion) 恰给
$\left\lVert \Phi^n(X)\right\rVert_1<2a$。
反向只须取 $X=\rho-\sigma$。

**白话图景。**这里不必逐一猜测所有不确定关系。
任何保持守恒资料的正反差异，都能拆成一对支撑正交、资料相同的状态。
所以只要检查这些最清楚的两端状态，已经覆盖所有未读方向。
候选要求的是：一个没有守恒理由维持的完全区别，不能沿正向过程永远原样保留。

<a id="section-5"></a>

## 5. 从逐对有限延伸到统一有限窗口

<a id="sec-c95-compact-window"></a>

### 定理 5.1（C95 的有限窗口、收敛与最终代表等价）

<a id="thm-c95-equivalence"></a>

对有限维 CPTP 过程 $\Phi$，下列条件等价：

1. C95 成立；

2. 存在整数 $N\ge1$ 与 $0\le q<1$，使


   <a id="eq-c95-uniform-window"></a>

   $$
   \left\lVert \Phi^N(X)\right\rVert_1\le q\left\lVert X\right\rVert_1
     \qquad(X\in\Delta);
   \tag{5.1}
   $$

3. 对每个密度态 $\rho$，正向状态序列 $\Phi^n(\rho)$ 收敛。

成立时，极限组成由 $\Phi$ 唯一决定的 CPTP 映射

<a id="eq-c95-limit"></a>

$$
\boxed{R=\lim_{n\to\infty}\Phi^n,\qquad
 \Omega_\rho:=R(\rho).}
\tag{5.2}
$$

它满足

<a id="eq-c95-terminal-retraction"></a>

$$
R^2=R,\qquad \Phi R=R\Phi=R,\qquad
 R(\rho)=R(\sigma)\Longleftrightarrow\rho\sim_{\mathcal S}\sigma.
\tag{5.3}
$$

每个守恒资料纤维中恰有一个 $\Phi$ 固定态，即 $\Omega_\rho$。
此外，存在与上面相同的 $N,q$，使

<a id="eq-c95-rate"></a>

$$
\boxed{\quad
 D_{\rm tr}\bigl(\Phi^n(\rho),\Omega_\rho\bigr)
 \le q^{\lfloor n/N\rfloor}D_{\rm tr}(\rho,\Omega_\rho)
 \le q^{\lfloor n/N\rfloor}.
 \quad}
\tag{5.4}
$$

**证明。**
**先处理零差异空间。**
若 $\Delta=\{0\}$，则 $\mathcal S=\operatorname{Herm}(\mathcal H)$，
所以 $E=\operatorname{id}$、$\Phi=\operatorname{id}$。
没有同资料正交态对，C95 的量词为空；三个条件均成立，$R=\operatorname{id}$。
式 [(5.1)](#eq-c95-uniform-window) 可取 $N=1,q=0$；
式 [(5.4)](#eq-c95-rate) 左侧恒为零。
以下设 $\Delta\ne\{0\}$。

**条件 1 推出条件 2。**
设 $\mathcal C$ 为全部同资料正交密度态对的集合。
状态空间有限维紧致，同资料是闭线性约束，
$\operatorname{Tr}(\rho\sigma)=0$ 是闭约束，所以 $\mathcal C$ 紧致。
引理 [4.3](#lem-c95-jordan-pair) 保证它非空。

对每个 $n\ge1$，令

$$
U_n=\{(\rho,\sigma)\in\mathcal C:
 D_{\rm tr}(\Phi^n\rho,\Phi^n\sigma)<1\}.
$$

这些集合相对开。迹距离收缩使 $U_n\subseteq U_{n+1}$，
C95 使它们覆盖整个 $\mathcal C$。
紧致性给有限子覆盖，取其中最大的指标 $N$，便有 $U_N=\mathcal C$。
连续函数在紧集上达到最大值，故

$$
q:=\max_{(\rho,\sigma)\in\mathcal C}
 D_{\rm tr}(\Phi^N\rho,\Phi^N\sigma)<1.
$$

对任意 $X\in\Delta$ 使用式 [(4.3)](#eq-c95-jordan-pair)，得到
式 [(5.1)](#eq-c95-uniform-window)。
反向，条件 2 作用在任意这样的正交态差上，立即给 C95。

**条件 2 推出条件 3。**
因 $\Phi\Delta\subseteq\Delta$，反复应用统一窗口和单步非扩张，得到

<a id="eq-c95-difference-rate"></a>

$$
\left\lVert \Phi^n(X)\right\rVert_1
 \le q^{\lfloor n/N\rfloor}\left\lVert X\right\rVert_1
 \qquad(X\in\Delta).
\tag{5.5}
$$

对任意状态 $\rho$，$\Phi(\rho)-\rho\in\Delta$，因此

$$
\left\lVert \Phi^{n+1}(\rho)-\Phi^n(\rho)\right\rVert_1
 \le q^{\lfloor n/N\rfloor}\left\lVert \Phi(\rho)-\rho\right\rVert_1.
$$

右侧对 $n$ 可求和，所以状态序列为 Cauchy 序列，存在极限。

**构造极限映射及其结构。**
密度态实线性张成全部自伴矩阵，后者复线性张成全部矩阵。
故逐态极限唯一延拓为复线性 $R$，而且有限维下 $\Phi^n$ 作为线性映射也收敛到 $R$。
对任意有限参考，$\operatorname{id}\otimes\Phi^n$ 的正性在极限保持，
故 $R$ 完全正；迹保持也传到极限。
连续性与移位给 $\Phi R=R\Phi=R$。
对任意固定态 $\omega$，$R(\omega)=\omega$，所以 $R^2=R$。

极限保留每个 $s\in\mathcal S$ 的读数。
若 $\rho\sim_{\mathcal S}\sigma$，其差在 $\Delta$，
由式 [(5.5)](#eq-c95-difference-rate) 知 $R\rho=R\sigma$。
反向，输出相同再读取守恒关系，便知输入同资料。
因此式 [(5.3)](#eq-c95-terminal-retraction) 成立。
若同一纤维内存在两个固定态，$R$ 一方面固定二者，另一方面必须融合二者，故它们相同。
每个纤维已有固定态 $R\rho$，所以存在与唯一性同时成立。

取 $X=\rho-R\rho\in\Delta$，并用 $\Phi^nR\rho=R\rho$，
式 [(5.5)](#eq-c95-difference-rate) 给出式 [(5.4)](#eq-c95-rate)。

**条件 3 推回条件 1。**
此时上述有限维线性极限与 CPTP 性仍可直接构造，
且 $R\Phi=\Phi R=R$、$R^2=R$。
对偶极限满足

$$
\operatorname{ran} R^*=\operatorname{Fix} E=\mathcal A:
$$

因为 $ER^*=R^*$ 给一个包含关系，而任何 $E$ 固定元均被全部 $E^n$、继而 $R^*$ 固定，
给另一个包含关系。
对 $X\in\Delta$ 及任意自伴 $b$，$R^*(b)\in\mathcal S$，因此

$$
\operatorname{Tr}(R(X)b)=\operatorname{Tr}(XR^*(b))=0.
$$

所以 $R(X)=0$，$\Phi^n(X)\to0$。
对同资料正交态对使用 $X=\rho-\sigma$，其输出迹距离趋于零，
必在某个有限 $n$ 小于一。由引理 [4.2](#lem-c95-trace-contractivity) 得 C95。

这里的有限 $N$ 是共同的*正向延伸长度*，并不意味着只检验有限个任意挑选的输入就足够。
量词仍覆盖整个实际声明的输入空间及其全部同资料正交态对。
几何收敛率只在定理条件下成立；本文没有由有限个样本推断它。
当 $q=0$ 时按 $q^0=1$ 理解零次幂，后续窗口的未读差异精确消失。

**白话图景。**每一对没有守恒理由维持的完全区别，只要迟早出现一次重叠，
有限维的紧致性就会把这些各自不同的等待时间收束为一个共同窗口。
每经过这个窗口，所有未读差异都按同一个严格小于一的比例减小。
因此最终代表并非提前指定的终点；它由同一个正向过程和保留下来的资料共同确定。

<a id="section-6"></a>

## 6. 最终态的唯一性范围与二元三维报告

<a id="sec-c95-terminal-scope"></a>

### 推论 6.1（全部初态共享一个终态的充要条件）

<a id="cor-c95-global-terminal"></a>

在 C95 下，存在对全部初态相同的 $\Omega$，当且仅当

$$
\mathcal S=\mathbb R I.
$$

此时 $R(X)=\operatorname{Tr}(X)\Omega$。
一般情形下，$\Omega_\rho$ 只由 $\rho$ 的守恒资料决定；
不同守恒资料可以对应不同终态。

**证明。**
若 $\mathcal S=\mathbb R I$，全部密度态同资料，故 $R$ 将它们送到同一个 $\Omega$。
由线性延拓得到所述公式。
反过来，若全部输入的输出相同，则对任意 $s\in\mathcal S$，
$\operatorname{Tr}(\rho s)=\operatorname{Tr}(\Omega s)$ 对全部密度态成立。
秩一态分离自伴算符，故 $s$ 必为标量。

因此，C95 的一般结果是*每个守恒资料纤维中的唯一最终态*。
在 $\Delta=0$ 的恒等边界中，每个状态已经是自己的终态；
这不产生一个与初态无关的共同终点。
“最终”在式 [(5.2)](#eq-c95-limit) 中指渐近极限，
不自动表示存在一扇最后的有限门，在它之后已经精确到达。

二态可区分性也能装入归一二元三维报告。
对等先验的输入标签 $\rho,\sigma$，取 $\rho-\sigma$ 的正谱投影作为最优二元判别效果。
其正确率与错误率分别为

$$
p_{\rm right}=\frac{1+D_{\rm tr}(\rho,\sigma)}2,
 \qquad p_{\rm wrong}=\frac{1-D_{\rm tr}(\rho,\sigma)}2.
$$

事实上，对任意效果 $0\le F\le I$，正确率为
$\frac12[1+\operatorname{Tr} F(\rho-\sigma)]$，而正谱投影恰达到最大正部分迹。
把这两个概率记录为

<a id="eq-c95-binary-report"></a>

$$
\Gamma(\rho,\sigma)
 =\operatorname{diag}(p_{\rm right},p_{\rm wrong})
 =\frac12\bigl(I+D_{\rm tr}(\rho,\sigma)Z\bigr),
 \qquad\mathbf b=(0,0,D_{\rm tr}).
\tag{6.1}
$$

支撑正交时报告在球面顶端 $D_{\rm tr}=1$；
C95 使同资料的这类报告在有限延伸后进入球内，
并由定理进一步趋于中心。
这是一份二态识别的归一报告，不把一般高维实际状态本身降成三个自由度。

**白话图景。**最终态不一定只有一个。
如果过程始终保留某个读数，不同读数就会保留不同的最终代表。
只有全部非平凡守恒区别都消失时，所有初态才共享同一个终点。
在二元报告中，最初可以完全判别的同资料两态位于球面；
正向过程让它们逐步变得不可判别，最终报告走向球心。

<a id="section-7"></a>

## 7. 忠实稳态下，平方缺额给出同一终态判据

<a id="sec-c95-square-interface"></a>

本节增加一个明确前件：过程具有忠实稳态

$$
\tau>0,\qquad\operatorname{Tr}\tau=1,\qquad\Phi(\tau)=\tau.
$$

它用于把 C95 连接到 v94 的平方缺额和普通可见代数 [6](#ref-v94)。
这不是 C95 定义的前件；纯态吸引过程可能没有全载体忠实稳态。
对非忠实情形必须另外说明循环支撑及其瞬态部分，不能先删掉输入方向再冒称全域结论。

在算符空间上定义对称加权内积

<a id="eq-c95-symmetric-inner-product"></a>

$$
\langle a,b\rangle_{\tau,s}
 =\frac12\operatorname{Tr}\tau(a^\dagger b+ba^\dagger),
 \qquad
 \left\lVert a\right\rVert_{\tau,s}^2
 =\frac12\operatorname{Tr}\tau(a^\dagger a+aa^\dagger).
\tag{7.1}
$$

忠实性保证其正定；有限维下它与任意固定矩阵范数等价。
这个内积只用于解析证明，没有改变状态空间或引入新的概率规则。

### 引理 7.1（有向过程的加权平方非增）

<a id="lem-c95-weighted-contraction"></a>

对 $E=\Phi^*$ 及任意 $a$，有

$$
\left\lVert E(a)\right\rVert_{\tau,s}\le\left\lVert a\right\rVert_{\tau,s}.
$$

对自伴 $s$ 与正整数 $m$，定义

<a id="eq-c95-square-defect"></a>

$$
\boxed{\quad
 Q_m(s)=E^m(s^2)-E^m(s)^2\ge0,
 \qquad
 \operatorname{Tr}(\tau Q_m(s))
 =\left\lVert s\right\rVert_{\tau,s}^2-\left\lVert E^m(s)\right\rVert_{\tau,s}^2.
 \quad}
\tag{7.2}
$$

**证明。**
完全正、保持单位的 $E$ 满足 Schwarz 不等式
$E(a^\dagger a)\ge E(a)^\dagger E(a)$，对 $a^\dagger$ 也成立。
两式相加后取 $\tau$ 期望，再用 $\Phi(\tau)=\tau$，得到范数非增。
对 $E^m$ 重复同一论证，并取 $s=s^\dagger$，得到式
[(7.2)](#eq-c95-square-defect)。

**白话图景。**同一关系沿正向过程拉回以后，其加权平方强度不会增加。
少掉的部分就是一个非负平方缺额。
忠实稳态照到每个方向，因此缺额的平均为零时，整个正缺额都必须为零。
这与上一轮的机制相同，但现在检查的是一个关系沿整条正向历史能否一直不损失。

<a id="section-8"></a>

## 8. 所有永不损失的关系形成一个可逆代数

<a id="sec-c95-reversible-algebra"></a>

对保持单位的完全正映射 $T$，记其乘法域为

$$
\operatorname{MD}(T)=\{a:
 T(a^\dagger a)=T(a)^\dagger T(a),\quad
 T(aa^\dagger)=T(a)T(a)^\dagger\}.
$$

这两个平方等号通过 Schwarz 极化，等价于

<a id="eq-c95-multiplicative-domain"></a>

$$
T(ab)=T(a)T(b),\qquad T(ba)=T(b)T(a)
 \quad\text{对全部 }b.
\tag{8.1}
$$

确实，对 $a+zb$ 的平方缺额作实、虚四方向的一阶比较，
第一个等号给 $T(a^\dagger b)=T(a)^\dagger T(b)$；
再对 $a^\dagger$ 使用另一平方等号，并取伴随，即得左右乘法关系。
反向在乘法关系中取 $b=a^\dagger$ 即可。
式 [(8.1)](#eq-c95-multiplicative-domain) 直接保证该集合含单位、对线性组合、伴随及乘法闭合，
所以它是普通矩阵乘法下的 $C^*$ 子代数。

### 定理 8.1（有限平方无损层级与可逆代数）

<a id="thm-c95-reversible"></a>

设存在上述忠实稳态。令

<a id="eq-c95-no-loss-spaces"></a>

$$
K_m=\{a:\left\lVert E^m(a)\right\rVert_{\tau,s}=\left\lVert a\right\rVert_{\tau,s}\},
 \qquad K_0=B(\mathcal H).
\tag{8.2}
$$

则

<a id="eq-c95-reversible-algebra"></a>

$$
K_m=\operatorname{MD}(E^m),\qquad K_{m+1}\subseteq K_m,
 \qquad
 \mathcal N:=\bigcap_{m\ge1}K_m=K_{d^2}.
\tag{8.3}
$$

$\mathcal N$ 是普通含单位 $C^*$ 代数；
$E$ 限制到 $\mathcal N$ 后是保持 $\tau$ 期望的 $*$ 自同构。
它包含固定代数 $\mathcal A=\operatorname{Fix} E$。

**证明。**
对任意 $a$，两项 Schwarz 缺额

$$
D_m(a)=E^m(a^\dagger a)-E^m(a)^\dagger E^m(a),
 \qquad D_m(a^\dagger)
$$

均为正，而且

$$
\left\lVert a\right\rVert_{\tau,s}^2-\left\lVert E^m(a)\right\rVert_{\tau,s}^2
 =\tfrac12\operatorname{Tr}\tau\bigl(D_m(a)+D_m(a^\dagger)\bigr).
$$

忠实性使右侧为零当且仅当两项缺额都为零，故 $K_m=\operatorname{MD}(E^m)$。
于是每个 $K_m$ 都是线性空间及普通 $C^*$ 代数。
范数逐步非增，若第 $m+1$ 步仍无损，第 $m$ 步必也无损，故这些代数递降。

若某一步 $K_m=K_{m+1}$，则对 $a\in K_m$，

$$
\left\lVert E^m(Ea)\right\rVert_{\tau,s}
 =\left\lVert E^{m+1}a\right\rVert_{\tau,s}
 =\left\lVert a\right\rVert_{\tau,s}
 =\left\lVert Ea\right\rVert_{\tau,s}.
$$

因此 $E(K_m)\subseteq K_m$，且 $E$ 在此空间为等距。
有限维等距为单射，故在这个不变有限空间上也满射。
继续迭代显示全部后续步骤都无损，因此 $K_m=\mathcal N$。
这也覆盖 $m=0$ 的相等情形。

算符空间复维数为 $d^2$，这些递降空间都含非零单位。
它们不可能连续严格下降 $d^2$ 次，故至迟在所声明的 $d^2$ 窗口内稳定，
得到 $\mathcal N=K_{d^2}$。
在 $\mathcal N\subseteq\operatorname{MD}(E)$ 上，$E$ 保持乘法、伴随和单位，
又已证明满射，故为 $*$ 自同构。
稳态条件给 $\operatorname{Tr}\tau E(a)=\operatorname{Tr}\tau a$。

任何固定元显然沿全部步骤保持范数，故 $\mathcal A\subseteq\mathcal N$。
其固定元也对普通乘法闭合：对 $a,b\in\mathcal A$，
$a\in\operatorname{MD}(E)$ 给 $E(ab)=E(a)E(b)=ab$。
所以 $\mathcal A$ 在忠实稳态条件下本身为普通 $C^*$ 子代数。

$\mathcal N$ 描述所有可以一直无损传递的关系。
它们不一定已经静止：一个关系可以在此代数中不断旋转，平方强度却始终不减。
所以无损、可逆和固定是三个需要区分的概念。
手性选择旋转方向，不会自动把这些旋转消除。

保单位、完全正且保普通迹的通道，其稳定乘法域与外围可逆结构已有经典研究
 [9](#ref-rahaman2017)。
本节在忠实不动态的加权内积下另给所需证明，
没有将普通迹伴随与这里的加权伴随混同。

**白话图景。**把所有永远不损失的关系收集起来，它们会自己组成一个更大的代数。
正向过程在其中仍然可逆，可以循环、旋转或互相搬运。
真正妨碍最终态的，正是其中还会继续变化的部分。
因此“向前走”还要增加一项限制：永远保留的区别，必须已经由守恒关系解释。

<a id="section-9"></a>

## 9. C95 正好排除可逆代数中的非固定运动

<a id="sec-c95-no-reversible-rotation"></a>

### 定理 9.1（二态终失正交与有限平方缺额等价）

<a id="thm-c95-square-equivalence"></a>

在忠实稳态前件下，以下条件等价：

1. C95 成立；

2. $\mathcal N=\mathcal A=\operatorname{Fix} E$；

3. 对每个 $s=s^\dagger$，


   <a id="eq-c95-finite-square-criterion"></a>

   $$
   E(s)\ne s\quad\Longrightarrow\quad
    \exists\,1\le m\le d^2:\ \operatorname{Tr}(\tau Q_m(s))>0;
   \tag{9.1}
   $$

4. 对每个这样的非固定 $s$，统一第 $d^2$ 步的
    $\operatorname{Tr}(\tau Q_{d^2}(s))$ 严格为正。

成立时，$E^n$ 收敛到关于式 [(7.1)](#eq-c95-symmetric-inner-product)
的 $\mathcal A$ 正交投影；其对偶正是式 [(5.2)](#eq-c95-limit) 的 $R$。

**证明。**
先说明固定空间对 $E$ 是约化子空间。
把 $E$ 视为该加权 Hilbert 空间上的收缩，记其 Hilbert 伴随为 $E^\sharp$。
若 $Ea=a$，则

$$
\langle a,(I-E^\sharp E)a\rangle_{\tau,s}=0.
$$

由于 $I-E^\sharp E\ge0$，得 $E^\sharp Ea=a$，继而 $E^\sharp a=a$。
所以 $\mathcal A^\perp$ 也被 $E$ 保持。

若条件 2 成立，单位向量 $b\in\mathcal A^\perp$ 不属于 $K_{d^2}$。
故 $\left\lVert E^{d^2}b\right\rVert_{\tau,s}<1$。
紧致单位球面给统一的 $q_\tau<1$，使该空间上的 $d^2$ 步范数至多缩为 $q_\tau$ 倍。
于是 $E^n$ 在 $\mathcal A$ 上恒等、在其正交补上趋于零，
收敛到所述正交投影。
有限维迹对偶给 $\Phi^n$ 收敛，定理 [5.1](#thm-c95-equivalence) 推出 C95。
若正交补为零，则 $E=\operatorname{id}$，结论同样成立。

反过来，C95 给 $E^n\to R^*$，其像为 $\mathcal A$。
由刚证明的约化性质，极限只能是该加权正交投影。
若 $a\in\mathcal N$，则每一步范数均等于 $\left\lVert a\right\rVert_{\tau,s}$，
取极限得 $\left\lVert R^*a\right\rVert_{\tau,s}=\left\lVert a\right\rVert_{\tau,s}$。
正交投影保持向量范数当且仅当向量已在其像中，所以 $a\in\mathcal A$。
结合原有包含关系，得到条件 2。

若条件 2 成立，非固定自伴 $s$ 不在 $K_{d^2}$，
式 [(7.2)](#eq-c95-square-defect) 立即给条件 4，继而给条件 3。
反过来，若 $\mathcal N\ne\mathcal A$，
两者对伴随闭合，因此可取一个自伴 $s\in\mathcal N$ 且 $E(s)\ne s$。
它的全部平方缺额都为零，违反条件 3。

此处的 $d^2$ 是有限维解析稳定上界，不是数值搜索或有限样本外推。
二态候选与平方缺额是同一性质的两种表示：
前者检查实际状态的可区分性，后者检查对偶关系是否永久无损地运动。
平方缺额版本使用忠实稳态，二态版本本身不需要这个额外条件。

**白话图景。**最终态存在的准确要求是：永远无损的关系都已经固定。
如果还有一个关系能在可逆部分持续转动，过程就仍保留着不会安静下来的区别。
若没有这样的关系，每个非固定方向在有限窗口内都会出现正平方缺额，
正向过程便逐步只留下守恒资料决定的最终代表。

以上通过加权收缩与有限代数层级，已经自足证明 C95 的平方缺额判据。
后文定理 [16.1](#thm-c95-peripheral) 将给出不要求忠实稳态的单位圆谱判据，
并区分实际状态极限与时间平均。
其中固定特征空间可以多维；这正对应本节允许多个守恒资料纤维各有自己的终态。

<a id="section-10"></a>

## 10. 参照由动力学产生：最大不动支撑与终态族

<a id="sec-c95-endogenous-anchor"></a>

以下假设同一个有限维 CPTP 过程 $\Phi$ 满足 C95。
记 $E=\Phi^*$，$\mathcal S=\operatorname{Fix}(E)\cap\operatorname{Herm}(H)$，
$\mathcal S_{\mathbb C}=\mathcal S+i\mathcal S$。
由定理 [5.1](#thm-c95-equivalence)，实际幂极限
$R=\lim_{n\to\infty}\Phi^n$ 存在，且
$R^2=R$、$\Phi R=R\Phi=R$。
极限对偶投影记为 $E_\infty=R^*$，以区别于单步对偶 $E$。

### 定义 10.1（内生参照与终端支撑）

<a id="def-c95-anchor"></a>

若 $d=\dim H$，定义

<a id="eq-c95-anchor"></a>

$$
\boxed{\tau_0=R(I/d),\qquad P=\operatorname{supp}\tau_0,\qquad Q=I-P.}
\tag{10.1}
$$

$I/d$ 是共同矩阵接口中的单位归一态。
$\tau_0$ 用作动力学产生的最大支撑见证；
它不被定义为每一个初态都必须到达的同一终点。

### 定理 10.2（最大不动支撑）

<a id="thm-c95-support"></a>

$\tau_0$ 是 $\Phi$ 的不动态，且以下结论成立：

1. 每份极限输出 $R(\rho)$ 都支撑在 $PH$ 上；每个不动态也如此。

2. $PH$ 对 $\Phi$ 不变，$\tau_0$ 在这个载体上忠实。

3. 原载体存在忠实不动态，当且仅当 $P=I$，亦当且仅当 $\tau_0>0$。

因此 $P$ 是全部不动态支撑的并，而不是预先任意选择的子空间。

**证明。**
由 $\Phi R=R$，有 $\Phi\tau_0=\tau_0$。
任意密度态满足 $0\le\rho\le I$，故正性给

$$
0\le R(\rho)\le R(I)=d\tau_0.
$$

所以全部极限输出都支撑在 $P$。
若 $\sigma$ 不动，则 $R(\sigma)=\sigma$，同一结论适用。
$\tau_0$ 自己是不动态且支撑为 $P$，从而取得全部不动支撑的并。

若 $\rho$ 支撑在 $P$，因为 $\tau_0|_{PH}>0$，存在有限 $c$ 使
$\rho\le c\tau_0$。于是
$\Phi(\rho)\le c\Phi(\tau_0)=c\tau_0$，证明不变性。
最后，若存在原载体上忠实的不动态 $\sigma$，其支撑必须包含于 $P$，
故 $P=I$；反向直接取 $\tau_0$。

**白话图景。**先给内部实际门，再让它反复作用，便能从中产生一份覆盖全部最终允许方向的参照。
最终方向是动力学留下来的，不能任意挑选。
但不同初态仍可能保留不同守恒资料，所以覆盖这些方向的参照，并不自动等于每条轨迹各自的终态。

<a id="section-11"></a>

## 11. 终端载体恢复 v94：普通代数、块重置与参照等价

<a id="sec-c95-terminal-algebra"></a>

令 $\Phi_P:B(PH)\to B(PH)$ 为压缩载体上的过程，
$R_P=\lim_n\Phi_P^n$，并定义

$$
\mathcal A_P=\operatorname{Fix}(\Phi_P^*).
$$

该空间含单位 $I_P=P|_{PH}$，不预先假定乘法闭合。

### 定理 11.1（终端代数与压缩读口）

<a id="thm-c95-terminal-algebra"></a>

有

<a id="eq-c95-compressed-fixed-readouts"></a>

$$
\boxed{\mathcal A_P=P\mathcal S_{\mathbb C}P.}
\tag{11.1}
$$

$\mathcal A_P$ 是通常矩阵乘法下的有限 $C^*$ 子代数，
而 $R_P$ 是 v94 对 $(PH,\mathcal A_P,\tau_0)$ 分类得到的唯一 C94 约化。
在适当共同坐标下，

$$
PH=\bigoplus_k(H_{L,k}\otimes H_{R,k}),
 \mathcal A_P=\bigoplus_k(B(H_{L,k})\otimes I_{R,k}),
$$

<a id="eq-c95-terminal-block-reset"></a>

$$
\tau_0=\bigoplus_k q_k\tau_{L,k}\otimes\eta_k,
 R_P(\rho)=\bigoplus_k\operatorname{Tr}_{R,k}(P_k\rho P_k)\otimes\eta_k.
\tag{11.2}
$$

其中 $q_k>0$，因子态均在相应载体上忠实。

**证明。**
$\Phi_P$ 是 CPTP，且固定忠实 $\tau_0|_{PH}$。
设 $a\in\mathcal A_P$。其 unital CP 对偶满足 Schwarz 不等式，故

$$
\Phi_P^*(a^\dagger a)-a^\dagger a\ge0.
$$

该正缺额的 $\tau_0$ 期望为零，忠实性迫使它为零。
对 $a^\dagger$ 同理；复极化使固定空间对普通乘法闭合。
这正是 v94 的平方缺额机制，得到普通代数 $\mathcal A_P$。

若 $s\in\mathcal S_{\mathbb C}$，对支撑在 $P$ 的输入使用 $\Phi$ 不变性，
得到 $\Phi_P^*(PsP)=PsP$，所以左侧包含 $P\mathcal S_{\mathbb C}P$。
反向，给 $a\in\mathcal A_P$，将其按零延拓到 $H$，记为 $\widehat a$。
令 $s=E_\infty(\widehat a)$。
则 $s\in\mathcal S_{\mathbb C}$，并且

$$
PsP=R_P^*(a)=a,
$$

因为 $a$ 对每一步 $\Phi_P^*$ 不动。这证明式 [(11.1)](#eq-c95-compressed-fixed-readouts)。

极限对偶 $R_P^*$ 的像恰为 $\mathcal A_P$。
因此 $R_P$ 保留这些读数，而且同这些读数的状态有同一输出。
它完全正、保迹并固定忠实 $\tau_0$，故满足 v94 的 C94。
对这套代数与忠实参照应用 v94 的分类，便得到式 [(11.2)](#eq-c95-terminal-block-reset)
以及过程的唯一性 [6](#ref-v94)。

这一证明也说明：在已经有忠实不动态时，固定代数的乘法闭合本身无需 C95。
C95 进一步排除持续旋转的外周模式，使条件期望成为实际幂极限，
而不只是在平均历史中出现。

### 推论 11.2（同一动力学的忠实不动参照具有同一规范整理）

<a id="cor-c95-stationary-reference-equivalence"></a>

设 $\tau,\kappa$ 都是 $\Phi$ 的不动态，并且在 $PH$ 上忠实。
则它们在 $PH$ 上定义的 v94 规范约化都等于 $R_P$，且

<a id="eq-c95-stationary-anchor-equivalence"></a>

$$
\boxed{\log\tau-\log\kappa\in\mathcal A_P,}
\tag{11.3}
$$

其中对数均在 $PH$ 上取。
若 $P=I$，这个结论直接作用于原载体；若 $P\ne I$，不能把奇异全空间对数写入该式。

**证明。**
不动态满足 $R_P(\tau)=\tau$，故块式迫使
$\tau=\bigoplus_k a_k\otimes\eta_k$；$\kappa$ 同理，且隐藏因子是同一组 $\eta_k$。
忠实性给每个 $a_k>0$。
两份参照都满足同一 $R_P$ 的 C94 条件，所以由唯一性得到同一约化。
取对数相减时 $I\otimes\log\eta_k$ 相消，剩余部分属于 $\mathcal A_P$。

对任意支撑在 $P$ 的输入 $\rho$ 与上述忠实参照 $\tau$，v94 的信息投影继续给

$$
D(\rho\Vert\tau)
 =D(\rho\Vert R_P\rho)+D(R_P\rho\Vert\tau).
$$

可见压缩 $C(\rho)=\bigoplus_k\operatorname{Tr}_{R,k}(P_k\rho P_k)$ 的 Petz 截面也正是
$b\mapsto\bigoplus_k b_k\otimes\eta_k$。
若原输入含 $P$ 外支撑，$D(\rho\Vert\tau)$ 为无穷；
上述有限相对熵分解须在明确压缩的任务中使用。

**白话图景。**最终允许的载体由动力学决定，在它内部就能恢复上一轮的完整量子可见代数。
同一动力学可以允许多份稳定参照，但它们的隐藏部分相同，给出同一台规范整理。
参照不是任意换；允许换的是与同一终端结构相容的那一族内部参照。

<a id="section-12"></a>

## 12. 瞬态关系如何延伸终端读数：完全正的调和边界

<a id="sec-c95-harmonic-boundary"></a>

当 $P\ne I$，原载体包含最终消失的瞬态方向。
这些方向的初始内容仍可能改变最终落入哪个可见区块，
所以不能先删掉它们再声称原全域问题已被解决。
原载体上的守恒读口，正是终端代数读数向瞬态区域的延伸。

### 定理 12.1（原守恒读口的调和延伸分类）

<a id="thm-c95-harmonic-extension"></a>

存在唯一 unital CP 映射
$\Psi:\mathcal A_P\to B(QH)$，使

<a id="eq-c95-harmonic-graph"></a>

$$
\boxed{\mathcal S_{\mathbb C}
 =\{J(a)=a\oplus\Psi(a):a\in\mathcal A_P\}.}
\tag{12.1}
$$

这里 $J(a)=E_\infty(\widehat a)$，压缩 $P J(a)P=a$。
当 $Q=0$ 时忽略空的第二块。
原读口对普通乘法闭合，当且仅当 $\Psi$ 保持乘法。
无论这个条件是否成立，均有

<a id="eq-c95-projected-product"></a>

$$
E_\infty(J(a)J(b))=J(ab).
\tag{12.2}
$$

因此若定义 $x\circ y:=E_\infty(xy)$，便得到与终端代数相同的乘积；
这个投影乘积是显式新定义，不能与原普通矩阵乘法混同。

**证明。**
所有 $R$ 输出均支撑在 $P$，故对任何 $B\in B(H)$，

$$
E_\infty(B)=E_\infty(PBP),\qquad E_\infty(P)=I.
$$

所以 $J$ 为 unital CP 映射，且前节已给 $P J(a)P=a$。

将 $J(a)$ 写成 $P\oplus Q$ 的块矩阵。
Schwarz 不等式 $J(a^\dagger a)\ge J(a)^\dagger J(a)$ 的 $P$ 压缩为

$$
a^\dagger a\ge a^\dagger a+(QJ(a)P)^\dagger(QJ(a)P),
$$

故 $QJ(a)P=0$。
对 $a^\dagger$ 重复同一论证，得到 $PJ(a)Q=0$。
于是 $J(a)=a\oplus\Psi(a)$，其中 $\Psi$ 作为 CP 映射的压缩，仍为 CP；
$J(I_P)=I$ 给 $\Psi(I_P)=I_Q$。

对任意 $s\in\operatorname{ran} E_\infty=\mathcal S_{\mathbb C}$，
有 $s=E_\infty(s)=E_\infty(PsP)=J(PsP)$。
反向 $J(a)$ 显然在该像中，故得到图形式及唯一性。

乘积 $J(a)J(b)=ab\oplus\Psi(a)\Psi(b)$。
若它仍在图内，其 $P$ 压缩迫使它等于 $J(ab)$，
这恰好要求 $\Psi(a)\Psi(b)=\Psi(ab)$；反向也直接成立。
最后，$E_\infty$ 忽略其输入的 $Q$ 块，所以
$E_\infty(J(a)J(b))=E_\infty(\widehat{ab})=J(ab)$。

### 命题 12.2（瞬态 Dirichlet 公式）

<a id="prop-c95-dirichlet"></a>

定义从瞬态输入出发的两个压缩过程

$$
\begin{aligned}
 T &:B(QH)\longrightarrow B(QH),&T(X)&=Q\Phi(QXQ)Q,\\
 B &:B(QH)\longrightarrow B(PH),&B(X)&=P\Phi(QXQ)P.
 \end{aligned}
$$

则 $T^n\to0$，且对任意 $a\in\mathcal A_P$，

<a id="eq-c95-dirichlet-series"></a>

$$
\boxed{\Psi(a)=B^*(a)+T^*\Psi(a)
 =\sum_{n=0}^{\infty}(T^*)^n B^*(a).}
\tag{12.3}
$$

级数在有限维算符范数下收敛。

**证明。**
$PH$ 不变，故 $\Phi$ 的任一 Kraus 表示中都有 $QK_jP=0$：
对 $v\in PH$，$\sum_j\left\lVert QK_jv\right\rVert^2=0$。
各 Kraus 算符因此是 $P\oplus Q$ 分块上三角矩阵。
于是即使输入有跨块相干项，其 $Q$ 输出仍只由 $Q$ 输入决定：

$$
Q\Phi(\rho)Q=T(Q\rho Q),\qquad
 Q\Phi^n(\rho)Q=T^n(Q\rho Q).
$$

实际极限 $R$ 全部输出在 $P$，所以 $T^n\to0$。
有限维中这给 $T$ 的谱半径严格小于一，故 Neumann 级数收敛。

因为 $J(a)$ 是单步对偶 $E$ 的固定元，
把 $E(J(a))=J(a)$ 压到 $Q$ 得
$\Psi(a)=B^*(a)+T^*\Psi(a)$。
迭代该等式，余项为 $(T^*)^{N+1}\Psi(a)$，随 $N\to\infty$ 消失，得到级数。
对单位，$B^*(I_P)=I_Q-T^*(I_Q)$，级数望远镜相消为 $I_Q$，
与调和延伸的归一性一致。

这条公式将终端读出写成全部可能瞬态停留步数的贡献。
它是算符关系的解析恒等式，没有要求运行枚举或把级数当成免费可取得的实验装置。

**白话图景。**最终边界上的一个问题，会反过来给每个瞬态内容指定一个守恒回答。
这个回答是内部过程将来怎样把内容送到边界的总结果。
先在瞬态中走几步、再进入终端区块，各种路径的贡献共同形成调和延伸。
终端问题本身能相乘；它们延伸到原空间以后，普通乘积是否仍守恒，还要另行检查。

### 12.1 一个一轮到达、却在原空间不成代数的三维实例

取 v94 已用过的 CPTP 投影，并把它作为实际单步 $\Phi$：

$$
\Phi(\rho)=\operatorname{diag}\left(
 \rho_{11}+\frac{\rho_{33}}2,
 \rho_{22}+\frac{\rho_{33}}2,0\right).
$$

Kraus 算符为
$P_1,P_2,\lvert 1\rangle\langle 3\rvert/\sqrt2,\lvert 2\rangle\langle 3\rvert/\sqrt2$。
它满足 $\Phi^2=\Phi$，所以同资料二态一轮便融合，C95 成立。
有

$$
\tau_0=\operatorname{diag}(1/2,1/2,0),\qquad P=P_1+P_2,
$$

终端代数为 $\mathcal A_P=\{\operatorname{diag}(a,b):a,b\in\mathbb C\}$，而

$$
J(a,b)=\operatorname{diag}\left(a,b,\frac{a+b}{2}\right),
 \qquad\Psi(a,b)=\frac{a+b}{2}.
$$

取 $a=1,b=-1$，其延伸 $D=\operatorname{diag}(1,-1,0)$ 守恒，但

$$
D^2=\operatorname{diag}(1,1,0)\notin\mathcal S_{\mathbb C},\qquad
 E_\infty(D^2)=I=J(1,1).
$$

所以原守恒空间只是终端代数的完全正调和延伸，普通乘法闭合确实可能失败。
这个例子并不要求舍弃原三维输入：第三方向的初始质量，会被平均送到两个终端区块。

### 12.2 每个守恒资料纤维一个终态，何时才有全域唯一终态

由 C95 的主定理，对初态 $\rho$ 定义
$\omega_\rho=R(\rho)$，则

$$
\omega_\rho=\omega_\sigma
 \quad\Longleftrightarrow\quad
 \rho\sim_{\mathcal S}\sigma.
$$

特别地，

<a id="eq-c95-unique-global-terminal"></a>

$$
\boxed{\text{全部输入具有同一终态 }\omega
 \quad\Longleftrightarrow\quad
 \mathcal S_{\mathbb C}=\mathbb C I.}
\tag{12.4}
$$

若右侧成立，全部密度态同资料，故极限相同。
反向，若 $R(\rho)=\omega$ 对全部密度态成立，则
$E_\infty(B)=\operatorname{Tr}(\omega B)I$，其像只为 $\mathbb C I$。
因此只有不存在非平凡守恒读数时，才有单一全域终态。

**白话图景。**手性给出的实际过程可以限制最终允许的状态，但最终态还受初始守恒资料约束。
有守恒区别，就可能有一族终态；所有守恒区别都退到归一常数时，才出现一个共同终点。
这个终点是指定内部动力学的结果，不能仅凭一个方向标签任意指定。

<a id="section-13"></a>

## 13. 由两个内部跃迁率锁定终态：有向量子位的解析模型

<a id="sec-c95-chiral-qubit"></a>

本节把“手性”具体化为绕指定轴的旋向标签 $\chi\in\{+1,-1\}$。
这只是本模型明确给出的有向控制含义，不把一个旋向标签直接等同于所有物理手性。
基态记为 $\lvert 0\rangle,\lvert 1\rangle$，令 $Z=P_0-P_1$。
给定两个内部跃迁率 $a,b\ge0$，且 $\gamma=a+b>0$，以及实数 $\nu\in\mathbb R$，并定义

$$
p=\frac b\gamma,\qquad s=2p-1=\frac{b-a}{a+b},\qquad
 \kappa_h=e^{-\gamma h},\qquad
 U_{\chi,h}=e^{-i\chi\nu h Z/2},\quad h\ge0.
$$

$h$ 是本模型的门参数；其物理时间单位仍须内部时钟校准。
本节沿用 $D_{\rm tr}(\rho,\sigma)=\tfrac12\left\lVert \rho-\sigma\right\rVert_1$ 记迹距离，
与前节的相对熵 $D(\rho\Vert\sigma)$ 区分。

### 定义 13.1（双跃迁与有向旋转过程）

先定义四个 Kraus 算符

$$
\begin{aligned}
K_0&=\sqrt p\begin{pmatrix}1&0\\0&\sqrt{\kappa_h}\end{pmatrix},
 &K_1&=\sqrt{p(1-\kappa_h)}\lvert 0\rangle\langle 1\rvert,\\
 K_2&=\sqrt{1-p}\begin{pmatrix}\sqrt{\kappa_h}&0\\0&1\end{pmatrix},
 &K_3&=\sqrt{(1-p)(1-\kappa_h)}\lvert 1\rangle\langle 0\rvert.
\end{aligned}
$$

令

$$
\Phi_{\chi,h}(\rho)
 =U_{\chi,h}\left(\sum_{j=0}^3K_j\rho K_j^\dagger\right)U_{\chi,h}^\dagger.
$$

端点 $p=0$ 或 $p=1$ 时，零 Kraus 项直接删去。

### 定理 13.2（旋向、收缩与最终态分别由不同关系决定）

<a id="thm-c95-chiral-qubit"></a>

上述映射为 CPTP。
若 $\rho=(I+xX+yY+zZ)/2$，则其 Bloch 作用为

<a id="eq-c95-qubit"></a>

$$
\boxed{
 \binom{x'}{y'}=\sqrt{\kappa_h}\,
 R_{\chi\nu h}\binom{x}{y},\qquad
 z'=\kappa_h z+(1-\kappa_h)s,}
\tag{13.1}
$$

其中 $R_\theta$ 是平面旋转。
当 $h>0$ 时，它满足 C95，且全部输入具有同一终态

<a id="eq-c95-balance"></a>

$$
\boxed{\omega_{a,b}
 =\begin{pmatrix}b/(a+b)&0\\0&a/(a+b)\end{pmatrix},
 \qquad a(\omega_{a,b})_{00}=b(\omega_{a,b})_{11}.}
\tag{13.2}
$$

旋向 $\chi$ 与频率 $\nu$ 不改变这个终态。

**证明。**
$K_0^\dagger K_0+K_1^\dagger K_1=pI$，
$K_2^\dagger K_2+K_3^\dagger K_3=(1-p)I$，故 Kraus 和保迹且完全正。
直接展开一份二阶矩阵：非对角元变成
$\sqrt{\kappa_h}e^{-i\chi\nu h}\rho_{01}$，而

$$
\rho'_{00}=\kappa_h\rho_{00}+(1-\kappa_h)p.
$$

这给式 [(13.1)](#eq-c95-qubit)。

重复同一门 $n$ 次，得到

$$
\begin{aligned}
\binom{x_n}{y_n}&=\kappa_h^{n/2}
 R_{n\chi\nu h}\binom{x_0}{y_0},\\
 z_n&=s+\kappa_h^n(z_0-s).
\end{aligned}
$$

由于 $0<\kappa_h<1$，它们收敛到 $(0,0,s)$。
对两输入的 Bloch 差 $\delta r$，

$$
|\delta r'|^2
 =\kappa_h(\delta x^2+\delta y^2)+\kappa_h^2\delta z^2
 \le\kappa_h|\delta r|^2.
$$

qubit 迹距离为 Bloch 欧氏距离的一半，故

<a id="eq-c95-qubit-contraction"></a>

$$
D_{\rm tr}(\Phi_{\chi,h}\rho,\Phi_{\chi,h}\sigma)
 \le e^{-\gamma h/2}D_{\rm tr}(\rho,\sigma).
\tag{13.3}
$$

全部不同二态都严格收缩，尤其满足 C95。

固定人口 $p_0$ 满足 $p_0=p$，即
$a p_0=b(1-p_0)$，归一性给式 [(13.2)](#eq-c95-balance)。
非对角元因严格衰减而只能为零，所以固定态唯一。

人口关系也给两个参数的跃迁含义：对小 $h$，

$$
\rho'_{00}-\rho_{00}
 =h\bigl(b\rho_{11}-a\rho_{00}\bigr)+o(h).
$$

$a$ 控制 $0\to1$，$b$ 控制 $1\to0$。
终态由两个内部通量平衡与归一共同确定，未先把任意目标态塞入终态定义。
跃迁率的具体数值仍须由所声明的内部装置与相互作用给出；
本模型说明它们怎样锁定终态，没有从旋向标签独自推导这两个数值。
公式还给 $\Phi_{\chi,h}\Phi_{\chi,k}=\Phi_{\chi,h+k}$。
若用实际时钟解释 $h$，其生成元具有 Hamiltonian
$H_\chi=(\hbar\chi\nu/2)Z$ 与两跃迁算符
$\sqrt a\lvert 1\rangle\langle 0\rvert$、$\sqrt b\lvert 0\rangle\langle 1\rvert$。
这里时间校准与过程供应仍沿用前稿的实际接口 [5](#ref-v80)、[3](#ref-v74)。

**白话图景。**旋向决定绕哪边转，跃迁总率决定区别怎样缩小，两方向的比例决定最后停在哪里。
最终态确实不能随意选：一旦内部跃迁关系给定，它就被平衡式锁定。
但只有旋向还不够，因为旋向、收缩和终点位置分别由不同关系控制。

### 13.1 同一旋向可以有不同终点，反向旋转也可以有同一终点

固定 $\chi$ 与 $\nu$，改变 $a/b$ 就改变 $\omega_{a,b}$。
例如 $a=b>0$ 给 $I/2$，而 $a=0,b>0$ 给 $P_0$。
因此“同一手性”不唯一决定终点。
反过来，固定 $a,b$ 并改变 $\chi$ 的符号，两条旋转方向相反的局部轨迹
仍趋于同一 $\omega_{a,b}$。

当 $a,b>0$，终态忠实，终端载体为整个 qubit。
当只有一个跃迁率非零，终态纯，终端载体降为一维。
这说明纯终点与混合终点都可以在同一框架中产生，
其差别由实际跃迁关系决定，而非由“最终”这个词预设。

对有限 $h>0$，$\kappa_h>0$，Bloch 映射具有代数上的仿射逆。
因此 $\Phi_{\chi,h}^n(\rho)=\omega_{a,b}$ 在有限 $n$ 成立，当且仅当
$\rho=\omega_{a,b}$。
一般输入只是在极限到达终态，并不存在有限门序列里的最后一门。
在忽略内部记录的局部 Bloch 球中，横向分量旋转并衰减，纵向分量趋向平衡值；
这些轨迹一般进入球内部，不是始终停留在纯态球面上的圆或椭圆。

### 13.2 逆旋向仍是合法门，但它不是原耗散门的逆

把 $\chi$ 改为 $-\chi$，仍得到 CPTP 过程。
连续作用两个相反旋向的门时，旋转抵消，但

$$
(x,y)\longmapsto\kappa_h(x,y),\qquad
 z\longmapsto\kappa_h^2z+(1-\kappa_h^2)s.
$$

区别继续衰减，没有返回原输入。

若硬取原仿射映射的代数逆，则

<a id="eq-c95-inverse-bloch"></a>

$$
\binom{x}{y}_{\!\rm inv}
 =\kappa_h^{-1/2}R_{-\chi\nu h}\binom{x}{y},\qquad
 z_{\rm inv}=s+\kappa_h^{-1}(z-s).
\tag{13.4}
$$

当 $|s|<1$，输入合法纯态坐标
$r=(\sqrt{1-s^2},0,s)$ 后，候选逆输出的长度平方为

$$
|r_{\rm inv}|^2
 =\kappa_h^{-1}(1-s^2)+s^2>1.
$$

当 $|s|=1$，选相反极点 $z=-s$，则
$z_{\rm inv}=s(1-2\kappa_h^{-1})$，绝对值同样大于一。
这给精确的三维球外证书；候选逆输出的两个本征值
$(1\pm|r_{\rm inv}|)/2$ 中有一个为负。
代数逆因而不是全域正过程。

**白话图景。**把转向反过来，只能撤销旋转，不能凭空找回已经转入记录的区别。
若要求局部逆门把这些区别放大回来，它就会把某些合法球内状态推到球外，出现负概率。
这准确区分了“反手性门仍可操作”与“整个局部过程可以物理逆转”。

<a id="section-14"></a>

## 14. 保留完整内部记录时，局部吸引子不成为整体内容的融合

<a id="sec-c95-internal-history"></a>

### 定理 14.1（每段历史的内部记录等距）

<a id="thm-c95-record"></a>

给定 CPTP 门 $\Phi(\rho)=\sum_jK_j\rho K_j^\dagger$，定义

$$
V\psi=\sum_jK_j\psi\otimes\lvert j\rangle.
$$

则 $V^\dagger V=I$，且偏迹得到 $\Phi$。
对连续 $n$ 次门，保留每次新的内部记录，得到等距 $W_n$，满足

$$
\operatorname{Tr}_{{\rm rec},1\ldots n}(W_n\rho W_n^\dagger)=\Phi^n(\rho),
 \qquad
 D_{\rm tr}(W_n\rho W_n^\dagger,W_n\sigma W_n^\dagger)
 =D_{\rm tr}(\rho,\sigma).
$$

因此局部二态收缩不意味着完整记录输出也融合。

**证明。**
$V^\dagger V=\sum_jK_j^\dagger K_j=I$。
对记录偏迹只保留相同标签项，给出 Kraus 和。
逐步把 $V$ 作用在系统因子、把旧记录保留，复合仍为等距，因而得到 $W_n$。
对 Hermitian $X=\rho-\sigma$，$W_nXW_n^\dagger$ 的非零本征值与 $X$ 相同，
仅在正交余空间补零；所以迹范数不变，得到距离等式。

所有记录可以在模型中作为 $\Omega$ 的内部对象，完整历史长度随门序列增加。
但数学等距表示不自动供应每一步所需的记录初态、控制和准备资源。
一旦后续允许重新读取这些记录，读口及守恒关系必须相应扩大，
不能继续把仅对局部系统成立的共同终态宣称为整个 $\Omega$ 的全信息终态
 [5](#ref-v80)、[6](#ref-v94)。

**白话图景。**局部系统可以越来越接近同一个终点，完整记录却仍保存输入之间原有的区别。
把记录也放进整体，内容没有因局部稳定而消失。
因此“观察者的最终态”必须同时说明观察者读哪些关系、保存哪些记录，以及哪些记录以后还会被重新打开。

<a id="section-15"></a>

## 15. 门序列条件：每扇门有终态，仍不保证整条历史有终态

<a id="sec-c95-switching"></a>

C95 的主定理消费同一个实际过程 $\Phi$ 的反复作用。
若允许每一步改变门，需要新的历史条件；逐门有吸引子不足以替代它。

### 命题 15.1（交替重置的二态反例）

令 $T_0(X)=\operatorname{Tr}(X)P_0$、$T_1(X)=\operatorname{Tr}(X)P_1$。
每扇门都是 CPTP，并在一轮内使全部输入到达唯一终态。
但交替序列 $T_0,T_1,T_0,T_1,\ldots$ 对任意初态产生

$$
P_0,P_1,P_0,P_1,\ldots,
$$

故没有逐步极限。

**证明。**
重置映射为 CPTP，且 $T_i^2=T_i$。
每步的输出由该步标签独自决定，因而直接得到交替序列。
两个子序列分别恒为 $P_0,P_1$，它们的迹距离为一，不能具有同一极限。

这里任意两份不同初态在第一步以后已经无法区分，但共同输出仍在移动。
因此对一般时变历史，二态间距离消失也不独自保证单条轨迹收敛；
还要控制移动的目标或把门选择规律纳入同一个内部动力学。

### 命题 15.2（固定周期只先给周期采样的极限）

给定周期为 $m$ 的 CPTP 门序列 $\Phi_1,\ldots,\Phi_m$，
记整周期过程 $\Gamma=\Phi_m\cdots\Phi_1$。
若 $\Gamma$ 满足 C95，令其幂极限为 $R_\Gamma$，则对 $0\le j<m$，

$$
\rho_{nm+j}\longrightarrow
 \omega_j(\rho)
 :=\Phi_j\cdots\Phi_1R_\Gamma(\rho),
$$

其中 $j=0$ 时前面的复合取恒等。
整条逐步历史收敛，当且仅当这些相位极限全部相同。

**证明。**
周期性给 $\rho_{nm+j}=\Phi_j\cdots\Phi_1\Gamma^n(\rho)$。
有限维线性映射连续，代入 $\Gamma^n\rho\to R_\Gamma\rho$ 即得各子序列极限。
有限多个子序列拼合的序列收敛，当且仅当其极限相同。

可以通过共同终态补足任意切换的条件。
例如，若所有实际门都固定同一 $\omega$，并且每个连续 $N$ 步块
都对全部输入将到 $\omega$ 的迹距离缩小至少同一个因子 $0<q<1$，
则逐块迭代及余下单步的距离不增给
$D_{\rm tr}(\rho_n,\omega)\le q^{\lfloor n/N\rfloor}D_{\rm tr}(\rho_0,\omega)$。
这个条件包含共同目标与统一收缩；交替重置例恰好缺少共同目标。

**白话图景。**一扇门把内容送到一个终点，另一扇门可以把它送到另一个终点。
即使每扇门都完全稳定，交替使用也可能永远来回。
若门序列有固定周期，先得到的是每逢同一周期相位所看见的稳定结果。
要谈整条历史同一个最终态，还必须让这些相位结果一致，或给出共同目标与统一收缩关系。

<a id="section-16"></a>

## 16. 实际极限、时间平均与单位圆上的残留运动

<a id="sec-c95-peripheral"></a>

上一节用二态比较和平方缺额描述是否到达最终代表。
本节给出同一问题的有限谱表示；这也把“绕圆的周期”与“趋向终点”明确区分。
谱判据属于量子通道混合理论的既有结果 [8](#ref-bcgpy2013)，以下给本轮所用形式的证明。

### 定理 16.1（不要求忠实稳态的外围谱判据）

<a id="thm-c95-peripheral"></a>

对任意有限维 CPTP 映射 $\Phi$，单位圆上的特征值均无非平凡 Jordan 块，且

<a id="eq-c95-peripheral"></a>

$$
\boxed{\quad
 \text{C95}
 \quad\Longleftrightarrow\quad
 \Phi^n\text{ 实际收敛}
 \quad\Longleftrightarrow\quad
 \operatorname{spec}(\Phi)\cap\{\lambda:|\lambda|=1\}=\{1\}.
 \quad}
\tag{16.1}
$$

此处 $1$ 的特征空间允许多维。
无论 C95 是否成立，Cesàro 平均

$$
\overline\Phi_n=\frac1n\sum_{k=0}^{n-1}\Phi^k
$$

均收敛到一个 CPTP 投影 $\overline R$，其像为 $\operatorname{Fix}\Phi$。
若 C95 成立，$\overline R=R$；否则平均极限不能替代实际极限。

**证明。**
对任意复矩阵 $A=X+iY$，其中 $X,Y$ 自伴，迹范数收缩给

$$
\left\lVert \Phi^n(A)\right\rVert_1
 \le\left\lVert X\right\rVert_1+\left\lVert Y\right\rVert_1\le2\left\lVert A\right\rVert_1.
$$

所以线性算符族 $\Phi^n$ 一致有界。
保迹又给 $\Phi^*(I)=I$，故 $1$ 确实属于 $\Phi$ 的谱。
模大于一的特征值将使幂指数增长；单位圆上的非平凡 Jordan 块将使幂至少多项式增长。
二者都不可能。

所有模小于一的 Jordan 块，其幂均趋于零：固定次数的多项式因子被严格指数衰减压过。
单位圆部分已经半单，在 $\lambda$ 本征方向上的作用为 $\lambda^n$。
这段序列收敛，当且仅当 $\lambda=1$。
因此实际幂收敛恰好等价于所述外围谱条件，再用定理 [5.1](#thm-c95-equivalence) 得 C95。

对于平均，$\lambda=1$ 的方向保留；其余单位圆方向满足

$$
\frac1n\sum_{k=0}^{n-1}\lambda^k
 =\frac{1-\lambda^n}{n(1-\lambda)}\longrightarrow0.
$$

严格圆内的 Jordan 块平均也趋于零。
由此得到到 $\operatorname{Fix}\Phi$ 的线性投影。
平均本身是 CPTP，有限维极限仍 CPTP，所以得到 $\overline R$。
若实际幂已经收敛，平均具有同一极限。

若还存在忠实稳态，定理 [8.1](#thm-c95-reversible) 中的 $E|_{\mathcal N}$
在加权内积下是满射等距，因而可以用单位圆本征向量张成。
反向，任何 $E(a)=\lambda a$、$|\lambda|=1$ 的方向都沿各步保持加权范数，必属于 $\mathcal N$。
故 $\mathcal N$ 正是全部无衰减相位方向的线性张成。
C95 允许 $\lambda=1$ 的守恒方向，排除 $\lambda\ne1$ 的持续转动方向。
这并不要求不动空间只有一维。

**白话图景。**圆上的点每一步只改变角度，长度不减，所以可以一直绕下去。
把许多时刻平均，旋转部分可以彼此抵消，但每一时刻的点并没有因此停下来。
真正的最终态要求所有不会缩小的运动都已经静止；允许留下的是守恒资料本身。
若还保留一个只转角度、不减大小的关系，平均可以稳定，实际轨迹仍不会到终点。

### 16.1 为什么只要求有限延伸，不要求每一门都严格衰减

令 $U_H=(X+Z)/\sqrt2$ 为 Hadamard 酉，取

$$
\Phi(\rho)=\Delta_Z(U_H\rho U_H^\dagger).
$$

其 Bloch 作用为

$$
(x,y,z)\longmapsto(0,0,x)\longmapsto(0,0,0).
$$

因此 $\Phi^2(\rho)=I/2$ 对全部密度态成立，C95 成立。
但 $X$ 方向的两个正交纯态第一步变为 $Z$ 方向的两个正交纯态，
迹距离第一步仍为一，第二步才成为零。
对偶上则有

$$
E(Z)=X,\qquad E^2(Z)=0,\qquad
 Q_1(Z)=0,\qquad Q_2(Z)=I.
$$

所以把候选加强为“每个非固定关系在单步必须出现正平方缺额”，会排除合法的有限步稳定过程。
本轮要求的共同窗口 $N$ 由紧致性得到；平方层级的 $d^2$ 上界属于另一个论证，
不能未经证明就把它认成同一个迹距离收缩窗口或精确混合时间。

**白话图景。**一扇门可以先把区别搬到另一个方向，下一扇相同的观察更新才把它送进记录。
第一步没有减少区别，不表示区别会永远保留。
这就是候选只要求某个有限正向延伸发生衰减，而不把每一步都严格收缩写成额外条件的原因。

<a id="section-17"></a>

## 17. 参照可以换坐标，实际终点不能任意换

<a id="sec-c95-anchor-covariance"></a>

### 命题 17.1（终态结构的共同酉协变）

<a id="prop-c95-covariance"></a>

给定酉 $W$，同时变换输入、读口与过程：

$$
\rho'=W\rho W^\dagger,
 \qquad
 \Phi'=\operatorname{Ad}_W\circ\Phi\circ\operatorname{Ad}_{W^\dagger}.
$$

则 C95 的真假不变。若成立，

<a id="eq-c95-covariance"></a>

$$
R'=\operatorname{Ad}_W\circ R\circ\operatorname{Ad}_{W^\dagger},
 \qquad
 \Omega'_{\rho'}=W\Omega_\rho W^\dagger,
 \qquad P'=WPW^\dagger.
\tag{17.1}
$$

**证明。**
$E'$ 的固定读口为 $W\mathcal SW^\dagger$，所以同资料关系随同共轭保持。
正交支撑及输出重叠的迹也在共同酉共轭下保持，故 C95 不变。
由 $(\Phi')^n=\operatorname{Ad}_W\Phi^n\operatorname{Ad}_{W^\dagger}$ 取极限得到 $R'$。
又因 $W(I/d)W^\dagger=I/d$，内生参照及其支撑按同一方式变换。

因此“选哪个坐标参照”与“固定过程实际走到哪个状态”是两种不同操作。
共同换坐标不会改变轨迹是否收敛、二态距离或终态的谱。
若保持 $\Phi$ 不动而把终点改成任意 $\omega'$，它至少必须满足
$\Phi(\omega')=\omega'$；对给定初态还必须保留同一份守恒资料。
在 C95 下这两项条件已把终点唯一锁定为 $R\rho$。

这也不把坐标协变直接认成物理各向同性。
各向同性还要求某类实际旋转在保持装置、控制和准备条件的比较中成为对称；
本轮模型中的指定轴及跃迁率可以打破这种对称，而坐标协变仍成立。

**白话图景。**画图时可以换一个方向看，所有状态、门和读数一起换坐标，结论不会变。
但保持同一台实际门不动，不能把任何一点改称它的终点。
终点必须在这台门下不再变化，并保留这条历史原有的守恒资料；本轮定理证明这会选出唯一答案。

### 17.1 反向删条件：实际失败发生在哪里

| 删去或混淆的条件 | 二态或关系见证 | 直接后果 |
|---|---|---|
| 有向性代替 C95 | 非平凡酉旋转保持两态距离 | 有旋向，仍可永久绕行 |
| 唯一不动态代替收敛 | 两个 $Z$ 极点在翻转通道中交换 | 平均稳定，实际序列不收敛 |
| 忽略守恒资料 | 去相干过程保留两个 $Z$ 极点 | 每纤维有终点，仍无全域单一终点 |
| 任意更换每一步门 | 两个一轮重置交替使用 | 初态差异消失，共同输出仍来回移动 |
| 把原载体忠实性省掉 | 三维例中的 $D$ 守恒而 $D^2$ 不守恒 | 原读口不是普通乘法代数，须保留调和延伸 |
| 把局部过程当完整记录过程 | $W_n$ 对两个不同输入保持原迹距离 | 局部终态不等于整体内容融合 |
| 把反旋向当成耗散逆过程 | 式 [(13.4)](#eq-c95-inverse-bloch) 的纯态输入 | 候选逆输出越过 Bloch 球，出现负本征值 |

这些见证说明各前件承担的工作，不说明所有自然过程都必须满足 C95。
特别是封闭酉演化通常有保持信息的运动；
它不满足吸引终态条件，仍完全属于标准量子理论。

<a id="section-18"></a>

## 18. 怎样接到现有量子力学公理：本轮所在的完整依赖链

<a id="sec-c95-reconstruction"></a>

本轮完成的是“实际有向过程何时选出最终代表”这一环。
它继承 V80 已给出的共同复比较与实际过程接口，
以及 v94 的规范约化定理 [5](#ref-v80)、[6](#ref-v94)。
下面把整个有限理论的推导关系放在一起；前件不会因写进定义而消失。

### 18.1 共同比较、状态与平方读出

给定内部关系标签上的共同复核 $K(x,y)$，要求所有有限 Gram 矩阵正半定。
在有限形式和上定义

$$
\left\langle\sum_xc_xe_x,\sum_yd_ye_y\right\rangle
 =\sum_{x,y}\overline{c_x}d_yK(x,y).
$$

正半定形式的零范数向量与全部向量正交，商去它们即得内积空间。
有限秩时得到有限复 Hilbert 空间；一般情形还须完备化及相应分析条件。
*共同复比较及全有限正性是这条表示的前件。*
分别给每个二元三维窗口一份合法报告，并不足以保证它们能粘成同一个全局正核。

在这个共同矩阵接口上，沿用整个正锥上的非负响应：
对任意 $A,B\ge0$ 有 $f(A+B)=f(A)+f(B)$，并有 $f(I)=1$。
加法先给非负有理齐次，正性又给序单调；
以有理数从两侧夹逼任意非负实数，得到非负实齐次。
于是 $f(A-B)=f(A)-f(B)$ 唯一延拓到自伴空间：
若 $A-B=C-D$，则 $A+D=C+B$，可加性保证结果相同。
再复线性延拓，有限维迹配对给唯一形式
$f(A)=\operatorname{Tr}(\rho A)$。
对每个秩一投影的正性迫使 $\rho\ge0$，$f(I)=1$ 给 $\operatorname{Tr}\rho=1$。
这里可加性覆盖整个共同正锥，不能仅用某一次测量菜单中的可加性替代。
反向每个这样的 $\rho$ 都给合法泛函。
对混合仿射且取值在 $[0,1]$ 的二元事件，类似地得到
$p_F(\rho)=\operatorname{Tr}(\rho F)$、$0\le F\le I$。
穷尽互斥菜单给 $\sum_eF_e=I$。
由同根相干标定把某个锐方向识别为 $F=P_\phi$，便有

$$
p(P_\phi\mid P_\psi)=\operatorname{Tr}(P_\psi P_\phi)
 =|\langle\phi,\psi\rangle|^2.
$$

这里平方律来自共同复内积、正读出及标定的连接。
本轮的平方缺额是在这套平方结构中进一步识别无损关系，
没有用“递归停止”替代这些实际前件。

**白话图景。**关系先要能在同一把尺上比较，而且所有有限比较放在一起都不能出现负强度。
去掉完全不可分辨的零方向，才得到 Hilbert 表示。
再要求同一个二元问题在所有状态上给合法概率，概率就成为一个正效果的读数。
当问题是某个相干方向时，读数就是重叠的模平方。

### 18.2 完整门、局部过程与测量后态

V80 的完整强度条件、定向参考及全输入差分约束，迫使实际完整输出为复线性等距。
保留所有结果和记录时写为 $V^\dagger V=I$；
只读取系统就得到

$$
\Phi(\rho)=\operatorname{Tr}_{\rm rec}(V\rho V^\dagger)
 =\sum_jK_j\rho K_j^\dagger,
 \qquad\sum_jK_j^\dagger K_j=I.
$$

附加任意共同参考后各项仍为正算符的共轭，故完全正性随之出现。
选择一组已记录结果得到 CP 分支 $\mathcal I_e$，其概率为
$\operatorname{Tr}\mathcal I_e(\rho)$；概率非零时的条件态是
$\mathcal I_e(\rho)/\operatorname{Tr}\mathcal I_e(\rho)$。
数学表示不自动供应任意所需记录、控制或装置资源。

同维单结果完整等距是酉门。
对满足 $U(0)=I$ 的实际 $C^1$ 酉历史，令 $\psi(t)=U(t)\psi(0)$，定义
$H(t)=i\hbar\dot U(t)U(t)^\dagger$，微分 $UU^\dagger=I$ 得 $H=H^\dagger$，于是

$$
i\hbar\dot\psi(t)=H(t)\psi(t).
$$

自治群条件才使 $H$ 可取常量；门参数还需内部时钟与单位校准。
因此“一个量子门”一般不是唯一的一根切向量，
实际连续门族及当前状态给出的是 $\dot\psi=-iH\psi/\hbar$ 的状态相关切向。

独立复合的积核
$K_{AB}=K_AK_B$ 及产品张成给出 $H_A\otimes H_B$。
这是一项明确的独立关系条件，不从“两个对象都在整体内”自动得到。
对具有投影效果 $P$ 的 CP 结果分支，再要求对 $PH$ 中全部纯态不扰动，
才给理想 Lüders 分支 $P\rho P$。
若 $P=0$，全部 Kraus 算符均为零，结论直接成立。
若 $P\ne0$，Kraus 条件先迫使 $K_j(I-P)=0$，
逐纯态不扰动及叠加又迫使 $K_jP=c_jP$，归一给 $\sum_j|c_j|^2=1$。
仅有结果可重复，还允许结果子空间内部的附加运动。

**白话图景。**保留整体完整关系时，门以等距方式接续历史；在同一个有限载体上就是酉门。
只看一部分记录时，局部出现完全正过程；读取一个具体结果，才得到相应条件后态。
平滑的酉门族给薛定谔形式，独立关系的乘法组合给张量积。
这些都能放进同一内部关系模型，但每一环各自需要的相容条件仍须明确。

### 18.3 本轮补齐：从物理过程到内生终端代数

在上述过程接口中，C95 把守恒读口、实际极限与终态锁为

<a id="eq-c95-reconstruction-closure"></a>

$$
\boxed{
 \begin{gathered}
 \mathcal S=\operatorname{Fix}(\Phi^*)_{\rm sa},\qquad
 R=\lim_n\Phi^n,\qquad \Omega_\rho=R\rho,\\
 \Omega_\rho=\Omega_\sigma
 \ \Longleftrightarrow\ \rho\sim_{\mathcal S}\sigma,\qquad
 \tau_0=R(I/d),\quad P=\operatorname{supp}\tau_0.
 \end{gathered}}
\tag{18.1}
$$

终端支撑上的普通代数 $\mathcal A_P$、块重置 $R_P$、
原空间守恒关系的调和延伸 $J$ 随后由定理推出。
这使 v94 的一份静态规范整理，成为指定正向过程的真正渐近实现。
如果没有 C95，同样的固定资料仍可经 Cesàro 平均出现，
但实际状态可能持续携带不衰减的旋转。

| 标准结构或新结论 | 实际消费的关系条件 | v95 的准确位置 |
|---|---|---|
| 复 Hilbert 空间 | 共同复核、所有有限 Gram 正性、零关系商 | 继承表示前件；未从手性独自推出复数 |
| 密度态、效果、Born 概率 | 全效果正归一响应、混合相容、同根相干标定 | 继承有限状态与概率接口 |
| 酉门与一般 CPTP 过程 | 完整实际等距、明确保留或忽略的记录 | C95 作用的过程载体 |
| 张量积与测量后态 | 独立积核；结果记录及理想不扰动条件 | 沿用分别声明的组合与仪器条件 |
| 薛定谔动力学 | 实际光滑酉族、内部时钟与单位校准 | 与局部吸引过程并存 |
| 守恒资料纤维 | $E(s)=s$ 由实际 $\Phi$ 定义 | 本轮由动力学确定读口 |
| 实际最终代表 | C95 的同资料正交二态有限重叠 | 推出 $R=\lim\Phi^n$ 及统一收敛界 |
| 终端量子代数 | 最大固定支撑上的忠实态、Schwarz 缺额 | 恢复 v94 普通代数与规范重置 |
| 瞬态与终端的关系 | 原过程的完全正调和延伸 | 保留全部原始输入的影响 |
| 全域单一 $\Omega$ | C95 再加 $\mathcal S=\mathbb R I$ | 充要条件，非任意选点 |

<a id="section-19"></a>

## 19. 本轮候选的完整白话表述与理论边界

<a id="sec-c95-final-plain"></a>

**C95 的一句话版本：**
*同一正向观察过程里，若两份内容保留的守恒资料完全相同，
它们就不能从完全可区分出发，一直沿全部正向历史保持完全可区分。*
量词包含混态；Jordan 正负部分通常不是纯态，不能仅检查纯态对。

**白话图景。**把量子看成整体内部可以相互比较、组合和留下记录的关系。
观察者沿一套确定的正向门序列看这些关系；有些读数一直保留，形成这条历史的守恒资料。
手性使绕行具有方向，但有方向的轨迹仍可能一直绕圈。
要使最终态出现，还必须保证：同一份守恒资料内部，没有一种完全区别能够永远无损地继续变化。
只要每对起初完全分开的同资料状态，迟早在有限延伸后不再完全分开，
有限维结构就会把这些分散的条件锁成共同的收缩窗口。
于是当前可读状态逐渐稳定，留下由守恒资料唯一决定的最终代表。

**白话图景。**这个最终代表不能随意选，因为它必须同时满足实际门的不动关系和原来的守恒读数。
有非平凡守恒资料时，不同资料对应不同终态；没有这些区别时，所有初态才共有一个 $\Omega$。
最终允许的载体也由过程自己选出，终端关系在其中形成普通量子代数。
开始时处于瞬态方向的内容仍然有作用：它通过内部迁移关系，决定最后的读数。
已经不在局部读口出现的区别，可以继续留在整体记录里；局部终态并不等于整个历史被删掉。
这样，“$\Omega$ 是最终态”就变成对观察者、实际过程、守恒资料和记录边界的共同约束。

本轮的完整性限于已声明的有限复量子接口：
候选、等价定理、收敛率、终端结构、非忠实边界、解析实例及反例在同一模型内闭合。
它没有由一个手性符号推出全部物理规律，也没有证明每一个封闭整体都必须收敛。
关系场若进一步承载时空与相互作用，仍须给出相应局域性、因果与动力学结构；
本轮不把有限通道的终态定理扩张成统一场方程或千禧年问题的解答。

**可检验的推进是：**
在所选观察更新下，$\Omega$ 不再是任意参照；
它由实际正向过程、初态的守恒资料和允许重新访问的记录共同限定。
若要一个与全部初态无关的 $\Omega$，必须进一步验证守恒读口只剩归一常数。

<a id="references"></a>

## 来源、版本与核读范围

<a id="ref-currentrepo"></a>

### [1]

the-omega-institute，*trureturing* 项目，
[当前公开首页](https://github.com/the-omega-institute/trureturing)。
2026 年 11 月 3 日（新加坡）核读默认 `dev` 分支页面及公开进展列表。
本轮未取得可固定的更新提交 SHA；下列仓库文稿均按已存快照
`c63ab162315fddd0801cbe9f47dbf3eda6e13360`
（2026 年 11 月 2 日）核对。
开放 PR 的标题与状态只作为进展信息，不作为已合并、已核验的数学证明。
本轮未执行仓库构建或测试。

<a id="ref-omega"></a>

### [2]

trureturing，*AURIC Omega Static Compatibility Fiber Theory*，
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)。
本轮连续核读第 4–5 节的响应商、正历史与闭路运输，
第 18 节中“中间安全判据（42）”及式 (42.1) 的安全后继论证，
以及第 31 节定理 31.1 的固定相位门闭包论证。
其中已经明确区分持续安全与最终完成，并证明正幂闭包可以包含逆相位门。
这里的“42”是第 18 节中的判据标签，不是文档第 42 节。

<a id="ref-v74"></a>

### [3]

trureturing，*AURIC v74：平滑量子历史、余切与内生运动*，
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_SMOOTH_QUANTUM_HISTORIES_COTANGENT_DYNAMICS_AND_ENDOGENOUS_MOTION_V74.md)。
本轮核读第 8 节定义 8.1、定理 8.2 及相邻范围说明，
以及“时钟重标和离散采样”小节：
接触形式、水平回路、交换子相位、回路朝向与时间标尺的区别。
这项手性表示不自行给出吸引性，也不把相位的第三方向等同于物理三维空间。

<a id="ref-records"></a>

### [4]

trureturing，*情境时空算术的量子扩展：载体、演化与有限记录*，
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/ContextualSpacetimeQuantum/001_016_FOUNDATIONS_AND_RECORDS.md)。
本轮连续核读第 8 节的定义与假设 8.1、定理 8.2–8.4：
新记录因子、无重新注入等条件下的 Schur 通道，
以及由 $C_{ij}=1$ 决定的不动空间与不动代数。
保留指针人口的此类过程一般具有多个不动态；
$|C_{ij}|=1$ 也不等价于 $C_{ij}=1$。

<a id="ref-v80"></a>

### [5]

trureturing，*AURIC v80：全结果二元差分不增公理——从有限定向锚统一重建量子读出与实际过程*，
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_ALL_OUTCOME_BINARY_DIFFERENCE_NONEXPANSION_FINITE_ORIENTED_ANCHORS_AND_ENDOGENOUS_QUANTUM_PROCESSES_V80.md)。
本轮核对摘要、共同复比较与实际后继的前件说明，以及第 16.1 节的条件式重建总表。
沿用状态、效果、实际仪器、独立复合与光滑动力学各自明确的输入条件，
不把完整有限接口的闭合扩张成任意场论或全部物理定律的重建。

<a id="ref-v94"></a>

### [6]

本对话研究稿，*AURIC v94：二元参考、内生充分约化与量子可见代数*，
2026 年 11 月 3 日（新加坡），28 页。
承接 C94 的全输入约化、二元参考保正、忠实内部参照、
普通可见代数与模相容的分类，以及唯一块重置和内部记录实现。
这些是本轮的既有接口；本轮不把其重新证明或重述计作新的量子重建结论。

<a id="ref-bg2007"></a>

### [7]

Daniel Burgarth、Vittorio Giovannetti，
*The Generalized Lyapunov Theorem and its Application to Quantum Channels*，
New Journal of Physics **9**，150，2007。
[DOI: 10.1088/1367-2630/9/5/150](https://doi.org/10.1088/1367-2630/9/5/150)；
[作者预印本 quant-ph/0605197v3](https://arxiv.org/pdf/quant-ph/0605197)。
本轮核读预印本第 1–6 页，尤其定义 6、定理 5 及其证明：
紧度量空间中具有不动点的连续映射，其渐近变形条件与混合等价。
本文全初态共享唯一终态的分支与这一既有混合机制相接；
允许多个守恒资料纤维的一般结论在正文另给有限维解析证明。

<a id="ref-bcgpy2013"></a>

### [8]

Daniel Burgarth、Giulio Chiribella、Vittorio Giovannetti、Paolo Perinotti、Kazuya Yuasa，
*Ergodic and Mixing Quantum Channels in Finite Dimensions*，
New Journal of Physics **15**，073045，2013。
[DOI: 10.1088/1367-2630/15/7/073045](https://doi.org/10.1088/1367-2630/15/7/073045)；
[作者预印本 arXiv:1210.5625v3](https://arxiv.org/pdf/1210.5625)。
本轮核读预印本第 1–9 页及第 19–22 页的相关段落，
包括遍历与混合的区别、二态交替反例、外围谱判据，
以及定理 9–10 的忠实遍历条件和相关证明。
不将唯一不动态等同于逐步收敛，也不把忠实遍历分支的循环谱结论推广到任意通道。

<a id="ref-rahaman2017"></a>

### [9]

Mizanur Rahaman，*Multiplicative Properties of Quantum Channels*，
Journal of Physics A: Mathematical and Theoretical，2017。
[DOI: 10.1088/1751-8121/aa7b57](https://doi.org/10.1088/1751-8121/aa7b57)；
[作者预印本 arXiv:1701.06205v4](https://arxiv.org/pdf/1701.06205)。
本轮核读导言、定理 1.3（预印本第 5 页），以及第 2 节引理 2.3、推论 2.4、
定理 2.5 及其证明和说明 2.6–2.7（预印本第 10–13 页）。
这些结果给出乘法域的有限稳定链、稳定域上的自同构与外围本征算子对应。
所引定理的映射同时保单位、完全正且保普通迹；
仅有忠实不变态的加权情形不能省略对应证明而直接套用。
