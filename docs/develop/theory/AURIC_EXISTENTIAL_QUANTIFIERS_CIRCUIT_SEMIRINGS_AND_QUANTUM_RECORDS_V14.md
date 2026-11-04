<a id="auric-v14"></a>

# AURIC 存在量词、电路半环与量子记录

**AURIC 研究续稿 · 从加权饱和、相干求和到支撑量词**

**v14.0 · 2026 年 10 月 29 日**

**固定源码。** 默认研究分支 `dev`，提交

`6936d5e4328efb1051abd0dc6b3eda328359a3ed`

提交时间：2026 年 10 月 29 日 20:19:52，新加坡时间。

> **转换说明（编者）。** 本文完整转换用户提供的同名 XeLaTeX 稿件，采用独立 Markdown 数学表达；陈述沿用源稿每节共享的编号。正文的“本轮”“最新”及 998 个文件、22 项变化、10 项新增、15 份源码等核对叙述均为原作者的稿件报告，不表示本次转换重新执行了该历史审计。标准结果保留原作者归属与引用，本次转换不主张数学首创或 Lean 认证。

> **记号补注（编者）。** 源稿用 $\varphi$ 而未给出数值定义；为便于独立阅读，沿用[固定黄金门前稿（文献 5）](#ref-repogate)第 2 节的记号 $\varphi=(1+\sqrt{5})/2$。此处仅明确记号，正文数学陈述和证明保持源稿。

<a id="sec-abstract"></a>

## 摘要

本稿将“概率是一种存在量词”的直觉分解为可证明的有限模型。非负权概率的正支撑给出受支撑限制的存在量词；半环路径电路统一可行性、计数与加权求和，但复振幅的抵消阻止逐项非零性成为可复合的布尔语义。以项目 CSA 的纤维饱和判据为基础，给出存在上界、全称下界、饱和缺陷、粗化余循环和条件预测误差的精确公式。量子部分证明完全正映射在支撑子空间上的像保持加法所对应的并生成及串联复合，形成一个保留相位几何的存在语义，并给出其右伴随与非正交读出判据。项目已收录的固定黄金门提供精确实例：相干作用十次回到原态，每步实际记录则产生 $(1-\varphi^{-30})/2$ 的跃迁概率。记录 Gram、独立两份复合及已知 Diósi 条件进一步说明何时可恢复经典加法；正相干核与正交可加权重则给出条件性的 Hilbert 重构和平方律。本稿保留完整记录、实际联合来源、Born 输入及资源成本，不从存在性推断多项式取得，也不宣称从裸五点图证明全部量子公理。

**核心命题。** 概率可看作带权的定量存在聚合；量子电路还必须保存相干复合。其正确存在语义使用状态支撑与效果的非正交性，而非计算基路径的普通布尔可达性。

## 目录

1. [最新项目位置与论证合同](#sec-1)
2. [概率作为带权量词：何时成立](#sec-2)
3. [电路的加法、乘法与半环语义](#sec-3)
4. [五模式的实际半环接口与隐藏关系参数](#sec-4)
5. [CSA 饱和判据的概率续推](#sec-5)
6. [量子电路：加的是振幅还是实际记录](#sec-6)
7. [量子的精确存在语义：完全正支撑量词](#sec-7)
8. [黄金门中的相干递归与概率递归](#sec-8)
9. [记录 Gram：加法与独立乘法如何一起约束相干](#sec-9)
10. [平方、Hilbert 重构与三阶干涉的条件性](#sec-10)
11. [最新制备与完整记录：产品态不等于独立来源](#sec-latest)
12. [语义存在与取得成本](#sec-12)
13. [本轮理论的确定结论与开放接口](#sec-13)

[参考文献](#sec-bibliography)

<a id="sec-1"></a>

## 1. 最新项目位置与论证合同

<a id="sec-1-1"></a>

### 1.1. 固定来源及已知结果

本轮相对上一稿固定的 `9ccde90` 比较当前 theory 树：998 个文件中有 22 项变化，含 10 项新增；定向取得并按 Git blob 校验了 15 份源码。这是有边界的来源核对，不是全库证明认证。上一轮固定黄金门稿已经被作为独立 Markdown 文档收入仓库（[5](#ref-repogate)）；收录不等于新增独立证明认证。

| 来源 | 本轮使用的既有内容 |
| --- | --- |
| Selection Calculus §§10、16、27（[1](#ref-reposelection)） | 交换半环核、合法路径和、正权归一化、布尔可行性与计数、投影计数差异、条件生成和指数小无条件概率。 |
| CSA §8 命题 10、§10（[2](#ref-repocsa)） | 直接像补集当且仅当纤维饱和；共同世界与来源共享；乘积域本身不推出概率独立。 |
| P10 Lean 源文件（[3](#ref-repop10)） | 实际声明为集合论的 `image_complement_iff_saturated`。本轮读取全部源码，没有重新构建 Lean。 |
| 最新相干重构续卷 §§57–63（[4](#ref-repocontinuation)） | 全记录转换与制备接口；尤其 §63.2 的随机来源联合律、状态值记录测度及固定乘积制备与独立抽样的区别。 |
| 固定黄金门稿（[5](#ref-repogate)） | $K=\zeta[I+(\zeta-1)\mathcal P]$、$K^{10}=I$ 及其明确编码和资源合同。 |
| Toric 关系稿（[6](#ref-repotoric)） | 五态独立子模型中的 $p_0p_{13}=p_1p_3$，及相应 odds ratio。该稿为开放来源材料，不作 Lean 认证使用。 |

本轮详细续推的是加权纤维缺陷、完全正映射的支撑量词、黄金门的记录对照，以及这些结果之间的精确接口。半环方法、条件期望、Gram 重构、量子测度与 Diósi 复合条件均有标准背景；不主张历史首创。

<a id="sec-1-2"></a>

### 1.2. 对象与前提

经典主要结论使用有限集合和明确给出的非负测度。量子主要结论使用有限维复 Hilbert 空间、完全正映射、指定制备及效果读出。概率解释采用已有 Born/密度算子合同。无限或连续记录只在第[11](#sec-latest)节按可测事件讨论，不把有限逐点支撑结论直接移用到连续域。

源代码核对、普通数学证明与形式化认证是不同事项。本稿所有代数与不等式均给纸面证明，没有执行数学数值实验、CAS、候选枚举或量子模拟。

<a id="sec-2"></a>

## 2. 概率作为带权量词：何时成立

<a id="statement-2-1"></a>

#### 定义 2.1（有限定量量词）

令 $(\Omega,\mu)$ 为有限概率空间，$R:\Omega\to\{0,1\}$ 为谓词。定义

$$
\mathsf Q_\mu R=\sum_{w\in\Omega}\mu(w)R(w),\qquad
\Omega_+=\{w:\mu(w)>0\}.
$$

对事件 $A$，写 $\mathsf Q_\mu A=\mathsf Q_\mu\mathbf{1}_A=\mu(A)$。

<a id="thm-weightedexists"></a>

#### 定理 2.2（存在与全称是概率的支撑端点）

有

$$
\mathsf Q_\mu R>0\iff\exists w\in\Omega_+:R(w)=1,
$$

$$
\mathsf Q_\mu R=1\iff\forall w\in\Omega_+:R(w)=1.
$$

当 $\mu$ 全支撑时，右边才是原论域上的普通存在和全称量词。

**证明。**

第一式由有限个非负数的和为正当且仅当至少一项为正。第二式对补谓词应用第一式，并用 $\mathsf Q_\mu(1-R)=1-\mathsf Q_\mu R$。

∎

<a id="statement-2-3"></a>

#### 命题 2.3（存在结构不确定权重）

在至少两个元素的有限集合上，所有严格正概率律给出完全相同的存在判定，但一般给出不同的事件概率。

**证明。**

全支撑时定理[2.2](#thm-weightedexists)只检测事件是否为空。取 $\Omega=\{a,b\}$，概率律 $(p,1-p)$ 随 $0<p<1$ 改变；单点事件 $\{a\}$ 的概率随之改变而非空性不变。

∎

因此“概率是一种存在量词”的准确有限版本是：概率是带权定量聚合，取其正支撑得到存在量词。纯粹的存在关系没有提供权重与归一化。

<a id="statement-2-4"></a>

#### 例 2.4（连续域的边界）

在 $[0,1]$ 上取均匀测度，事件 $\{1/2\}$ 非空但概率为零。连续情形应讨论正测度、几乎处处或测度支撑，不能无条件写 $\mu(A)>0\iff A\ne\varnothing$。

<a id="sec-3"></a>

## 3. 电路的加法、乘法与半环语义

<a id="statement-3-1"></a>

#### 定义 3.1（带权路径电路）

设有限有向无环图具有初点 $s$，边 $e$ 携带半环 $S$ 中的权重 $a_e$。对路径 $\gamma$ 按接线顺序定义 $w(\gamma)=\bigotimes_{e\in\gamma}a_e$，并定义

$$
Z(v)=\bigoplus_{\gamma:s\leadsto v}w(\gamma).
$$

空路径的权重为 $1$，空路径族的和为 $0$。允许乘法非交换时必须保留顺序。

<a id="thm-semiring"></a>

#### 定理 3.2（路径和的局部递推）

以 $Z(s)=1$ 为初值，其余按拓扑排序递推

$$
Z(v)=\bigoplus_{e:u\to v}Z(u)\otimes a_e
$$

得到上述完整路径和。每个内部切口的指标必须在相邻因子中表示同一中间对象。

**证明。**

到达非初点 $v$ 的每条路径有唯一末边 $u\to v$，此前部分是到达 $u$ 的路径。按末边作不交分类，再用分配律即得；拓扑排序上的归纳覆盖全部顶点。

∎

| 系数 | 替代项聚合 | 路径内复合 | 输出含义 |
| --- | --- | --- | --- |
| $\mathbb{B}$ | $\lor$ | $\land$ | 是否存在合法路径 |
| $\mathbb{N}$ | $+$ | $\times$ | 路径数量或有标签重数 |
| $\mathbb{R}_{\ge0}$ | $+$ | $\times$ | 非负总权；另需归一化 |
| $\mathbb{C}$ | $+$ | $\times$ | 相干振幅；存在抵消 |

这类半环解释属于成熟方法（[7](#ref-goodman)、[8](#ref-amc)），项目也已明确使用（[1](#ref-reposelection)，§§10、16）。

<a id="thm-supportsemiring"></a>

#### 定理 3.3（非零支撑何时保持半环计算）

对非平凡半环 $S$，定义 $\epsilon(a)=\mathbf{1}_{a\ne0}$。则 $\epsilon:S\to\mathbb{B}$ 为保 $0,1$ 的半环同态，当且仅当

$$
a+b=0\Longrightarrow a=b=0,
\qquad ab=0\Longrightarrow a=0\text{ 或 }b=0.
$$

**证明。**

保加法等价于 $a+b\ne0\iff a\ne0\lor b\ne0$，即第一条件；保乘法等价于 $ab\ne0\iff a\ne0\land b\ne0$，即第二条件。半环零元吸收性及 $0\ne1$ 给边界。

∎

自然数和非负实数满足这些条件。复数不满足第一条件，因为 $1+(-1)=0$。更强地，不存在保 $0,1$ 的半环同态 $h:\mathbb{C}\to\mathbb{B}$：否则

$$
0=h(0)=h(1+(-1))=h(1)\lor h(-1)=1.
$$

因此逐项记录“非零或零”不能保留相干电路复合的结果。

<a id="sec-3-1"></a>

### 3.1. 加法原理和乘法原理的适用域

普通概率总有

$$
P(A\cup B)=P(A)+P(B)-P(A\cap B),
$$

及在 $P(A)>0$ 时

$$
P(A\cap B)=P(A)P(B\mid A).
$$

互斥事件才可直接相加；独立事件才可直接相乘其无条件边缘。两个门画在不同位置或来源标签不同，均不单独证明独立。

<a id="statement-3-4"></a>

#### 命题 3.4（安全的布尔电路加乘解释）

考虑否定只出现在文字上的布尔电路，并为变量提供乘积型文字权。若每个 OR 节点的子事件互斥，每个 AND 节点的子电路使用互不相交的变量集，且 OR 子电路具有相同变量域，则 OR 取和、AND 取积得到其加权模型数。对归一化文字权，缺失变量的自由权和为一，可以省去最后的同域条件。

**证明。**

叶为文字权。互斥 OR 的模型集合是不交并，给求和。变量不交的 AND 模型是 Cartesian 积，乘积型权在该积上因子化，给乘法。相同变量域避免遗漏自由变量；归一化时每个自由变量贡献的总因子为一。对电路作结构归纳。

∎

这对应确定、可分解及平滑电路的标准条件（[8](#ref-amc)、[9](#ref-darwiche)）。任意门网不能直接套用：当 $0<p<1$ 时，$A\lor A=A$ 而 $p+p\ne p$；$A\land A=A$ 而 $p^2\ne p$。重复推导路径的计数也可能不同于实际世界的计数。

<a id="sec-4"></a>

## 4. 五模式的实际半环接口与隐藏关系参数

本节核公式取交换半环，概率实例取非负实数。项目的高到低三位置扫描使用

$$
B(t)=\begin{pmatrix}1&t\\1&0\end{pmatrix},\qquad
K_{\mathrm{HL}}=B(c)B(b)B(a)
=\begin{pmatrix}1+b+c&a(1+c)\\1+b&a\end{pmatrix}.
$$

初末权为 $\lambda,\omega$ 时，完整合法路径权为

$$
Z=\lambda^{\mathsf T}K_1\cdots K_L\omega.
$$

局部核输入与输出的接缝位必须实际共享；该权重因子化是模型前提。非负权且 $Z>0$ 后才能归一化。项目的实际提议概率核还可能为次随机矩阵，其缺失行质量是拒绝结果，不能删去后悄然重新归一化（[1](#ref-reposelection)，§10）。

<a id="prop-odds"></a>

#### 命题 4.1（活动权模型与关系自由度）

取 $a,b,c,d>0$，在模式 $(\mathrm{null},1,2,3,13)$ 上定义

$$
Z_d=1+a+b+c+dac,\qquad
(p_0,p_1,p_2,p_3,p_{13})=\frac{(1,a,b,c,dac)}{Z_d}.
$$

这与严格正五态概率单纯形双射，逆式为

$$
a=\frac{p_1}{p_0},\quad b=\frac{p_2}{p_0},\quad
c=\frac{p_3}{p_0},\quad d=\frac{p_0p_{13}}{p_1p_3}.
$$

原三活动权模型正是 $d=1$ 子族，满足 $p_0p_{13}=p_1p_3$。

**证明。**

正参数显然给严格正归一概率。反向代入，前四个权为相应概率除以 $p_0$，且 $dac=p_{13}/p_0$，所以 $Z_d=1/p_0$。这既给逆式也给唯一性。

∎

这里 $d$ 精确记录一个没有被三个单位置活动权决定的联合关系。$d=1$ 对应两个端点占位在给定中间占位为零后的条件独立，不是三个位置的无条件独立。其 odds-ratio 与独立子模型含义在项目已有讨论（[6](#ref-repotoric)）；本命题仅给直接坐标反演，不依赖那份开放供文中的完整 toric 理想证明。该坐标适用于严格正内部，零概率边界需另分层处理。

<a id="sec-5"></a>

## 5. CSA 饱和判据的概率续推

<a id="sec-5-1"></a>

### 5.1. 存在上界、全称下界与饱和缺陷

本节把论域先限制为有限概率测度的支撑。因此始终假定 $\mu(w)>0$、$\mu(\Omega)=1$，并取满射记录

$$
f:\Omega\twoheadrightarrow Y,\qquad \nu=f_*\mu.
$$

于是每个 $\nu(y)>0$。若原论域含零权点，以下所有 $A,f$ 都应限制到正支撑；不能让一个零权见证触发整条正质量纤维。

<a id="statement-5-1"></a>

#### 定义 5.1（记录量词与缺陷）

对事件 $A\subseteq\Omega$，定义

$$
u_f(A)=\nu(f[A]),\qquad
\ell_f(A)=\nu(Y\setminus f[A^c]),\qquad
\delta_f(A)=u_f(A)-\mu(A).
$$

$u_f$ 把“记录纤维里存在一个 $A$ 见证”当真；$\ell_f$ 只在“纤维内所有世界属于 $A$”时当真。

<a id="thm-saturation"></a>

#### 定理 5.2（加权纤维饱和与模糊质量）

有

<a id="eq-bracket"></a>

$$
\begin{aligned}
\ell_f(A)&\le\mu(A)\le u_f(A),
\end{aligned}
\tag{5.1}
$$

<a id="eq-defect"></a>

$$
\begin{aligned}
\delta_f(A)&=\mu\bigl(f^{-1}(f[A])\setminus A\bigr),
\end{aligned}
\tag{5.2}
$$

<a id="eq-ambiguity"></a>

$$
\begin{aligned}
\delta_f(A)+\delta_f(A^c)
&=u_f(A)-\ell_f(A)
=\nu\bigl(f[A]\cap f[A^c]\bigr).
\end{aligned}
\tag{5.3}
$$

以下条件等价：$\delta_f(A)=0$；$A=f^{-1}(f[A])$；$A$ 是若干完整记录纤维的并；$f[A^c]=Y\setminus f[A]$。

**证明。**

存在饱和闭包 $f^{-1}(f[A])$ 包含 $A$，全称纤维并 $f^{-1}(Y\setminus f[A^c])$ 包含于 $A$，给式[(5.1)](#eq-bracket)。由推送测度定义及不交差集分解得到式[(5.2)](#eq-defect)。

满射保证 $f[A]\cup f[A^c]=Y$；有限测度的容斥式给

$$
\nu(f[A])+\nu(f[A^c])-1=\nu(f[A]\cap f[A^c]).
$$

结合 $\mu(A)+\mu(A^c)=1$ 与 $\ell_f(A)=1-u_f(A^c)$ 得式[(5.3)](#eq-ambiguity)。每个原子均为正质量，式[(5.2)](#eq-defect)为零恰好意味着差集为空。其余等价是项目 CSA 命题 10 的纤维饱和判据（[2](#ref-repocsa)、[3](#ref-repop10)）。

∎

若 $\Omega=\{a,b\}$、$\mu(a)=\mu(b)=1/2$，$f$ 把两者合成同一记录，而 $A=\{a\}$，则 $\mu(A)=1/2$，但 $u_f(A)=1$、$\ell_f(A)=0$。同时 $\exists A$ 与 $\exists A^c$ 为真：它们表示纤维里分别有见证，未构成同一世界上的矛盾。

<a id="thm-cocycle"></a>

#### 定理 5.3（粗化缺陷的精确复合）

再取满射 $g:Y\twoheadrightarrow Z$，第二层使用测度 $\nu$。则

$$
\boxed{\delta_{g\circ f}(A)=\delta_f(A)+\delta_g(f[A]).}
$$

因此继续合并记录时，存在上界单调上升，全称下界单调下降，模糊区间单调扩大。

**证明。**

在定义中加减 $\nu(f[A])$：

$$
(g_*\nu)(g[f[A]])-\mu(A)
=\bigl[(g_*\nu)(g[f[A]])-\nu(f[A])\bigr]
+\bigl[\nu(f[A])-\mu(A)\bigr].
$$

每个缺陷非负给上界单调性；对补集使用同一结果得下界，二者相减给区间。

∎

<a id="sec-5-2"></a>

### 5.2. 定量预测保留什么，布尔化又丢掉什么

定义条件预测

$$
h_f(y)=\frac{\mu(A\cap f^{-1}(y))}{\nu(y)}.
$$

<a id="thm-tower"></a>

#### 定理 5.4（塔式递归与尖锐读出）

有

$$
\mu(A)=\sum_y\nu(y)h_f(y),\qquad
u_f(A)=\nu(h_f>0),\quad \ell_f(A)=\nu(h_f=1).
$$

令 $\xi=g_*\nu$，则

$$
h_{g\circ f}(z)=\sum_{g(y)=z}\frac{\nu(y)}{\xi(z)}h_f(y).
$$

并且 $h_f$ 只取 $0,1$ 当且仅当 $A$ 饱和。

**证明。**

将 $A$ 按记录纤维不交分割即第一式。正支撑使 $h_f(y)>0$ 等价于该纤维有选点，$h_f(y)=1$ 等价于没有未选点。按 $g$ 的纤维再分组，分子相加、分母为 $\xi(z)$，得到塔式公式。

∎

因此保留 $[0,1]$ 值的条件预测能够精确继续计算总概率；将它提前替换为“是否大于零”的存在位，会恰好产生定理[5.2](#thm-saturation)的缺陷。

<a id="thm-variance"></a>

#### 定理 5.5（预测误差与记录粗化）

对任意预测器 $a:Y\to\mathbb{R}$，

$$
\mathbb{E}_\mu[(\mathbf{1}_A-a\circ f)^2]
=\sum_y\nu(y)h_f(y)(1-h_f(y))
+\sum_y\nu(y)(h_f(y)-a(y))^2.
$$

故最优预测器唯一为 $h_f$。其最小误差 $\mathcal V_f(A)$ 为零恰好对应饱和，并满足

$$
\mathcal V_{g\circ f}(A)-\mathcal V_f(A)
=\sum_y\nu(y)[h_f(y)-h_{g\circ f}(g(y))]^2\ge0.
$$

**证明。**

每条纤维内设 $h=h_f(y)$，用恒等式

$$
h(1-a)^2+(1-h)a^2=h(1-h)+(a-h)^2
$$

再乘 $\nu(y)$ 求和。正权给唯一性，$h(1-h)=0$ 的逐点条件给饱和。取 $a=h_{g\circ f}\circ g$，其左边正是粗记录的最小误差，由前式得到差值。

∎

这刻画内生观察者合并记录后预测精度的损失，但它已在经典模型内成立，不能单独作为量子不确定性的推导。

<a id="sec-6"></a>

## 6. 量子电路：加的是振幅还是实际记录

<a id="sec-6-1"></a>

### 6.1. 两种求和不交换

对纯输入 $|x\rangle$ 及电路 $U_L\cdots U_1$，输出振幅为

$$
\langle y|U_L\cdots U_1|x\rangle
=\sum_{x_1,\ldots,x_{L-1}}
(U_L)_{y x_{L-1}}\cdots(U_1)_{x_1x}.
$$

概率则在该相干总和之后取平方模。若中间基标签被实际记录并按该标签退相干，才得到相应的路径概率和。

<a id="statement-6-1"></a>

#### 例 6.1（非零路径可以完全抵消）

令 $H=2^{-1/2}\left(\begin{smallmatrix}1&1\\1&-1\end{smallmatrix}\right)$。两次 $H$ 后从零到一的两条中间路径振幅分别为 $1/2,-1/2$，总和为零。它们都非零，不代表最终事件有正概率。若中间位被测量，输出一的概率变为 $1/2$。两种情况具有不同的物理操作。

<a id="sec-6-2"></a>

### 6.2. 实际记录仍服从普通加乘法

<a id="statement-6-2"></a>

#### 定义 6.2（自适应量子仪器记录）

固定有限深度、有限结果菜单的记录树。给定 $\rho\ge0$、$\operatorname{Tr}\rho=1$，令 $\sigma_\varnothing=\rho$。每条已记录历史 $h$ 之后提供仪器 $\{\Phi_a^h\}_a$，其中各映射完全正且其和保迹。令 $\sigma_h$ 为沿实际历史复合得到的未归一态，$p(h)=\operatorname{Tr}\sigma_h$。

<a id="thm-instrument"></a>

#### 定理 6.3（完整记录的概率递归）

有 $\sum_a p(ha)=p(h)$。当 $p(h)>0$，

$$
p(ha)=p(h)p(a\mid h),\quad
p(a\mid h)=\operatorname{Tr}\Phi_a^h\left(\frac{\sigma_h}{p(h)}\right).
$$

对互斥的完整记录集合 $A$，$p(A)=\sum_{h\in A}p(h)$，其粗化操作为 $\sum_{h\in A}\Phi_h$。

**证明。**

由 $\sigma_{ha}=\Phi_a^h(\sigma_h)$，线性和保迹性给归一化递归；提取标量 $p(h)$ 给条件乘法。完整记录互斥，其操作按分支加和，取迹得最后一式。

∎

若单 Kraus 分支为 $M_h$，记录粗化是

$$
\sum_hM_h\rho M_h^\dagger.
$$

它一般不同于

$$
\left(\sum_hM_h\right)\rho\left(\sum_kM_k\right)^\dagger.
$$

后者含交叉项，还未必迹不增，必须另行实现。已经形成正交记录后不去读取它，不会恢复被丢失的相干；相干恢复需要相应联合操作。

<a id="sec-7"></a>

## 7. 量子的精确存在语义：完全正支撑量词

<a id="statement-7-1"></a>

#### 定义 7.1（完全正映射的支撑像）

令 $\Phi:\mathcal L(\mathcal H)\to\mathcal L(\mathcal K)$ 完全正，取任一 Kraus 表示

$$
\Phi(X)=\sum_aK_aXK_a^\dagger.
$$

对线性子空间 $S\subseteq\mathcal H$ 定义

$$
\mathsf F_\Phi(S)=\operatorname{span}_a K_aS.
$$

子空间的并生成 $S\vee T$ 指 $\operatorname{span}(S\cup T)$。有限维中正算子的支撑为其像空间。

<a id="thm-cpsupport"></a>

#### 定理 7.2（支撑量词及其加乘相容）

对任意 $\rho\ge0$，

$$
\boxed{\operatorname{supp}\Phi(\rho)=\mathsf F_\Phi(\operatorname{supp}\rho).}
$$

因此 $\mathsf F_\Phi$ 不依赖 Kraus 表示，保持子空间并生成，且在相应可加或可复合的类型下有

$$
\mathsf F_{\Phi+\Psi}=\mathsf F_\Phi\vee\mathsf F_\Psi,
\qquad
\mathsf F_{\Phi\circ\Psi}=\mathsf F_\Phi\circ\mathsf F_\Psi.
$$

固定同一载体时，$\Phi\mapsto\mathsf F_\Phi$ 是从完全正自映射的加法、复合半环到保并生成子空间映射半环的保 $0,1$ 同态。

**证明。**

令 $A_a=K_a\rho^{1/2}$。对任意向量 $v$，

$$
\left\langle v,\sum_aA_aA_a^\dagger v\right\rangle
=\sum_a\|A_a^\dagger v\|^2.
$$

故该和的核为 $\bigcap_a\ker A_a^\dagger$，取正交补得到像空间为 $\operatorname{span}_a\operatorname{ran} A_a$。有限维中 $\operatorname{ran}\rho^{1/2}=\operatorname{supp}\rho$，给首式。

用 $\rho=P_S$ 即知定义只由 $\Phi$ 决定。线性像保持并生成；$\Phi+\Psi$ 可取两个 Kraus 列表的并，复合映射可取所有乘积 $K_aL_b$，分别给两条恒等式。零映射送一切子空间到零，恒等映射保持子空间。这里不声称同态满射。

∎

完全正映射的标准表示背景见（[10](#ref-watrous)，第2章）。概率意义还要求规范初态、适当的迹不增过程及 $0\le E\le I$；全部 CP 映射作为代数载体时不自动满足这些归一化条件。

<a id="thm-quantumexists"></a>

#### 定理 7.3（正概率的几何存在判据）

设 $\rho\ge0,E\ge0$，则

$$
\begin{aligned}
\operatorname{Tr}[E\Phi(\rho)]>0
&\iff \mathsf F_\Phi(\operatorname{supp}\rho)\not\perp\operatorname{supp} E\\
&\iff \exists a,\ v\in\operatorname{supp}\rho:\ E^{1/2}K_av\ne0.
\end{aligned}
$$

**证明。**

有

$$
\operatorname{Tr}[E\Phi(\rho)]
=\sum_a\|E^{1/2}K_a\rho^{1/2}\|_{\mathrm{HS}}^2.
$$

该和为正当且仅当至少一个矩阵非零，等价于在 $\operatorname{ran}\rho^{1/2}$ 上有一个未被 $E^{1/2}K_a$ 杀掉的向量。又 $\ker E^{1/2}=(\operatorname{supp} E)^\perp$，给中间条件。

∎

这是“概率对应某种存在”的一个严格量子版本。Kraus 指标是表示指标，未必是实际可读历史；上述真值具有表示不变性，不能据此宣布隐藏轨迹存在。

<a id="statement-7-4"></a>

#### 例 7.4（非正交不等于交非零）

$S=\operatorname{span}|0\rangle$ 与 $T=\operatorname{span}|+\rangle$ 的交为零，但它们不正交，$\operatorname{Tr}(P_TP_S)=1/2$。因此不能把定理[7.3](#thm-quantumexists)换写成普通集合交有元素。

<a id="thm-adjunction"></a>

#### 定理 7.5（支撑量词的右伴随）

定义

$$
\mathsf G_\Phi(T)=\bigcap_a K_a^{-1}(T).
$$

则

$$
\mathsf F_\Phi(S)\subseteq T
\iff S\subseteq\mathsf G_\Phi(T),
$$

且对 Hilbert–Schmidt 对偶 $\Phi^*$，

$$
\mathsf G_\Phi(T)=\bigl[\mathsf F_{\Phi^*}(T^\perp)\bigr]^\perp,
\quad
\mathsf F_\Phi(S)\perp T\iff S\perp\mathsf F_{\Phi^*}(T).
$$

**证明。**

$\operatorname{span}_aK_aS\subseteq T$ 等价于对每个 $a$ 都有 $K_aS\subseteq T$，再等价于 $S\subseteq\bigcap_aK_a^{-1}(T)$。此外 $K_av\in T$ 当且仅当对全部 $w\in T^\perp$ 有 $\langle K_a^\dagger w,v\rangle=0$。对所有 $a,w$ 求交给第一条正交补公式；同样的内积恒等式给最后一式。

∎

对迹递减分支，$\mathsf G_\Phi(T)$ 是宽松的全称前条件：它保证所有存活输出落在 $T$，不保证输出一定出现。被全部 $K_a$ 杀掉的输入也因空条件而属于该空间。保迹通道满足 $\sum_aK_a^\dagger K_a=I$，排除了非零输入被全部杀掉的情况。对规范初态和通道，上一伴随给出全称端点

$$
\operatorname{supp}\rho\subseteq\mathsf G_\Phi(T)
\iff\operatorname{Tr}[P_T\Phi(\rho)]=1.
$$

对迹递减过程，右边的一应换成总存活质量 $\operatorname{Tr}\Phi(\rho)$。两式均由对补投影 $I-P_T$ 应用定理[7.3](#thm-quantumexists)得到。

<a id="statement-7-6"></a>

#### 命题 7.6（该存在语义仍保留相位几何）

若两个酉门 $U,V$ 对全部子空间有相同支撑像，则 $U=e^{i\theta}V$。

**证明。**

$V^\dagger U$ 保持每条射线。取正交基 $e_j$ 得 $V^\dagger Ue_j=\lambda_je_j$；再取 $e_i+e_j$ 所在射线，迫使 $\lambda_i=\lambda_j$。酉性给共同模为一。

∎

因此子空间量词没有把量子计算化为普通布尔路径可达性。纯态支撑本身是一条带相对复相位的射线；存在语义舍去概率尺度，却保留了大量相干结构。也不能只记录整个 CP 映射是否非零：两个非零正交投影对应的 CP 分支，其串联可以是零映射；中间支撑的相容性仍然必要。

<a id="sec-8"></a>

## 8. 黄金门中的相干递归与概率递归

使用项目已经收录的固定门（[5](#ref-repogate)）。在不变空间 $\operatorname{span}\{|000\rangle,|010\rangle\}$ 上，

$$
P=\begin{pmatrix}\varphi^{-1}&\varphi^{-3/2}\\\varphi^{-3/2}&\varphi^{-2}\end{pmatrix},
\quad \zeta=e^{3\pi i/5},\quad
K=\zeta[I+(\zeta-1)P].
$$

因为 $P^2=P$，门的特征值为 $\zeta,\zeta^2$，故 $K^{10}=I$。

<a id="thm-goldenrecord"></a>

#### 定理 8.1（同一黄金门的两种十步记录律）

从 $|000\rangle$ 出发，十次相干作用后读出 $010$ 的概率为零。若每次门后都作计算基测量，或对计算基退相干，则该概率为

$$
\boxed{\frac{1-\varphi^{-30}}2>0.}
$$

**证明。**

相干情形由 $K^{10}=I$ 立即得到。逐步记录时的转移概率矩阵为

$$
T=|K|^{\circ2}
=\begin{pmatrix}\varphi^{-2}&\varphi^{-1}\\\varphi^{-1}&\varphi^{-2}\end{pmatrix}.
$$

确实，非对角元为

$$
|\zeta-1|^2\varphi^{-3}
=(2-2\cos(3\pi/5))\varphi^{-3}
=\varphi^2\varphi^{-3}=\varphi^{-1};
$$

对角元由酉性列归一化为 $1-\varphi^{-1}=\varphi^{-2}$。$T$ 在常数与反号方向上的特征值分别为 $1$ 与

$$
\nu=\varphi^{-2}-\varphi^{-1}=-\varphi^{-3}.
$$

于是

$$
T^r=\frac12\begin{pmatrix}1+\nu^r&1-\nu^r\\1-\nu^r&1+\nu^r\end{pmatrix}.
$$

取 $r=10$ 即得结论。

∎

每个 $T$ 元素严格为正，所以布尔路径存在性在任意正步数都允许两种输出，却不能判断相干十步后的精确零。两种递归的差别来自中间记录操作。对同一门字仅改变人的知晓状态，不会使已经形成的物理记录自动消失。

<a id="sec-9"></a>

## 9. 记录 Gram：加法与独立乘法如何一起约束相干

<a id="sec-9-1"></a>

### 9.1. 一个有归一化保证的记录模型

取正交路径基 $|h\rangle$、归一化输入 $\sum_h\psi_h|h\rangle$（$\sum_h|\psi_h|^2=1$）及单位记录向量 $r_h$。允许记录耦合

$$
|h\rangle|0\rangle_R\longmapsto|h\rangle|r_h\rangle_R.
$$

路径因子正交，故即使 $r_h$ 不正交，这仍是等距映射。路径再经酉门 $U$ 后，给定输出 $y$ 的未归一记录向量为

$$
v_y=\sum_h a_{yh}r_h,\quad a_{yh}=U_{yh}\psi_h,
\quad p(y)=a_y^\dagger G a_y,
\quad G_{hk}=\langle r_h,r_k\rangle.
$$

对 $y$ 求和，酉性的列正交消掉交叉项，得 $\sum_yp(y)=\sum_h|\psi_h|^2=1$。相同记录给振幅先求和；正交记录给模平方先求和。

<a id="thm-gram"></a>

#### 定理 9.1（对全部系数经典可加当且仅当记录正交）

对固定单位记录向量，令 $q_a(A)=\|\sum_{h\in A}a_hr_h\|^2$。对所有复系数 $a$ 和所有不交 $A,B$ 有

$$
q_a(A\cup B)=q_a(A)+q_a(B)
$$

当且仅当 $G=I$。

**证明。**

对单点 $i,j$，差值为 $2\operatorname{Re}(\overline a_i a_jG_{ij})$。分别取系数 $(1,1)$ 和 $(1,i)$，迫使 $G_{ij}$ 的实部与虚部都为零。反向，正交性消去全部交叉项；单位范数固定对角为一。

∎

全系数变化是本定理的数学前提，有限实际控制菜单未必能供应。近似版本也精确：

$$
\sup_{a\ne0}\frac{|a^\dagger Ga-\|a\|^2|}{\|a\|^2}=\|G-I\|_{\mathrm{op}}.
$$

这是自伴矩阵 $G-I$ 的 Rayleigh 商。若有 $M$ 个记录且非对角内积绝对值至多 $\eta$，则由 Cauchy–Schwarz 得误差至多 $\eta(M-1)\|a\|^2$。

<a id="thm-diosi"></a>

#### 定理 9.2（单份加法与两份独立复合的共同约束）

固定分支向量 $v_h$，记 $D_{hk}=\langle v_h,v_k\rangle$。若
$q(A)=\|\sum_{h\in A}v_h\|^2$ 对全部不交事件可加，且相同的两份独立张量族 $v_h\otimes v_k$ 也具有此性质，则 $D$ 对角。反之，对角 $D$ 的任意独立张量幂都可加。

**证明。**

单份加法等价于对 $i\ne j$ 有 $\operatorname{Re}D_{ij}=0$，可写 $D_{ij}=it$，$t\in\mathbb{R}$。两份族中不同历史 $(i,i)$ 与 $(j,j)$ 的交叉内积为

$$
D_{ij}^2=-t^2.
$$

两份加法要求其实部为零，故 $t=0$。反向，对角矩阵的张量积仍对角。

∎

**来源与地位。**  这是 Diósi 已知复合障碍的有限 Gram 证明（[11](#ref-diosi)）。它说明只要求一次固定实验的加法一致性，仅排除交叉项实部；再要求与独立乘法稳定相容，才同时排除虚部。独立张量族是额外可用的复合合同，不由两个来源名字或两份边缘概率自动供应。

<a id="sec-10"></a>

## 10. 平方、Hilbert 重构与三阶干涉的条件性

<a id="sec-10-1"></a>

### 10.1. 从正相干核到 Hilbert 空间

<a id="thm-gramreconstruction"></a>

#### 定理 10.1（有限正核的最小实现）

给定 Hermitian 正半定矩阵 $D\in\mathbb{C}^{M\times M}$，定义

$$
\mathcal H_D=\mathbb{C}^M/\ker D,\qquad
\langle[c],[d]\rangle=c^\dagger Dd.
$$

这是维数 $\operatorname{rank} D$ 的 Hilbert 空间。$v_h=[e_h]$ 满足 $\langle v_h,v_k\rangle=D_{hk}$ 并张成该空间。任意另一个张成的 Gram 实现与它唯一酉等价。

**证明。**

正半定性给 $c^\dagger Dc=0\iff D^{1/2}c=0\iff Dc=0$，所以商上的内积良定义且正定。有限维保证完备。将 $[e_h]$ 映到另一组同 Gram 向量，保全部内积、核恰相同、由张成性满射，故给唯一酉映射。

∎

直接和核对应正交替代项；张量核的最小实现满足 $\mathcal H_{D\otimes E}\simeq\mathcal H_D\otimes\mathcal H_E$，由标准基向量对的内积相乘直接验证。这给“静态谱关系构成 Hilbert 空间”一个精确有限版本，但所给对象必须是正相干核，裸图的邻接与存在关系没有决定该核。

<a id="thm-square"></a>

#### 定理 10.2（平方律的条件性唯一性）

设 $\dim\mathcal H\ge2$，$W:\mathcal H\to[0,\infty)$ 满足：对全部酉变换不变；对正交向量可加；单位向量权重为一。则

$$
\boxed{W(v)=\|v\|^2.}
$$

**证明。**

酉群在同范数向量上可迁，使 $W(v)=f(\|v\|^2)$。取两个正交单位方向，在其上选择平方范数分别为 $s,t$ 的向量，得 $f(s+t)=f(s)+f(t)$。非负性使 $f$ 单调，单位归一化给 $f(1)=1$，因而 $f(q)=q$ 对所有非负有理数成立。用有理数从上下夹逼任意实数，得 $f(s)=s$。不需要额外连续性假设。

∎

这解释在已给 Hilbert 几何、酉对称和正交记录可加性之后，平方为何被固定。它对实 Hilbert 空间同样成立，没有选择复数域；$W$ 是未归一权，超过一的范数允许超过一的权。测量概率还需要规范制备和效果。完整效果域上的非情境正可加赋值有更强的迹表示定理（[13](#ref-busch)），本稿不以布尔存在替代那些假设。

<a id="sec-10-2"></a>

### 10.2. 历史量子权不一定是所有子集上的概率

给固定分支向量，定义

$$
q(A)=\left\|\sum_{h\in A}v_h\right\|^2.
$$

它非负但一般不单调：两个非零向量 $v,-v$ 分别有正权，合并后为零。即使总权已归一，也不能自动把所有未记录历史子集当成普通概率事件。

<a id="statement-10-3"></a>

#### 定理 10.3（固定分支族的三阶交叉项消失）

对两两不交的 $A,B,C$，

$$
\begin{aligned}
0={}&q(A\cup B\cup C)-q(A\cup B)-q(A\cup C)-q(B\cup C)\\
&+q(A)+q(B)+q(C).
\end{aligned}
$$

**证明。**

记三组向量和为 $u,v,w$。展开平方范数：每个自身项的系数为 $1-2+1=0$，每个两两实内积项的系数为 $1-1=0$。

∎

这是标准 Sorkin 二阶量子测度关系（[12](#ref-sorkin)）。它要求比较中使用同一分支族；改变实际装置可能改变这些向量，不能不核对边界条件便套用实验比较。

<a id="statement-10-4"></a>

#### 例 10.4（非负事件值和三阶恒等式还不够）

取

$$
D=\frac17\begin{pmatrix}1&2&0\\2&1&0\\0&0&1\end{pmatrix}.
$$

全部子集指示向量的值 $\mathbf{1}_A^{\mathsf T}D\mathbf{1}_A$ 非负，总事件值为一，且因二次形式而满足上述三阶关系。但 $c=(1,-1,0)$ 满足 $c^\dagger Dc=-2/7$，故 $D$ 非正半定，不能成为 Hilbert Gram 核。对任意复系数的强正性是额外约束。

<a id="sec-latest"></a>

## 11. 最新制备与完整记录：产品态不等于独立来源

固定有限来源集 $T_D$，在原文假设 62.1、共同初始化及相位约定下，记实际规范量子输出为 $\pi_s=|\psi_{X,D,n}(s)\rangle\langle\psi_{X,D,n}(s)|$，即原文的 $\widetilde\pi_s$。最新项目定理 63.2 对固定已知来源对 $(s,t)$ 给出产品态制备。若随机选择者的实际联合律为 $\mu(s,t)$，则量子边缘为

$$
\rho_\mu=\sum_{s,t}\mu(s,t)\pi_s\otimes\pi_t.
$$

若另供 $\mu(s,t)=\mu_1(s)\mu_2(t)$，分配律才给所对应的边缘态乘积。反过来，某些不忠实编码也可能使相关来源偶然给产品态，所以这里不把来源独立声称为所有编码中的必要条件。

<a id="statement-11-1"></a>

#### 命题 11.1（共享来源标签的相关差）

令 $\pi_\alpha\ne\pi_\beta$，以各半概率选择 $(\alpha,\alpha)$ 或 $(\beta,\beta)$。若 $\bar\pi=(\pi_\alpha+\pi_\beta)/2$，则

$$
\frac12(\pi_\alpha\otimes\pi_\alpha+\pi_\beta\otimes\pi_\beta)
-\bar\pi\otimes\bar\pi
=\frac14(\pi_\alpha-\pi_\beta)\otimes(\pi_\alpha-\pi_\beta)\ne0.
$$

**证明。**

直接展开。非零差算子 $\Delta$ 的 Hilbert–Schmidt 范数为正，故 $\|\Delta\otimes\Delta\|_{\mathrm{HS}}=\|\Delta\|_{\mathrm{HS}}^2>0$。

∎

这正是项目新段中的例子（[4](#ref-repocontinuation)，§63.2）：每个条件来源对可制备为乘积态，仍不推出随机流无条件独立。

完整经典记录空间记为 $(\mathcal R,\Sigma)$，定义分量测度

$$
\nu_{s,t}(B)=\Pr\{S=s,T=t,\mathsf R\in B\}.
$$

实际联合输出由状态值测度

$$
\Omega_\nu(B)=\sum_{s,t}\nu_{s,t}(B)\pi_s\otimes\pi_t
$$

表示，满足

$$
\operatorname{Tr}\Omega_\nu(B)=\Pr\{\mathsf R\in B\},\qquad
\Omega_\nu(\mathcal R)=\rho_\mu.
$$

它是正算子值状态测度，不是 POVM 效果族：其总量是密度算子而非恒等算子。连续记录按可测事件保留，不能为每个连续值虚设一个归一正交向量。给定来源对后若还有随机种子，完整记录未必是纯记录；删掉它或把它换成固定辅助位会改变输入合同。

这一进展为本稿规定了明确边界：独立乘法、实际联合律和完整记录都必须提供；Born 标定继续是原有密度算子模型的输入，正如项目命题 63.3 所明确说明。

<a id="sec-12"></a>

## 12. 语义存在与取得成本

<a id="prop-sat"></a>

#### 命题 12.1（存在可以编码成正概率，但精度必须计入）

对 $m$ 个变量的布尔公式 $F$，从全部赋值均匀抽样，令

$$
p_F=\frac{\#\operatorname{SAT}(F)}{2^m}.
$$

则 $F$ 可满足当且仅当 $p_F>0$。然而仅依据估计接口承诺 $|\widehat p-p|\le\eta$，若 $\eta\ge2^{-m-1}$，则不能在最坏情形保证区分 $p=0$ 与 $p=2^{-m}$。

**证明。**

等价来自定理[2.2](#thm-weightedexists)。两个允许估计区间在误差至少半间距时相交，交点可以同时是两种真值的合法返回，因此仅凭该承诺不能区分。

∎

这不是对一切 SAT 算法的下界。它只说明存在等价不自动供应足够精度的取得接口。独立直接抽样 $N$ 次漏掉唯一见证的概率为 $(1-2^{-m})^N$；由联合界，若要常数命中概率，此种抽样需要指数级试次数。

量子验证器若保留正交见证标签，制备

$$
2^{-m/2}\sum_w|w\rangle|F(w)\rangle,
$$

测量最后一位的接受概率仍为 $p_F$。进一步干涉或放大需要实际算法，不能仅凭“量子”“静态图”或“有路径”三词取得。项目已有 §27 的投影计数与条件概率接口边界，正与此相符（[1](#ref-reposelection)）。

<a id="sec-13"></a>

## 13. 本轮理论的确定结论与开放接口

1. 概率的正支撑给出受测度支撑限制的存在量词；权重和归一化是额外数据。

2. 电路加乘在明确的半环与复合合同中成立。路径、实际世界和可读记录的重数不能混用。

3. 粗观察将定量预测强行布尔化时，误差有精确的纤维缺陷、模糊区间和粗化复合公式；它延续 CSA 的饱和判据。

4. 量子相干求和允许抵消，逐条路径非零性不能决定最终概率。黄金门十步对照给出项目内的精确实例。

5. 完全正映射的支撑像提供可复合的量子存在语义，但其载体是保留相位的子空间几何；非正交性不能改成普通集合交。

6. 实际记录的经典可加性由 Gram 条件控制。固定一次加法与独立张量复合共同要求更强的正交性；这是标准 Diósi 条件的项目化应用。

7. 正相干核能够重构 Hilbert 空间；在已给几何、酉对称和正交可加性之后，正权唯一是范数平方。此链条尚未从纯布尔逻辑选出复数、Born 或全部量子动力学。

适合下一次继续验证的对象已经具体化：将支撑量词、完整记录及原生门字放入同一有限模型，证明指定观察菜单下的实际可达子空间和最小记录成本。其状态、操作、记录和误差都应保留，不能用存在论断代替取得过程。

<a id="sec-bibliography"></a>

## 参考文献

<a id="ref-reposelection"></a>

**[1]** trureturing. [AURIC FIB Atom Selection Calculus](https://github.com/the-omega-institute/trureturing/blob/6936d5e4328efb1051abd0dc6b3eda328359a3ed/docs/develop/theory/AURIC_FIB_ATOM_SELECTION_CALCULUS.md)，固定提交 `6936d5e`，尤其 §§10、16、27。

<a id="ref-repocsa"></a>

**[2]** trureturing. [Contextual Spacetime Arithmetic](https://github.com/the-omega-institute/trureturing/blob/6936d5e4328efb1051abd0dc6b3eda328359a3ed/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC.md)，固定提交 `6936d5e`，§§8–10。

<a id="ref-repop10"></a>

**[3]** trureturing. [直接像补集与纤维饱和的 Lean 源文件](https://github.com/the-omega-institute/trureturing/blob/6936d5e4328efb1051abd0dc6b3eda328359a3ed/D5/S3/ConceptDynamics/Negation/DirectImageComplementSaturation.lean)，固定提交 `6936d5e`。

<a id="ref-repocontinuation"></a>

**[4]** trureturing. [AURIC 相干重构续卷](https://github.com/the-omega-institute/trureturing/blob/6936d5e4328efb1051abd0dc6b3eda328359a3ed/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION.md)，固定提交 `6936d5e`，尤其新增 §§57–63。

<a id="ref-repogate"></a>

**[5]** trureturing. [固定黄金门与编织相容理论](https://github.com/the-omega-institute/trureturing/blob/6936d5e4328efb1051abd0dc6b3eda328359a3ed/docs/develop/theory/AURIC_FIXED_GOLDEN_GATE_AND_BRAID_COMPATIBILITY_ZH.md)，用户提供正式稿的 Markdown 转换版，固定提交 `6936d5e`。

<a id="ref-repotoric"></a>

**[6]** trureturing. [循环控制、KL 作用与 Toric 关系](https://github.com/the-omega-institute/trureturing/blob/6936d5e4328efb1051abd0dc6b3eda328359a3ed/docs/develop/theory/AURIC_FIB_ATOM_CIRCULATION_CONTROL_KL_ACTION_AND_TORIC_RELATIONS.md)，§§3、12；来源状态为开放供文。

<a id="ref-goodman"></a>

**[7]** J. Goodman. Semiring Parsing. Computational Linguistics 25(4), 573–606 (1999). <https://aclanthology.org/J99-4004/>.

<a id="ref-amc"></a>

**[8]** A. Kimmig, G. Van den Broeck, L. De Raedt. Algebraic Model Counting. <https://arxiv.org/abs/1211.4475>.

<a id="ref-darwiche"></a>

**[9]** A. Darwiche. On the Tractable Counting of Theory Models and its Application to Truth Maintenance and Belief Revision. <https://arxiv.org/abs/cs/0003044>.

<a id="ref-watrous"></a>

**[10]** J. Watrous. The Theory of Quantum Information (2018), Chapter 2. [作者公开预出版稿](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)。

<a id="ref-diosi"></a>

**[11]** L. Diósi. Anomalies of weakened decoherence criteria for quantum histories. Phys. Rev. Lett. 92, 170401 (2004). <https://arxiv.org/abs/quant-ph/0310181>.

<a id="ref-sorkin"></a>

**[12]** R. D. Sorkin. Quantum Mechanics as Quantum Measure Theory (1994). <https://arxiv.org/abs/gr-qc/9401003>.

<a id="ref-busch"></a>

**[13]** P. Busch. Quantum states and generalized observables: a simple proof of Gleason's theorem. Phys. Rev. Lett. 91, 120403 (2003). <https://arxiv.org/abs/quant-ph/9909073>.
