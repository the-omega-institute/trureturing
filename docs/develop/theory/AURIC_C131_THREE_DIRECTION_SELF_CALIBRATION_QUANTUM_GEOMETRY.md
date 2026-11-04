# 三向自校准

> 参考输入：AI 撰写的工作稿，由用户提供于本会话（2026-11-04，Asia/Singapore）。Lean 是仓库的数学真源；本文仅为参考文稿，未作形式化认证。

AURIC 量子关系研究

从同源实读重建量子几何

C131

一份关系，正着对照一次，

再把参照向左右各转一个直角。

这三种实读数，都不能为负。

$$
\boxed{\Re B(f,\zeta f)\ge0,\qquad
 f\in\mathbb Z[i]^{(X)},\quad \zeta\in\{1,i,-i\}.}
$$

$$
B(f,g)=\sum_{h,k}\overline{f(h)}K(h,k)g(k).
$$

原始输入为任意标签集 $X$ 与任意复数值二元表 $K$。
不用预给共轭对称、非负自读、Hilbert 空间或正单位。
三个固定相位的同源检查，等价于全部有限复正性。

本轮减少的是独立比较对象及检查形式。复数、共轭、实数序、
同核有限和及全部有限配方仍是前件；模型的物理实现另须内部证据。

固定源码：`2c54932b6f9a7eb9a838e5be71e91d97e10027be`
提交时点：2026-11-04 17:36:07，Asia/Singapore
相对 C130 新增 15 个可达提交；量子核心子树未变

自包含研究稿：定义、定理、证明、反例与精确几何

## 摘要与本轮的减法

C130 要比较任意两份独立配方，约束互读与两份自读的合计。本轮只取一份配方，
第二份由它作固定相位变化得到；每次仅检查一个互读实部。写 $B(f,f)=a+ib$，
三个读数为 $a,-b,b$，因此同时非负当且仅当 $a\ge0,b=0$。
这使全部高斯整数配方的自比较成为非负实数。再由两个基向量的有限组合恢复
Hermitian 性，以清分母和固定有限矩阵的连续性恢复全部复配方正性。

由正核的零差商构造比较 Hilbert 空间。相位操作 $J=i$ 在实化空间中与所得度量相容，
使 $u,Ju$ 等长且实正交，先得到一个圆。加入第二元 $v$ 后，$u,Ju,v$ 给出至多三个
实方向；若出现非零余向 $w$，要求对同一个 $J$ 闭合便必须补入 $Jw$，
形成最小的复二维空间。单位态球 $S^3$ 取公共相位商，才得到 Bloch 球面 $S^2$。

本轮还证明：在固定相位、单项实线性符号检查这一限定类别中，三个方向最少；
加入第四方向 $-1$ 反而只允许零核。精确零差能沿保留旧表的正核续写传播，
但当前观察窗口的不可分辨性可以被新增读口打破。最后将同一候选接入原矩阵过程、
完整效果及复合和时间接口，给出有限量子理论的条件性闭合。

正型核、Hilbert 表示、CP 表示及 Hopf 几何均有既有来源。
本轮交付是它们的一个更小检查入口及其完整推导，不宣称这些结构首次发现，
也不把定义某模型类当作已经证明自然界唯一属于它。

| 项目 | C130 | C131 |
|---|---|---|
| 原始对象 | $X$ 与任意复核 $K$ | 相同 |
| 独立配方 | 任意 $f,g$ | 只取一个 $f$ |
| 第二个输入 | 独立选择 | 固定为 $\zeta f$ |
| 单次检查 | 两个自读与一个互读的预算 | 一个互读实部的符号 |
| 相位检查 | 包含在全体配方对中 | 固定三个：$1,i,-i$ |
| 选择的模型类 | 复正型核 | 完全相同 |
| 仍未取消 | 复数、有限和、全部有限配方 | 同样保留 |

## 目录

- [1. 最新项目进展及本轮的准确起点](#section-1)
- [2. 唯一候选：一份配方的三向自校准](#section-2)
- [3. 从三向校准重建内积与接续](#section-3)
- [4. 从三个方向到圆与量子球面](#section-4)
- [5. 从三向自校准恢复有限量子规则](#section-5)
- [6. 把定义关系留在整体内部](#section-6)
- [7. 唯一候选、所得理论与未消去的前件](#section-7)
- [参考文献](#references)

<a id="section-1"></a>

## 1. 最新项目进展及本轮的准确起点

<a id="sec-c131-source"></a>

### 1.1 本轮固定的源码

本轮一次性核对默认分支 `dev`，固定 HEAD 为
`2c54932b6f9a7eb9a838e5be71e91d97e10027be`，
提交时点为 2026-11-04 17:36:07（Asia/Singapore），即 09:36:07 UTC。
相对 C130 的 `8e15c484cf57`，完整可达差集有 15 个新增提交，
其中默认分支第一父链为两次合并。关闭重命名推断的净树差分为 28 条路径，
其中 22 新增、2 修改、4 删除。量子及概念动力学子树均未变化 [1](#ref-repo-c131-pin)。

新增的两项实质主题是：

1. Ta 问题 11.6 的有限群反例。两群具有相同的阶、中心阶和共轭类数 $(64,4,22)$，
   但其完整 good-involution 函数计数分别为 $8\,847\,360$ 与 $2\,160\,000$。
   所计为全部函数，未按 quandle 同构取商 [2](#ref-repo-c131-ta)。

2. Giacomelli 的无穷对数凹初值锥。在文中声明的完整窗口、包含零层及零初值的定义下，
   齐次性保证非负缩放封闭，$H(x,t)=(1-t)x$ 将整个集合强变形收缩到零，
   从而可缩、道路连通且单连通 [3](#ref-repo-c131-giacomelli)。

第二项没有证明凸性，其收缩也不能直接移到去零、归一或射影后的空间。
它给本轮几何工作的一个方法提醒：先说清楚保留了哪些点、又取了什么商。
这只是方法上的联系；上述两个新增结果没有推导出本轮量子候选。
本轮进行了源码与证明文字核读，没有运行新的 Lean 构建，也没有向仓库写入 C131。

### 1.2 哪些结论项目早已有

V71 定义 5.2 与定理 5.3 已在固定 Hermitian 核及同一半双线性延拓下，
证明全部有限复合对象的二元正性、对角正性与全部有限 Gram 正性等价。
C114 定义 5.1、定理 6.1 已给递归二元兼容的等价形式；
第 7 节保留奇异 Schur 续写的值域条件 [4](#ref-repo-c131-v71)、[5](#ref-repo-c131-c114)。
这些等价和 Hilbert 表示不能重复算作本轮新发现。

C130 已将起点退到任意复核，并给一个实预算不等式。
C131 在相同起点上减少检查对象：每个检查只涉及 $f$ 与其三个固定相位版本之一。
下面会证明这与原来全体独立配方对的预算条件完全等价。
所谓更简洁，指这项明确的检查族压缩；它不降低数学模型的选择强度，
也没有证明跨所有语言、定义与逻辑的绝对最小公理。

### 1.3 从失败后果逆推三个方向

若同源自读有虚部，左右四分之一转所得实读必有一个为负；
若其没有虚部却为负，正向自读直接失败。
因此这三个方向分别承担不可互相删除的工作。
同时，对每一份有限配方都要检查：一个原始标签自读正常，
不保证多份历史合起来仍正常。二元法则作用在可合成的对象上，
并没有把原始支持大小限制为二。

把满足此关系的对象称为 C131 关系系统，是数学定义。
把实际控制、比较和记录识别成这样的系统，则需要证明它们满足同一有限和、
相位及读出关系。后文会分别写出这些接口，避免让“内生”承担未经证明的存在性。

**白话。**前一轮要把任意两份内容拿来对账；这一轮只让每份内容先和自己校准。
正着看要留非负的量，向左、向右各转一个直角，都不能留下负账。
左右的账本来互为相反，所以只能一起归零。复杂的互相比较随后由这件小事恢复。

<a id="section-2"></a>

## 2. 唯一候选：一份配方的三向自校准

<a id="sec-c131-core"></a>

### 定义 2.1（原始核与有限配方）

给定集合 $X$ 与任意复值二元核 $K:X\times X\to\mathbb C$，不预设 Hermitian 性、正性或物理态向量空间。令 $\mathcal R_0=\mathbb Z[i]^{(X)}$ 为有限支撑配方，定义

$$
B(f,g)=\sum_{h,k}\overline{f(h)}K(h,k)g(k),\qquad Q(f)=B(f,f).
$$

全部比较使用同一核、同一聚合公式。配方是有限代数写法，不自动供应原装置上的复制、相干制备或幅度放大。

### 定义 2.2（C131：三向自校准）

对每份 $f\in\mathcal R_0$，只取固定相位菜单 $\mathcal S=\{1,i,-i\}$，要求

<a id="eq-c131-candidate"></a>

$$
\boxed{\Re B(f,\zeta f)\ge0\qquad(\zeta\in\mathcal S).}
\tag{1}
$$

这是同一份配方与其三个指定版本之间的二元比较。没有独立的第二配方、增益参数、预算相减、正单位或追加次序。

### 定理 2.3（三向校准等价全部有限正性）

<a id="thm-c131-psd"></a>

C131 恰好选择 Hermitian 正型核：对任意有限列表，矩阵 $[K(h_j,h_k)]$ Hermitian 正半定。将配方系数扩为 $\mathbb Q(i)$ 或 $\mathbb C$，所得条件不变。零核与空标签集合均包含。

**证明。**
固定 $f$，写 $Q(f)=a+ib$。由聚合公式，三项实读数恰为

<a id="eq-c131-three-readouts"></a>

$$
\bigl(\Re B(f,f),\Re B(f,if),\Re B(f,-if)\bigr)
 =(a,-b,b).
\tag{2}
$$

三者非负迫使 $a\ge0,b=0$。所以全部整数配方的自比较都是非负实数。

单标签配方给实对角；$\delta_h+\delta_k$ 与 $\delta_h+i\delta_k$ 的实自比较分别给
$\Im(K(h,k)+K(k,h))=0$ 和 $\Re(K(h,k)-K(k,h))=0$，从而 $K(k,h)=\overline{K(h,k)}$。
对任意有限有理配方，用同一正整数 $N$ 清分母；$Q(Nf)=N^2Q(f)$，故非负实性延伸到有理系数。再在固定有限表上逐项用有理实、虚部逼近复系数。二次多项式连续，非负实轴闭，得到全部有限复二次型非负。此处没有给 $X$ 添加拓扑或实际连续控制。

反向，正型核使每个 $Q(f)=a\ge0$，三读数就是 $(a,0,0)$，故候选成立。

三实读数 $(a,-b,b)$ 在 $\mathbb R^3$ 中落在约束平面 $u+v=0$；该平面与非负正交象限的交，恰是 $(a,0,0)$、$a\ge0$ 的射线。这里仅有两个独立数，不是物理三维，也不表示三个独立实验资源。

### 2.1 为什么恰好保留这三个相位

### 命题 2.4（固定单项实探针类中的最小性）

<a id="prop-c131-minimal-probes"></a>

若探针限定为固定相位 $\zeta$ 的单项不等式 $\Re B(f,\zeta f)\ge0$，相位不依赖 $f,K$，则至少三种相位才能对所有核恰好选择正型核。这里计算的是此类不等式的数目，不是独立实数据量；结论不适用于含模、复射线条件或其他复合语法的任意公理。

**证明。**
只看单标签核 $q=a+ib$ 已足够。每个探针对应过原点的闭半平面 $\Re(\zeta q)\ge0$，所需交集是非负实射线。为保留 $q=1$，各探针须有 $\Re\zeta\ge0$。若至多两个探针中，有探针在 $q=1$ 处严格为正，则一个足够小的非实偏移仍可同时满足它们；若两者均在此处为零，它们只能沿两个虚相位，交集要么是半平面，要么是整条实轴，不能排除 $q=-1$。故两个不够。式 [(2)](#eq-c131-three-readouts) 已证明三个足够。

删去任一指定相位都有单标签反例：删 $1$ 时 $K=-1$ 通过；删 $i$ 时 $K=1+i$ 通过；删 $-i$ 时 $K=1-i$ 通过。
反过来，若再加入 $-1$ 并要求其读数也非负，就同时有 $a,-a,b,-b\ge0$，所以全部 $Q(f)=0$；极化于是给 $K=0$。不能把候选扩大成所有相位的实读数均非负。

配方内的相对复系数仍不能省掉。Hermitian 表

$$
G=\begin{pmatrix}1&2i\\-2i&1\end{pmatrix}
$$

对所有实整数配方的自比较为 $x^2+y^2$，三向检查全通过；但对复配方 $(1,i)$，自比较为 $-2$。固定三个外部探针相位没有取消完整配方内部的相对相位。

### 推论 2.5（严格失败具有有限整数见证）

<a id="cor-c131-finite-witness"></a>

每个非 Hermitian 或非正核，都存在有限整数配方 $f$ 和一个 $\zeta\in\mathcal S$，使 $\Re B(f,\zeta f)<0$。

**证明。**
非 Hermitian 时，单标签、两标签和或带 $i$ 的两标签和中，至少一个自比较非实；两个侧向探针之一便严格为负。Hermitian 非正时，一张有限表有严格负的复二次型方向；有理逼近保留负号，清分母后用 $\zeta=1$ 即得见证。

该结论没有统一的配方支持、整数大小或搜索成本保证。标准复数与共轭、同核有限和、全部有限配方及正实读出方向仍有内容；本轮压缩的是比较模板，未从无结构日志中选出复量子物理。

固定原始标签数也不能替代全部有限配方。对任意 $r\ge1$，令
$G=(2r+1)I_{r+1}-2J_{r+1}$，其中 $J$ 为全一矩阵。
任意 $m\le r$ 阶主块在全一方向的本征值为 $2r+1-2m\ge1$，
在其正交补上的本征值为 $2r+1$，
所以严格正定；全表却在全一向量上有本征值 $-1$。
这推广了项目 C114 例 6.3 的有限阶障碍 [5](#ref-repo-c131-c114)。
三种校准方向及后文的三实维图，都不能解释为只检验三个原始标签。

### 2.2 三读数误差的矩阵控制

### 定理 2.6（有限表的稳定版本）

<a id="thm-c131-stability"></a>

在一张固定有限表上，选系数欧氏范数，写 $G=H+iA$，其中
$H=(G+G^*)/2$、$A=(G-G^*)/(2i)$。对 $\varepsilon\ge0$，全部整数配方的三读数均至少为 $-\varepsilon\|f\|_2^2$，当且仅当

<a id="eq-c131-stability"></a>

$$
H\succeq-\varepsilon I,\qquad
 -\varepsilon I\preceq A\preceq\varepsilon I.
\tag{3}
$$

令 $H_+$ 为 $H$ 的谱正部，则
$\|G-H_+\|_{\rm op}\le2\varepsilon$，且 $H_+\succeq0$。

**证明。**
三读数分别为 $f^*Hf,-f^*Af,f^*Af$。对各自加上 $\varepsilon\|f\|^2$，清分母与有限表连续性将整数条件恰好转为三个 Hermitian 矩阵的正性，即式 [(3)](#eq-c131-stability)。谱分解给 $\|H-H_+\|\le\varepsilon$，另有 $\|A\|\le\varepsilon$，三角不等式给所示 $2\varepsilon$ 界；无需 $H,A$ 交换。

这里只给便利上界，不主张常数最佳。谱正部只修复当前有限表；不同窗口分别修复未必相容，也不自动保持原记录归一化、过程接续或实际装置实现。

若已认证 $\|G-\widehat G\|_{\rm op}\le\eta$，则因 $|\zeta|=1$，
$|\Re(f^*G\zeta f)-\Re(f^*\widehat G\zeta f)|\le\eta\|f\|_2^2$。
因此一个负读数超过这一误差界的具体配方，就稳健地否定该有限表。
上述全配方稳定定理则要求每个配方的齐次误差界，不能从三次孤立观测直接宣称。

**白话。**一份配方只对照三个版本：正向、左侧和右侧。两侧的实读数按同一计算规则互为相反数；都不越过零，就只能同时为零。正向留下非负读数。三向校准把此前借助任意增益才能看清的虚部，直接锁在这一份配方的内部比较里；整张关系表仍须让每份有限配方都能通过。

<a id="section-3"></a>

## 3. 从三向校准重建内积与接续

<a id="sec-c131-hilbert"></a>

正型核的 Hilbert 表示是成熟结构 [6](#ref-aronszajn1950)。下面从本轮定义直接构造，明确它何时只是数学表示。

### 定理 3.1（固定核中的零差商及最小表示）

<a id="thm-c131-hilbert"></a>

C131 成立后，构造自由复线性包络 $\mathcal F=\mathbb C^{(X)}$，沿用有限和 $B$，令 $\mathcal N=\{f:Q(f)=0\}$。则 $\mathcal N$ 为根空间，商 $\mathcal F/\mathcal N$ 具有内积，其完成 $\mathcal H$ 有稠密生成表示

$$
\iota(h)=[\delta_h],\qquad
 K(h,k)=\langle\iota(h),\iota(k)\rangle.
$$

同一核的最小表示唯一到保持标签的酉等价；零核给零空间，标签映射不必单射。

**证明。**
半双线性由有限和定义，Hermitian 正性由前节定理给出。若 $Q(f)=0$，对任意 $g,t$ 有
$Q(f+tg)=2\Re(tB(f,g))+|t|^2Q(g)\ge0$。选反号相位和足够小的 $t$，得到 $B(f,g)=0$。因此零集合恰为线性根空间，商内积良定义，完成后即得表示。

两份最小表示间，对同系数有限组合逐项对应；两边范数均由同一核计算，故零向量对应、映射良定义且等距。稠密性使它唯一延伸成酉算符。

这里的零差是当前固定核中的向量等价。从集合构造线性包络，不等于原装置已经能制备每个形式向量。原标签上的相干、乘法和过程身份，还要与核值逐项相容。

### 3.1 极化与 C130 的二元互读界

恢复一般的两配方互读时，有精确四项极化公式

<a id="eq-c131-polarization"></a>

$$
B(f,g)=\frac14\bigl[Q(f+g)-Q(f-g)
 -iQ(f+ig)+iQ(f-ig)\bigr].
\tag{4}
$$

前两项之差为 $2(B(f,g)+B(g,f))$，后两种自读之差为 $2i(B(f,g)-B(g,f))$，代回即得。三个自校准相位与四项极化公式负责不同任务，不能混算成三次读数已重建整张核。

对任意有限复配方，正性给

<a id="eq-c131-recovers-c130"></a>

$$
\Re Q(f)+\Re Q(g)-2\Re B(f,g)=Q(f-g)\ge0,
\tag{5}
$$

于是 C130 的全部独立二元预算约束成为后果。反向，若原整数配方满足 C130，写 $Q(f)=a+ib$；空配方给 $a\ge0$，对 $(nf,(n+i)f)$ 的预算差为 $a+2nb$。全部整数 $n$ 迫使 $b=0$，所以三向校准也成立。

同源侧移仅需作为推论保留：$\Re B(f,(1+in)f)=Q(f)\ge0$。它没有作为另一候选进入本轮。新条件直接使用固定侧向探针，省去这族无界增益量词；有限配方内部的无界整数系数仍未取消。

### 3.2 C129 的旧影子与奇异新余量

对旧列表追加一个标签，所得正表为
$\left(\begin{smallmatrix}G&b\\b^*&q\end{smallmatrix}\right)$。若 $u\in\operatorname{ker} G$，旧组合自比较为零，根空间性质使 $u^*b=0$，所以 $b\in\operatorname{Ran} G$。此时才取 $c=G^+b$；评价 $(-c,1)$ 得
$s=q-b^*G^+b\ge0$。选 $|r|^2=s$，恢复

<a id="eq-c131-recovers-c129"></a>

$$
G_{L+h}=\begin{pmatrix}
 G&Gc\\c^*G&c^*Gc+|r|^2
 \end{pmatrix}.
\tag{6}
$$

若 $G=0$，它先强制 $b=0$，再给 $q=|r|^2$；奇异旧表不能只检查伪逆余量而漏掉像空间条件。

反向，C129 的块式等于 $T^*\operatorname{diag}(G,|r|^2)T$，其中
$T=\left(\begin{smallmatrix}I&c\\0&1\end{smallmatrix}\right)$。从空表归纳即可得全有限正性，再由本轮定理恢复三向校准。新增影子与余量因而处在推论层，追加顺序未被用来先选正性。

在构造空间中，半双线性还直接给
$Q(a+tz)+Q(a-tz)-2Q(a)=2|t|^2Q(z)\ge0$，即 C128。候选仍允许零核；若原完整记录后来供应 $Q(e)=1$，两个零差之和不能成为 $e$，也恢复 C127。概率的一份一并未被预置在三向校准中。

**白话。**同一份配方的正读与侧读先自洽，所有配方才能共同放进一个正比较空间。当前固定核中的向量零差，在本核的全部比较中都不造成差别，把它合并就得到内积。随后，两份独立配方的互读预算、追加历史的旧影子和新余量、相反微移的合计读数，都能从这个空间重新计算出来。

<a id="section-4"></a>

## 4. 从三个方向到圆与量子球面

<a id="sec-c131-geometry"></a>

三探针在复读数平面上分别给 $p\ge0,-y\ge0,y\ge0$，其中 $Q(f)=p+iy$；交集是非负实射线。以下使用前文已构造的正核商空间 $\mathcal H$，内积对第一变量共轭线性。连续实系数与相位属于这个数学模型，实际控制仍须由原接口供应。

### 4.1 同一复方向中的实正交圆

令 $Ju=iu$，并把 $\mathcal H$ 看作实向量空间，定义 $g(u,v)=\Re\langle u,v\rangle $。$J$ 的存在来自复系数；三探针恢复它与正度量的相容关系。

### 命题 4.1（实相位平面）

有 $J^2=-I$、$g(Ju,Jv)=g(u,v)$ 及 $g(u,Ju)=0$。若 $u\ne0$，则 $u,Ju$ 实线性独立、等长且实正交；对 $a,b,\theta\in\mathbb R$ 有

<a id="eq-c131-phase-circle"></a>

$$
\|au+bJu\|^2=(a^2+b^2)\|u\|^2,
 \qquad
 u\cos\theta+Ju\sin\theta=e^{i\theta}u.
\tag{7}
$$

**证明。**
复乘法给 $J^2=-I$ 与 $\langle Ju,Jv\rangle =\langle u,v\rangle $；自比较已为实数，故 $\Re\langle u,iu\rangle =0$。展开实二次式即得等式。若 $(a+ib)u=0$ 且 $u\ne0$，则 $a=b=0$。

这个圆的全部点属于同一条复射线，$u$ 与 $iu$ 也并非复正交；在射线商中整圆只代表一点。它不能直接充当一圈不同的 Bloch 纯态。

所得内积还能写成 $\langle u,v\rangle=g(u,v)+i\omega(u,v)$，其中
$\omega(u,v)=g(Ju,v)=-\omega(v,u)$，且 $\omega(u,Ju)=\|u\|^2$。
距离部分与相位部分由同一个 $J$ 连接，未增加第二张独立的关系表。

对早先的 $a^2+xab+b^2=1$，$x=0$ 才是 $(a,b)$ 平面中的圆；
$x=2$ 时为 $(a+b)^2=1$，是两条直线。若在 $a^2+b^2=1$ 上另定义
$X=2ab$、$Z=a^2-b^2$，则 $X^2+Z^2=1$，而原二次读数变成
$1+(x/2)X$。交叉项是在提升后的关系坐标中成为线性读数，
不是 $ab$ 对原变量本身变成线性。

<a id="fig-c131-three-probes-window"></a>

```latex
\begin{tikzpicture}[font=\small,>=Latex,scale=1.12]
 \path[use as bounding box] (-0.25,-0.20) rectangle (12.20,4.45);
 \node at (2.05,4.12) {三探针截出正射线};
 \begin{scope}[xshift=2.05cm,yshift=2.05cm]
  \fill[blue!5] (-1.35,0) rectangle (1.80,1.35);
  \fill[orange!7] (-1.35,-1.35) rectangle (1.80,0);
  \fill[teal!8,opacity=0.50] (0,-1.35) rectangle (1.80,1.35);
  \draw[black!40,dashed] (0,-1.35)--(0,1.35);
  \draw[black!40,->] (-1.48,0)--(1.98,0) node[below] {$p$};
  \draw[black!40,->] (0,-1.48)--(0,1.58) node[right] {$y$};
  \draw[blue!65!black,thick,->] (0,0)--(0,0.86);
  \draw[orange!85!black,thick,->] (0,0)--(0,-0.86);
  \draw[teal!75!black,line width=1.35pt,->] (0,0)--(1.73,0);
  \fill (0,0) circle (1.5pt);
  \node[left,blue!65!black] at (-0.10,0.67) {$\zeta=-i$};
  \node[left,orange!85!black] at (-0.10,-0.67) {$\zeta=i$};
  \node[blue!65!black] at (0.94,1.05) {$y\ge0$};
  \node[orange!85!black] at (0.94,-1.05) {$y\le0$};
  \node[above,teal!75!black] at (1.07,0.11) {$\zeta=1$};
 \end{scope}
 \node at (2.05,0.23) {交集：$Q(f)\in\R_{\ge0}$};

 \node at (8.85,4.12) {三个实方向的关系窗口};
 \begin{scope}[xshift=8.20cm,yshift=1.10cm,
  x={(1cm,-0.25cm)},y={(0.55cm,0.35cm)},z={(0cm,0.90cm)}]
  \fill[teal!6] (0,0,0)--(1.85,0,0)--(1.85,1.60,0)--(0,1.60,0)--cycle;
  \draw[black!60,->] (0,0,0)--(2.20,0,0) node[above right] {$\hat u$};
  \draw[black!60,->] (0,0,0)--(0,2.25,0) node[below left] {$J\hat u$};
  \draw[black!60,->] (0,0,0)--(0,0,2.55) node[above] {$\hat w$};
  \draw[black!35,dashed] (1.20,0,0)--(1.20,0.80,0)--(0,0.80,0);
  \draw[black!50,->] (0,0,0)--(1.20,0.80,0);
  \draw[orange!85!black,thick,->] (1.20,0.80,0)--(1.20,0.80,1.65)
   node[midway,right] {$w$};
  \draw[teal!75!black,very thick,->] (0,0,0)--(1.20,0.80,1.65)
   node[above right] {$v$};
  \fill[black!60] (1.20,0.80,0) circle (1.4pt);
  \node[below right] at (1.20,0.80,0) {$v_\parallel$};
 \end{scope}
 \node[font=\footnotesize,align=center] at (8.85,0.12)
  {$Jw\perp\Span_{\R}\{u,Ju,w\}$\\第四实方向未画入此窗口};
\end{tikzpicture}
```

**图 1。**左图彩色箭头标出三个半平面的法向，粗水平射线才是允许读数的交集。右图取非退化情形，以单位方向 $\hat u=u/\|u\|$、$J\hat u$、$\hat w=w/\|w\|$ 作实正交轴；$v_\parallel$ 是 $v$ 在相位平面上的投影，橙箭头是平移后的残差 $w$。这些方向属于关系空间，并非物理空间。

### 4.2 二元关系、三实方向与最小复闭合

取非零 $u$ 与另一元 $v$，记 $p=\|u\|^2>0$、$q=\|v\|^2$、$\langle u,v\rangle =x+iy$。由于 $g(Ju,v)=y$，三元实 Gram 表为

<a id="eq-c131-real-three-gram"></a>

$$
G_{\mathbb R}(u,Ju,v)=
 \begin{pmatrix}p&0&x\\0&p&y\\x&y&q\end{pmatrix}\succeq0.
\tag{8}
$$

### 命题 4.2（三维窗口所需的第四方向）

令

$$
v_\parallel=\frac{x}{p}u+\frac{y}{p}Ju,
 \qquad w=v-v_\parallel,
 \qquad \delta=\|w\|^2=q-\frac{x^2+y^2}{p}\ge0.
$$

若 $\delta>0$，三实方向窗口 $W=\operatorname{span}_{\mathbb R}\{u,Ju,w\}$ 对 $J$ 不闭合；其最小 $J$ 闭合空间为

<a id="eq-c131-complex-closure"></a>

$$
W+JW=\operatorname{span}_{\mathbb R}\{u,Ju,w,Jw\}
 =\operatorname{span}_{\mathbb C}\{u,v\}\cong\mathbb C^2.
\tag{9}
$$

**证明。**
投影式给 $g(u,w)=g(Ju,w)=0$，勾股分解给 $\delta$。由 $g(Ja,b)=-g(a,Jb)$ 得 $Jw$ 与 $u,Ju,w$ 全部实正交，而 $\|Jw\|=\|w\|>0$。故它不能在 $W$ 内。补入 $Jw$ 后，$J$ 把四个方向分别配对，空间已经闭合；任何含 $W$ 的 $J$ 闭合空间都必须含 $Jw$。

若 $\delta=0$，两元只生成一个复方向，无需产生 $\mathbb C^2$；若 $u=0$，其比较与 $Ju$ 均为零，不能使用含 $1/p$ 的坐标。候选允许秩一模型及零模型，不强迫第二个独立复方向存在。

### 4.3 公共相位圆的商为何是球面

在 $\delta>0$ 时，以 $e_0=u/\sqrt p$、$e_1=w/\sqrt\delta$ 作复正交单位基。单位向量 $\psi=\alpha e_0+\beta e_1$ 满足 $|\alpha|^2+|\beta|^2=1$，构成四个实坐标中的单位态球 $S^3$。

### 命题 4.3（二元纯态的 Hopf 商）

映射

<a id="eq-c131-hopf-map"></a>

$$
h(\alpha,\beta)=
 \bigl(2\Re(\bar\alpha\beta),\,2\Im(\bar\alpha\beta),\,
 |\alpha|^2-|\beta|^2\bigr)=(X,Y,Z)
\tag{10}
$$

将 $S^3$ 满射到 $S^2$，其每条纤维恰是公共相位圆。因此 $S^3/U(1)\cong S^2$。这是标准的单量子比特 Hopf 几何 [7](#ref-mosseri2001)。

**证明。**
$X^2+Y^2+Z^2=(|\alpha|^2+|\beta|^2)^2=1$。
取 $\alpha=\cos(\theta/2)$、$\beta=e^{i\phi}\sin(\theta/2)$，像为
$(\sin\theta\cos\phi,\sin\theta\sin\phi,\cos\theta)$，遍历球面。
同一像固定 $|\alpha|^2=(1+Z)/2$、$|\beta|^2=(1-Z)/2$ 与 $\bar\alpha\beta=(X+iY)/2$。若 $\alpha\ne0$，先用公共相位匹配 $\alpha$，则 $\beta$ 也被固定；若 $\alpha=0$，有 $|\beta|=1$，整条纤维仍是一相位圆。另一极 $\beta=0$ 同理。反向公共相位显然不改变像；连续映射遂在紧商空间与 Hausdorff 球面间诱导同胚。

公共相位沿纤维移动，坐标不变；相对相位 $\phi$ 沿固定纬圈改变坐标，两极的相对相位无须定义。物理上把纯态识别为射线，依赖后文的一致效果评价，而不是仅凭图形宣布某种读出不可见。

### 4.4 混合球、原锥与方向边界

一般二阶 Hermitian 表有四个实坐标 $t,s_x,s_y,s_z$，并满足

<a id="eq-c131-positive-cone-ball"></a>

$$
A=\begin{pmatrix}t+s_z&s_x-is_y\\s_x+is_y&t-s_z\end{pmatrix},
 \qquad A\succeq0\ \Longleftrightarrow\ t\ge\|\mathbf s\|.
\tag{11}
$$

这由本征值 $t\pm\|\mathbf s\|$ 直接给出。若 $t>0$，令 $\rho=A/(2t)$、$\mathbf r=\mathbf s/t$，迹一截面就是 $\|\mathbf r\|\le1$ 的 Bloch 球，球面对应秩一，内部对应秩二 [8](#ref-arrighi2003)。对 $\rho=\lvert \psi\rangle \langle \psi\rvert $，这些坐标恰是上节的 $h(\alpha,\beta)$。
任意 $\mathbf r=R\mathbf n$、$0\le R\le1$ 都是对跖纯态 $\pm\mathbf n$ 按 $(1\pm R)/2$ 的凸组合；中心可任取单位 $\mathbf n$。实际供应这些混合还须原混合接口。原正锥的非零边界对应纯态；$t=0$ 强迫 $A=0$，保留为不能归一的锥顶。

复共轭交换两个侧探针；在式~[(10)](#eq-c131-hopf-map) 中它给 $(X,Y,Z)\mapsto(X,-Y,Z)$。候选仍成立，故没有选定物理空间手性或日志时间箭头。圆与平方因子使用了复乘法及共轭，不能把复标量的校准也算作本轮推出的事实。

**白话。**先看同一份内容朝自身、朝左侧、朝右侧的三个读数。三边都不许读出负数，左右两项便只能相互抵成零，自身留下非负的一项。于是同一复方向展开成两个实正交方向，等长走一圈就是圆。加入另一份内容，最多先看到三个实方向；若真多出第三个方向，同一个四分之一转还要求补上第四个。把两份内容共同转动的那一圈视作同一射线，剩下的关系便落到量子球面。

<a id="section-5"></a>

## 5. 从三向自校准恢复有限量子规则

<a id="sec-c131-quantum"></a>

三向自校准先恢复正核与比较空间。要接回原过程，须使用它实际对应的乘法、复线性、记录与联合接口；自由表的任意正完成不能替代这些关系。这里选择全复矩阵代数，是另一个明确的结构前件，不由 C131 单独产生。以下给一套有限复矩阵理论的条件性闭合，标准表示与概率定理有成熟来源 [9](#ref-watrous2018)、[10](#ref-busch2003)。

### 5.1 一张有限来源表选择完全正过程

### 定义 5.1（事件的原始核）

取 $d,m\ge1$。对仅给复线性的 $\Phi:M_d(\mathbb C)\to M_m(\mathbb C)$，以 $(a,u)\in M_d\times\mathbb C^m$ 为原始历史标签，定义

$$
K_\Phi((a,u),(b,v))=\langle u,\Phi(a^*b)v\rangle.
$$

不预设 $\Phi$ 保伴随、正、完全正或归一化。

### 定理 5.2（有限来源表的三向自校准与 CP）

<a id="thm-c131-cp"></a>

固定一来源行 $p$。以下等价：

1. 核 $K_\Phi$ 满足 C131；

2. 对有限列表 $((E_{pi},e_\mu))_{i,\mu}$，其每个高斯整数配方均通过三种相位的同源实读检查；

3. $\Phi$ 完全正。

成立后 $\Phi$ 自动保伴随，且存在 $d\times m$ 矩阵 $A_\alpha$，使

$$
\Phi(x)=\sum_\alpha A_\alpha^*xA_\alpha.
$$

**证明。**
该列表的比较表第 $((i,\mu),(j,\nu))$ 项为
$\langle e_\mu,\Phi(E_{ij})e_\nu\rangle$，即 Choi 表 $C_\Phi=[\Phi(E_{ij})]$。
由三向自校准与正核的等价，(2) 恰要求 $C_\Phi\succeq0$。
将其分解为 $\sum_\alpha w_\alpha w_\alpha^*$，写
$w_\alpha=\sum_i e_i\otimes A_\alpha^*e_i$，比较各块即得 Kraus 式；它的每一级矩阵放大都将正矩阵送到正矩阵，所以给 (3)。
CP 反向作用于任意正块表 $[a_i^*a_j]$，再用向量族评价，得到

$$
\sum_{ij}\bar z_i K_\Phi((a_i,u_i),(a_j,u_j))z_j\ge0.
$$

于是全核正，三向等价定理给 (1)；(1) 显然给 (2)。

在核商空间上令 $\pi(x)[a,u]=[xa,u]$。它保零差，因为
$\langle\pi(x)h,k\rangle=\langle h,\pi(x^*)k\rangle$。
取 $b=(\|x\|^2I-x^*x)^{1/2}$，有
$\|x\|^2Q(h)-Q(\pi(x)h)=Q(\pi(b)h)\ge0$，故有界。
核公式也保证 $Vu=[I,u]$ 对 $u$ 线性，直接得到

$$
\Phi(x)=V^*\pi(x)V.
$$

这里 $V$ 不必等距；单位效果未归一时不能补出等距结论。零映射使用零比较空间及空 Kraus 和，也满足本轮候选。

### 5.2 完整记录、Born 与读后态

### 命题 5.3（原记录的归一化）

若原事件族 $\Phi_j:M_{d_j}\to M_m$ 各满足候选，并另有完整记录约束 $\sum_j\Phi_j(I)=I$，则态方向过程

$$
\mathcal T_j(\rho)=\sum_\alpha A_{j\alpha}\rho A_{j\alpha}^*,
 \qquad \sum_{j,\alpha}A_{j\alpha}^*A_{j\alpha}=I
$$

构成完整 CP 仪器。各支迹不增，总输出保迹。

**证明。**
令 $E_j=\Phi_j(I)=\sum_\alpha A_{j\alpha}^*A_{j\alpha}\ge0$，则
$I-E_j=\sum_{k\ne j}E_k\ge0$。迹循环给 $\operatorname{Tr}\mathcal T_j(\rho)=\operatorname{Tr}(\rho E_j)$，即得支迹界与总保迹。

概率本身需要一致的效果评价。对全部 $0\le E\le I$ 给 $p(E)\ge0$，满足 $p(I)=1$，且 $E+F\le I$ 时 $p(E+F)=p(E)+p(F)$；同一效果在不同完整测试中赋同值。

### 定理 5.4（效果评价与纯态）

该评价唯一为 $p(E)=\operatorname{Tr}(\rho E)$，其中 $\rho\ge0,\operatorname{Tr}\rho=1$。
密度态的极点恰是秩一态；对归一纯态与秩一投影有 $p=|\langle\varphi,\psi\rangle|^2$。

**证明。**
可加性给有理齐次性，非负性给单调性，有理夹逼给实齐次性。对 $B\ge0$，以 $s>0,s\ge\|B\|$ 定义 $f(B)=s\,p(B/s)$，它与 $s$ 无关且在正锥可加。由正负分解延伸为 Hermitian 空间上的实线性泛函；有限迹配对给唯一 Hermitian $\rho$，正性与归一分别给 $\rho\ge0$ 和迹一。
秩至少二时可反向微调两个正谱权，得非平凡凸分解；秩一态的正分解只能支持同一射线，故它是极点。对两个秩一矩阵直接相乘取迹，即得 Born 平方律。相同纯态的归一向量只差整体相位。

该全效果版本包括二维 [10](#ref-busch2003)。候选未自动供应全部物理效果。
原支有 $p_j=\operatorname{Tr}(\rho E_j)$；仅当 $p_j>0$ 时定义 $\rho_j=\mathcal T_j(\rho)/p_j$。
若同空间支效果为投影 $P$，且保持 $\operatorname{Ran} P$ 内每条纯射线，则得到 Lüders 更新：$P=0$ 时所有 Kraus 项为零；$P\ne0$ 时效果先给 $A_\alpha(I-P)=0$，射线保持使每个 $A_\alpha v$ 与 $v$ 共线。对基向量及两两和应用，得 $A_\alpha=c_\alpha P$。效果给 $\sum|c_\alpha|^2=1$，故 $\mathcal T(\rho)=P\rho P$。仅有结果可重复性不排除结果子空间内的旋转。

### 5.3 可观测量、不确定界与独立复合

有限锐测量由正交投影 $\sum_iP_i=I$ 和实结果 $a_i$ 给自伴算符 $A=\sum_i a_iP_i$，反向由有限谱分解得到。其期望为 $\operatorname{Tr}(\rho A)$。
对自伴 $A,B$ 中心化为 $A_0,B_0$，在算符历史上用
$\Gamma_\rho(X,Y)=\operatorname{Tr}(\rho X^*Y)$。二元 Gram 行列式非负给

$$
\operatorname{Var}_\rho(A)\operatorname{Var}_\rho(B)
 \ge |\operatorname{Tr}(\rho A_0B_0)|^2
 \ge\tfrac14|\operatorname{Tr}(\rho[A,B])|^2.
$$

第二步保留复数的虚部。具体位置、动量及交换常数并非三向自校准选出；无限维无界算符还需定义域等独立条件。

若 $M_d,M_m$ 保单位保星地嵌入同一非零联合代数，两像交换并共同生成，则
$a\otimes b\mapsto\iota_A(a)\iota_B(b)$ 是满的保单位星同态。定义域 $M_d\otimes M_m\cong M_{dm}$ 简单：非零理想经矩阵单位左右相乘即含全部矩阵单位。故核为零，给张量联合。
CP 串接与并接的 Kraus 族分别为 $B_\beta A_\alpha$ 与 $A_\alpha\otimes B_\beta$。完整局部保迹过程不改变另一侧边缘，因为其伴随把 $I\otimes E$ 送回 $I\otimes E$。条件于特定结果时，边缘可变，所选标签的信息不能丢去。

### 5.4 可逆、时间及物理接口

### 命题 5.5（同维可逆过程与时间群）

同维 CPTP 过程若有 CPTP 左逆，则为酉共轭。若再给连续一参数 CPTP 群，则存在自伴 $H$，使

$$
\mathcal T_t(\rho)=e^{-itH/\hbar}\rho e^{itH/\hbar},
 \qquad i\hbar\dot\rho=[H,\rho].
$$

**证明。**
两过程的 Kraus 族记为 $A_i,B_j$。恒等通道 Choi 秩一给 $B_jA_i=c_{ji}I$。
对一个非零 $A_i$，逆过程保迹保证至少一个乘积非零；同维使相应 $B_j$ 可逆，从而所有 $A_i$ 共线。合并成一个 $A$ 后，保迹给 $A^*A=I$，方阵即酉。
有限维连续群写为 $e^{t\mathcal L}$；酉共轭性使生成元为保星导子。取 $D=\sum_k\mathcal L(E_{k1})E_{1k}$，导子律给 $[D,E_{ij}]=\mathcal L(E_{ij})$；保星性使 $D+D^*$ 为中心。换成反自伴部分并写成 $-iH/\hbar$，得到公式。

选定纯态相位代表后有 $i\hbar\dot\psi=H\psi$。具体钟、生成元与 $\hbar$ 标定并非原始核给出的事实。内积、正过程、完整概率、独立联合与时间的来源必须逐层对应。

| 通常规则 | 本轮推导与保留条件 |
|---|---|
| Hilbert 与叠加 | 正核的自由复包络及零差商；实际叠加仍须原控制接口。 |
| CP 与过程表示 | 指定复线性矩阵事件的来源核；有限 Choi 表上每个整数配方的三种相位检查。 |
| 概率与仪器 | 全效果一致可加评价；原完整记录归一化。 |
| 测量更新 | 已给 CP 仪器；逐射线保持时才选出 Lüders。 |
| 复合与局部性 | 交换且共同生成的独立子代数；完整局部保迹。 |
| 酉与时间 | 同维 CPTP 左逆；连续群和另行标定的物理时钟。 |

**白话。**三个固定相位的同源实读都不为负，先选择正比较表；接上原过程的乘法与复线性，就选择完全正过程。完整记录给归一化，一致的效果赋值给 Born 规则，独立联合和可逆时间再给张量与酉演化。每一步都来自具体内部关系；公式更短，并没有免除这些关系实际存在的要求。

<a id="section-6"></a>

## 6. 把定义关系留在整体内部

<a id="sec-c131-internal"></a>

三向自校准给出可用来比较关系的正空间。下面说明已经声明的线性关系如何成为
核内部的有限条件，以及不同观察窗口能在什么前提下接成同一结构。
此处的结论不要求某个观察者已经读完整个整体。
下文 $B(k,r)$ 与 $Q(k)$ 分别是 $B(\delta_k,r)$ 与 $Q(\delta_k)$ 的简写。

### 6.1 一条定义关系的零差证书

### 定理 6.1（固定核中的关系证书）

<a id="thm-c131-zero-relation"></a>

设 $K$ 满足 C131。对有限复配方 $r=\sum_j c_j\delta_{h_j}$，以下等价：

1. $Q(r)=0$；

2. $\sum_j c_j\iota(h_j)=0$；

3. 对全部 $k\in X$，$\sum_j c_jK(k,h_j)=0$。

若一个更大正核精确保留这些旧标签间的全部核值，则该关系在更大核的表示中仍成立。

**证明。**
前两项等价于该向量的平方范数为零。第二项取与 $\iota(k)$ 的内积得到第三项。
反向用 $r$ 的有限系数合成第三项，得到 $Q(r)=0$。
扩张若保留旧表，计算 $Q(r)$ 所需的每个数都保持原值；
新核的正性再使这个零范数向量与全部新标签正交。

例如声明 $h_3=\alpha h_1+\beta h_2$ 在比较空间中的意义，
就是对 $r=\delta_{h_3}-\alpha\delta_{h_1}-\beta\delta_{h_2}$ 要求 $Q(r)=0$。
这把一个向量定义关系写成有限子表上的核约束。
它没有由 C131 自动证明任意预想关系都成立；该零值仍需实际来源或数学证明。
若 $\alpha,\beta$ 不是高斯整数，这里使用的是已经重建的复延拓，
不能反称原观察者已经供应了相应物理控制。

在精确正核下，若仅能证明 $0\le Q(r)\le\varepsilon$，Cauchy–Schwarz 给

$$
|B(k,r)|\le\sqrt{Q(k)\,\varepsilon}.
$$

只有把测试域限定为 $Q(k)\le1$ 时，才得到统一的 $\sqrt\varepsilon$ 界。
小误差不等于精确等同，也不在无界测试域中给统一误差。

### 6.2 当前不可分辨，不等于在所有读口下相同

上一定理要求*保留旧表的核扩张*。新增读口若改变了旧历史的比较值，
就不是这一种扩张。取实际向量 $v_a=e_1$、$v_b=e_1+e_2$，
旧读口 $P$ 只投影到 $e_1$，新读口为恒等：

$$
K_{\rm old}=
 \begin{pmatrix}1&1\\1&1\end{pmatrix},
 \qquad
 K_{\rm new}=
 \begin{pmatrix}1&1\\1&2\end{pmatrix}.
$$

两表都满足 C131，但 $Q_{\rm old}(\delta_b-\delta_a)=0$、
$Q_{\rm new}(\delta_b-\delta_a)=1$。原来的盲向被新读口看见，
并没有违反零差传播定理，因为旧的 $(b,b)$ 条目已经改变。
保留旧报告和新增信息，与坚持同一张固定比较表，是不同要求。

若标签是门程序，固定源的向量关系也不能升级为程序对所有输入的恒等式。
定义源核 $K_\Omega(A,B)=\langle A\Omega,B\Omega\rangle$。
设 $\Omega=\lvert 0\rangle $，则 $I\Omega=Z\Omega$，相应源核中 $Q_\Omega(I-Z)=0$；
然而 Hadamard 门 $H_{\rm Had}$ 给
$IH_{\rm Had}\Omega=\lvert +\rangle $、$ZH_{\rm Had}\Omega=\lvert -\rangle $。
同一源上的输出相同，不能识别全部右侧输入上下文。
若输入空间有限维，要认证算符 $A=B$，一种充分的有限条件是：
在一组张成输入空间的源向量上，逐一认证 $Q_{\Omega_j}(A-B)=0$。
此时 $(A-B)\Omega_j=0$ 对一组基成立，由线性性才推出算符恒等。

### 6.3 内部接续如何成为算符

### 命题 6.2（保核动作的表示）

若原幺半群 $M$ 作用于 $X$，并有
$K(a\cdot h,a\cdot k)=K(h,k)$，则
$T_a\iota(h)=\iota(a\cdot h)$ 给最小比较空间上的等距表示。
若动作 $a$ 在原系统中有逆，则 $T_a$ 为酉。

**证明。**
对任意有限组合，保核等式使作用前后平方范数相同，
所以保持根空间、下降到商并等距延拓到完成。
原标签上的乘法律给 $T_aT_b=T_{ab}$；逆动作给双侧逆，等距因而满射。

这恢复 V71 第 7 节的动作重建 [4](#ref-repo-c131-v71)。
有序追加本身不供应逆：取 $X=\mathbb N_0$、$K(m,n)=\delta_{mn}$，
加一重建为 $Se_n=e_{n+1}$。它保持范数，像却不含 $e_0$，所以不是酉算符。

### 6.4 有向相容的有限关系，可以拼接

### 定义 6.3（有向的内部比较系统）

取非空有向偏序集 $I$。给集合 $X_\alpha$，满足
$\alpha\le\beta\Rightarrow X_\alpha\subseteq X_\beta$，
并令 $X=\bigcup_\alpha X_\alpha$。
各 $X_\alpha$ 上给满足 C131 的核 $K_\alpha$。
对每个 $\alpha\le\beta$，要求
$K_\beta|_{X_\alpha\times X_\alpha}=K_\alpha$。
这是实际提供的相容数据；不是从没有共同读口的孤立记录中推断出来的。

### 定理 6.4（关系与比较空间的有向拼接）

<a id="thm-c131-gluing"></a>

上述系统唯一决定一个限制为各 $K_\alpha$ 的全局核 $K$；
$K$ 满足 C131。其最小比较 Hilbert 空间，是各局部最小比较空间在保核等距嵌入下的完成。

**证明。**
任意两标签都属于某个共同上界的集合，用其中核值定义 $K(h,k)$。
两个不同选取再有共同上界，限制相容性使定义无歧义。
每份配方仅有有限支持；有限多个指标有共同上界，所以整份配方及三种相位检查
都在一个 $X_\gamma$ 内完成。其非负性给全局 C131。
局部向量的同核有限和范数在嵌入时不变，零差因而保持，
各局部表示等距进入全局表示。它们的并的线性包络含全部标签向量，
在全局最小空间中稠密，完成后得到所称空间。

若没有包含每个有限配置的共同上界，仅有重叠处相同仍不够：
三标签表 $2I_3-J_3$ 的每个二阶主块都正，却在全一向量上给 $-3$。
这些两点窗口无法成为一个全部正的共同表。

因此，可以把已经给出的相容关系整体记为
$\Omega_{\rm rel}=(X,K,\text{已认证的结构关系})$。
这是一个数学结构的记号，不自动是归一量子态；
正归一状态、单位源以及具体动力学还须相应接口。
固定整个核后的最小表示酉等价唯一，不表示不同的兼容核只有一个。

### 6.5 两个观察者的未知交叉关系

若观察者 A 仅有 $K(a,a)=1$，B 仅有 $K(b,b)=1$，共同核可以是

$$
G_z=\begin{pmatrix}1&z\\\bar z&1\end{pmatrix},
 \qquad |z|\le1.
$$

所有这些核都满足 C131，且给相同的各自读数。
取 $z=0$，两位观察者的代表向量张成正交直线；取 $z=1$，
它们在零差商中成为同一向量。未知的是重建后可见子空间或共同内容的交集，
不是已经写明的标签集合交集。共同的内部比较可以增加约束，
单靠各自自读不能确定交集。

在已给的同一空间中，若认证的可见闭子空间
$\mathcal H_n\subseteq\mathcal H_{n+1}$，记其投影为 $P_n$，则对固定目标 $v$，

$$
\|v-P_nv\|^2-\|v-P_{n+1}v\|^2
 =\|(P_{n+1}-P_n)v\|^2\ge0.
$$

令 $\mathcal H_\infty=\overline{\bigcup_n\mathcal H_n}$。取有限窗口向量逼近
$P_\infty v$ 并用投影最小距离性，得到 $P_nv\to P_\infty v$。
这是可回答问题的逼近；任意量子门序列并不因此收敛到同一个态。
若每个窗口含源向量 $\xi$，则 $P_n\xi=\xi$，源本身不需要不断补长。

### 6.6 日志方向与相位方向

两侧探针 $i$ 与 $-i$ 是相位选择，不是把真实日志向前、向后播放。
对于共轭核，有

$$
B_{\bar K}(f,g)=\overline{B_K(\bar f,\bar g)}.
$$

由于 $\{1,i,-i\}$ 在共轭下不变，C131 对整体复共轭相容；
两个侧读口互换并不选择绝对手性。档案若按保留式协议追加，
它的前缀关系可提供时间方向，但这个协议不由三向实读单独推出。

若 $K_{12}K_{23}K_{31}\ne0$，其相位在每个标签分别重定相位后不变，
因为三个端点的相位因子成对抵消；全局共轭使它反号。
这种三元环携带的是相对复定向，不能据此识别物理空间宇称或弱相互作用手性。
同样，$i$ 与 $-i$ 不是两种粒子的标号。

**白话。**每条定义都可以拿它的两边相减，问剩下的差在共同关系表里是否真为零。
如果精确为零，任何保留这张旧表的合法续写都不能让它重新有量。
但一个观察者暂时看不出的差，可能在新的读口下出现；那是它先前看得不全。
两个观察者可以靠内部共同记录拼接关系，只有它们自己的记录时，
同一条线还是两条不同的线，仍然不能由空白处猜出来。

<a id="section-7"></a>

## 7. 唯一候选、所得理论与未消去的前件

<a id="sec-c131-close"></a>

本轮只提出一个候选：

$$
\boxed{
 \Re\sum_{h,k}\overline{f(h)}K(h,k)\,\zeta f(k)\ge0,
 \quad f\in\mathbb Z[i]^{(X)},\quad\zeta\in\{1,i,-i\}.
 }
$$

其数学后果已经闭合为：全部有限正核、零差商及最小 Hilbert 表示；
同源圆和二元三实窗口；有需要时的最小复二维闭合及 Bloch 几何；
保核作用的表示；固定旧核关系的传播与有向拼接。
接入已声明的复矩阵过程、全效果评价、完整记录、独立联合及可逆时间后，
有限 CP 仪器、Born 规则、张量复合、Lüders 的条件性更新和 Schrödinger 型演化随之恢复。

这些连接闭合了上述有限维理论的状态、过程、测量、复合与可逆时间规则。
“条件性”有具体内容：复数及相位规则没有从无结构集合中生出；
形式配方不自动成为实验控制；选择全复矩阵代数、完整效果与具体时间运动，
都不由该核约束单独决定。经典可交换模型和秩一模型也满足它。
此外尚未从这里推出相对论性场、粒子种类、规范群、耦合或基本常数。
用定义记下内部约束，并不取消这些约束被物理实现的证明义务。

### 本轮完整白话

把一份已经组合好的历史当成同一个参照：先正着和自己对照，再把参照向左、
向右各转一个直角。这三种对照的实读数都不能为负。左右两笔本来一正一反，
所以只能同时为零；正着留下来的才是这份历史的量。
若这份量非零，它和自己的转向版本形成两个等长的实直角方向，一个圆就出来了。
再拿另一份历史来，先扣掉它在这个圆平面上的影子，
剩下的若不为零，就添出第三个方向；让这个新方向也服从同一个转向规则，
还要补出第四个方向。四个实方向组成最小的复二维空间，
先把总量归一，再把整体一起转动的同一圈视为同一个纯态，才得到熟悉的量子球面。
所有有限历史都用同一办法比较，它们就能接入一个共同的正空间。
观察者只读到自己有依据的那部分；有了共同记录才能继续接，
没读到的交叉关系仍然留空。正性、相位与续写因此被写成内容之间可以核对的关系，
实际世界为什么提供这些关系，则仍要由内部的控制和记录来回答。

<a id="references"></a>

## 参考文献

<a id="ref-repo-c131-pin"></a>

### [1]

The Omega Institute, *trureturing*, immutable commit
[2c54932b6f9a7eb9a838e5be71e91d97e10027be](https://github.com/the-omega-institute/trureturing/commit/2c54932b6f9a7eb9a838e5be71e91d97e10027be)。
2026-11-04 09:36:07 UTC，17:36:07 Asia/Singapore。
相对 C130 固定提交的可达增量为 15；第一父链增量为两次合并。
本轮核对实际树差分及下述材料，没有运行新的 Lean 构建。

<a id="ref-repo-c131-ta"></a>

### [2]

The Omega Institute,
*The three invariants do not determine the good-involution count*。
[固定快照 Blueprint](https://github.com/the-omega-institute/trureturing/blob/2c54932b6f9a7eb9a838e5be71e91d97e10027be/Blueprint/D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation.md)，定义 1.1–1.2、定理 1.3、1.5。
两原生半直积及完整函数计数的源码定位；不声称本轮重做形式验证。

<a id="ref-repo-c131-giacomelli"></a>

### [3]

The Omega Institute,
*Giacomelli's full cone of infinitely log-concave initial data*。
[固定快照全文](https://github.com/the-omega-institute/trureturing/blob/2c54932b6f9a7eb9a838e5be71e91d97e10027be/docs/develop/theory/GIACOMELLI_INFINITE_LOG_CONCAVITY_CONE_CONTRACTION.md)，定义 1.1–1.3、定理 2.1。
本轮全文核读。完整窗口、包含零层及零点是其明确条件；
收缩不证明凸性，也不直接迁移到归一或射影空间。

<a id="ref-repo-c131-v71"></a>

### [4]

The Omega Institute,
*AURIC Universal Binary Relation Kernels, Quotient Residuals and Unbounded Recursion V71*。
[固定快照全文](https://github.com/the-omega-institute/trureturing/blob/2c54932b6f9a7eb9a838e5be71e91d97e10027be/docs/develop/theory/AURIC_UNIVERSAL_BINARY_RELATION_KERNELS_QUOTIENT_RESIDUALS_AND_UNBOUNDED_RECURSION_V71.md)。
定义 5.2、定理 5.3 为既有正核等价；第 6–7 节为奇异续写与历史作用重建。
与 C130 已读内容相同，本轮再次核对最接近的第 5 节及相关前件。

<a id="ref-repo-c131-c114"></a>

### [5]

The Omega Institute,
*AURIC Quadratic Readout and Recursive Relational Compatibility C114*。
[固定快照全文](https://github.com/the-omega-institute/trureturing/blob/2c54932b6f9a7eb9a838e5be71e91d97e10027be/docs/develop/theory/AURIC_QUADRATIC_READOUT_AND_RECURSIVE_RELATIONAL_COMPATIBILITY_C114.md)。
定义 5.1、定理 6.1、例 6.2–6.3；第 7 节续写保留值域条件。
原相干、混合、参考、独立联合及仪器接口仍属明确前件。

<a id="ref-aronszajn1950"></a>

### [6]

N. Aronszajn, *Theory of reproducing kernels*,
*Transactions of the American Mathematical Society* **68**(3), 337–404 (1950).
[原始论文扫描件](https://pages.stat.wisc.edu/~wahba/stat860public/pdf2/aronszajn.pdf)；
[doi:10.1090/S0002-9947-1950-0051437-7](https://doi.org/10.1090/S0002-9947-1950-0051437-7)。
正核与 Hilbert 表示的经典来源；本稿给出所用构造的自包含证明。

<a id="ref-mosseri2001"></a>

### [7]

R. Mosseri and R. Dandoloff,
*Geometry of entangled states, Bloch spheres and Hopf fibrations* (2001).
[arXiv:quant-ph/0108137v1](https://arxiv.org/pdf/quant-ph/0108137)，第 2 节。
公共相位圆纤维与单量子比特球面对应。
本文准确区分整个 Hilbert 空间与其中的单位态球 $S^3$。

<a id="ref-arrighi2003"></a>

### [8]

P. Arrighi and C. Patricot,
*A note on the correspondence between qubit quantum operations and special relativity* (2003).
[arXiv:quant-ph/0212135v3](https://arxiv.org/pdf/quant-ph/0212135)，第 I 节、Lemma 1。
二阶 Hermitian 正锥与四维 Lorentz 锥的坐标对应；
本文不据此推出物理时空或运动。

<a id="ref-watrous2018"></a>

### [9]

J. Watrous, *The Theory of Quantum Information*, Cambridge University Press (2018).
[作者公开第 2 章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)，Theorem 2.22。
有限 Choi、Kraus、Stinespring 等价；正文另证明三向同源条件如何接入原过程核。

<a id="ref-busch2003"></a>

### [10]

P. Busch, *Quantum states and generalized observables: a simple proof of Gleason's theorem*,
*Physical Review Letters* **91**, 120403 (2003).
[arXiv:quant-ph/9909073v3](https://arxiv.org/pdf/quant-ph/9909073)。
全效果一致可加评价的密度算符表示，包括二维。
完整效果、正性、可加性及归一化不能省去。
