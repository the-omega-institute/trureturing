<a id="manuscript-title"></a>
# AURIC：存在量词、平方权重<br>与提示误差的关系结构

定义、定理与纸面证明　v47.0

2026 年 10 月 31 日　Asia/Singapore

**原稿元数据。** 文档标题：AURIC：存在量词、平方权重与提示误差；作者署名：AURIC research continuation；主题：Semiring recursion, phase-invariant orthogonal weights, Fisher geometry and prompt risk。原页眉：AURIC：存在量词、平方权重与提示误差；v47 / 2026-10-31。原页脚为页码；原稿指定 XeLaTeX、两次编译及可选 Noto CJK 字体路径。

**原作者陈述的归属。** 以下摘要、正文、附录和文献中的“本文”“本轮”、纸面证明、源文读取范围、历史与 diff／blob 核对、API 限流和 PDF 编排用途均保留原作者陈述，不因转写成为本 Markdown 的独立认证。“编者适用条件注”单独列出，不属原稿。转写源为完整外来 TeX：42,989 UTF-8 字节，SHA-256 <code>95e9862e8a50acf27ac68287<wbr>73bbb5186d254c99dfc02e05<wbr>4f2b16fef2d77c9d</code>。

<a id="abstract"></a>
## 摘要

本文继续检验“加乘递归、二元关系、存在量词、复平面与归一化共同选择平方概率”的直觉。
有限半环推前统一描述存在、计数、非负质量和相干振幅，但这些标量语义不能互换；
存在性只保留支撑，复相消则阻止振幅通过保持全部加乘的映射成为非负概率。
连续正乘性只选择幂律，归一化本身允许任意正指数。
本文将项目既有平方定理的前提压缩为：在至少复二维的整个分支向量域上，
全局相位不变、正交可加、非负和一个单位标定已经推出平方范数，无须另设径向性或连续性。
五模式 AURIC 的三个边缘量与一个联合量，和二态射影的三个 Bloch 坐标分别定型。
最新项目的保留记录切口说明：归一化后射线会漏掉预测所需的关系参数，
连续摘要响应因此可有严格的统一误差底。
对机器学习，本文证明参数冗余、softmax 商结构和
“实际风险变化等于负条件信息增益加模型失配变化”；
再通过 KL 局部展开、Fisher 平方根提升及概率–相位度量连接经典统计与量子几何。
所有数学为纸面推导，没有运行数学数值、枚举、CAS、Lean 或神经网络实验。

<a id="section-1"></a>
## 1. 主张、项目快照与内生解释约定

本轮最重要的结论是：

> 归一化有很多方案。平方的唯一性来自更强的关系相容要求：
> 同一个非负总权重必须与全部正交分解一致，并对整体相位不敏感。
> 加乘递归传递已经指定的结构；存在量词和归一化本身不选择它。

对于机器学习，相应结论是：
提示提供的信息、提示改变的任务和模型利用信息的误差，应分别刻画。
“输出归一化”不等于“参数归一化”，也不保证实际预测误差单调下降。

本轮固定仓库 `the-omega-institute/trureturing` 的 `dev` 提交：
<code>6984386a601c1bed4fbcc1e2<wbr>885c1150b1138586</code>。
 提交时间为 2026-10-31 18:57:55（新加坡）。
相对上一轮固定提交
<code>02c695f8c17e35965f806034<wbr>27074b1dd434eed9</code>，
 官方比较 diff 的 theory 路径只有两项变化：
既有 V44 边界图册的项目转写，以及原生终端卷 RRO 严格追加的
§§28–33。量子原则续卷 III 的 §§173–176 本轮未变。
［[1](#ref-head)，[2](#ref-compare)，[5](#ref-rro)，[6](#ref-iii)］

本文承接“唯一极限静态整体”的解释框架：
输入、参数、观察者、随机种子、提示、时钟、记录和辅助寄存器均为该整体内部的对象。
条件概率是在整体的给定权重上，按内部记录作限制；
本文没有引入本体外部的观察者、环境或时间。
这个内生解释本身尚未指定概率权重、复域、正核或酉动力学，
因此这些结构将作为明确的数学前件，而不从“整体唯一”直接推出。

证明身份分三类：项目来源已有结论、本文给出的自足数学推导、以及仍需物理或算法前件的解释。
本文不主张半环、Fisher 几何、条件熵或正交可加理论的全球原创性；
本轮推进在于把这些接口精确连接，并缩减一个平方定理的前提。

<a id="section-2"></a>
## 2. 先区分：二元关系、二维坐标与概率归一化

<a id="statement-2-1"></a>
#### 定义 2.1（三种不同的二元性）

二元关系是 $R\subseteq X\times Y$，意指有两个自变量；
实二维向量空间有两个独立实坐标；
二态复量子系统则以 $\mathbb C^2$ 为振幅空间。
关系的元数、坐标的维数和量子基态数是三个不同量。

<a id="statement-2-2"></a>
#### 命题 2.2（二元核可以需要任意高维）

对任意 $N\ge1$，二元核 $K(i,j)=\delta_{ij}$ 的最小 Gram 实现维数为 $N$。

**证明。**
若 $K(i,j)=\langle v_i,v_j\rangle$，则 $v_1,\ldots,v_N$ 是非零两两正交向量，
因而线性独立，维数至少 $N$；标准基达到该维数。

∎

所以“关系都是二元的”并不蕴含“全部信息都在一个复数中”。
任意高阶关系确实可用二元关系和辅助节点表示，但高阶信息会保留在辅助节点中。
具体地，对 $R\subseteq X_1\times\cdots\times X_n$，取内部辅助域 $T=R$，
令 $B_i(t,x_i)$ 表示 $t$ 的第 $i$ 个分量是 $x_i$，则

$$
R(x_1,\ldots,x_n)\iff \exists t\in T\ \bigwedge_i B_i(t,x_i).
$$

这是一种保真编码，不是把信息维数压缩为二。

<a id="statement-2-3"></a>
#### 命题 2.3（一个复平面中的两条实轴不是两个量子基态）

在一维复内积空间 $\mathbb C$ 中，$1$ 与 $i$ 并不复正交，因为
$\langle1,i\rangle=i\ne0$。
它们只在底层实内积 $\operatorname{Re}(\bar z w)$ 下正交。

二态纯量子态可写作 $\alpha\lvert 0\rangle+\beta\lvert 1\rangle$。
在 $\alpha\ne0$ 的局部区域，$z=\beta/\alpha$ 是射影复坐标；
它把整体非零复缩放取商，仍须补上另一张图册覆盖 $\alpha=0$。
复平面在这里是一张射影坐标图，并非二态的整个振幅空间。

<a id="statement-2-4"></a>
#### 定义 2.4（三个归一化层次）

对有限复向量 $a$，应分别指定：
长度或范数 $N(a)$；非负未归一权重 $W(a)$；
以及事件分布 $p_i=w_i/\sum_jw_j$。
范数、二次型、总质量为一是不同数学条件。

> **编者适用条件注（事件分布的定义域）。** 此处事件权须满足 $w_i\ge0$ 且 $\sum_j w_j>0$，才定义所写的分布；全零权不在该商的定义域。这是本段有限归一化公式的分母条件。


<a id="statement-2-5"></a>
#### 定理 2.5（一维复范数唯一，但其平方不是范数）

若 $N$ 是 $\mathbb C$ 上的复范数，使用标准齐次性
$N(\lambda z)=|\lambda|N(z)$，则 $N(z)=c|z|$，其中 $c=N(1)>0$。
而 $Q(z)=N(z)^2$ 不满足范数的三角不等式。

**证明。**
由 $z=z\cdot1$ 直接得 $N(z)=|z|N(1)$。
对 $z\ne0$，$Q(z+z)=4Q(z)>2Q(z)$，故 $Q$ 不是范数。

∎

这里的复范数公理已经使用标准复模，不能倒过来充当标准复模的无前提起源证明。
如果只把 $\mathbb C$ 当作实平面，$|x|+|y|$、
$\max(|x|,|y|)$ 和 $(|x|^p+|y|^p)^{1/p}$（$p\ge1$）等都是实范数，
但一般不对全部复数乘法满足上述复齐次性。

<a id="section-3"></a>
## 3. 加乘、存在量词与递归：应固定在哪一个半环

<a id="statement-3-1"></a>
#### 定义 3.1（有限关系的半环计算）

设 $X,Y,Z$ 为有限集，$S$ 是交换半环，关系权重为 $A:X\times Y\to S$、
$B:Y\times Z\to S$。定义复合

$$
(B\circ A)(x,z)=\bigoplus_{y\in Y}A(x,y)\otimes B(y,z).
$$

对有限映射 $f:X\to Y$ 及权重 $a:X\to S$，定义推前

$$
(f_!a)(y)=\bigoplus_{x:f(x)=y}a(x).
$$

| 标量域 | 加法 | 乘法 | 汇总的含义 |
| --- | --- | --- | --- |
| $\mathbb B=\{0,1\}$ | 或 | 且 | 存在见证、关系可达性 |
| $\mathbb N$ | 普通加法 | 普通乘法 | 见证数、组合计数 |
| $\mathbb R_{\ge0}$ | 普通加法 | 普通乘法 | 非负质量与条件路径权 |
| $\mathbb C$ | 复加法 | 复乘法 | 同一终端的相干振幅 |

<a id="statement-3-2"></a>
#### 定理 3.2（推前与递归复合相容）

若 $X\xrightarrow fY\xrightarrow gZ$ 为有限映射，则
$(g\circ f)_!=g_!f_!$。
上述关系复合也满足结合律。

**证明。**
对固定 $z$，$g_!f_!a$ 是先按 $f(x)=y$ 分组，再对 $g(y)=z$ 求和；
每个 $g(f(x))=z$ 的 $x$ 恰出现一次。
关系复合的两种括号都展开成同一个有限双重和，
由分配律与乘法结合律相同。

∎

这给“关系连接关系”的精确形式。它没有选择上表中的哪一个标量域。
项目 V14 已将这些不同电路语义分开；本节在同一接口上继续推导。
［[3](#ref-v14)］

<a id="statement-3-3"></a>
#### 定理 3.3（存在是非负质量的支撑语义）

定义 $s:\mathbb R_{\ge0}\to\mathbb B$ 为 $s(t)=1$ 当且仅当 $t>0$。
则 $s$ 保持零、一、加法和乘法。因此

$$
s(f_!\mu)=\exists_f s(\mu).
$$

在有限概率空间中，

$$
\Pr(A)>0\iff \exists x\in A:\mu(x)>0.
$$

**证明。**
对非负数，$a+b>0$ 当且仅当至少一项为正，$ab>0$ 当且仅当两项都为正。
对有限和反复应用即得结论。

∎

在所述有限情形，若分布满支撑，末式就等价于原论域中的普通“$A$ 非空”。
连续均匀分布的单点事件非空却有概率零。
即使在两个点上，$(1/2,1/2)$ 与 $(9/10,1/10)$ 也具有相同存在支撑。
所以支撑映射忘掉数值，存在判定不能逆向恢复概率。

<a id="statement-3-4"></a>
#### 定理 3.4（相干振幅不能通过保加乘映射直接成为非负概率）

不存在保零、保一的半环同态 $h:\mathbb C\to\mathbb R_{\ge0}$。

**证明。**
否则 $0=h(1+(-1))=1+h(-1)\ge1$，矛盾。

∎

平方模确实保持乘法，但

$$
|a+b|^2=|a|^2+|b|^2+2\operatorname{Re}(a\bar b).
$$

相干替代项之间必须保留交叉关系；不能把每条非零路径的“存在”直接相加成概率。
若路径携带正交记录，则交叉项消失，这才接上概率可加性。
此外，普通概率满足

$$
\Pr(A\cup B)=\Pr(A)+\Pr(B)-\Pr(A\cap B),\qquad
\Pr(A\cap B)=\Pr(A)\Pr(B\mid A)
$$

（第二式要求 $\Pr(A)>0$）。
互斥性、独立性或条件化规则不是一个裸加乘符号自动携带的。

<a id="statement-3-5"></a>
#### 命题 3.5（“加乘足以表示逻辑”的正反两个版本）

仅用非负常数、非负输入与有限次普通 $+$、$\times$ 的电路，不能实现位上的 NOT。
但在 $\mathbb F_2$ 上，常数与加乘可以表示任意有限 Boolean 函数。

**证明。**
前者的每个节点对输入坐标单调不减，按电路归纳成立；
NOT 把 $0$ 映为 $1$、$1$ 映为 $0$，与单调性冲突。
后者对 $f:\{0,1\}^n\to\{0,1\}$ 可写

$$
f(x)=
\sum_{\substack{b\in\{0,1\}^n\\ f(b)=1}}
\prod_{i:b_i=1}x_i\prod_{i:b_i=0}(1+x_i)
\quad\text{于 }\mathbb F_2.
$$

每个乘积恰为点 $b$ 的指示函数；在一个输入上至多一项非零，故等式成立。

∎

在 $\mathbb F_2$ 中加法是 XOR，$1+1=0$；
在 Boolean 半环中 $1\lor1=1$；在非负实数中 $1+1=2$。
符号上的加乘表达能力，不能代替对标量语义的选择。

<a id="section-4"></a>
## 4. 复乘法与 log 选择幂律，尚不选择指数二

<a id="statement-4-1"></a>
#### 命题 4.1（归一化保留所有正幂）

对非零有限复向量 $a$ 和任意 $r>0$，

$$
\Pi_i^{(r)}(a)=\frac{|a_i|^r}{\sum_j|a_j|^r}
$$

均连续、非负、归一，且对整体非零复缩放不变。
对另一非零有限复向量 $b$，张量分量 $a_i b_j$ 还有
$\Pi_{ij}^{(r)}(a\otimes b)=\Pi_i^{(r)}(a)\Pi_j^{(r)}(b)$。

**证明。**
分母为正；整体缩放的因子在分子分母相消。
张量分母为 $(\sum_i|a_i|^r)(\sum_j|b_j|^r)$。

∎

例如在固定振幅 $a=(\sqrt3/2,1/2)$ 上，
$\Pi^{(2)}=(3/4,1/4)$，而 $\Pi^{(4)}=(9/10,1/10)$。
二者不能仅靠“总和一、复相位、二元、乘法复合”区分。
反过来，任意概率表 $q$ 都可取 $a_i=q_i^{1/r}$，
使 $\sum_i a_i^r=1$。概率表自身不识别振幅指数；
必须先固定振幅坐标和允许的相干变换。

<a id="statement-4-2"></a>
#### 定理 4.2（连续正乘性权重的分类）

设 $w:\mathbb C^\times\to(0,\infty)$ 连续且
$w(zz')=w(z)w(z')$。则存在 $r\in\mathbb R$ 使 $w(z)=|z|^r$。
若可连续延伸到 $w(0)=0$，则 $r>0$。

**证明。**
$\log w$ 将单位圆连续同态地映入加法群 $\mathbb R$。
其像为紧子群，而 $\mathbb R$ 的非零子群包含某个非零元的全部整数倍，不能紧，
故单位圆上的像为零。
再令 $g(t)=\log w(e^t)$，则 $g(s+t)=g(s)+g(t)$。
连续加法函数为 $g(t)=rt$，由有理数逼近即可证明。
所以 $w(\rho e^{i\theta})=\rho^r$；趋零条件排除 $r\le0$。

∎

对非负权采用 $\log0=-\infty$ 后，原加乘被改写为

$$
s\oplus t=\log(e^s+e^t),\qquad s\otimes t=s+t.
$$

这是 log 坐标下的半环同构，不会单独增加一个虚轴或选定 $r=2$。

> **编者适用条件注（log 半环的端点）。** 同构的目标域为 $\mathbb R\cup\{-\infty\}$，含 $e^{-\infty}=0$ 及 $(-\infty)\otimes t=-\infty$ 的零元约定，不含 $+\infty$；因而不使用 $-\infty+(+\infty)$。此域和约定见固定 [V17 定理 2.3](https://github.com/the-omega-institute/trureturing/blob/6984386a601c1bed4fbcc1e2885c1150b1138586/docs/develop/theory/AURIC_SUM_PRODUCT_LOGARITHMS_AND_QUANTUM_PYTHAGOREAN_GEOMETRY_V17.md)。

不过复乘法确有一个天然二次不变量。对 $z=x+iy$，

$$
M_z=\begin{pmatrix}x&-y\\y&x\end{pmatrix},
\qquad \det M_z=x^2+y^2=|z|^2.
$$

它是复域对实域的代数范数，也是实平面面积的缩放。
$\det M_{zz'}=\det M_z\det M_{z'}$，但 $(\det M_z)^t$ 仍可乘；
因此面积解释尚未完成概率选律。

> **编者适用条件注（行列式幂的零点）。** 若幂权 $({\det M_z})^t$ 包含 $z=0$ 且要求零点权为零，则取 $t>0$；任意实指数的乘性只在 $z\ne0$ 的正行列式域使用。这个端点限定由本节 $\det M_z=|z|^2$ 及正幂定义直接给出。


<a id="section-5"></a>
## 5. 平方唯一性：由相位和全部正交分解推出

项目 V14 定理 10.2 使用全酉不变性、正交可加、非负与单位标定。
在复空间中，全酉不变性可压缩为整体相位不变性，径向性能够证明出来。
［[3](#ref-v14)］

<a id="statement-5-1"></a>
#### 定义 5.1（完整分支向量的统一权重）

令 $\mathcal H$ 为复内积空间，$\dim_\mathbb C\mathcal H\ge2$。
函数 $W:\mathcal H\to[0,\infty)$ 定义在全部未归一向量上，满足：

1. $W(e^{i\theta}x)=W(x)$；
2. $x\perp y$ 时 $W(x+y)=W(x)+W(y)$；
3. 对某个单位向量 $e$，$W(e)=1$。

没有另设连续性、齐次性或只依赖长度的假设。

<a id="statement-5-2"></a>
#### 定理 5.2（相位不变的正交权重唯一为平方）

<a id="thm:square"></a>

上述条件蕴含

$$
\boxed{W(x)=\|x\|^2\quad\text{对所有 }x\in\mathcal H.}
$$

**证明。**
先由 $W(0)=W(0)+W(0)$ 得 $W(0)=0$。
若 $\|x\|=\|y\|$，选择相位使 $z=e^{i\theta}y$ 满足
$\langle x,z\rangle\in\mathbb R$。令

$$
u=\frac{x+z}{2},\qquad v=\frac{x-z}{2}.
$$

等范数与实内积使 $\langle u,v\rangle=0$。
由于 $x=u+v$、$z=u-v$，有

$$
W(x)=W(u)+W(v)=W(u)+W(-v)=W(z)=W(y).
$$

因此等范球面上的权重相同，径向性成立。

定义 $F(t)=W(\sqrt t\,e)$，$t\ge0$。
取两个正交单位向量 $e_1,e_2$，则

$$
F(s+t)=W(\sqrt s\,e_1+\sqrt t\,e_2)=F(s)+F(t).
$$

非负性使 $F$ 单调，单位标定给 $F(1)=1$。
加法性给所有非负有理数 $q$ 上 $F(q)=q$；
再从上下用有理数夹逼任意实数，得 $F(t)=t$。

∎

<a id="statement-5-3"></a>
#### 推论 5.3（正交读出的 Born 形式与递归不变性）

若 $\psi=\sum_i\psi_i\ne0$ 为有限正交分解，并用同一个 $W$ 标定读出，则

$$
p_i=\frac{W(\psi_i)}{\sum_jW(\psi_j)}
=\frac{\|\psi_i\|^2}{\|\psi\|^2}.
$$

把正交叶向量按任意二叉树逐级合并，根权重与全部叶权重之和相同。
对 $\psi_i=P_i\psi$，上式为对应正交投影的 Born 形式。

**证明。**
反复应用正交可加性得到 $W(\psi)=\sum_iW(\psi_i)$，
再用定理 [5.2](#thm:square)。树上任一内节点的两组叶和仍正交，
故对树深归纳即可。

∎

若已经写成 $W(x)=\|x\|^r$，取两个正交单位向量便有
$2^{r/2}=2$，立刻得到 $r=2$。
指数二的实质在于同一个权重必须兼容 Hilbert 合成长度和正交记录可加性，
不是每次递归都把上一次的概率再次平方。

<a id="statement-5-4"></a>
#### 说明 5.4（本定理没有省掉的前件）

复一维没有两个非零复正交向量，所有 $|z|^r$（$r>0$）仍满足相应条件。
本定理的 $W$ 定义在整个未归一分支向量域，并不是固定输入态上的投影 frame function；
因此复二维成立不与二态投影版本的 Gleason 边界冲突。
“权重决定实际测量概率”仍是所声明的读出接口。
Hilbert 内积、复线性合成及相位等价没有由普通存在逻辑单独重构。

<a id="statement-5-5"></a>
#### 命题 5.5（正关系核给出 Hilbert 商，但不独立指定概率）

给有限 Hermitian 正半定矩阵 $D$。在
$\mathcal H_D=\mathbb C^N/\ker D$ 上定义

$$
\langle[c],[d]\rangle=c^\dagger Dd.
$$

它是维数 $\operatorname{rank} D$ 的内积空间；若 $v_i=[e_i]$，则
$\langle v_i,v_j\rangle=D_{ij}$，且

$$
\left\|\sum_i c_i v_i\right\|^2=c^\dagger Dc.
$$

**证明。**
由正半定性，$c^\dagger Dc=0$ 当且仅当 $D^{1/2}c=0$，
也即 $Dc=0$。所以该式在商空间良定义且正定；
维数与 Gram 等式直接成立。

∎

此处“商”由关系核的零空间精确给出；正性、复域和核本身是输入。
在该空间再满足定理 [5.2](#thm:square) 的统一权重条件，才得到相应平方读出。

<a id="section-6"></a>
## 6. AURIC 五模式：三个边缘量与一个独立联合量

以项目固定的五个合法窗口
$000,100,010,001,101$ 为标签，分别记概率
$p_0,p_1,p_2,p_3,p_{13}$。取三轴顺序 $(1,3,2)$：

$$
x=\mathbb E b_1,\qquad y=\mathbb E b_3,\qquad z=\mathbb E b_2,\qquad
\kappa=\mathbb E(b_1b_3).
$$

这里 $\kappa$ 是分布的联合量；任务函数展开中的交互系数 $c_{13}$
是另一个对象，不能仅因下标相同就相等。
［[4](#ref-v17)，[7](#ref-ml)］

<a id="statement-6-1"></a>
#### 定理 6.1（五模式的精确恢复与关系自由度）

归一五概率由 $(x,y,z,\kappa)$ 恢复为

$$
\begin{aligned}
p_{13}&=\kappa,&p_1&=x-\kappa,&p_3&=y-\kappa,\\
p_2&=z,&p_0&=1-x-y-z+\kappa.
\end{aligned}
$$

其非负条件恰为

$$
z\ge0,\qquad
\max(0,x+y+z-1)\le\kappa\le\min(x,y).
$$

因而三轴与归一化一般不能单独确定联合关系。

**证明。**
逐窗口读取 $b_1,b_3,b_2,b_1b_3$ 给
$x=p_1+p_{13}$、$y=p_3+p_{13}$、$z=p_2$、$\kappa=p_{13}$。
解线性式再用总和一，得到恢复公式；
五项非负恰为所列不等式。

∎

例如 $x=y=1/2,z=0$ 时，$\kappa$ 可在 $[0,1/2]$ 任取。
端点分别对应全反相关和全正相关；三个边缘读数与归一化完全相同。
$p_0$ 是一个具体模式的质量，不是归一化算子；
归一化是五项总和为一这一全局等式。
这也没有把模式 $F[\mathrm{null}]$ 指定成观察者本体。

<a id="statement-6-2"></a>
#### 命题 6.2（二态射影的三坐标属于另一种有条件编码）

对归一 $\psi=(\alpha,\beta)$，定义

$$
r_x=2\operatorname{Re}(\bar\alpha\beta),\quad
r_y=2\operatorname{Im}(\bar\alpha\beta),\quad
r_z=|\alpha|^2-|\beta|^2.
$$

则 $r_x^2+r_y^2+r_z^2=1$。
若 $\alpha\ne0$，令 $\zeta=\beta/\alpha$，则

$$
r=\frac{(2\operatorname{Re}\zeta,\;2\operatorname{Im}\zeta,\;1-|\zeta|^2)}
{1+|\zeta|^2}.
$$

**证明。**
前两项平方和为 $4|\alpha|^2|\beta|^2$；
加上第三项得到 $(|\alpha|^2+|\beta|^2)^2=1$。
再代入比值即得第二式。

∎

这里球面有两个独立实自由度；一般归一五概率有四个。
如果采用前轮指定的 Bloch–AURIC 仿射编码，必须保留其适用态族和映射；
不能把任意四维五概率族与纯二态球面无条件认同。

<a id="section-7"></a>
## 7. 商、余关系与项目新增的预测误差下界

<a id="statement-7-1"></a>
#### 定义 7.1（任务相对的观察商与关系余量）

设内部状态为 $h$，已保留摘要为 $m(h)$，所需预测为概率行 $K(h)$。
若存在 $G$ 使 $K=G\circ m$，称 $m$ 对此任务充分。
额外记录 $r(h)$ 若使 $K=G(m,r)$，可称为该任务的关系余量。
它不必是数值相减的余数，也不保证是有限比特寄存器。

<a id="statement-7-2"></a>
#### 定理 7.2（恢复判据与不可消去的误差）

精确恢复 $K=G\circ m$ 的充要条件是 $K$ 在 $m$ 的每个纤维上常值。
若 $m(h)=m(h')$，任意只依赖 $m$ 的预测器 $\widehat K$ 满足

$$
\max\{\operatorname{TV}(\widehat K(m(h)),K(h)),
\operatorname{TV}(\widehat K(m(h')),K(h'))\}
\ge\frac12\operatorname{TV}(K(h),K(h')).
$$

**证明。**
必要性由函数复合直接成立；充分性是在每个实际像点取该纤维的公共值。
下界来自 TV 三角不等式。

∎

这将“归一化之后仍有误差”分成两种情形：
关系已经被摘要丢失，或关系虽保留但解码器尚未正确利用。
重新把预测行除以总质量不会恢复前一种信息。

<a id="statement-7-3"></a>
#### 命题 7.3（全部二元边缘仍会漏掉高阶关系）

对 $x,y,z\in\{0,1\}$ 与 $|\eta|\le1$，令

$$
P_\eta(x,y,z)=\frac18[1+\eta(-1)^{x+y+z}].
$$

它归一且非负，全部二元边缘都为均匀 $1/4$，但
$\mathbb E_\eta[(-1)^{X+Y+Z}]=\eta$。

**证明。**
总奇偶修正和为零；对任意一位求和，修正的两项相消。
乘上奇偶符号再求和，常数部分相消，余下 $\eta$。

∎

二元关系的表示能力与二元边缘的充分性因此需要分别检验。

<a id="section-7-1"></a>
### 7.1. 本轮 RRO 增补的具体对应

新 RRO §§28–33 在原 $89$ 配置来源中，
区分旧终端 $W$、记录 $I$ 的分别边缘与同源联合表：

$$
\dim\ker W_*=34,\qquad
\dim\ker(W_*,I_*)=33,\qquad
\ker(W,I)_*=\{0\}.
$$

> **编者适用条件注（RRO 的核空间）。** 三个核均取在实有符号配置律空间 $\mathbb R^E$ 上，其中 $E$ 是固定外部边界下的完整 $89$ 配置集；归一概率律的差落在总质量零超平面内。这不是非线性密度场族的维数。定义域及三种推前的区分见固定 [RRO 定义 28.1、定理 28.2](https://github.com/the-omega-institute/trureturing/blob/6984386a601c1bed4fbcc1e2885c1150b1138586/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FIBONACCI_NATIVE_TERMINAL_CERTIFICATION.md)。


以下固定 $0<\varepsilon<1$，以及 III §§164–165 的两个既定修正场之一
$H\in\{h,h_{\rm sm}\}$。它们在源指定向量 $z_*$ 上均满足 $H(z_*)>0$。
对非零读取前向量 $z$，其旧修正族
$\Pi_q(z)=b_q(z)+\varepsilon H(z)c_q$，
$b_q(z)=|z_q|^2/\|z\|^2$，保留五奇位共同关系。
令 $M_i$ 为记录 $I=i$ 的正交投影，并记

$$
t_i(z)=\frac{\|M_i z\|^2}{\|z\|^2}>0,\qquad
\phi_i(z)=\frac{M_i z}{\|M_i z\|}.
$$

在给定读取前实际条件律、字面保留配置及正质量分支的前件下，
紧接旧终端行满足

$$
K_i=B_i+\gamma_i C_i,\qquad
\gamma_i=\frac{\varepsilon H}{t_i},\qquad
\operatorname{TV}(K_i,B_i)=8\gamma_i.
$$

$B_i$ 是后射线 $[\phi_i(z)]$ 的 Born 旧终端行；
$C_i$ 是源规定的固定符号行，含十六个非零单元，八个 $+1$、八个 $-1$。
记录与后射线之外，$\gamma_i$ 是恢复这一个终端任务所需的相对最小修正量。
令 $\chi_a$ 为原生有限前缀 $a$ 的源态，
$\mathcal A_i=\{a:t_i(\chi_a)>0\}$。
对仅依赖已保留 $i$ 与后射线、在实际后射线域上连续的预测器 $R_i$，
定义

$$
E_i(R_i)=\sup_{a\in\mathcal A_i}
\operatorname{TV}\bigl(R_i([M_i\chi_a]),K_i(\chi_a)\bigr).
$$

源文进一步证明统一误差下界

$$
E_i(R_i)\ge8\varepsilon H(z_*)>0.
$$

这是“一份归一摘要仍可漏掉关系”的精确项目实例。
［[5](#ref-rro)，§§28–33］

上述结论的任务域是一个保留记录切口、空未来、紧接旧终端。
它没有提供 $\gamma_i$ 对非空未来的闭合更新，没有宣称构造完整非 Born 过程，
也没有给任意有限测试集同样的误差底。
本文将其用于定位信息缺口，而不把它当作实际大模型的性能定理。

<a id="section-8"></a>
## 8. 模型参数编码关系，但不等于归一化关系

公开的标准 Transformer 以一般可学习实矩阵构成线性投影，
在注意权和输出概率处使用 softmax；激活归一化与这些参数矩阵是不同对象。
［[8](#ref-transformer)，§§3.1–3.4］
以下仅讨论公开架构公式，不推断本助手未公开的具体实现。

<a id="statement-8-1"></a>
#### 定义 8.1（标准点积注意力与概率读出）

对输入矩阵 $X$，令

$$
Q=XW_Q,\quad K=XW_K,\quad V=XW_V,\quad
A=\operatorname{softmax}_{\rm row}(QK^\top/\sqrt{d_k}),
$$

输出为 $AV$。独立的有限词元读出可写

$$
q_\theta(y\mid x)=
\frac{\exp\ell_{\theta,y}(x)}{\sum_j\exp\ell_{\theta,j}(x)}.
$$

softmax 作用于 logits；它没有要求所有 $W$ 为概率行或酉矩阵。

> **编者适用条件注（有限 softmax 的定义域）。** 注意力式取 $d_k\ge1$；这里及下述 softmax 商定理取非空有限类别集 $d\ge1$ 和有限实 logits；空类别集的分母为零，不定义该映射。该限定直接来自本定义的指数和。


<a id="statement-8-2"></a>
#### 定理 8.2（参数可以无界变化而表示关系不变）

对没有额外 Q/K 归一化的上述注意力，任取 $c>0$，
置 $W_Q'=cW_Q$、$W_K'=c^{-1}W_K$，其输出对所有 $X$ 完全不变。
若 $W_Q\ne0$，参数范数可随 $c\to\infty$ 无界增大。

**证明。**
$Q'K'^\top=(cQ)(c^{-1}K)^\top=QK^\top$，所以 $A$ 与 $AV$ 相同。

∎

若正则项、量化或额外归一化属于比较任务，还须把它们纳入合同；
上述结论针对指定推断函数。
相同推断行为也不保证在同一优化器下具有相同未来训练轨迹。

<a id="statement-8-3"></a>
#### 定理 8.3（softmax 恰好实现一个商）

对 $s,t\in\mathbb R^d$，

$$
\operatorname{softmax}(s)=\operatorname{softmax}(t)
\iff s-t=c\mathbf1\quad\text{对某个 }c\in\mathbb R.
$$

因此 softmax 在 $\mathbb R^d/\operatorname{span}\{\mathbf1\}$
与正概率单纯形之间给出双射。

**证明。**
同加常数在分子分母相消。
反之，相等概率的比值给 $e^{s_i-s_j}=e^{t_i-t_j}$，
故所有坐标差 $s_i-t_i$ 相同。
任意正概率 $p$ 都有代表 $s_i=\log p_i$，给满射。

∎

这是“参数或关系具有商结构”的一个严格版本：
归一化删除一个共同 log 尺度，而没有选择出唯一的原始 logits。
对完整模型还可定义 $\theta\sim\theta'$，
当且仅当它们在全部允许输入上给同一分布；这是任务相对的行为商。

<a id="statement-8-4"></a>
#### 命题 8.4（概率归一化通常不是酉性）

若实方阵 $A\ge0$、每行和为一且正交，则 $A$ 为置换矩阵。

**证明。**
任一行满足 $\sum_j a_j=\sum_j a_j^2=1$，所以
$2\sum_{j<k}a_ja_k=0$。非负性迫使每行恰有一个一；
行间正交使这些一位于不同列。

∎

因此一般严格正的注意力行权没有酉性。

> **编者适用条件注（严格正方阵的一维例外）。** 若把该句用于严格正方阵，须取阶数 $d\ge2$；$d=1$ 的 $[1]$ 同时严格正、行随机且酉。此例外由上面命题 8.4 的置换结论直接给出；一般矩形注意力权也不能直接套用方阵酉性的判据。

LayerNorm 会把 $a$ 与 $a+c\mathbf1$ 识别为同一输出；
理想无 $\epsilon$ 的 RMSNorm 对正缩放不变，也非单射。
有 $\epsilon$ 时不能沿用精确尺度不变性，但其一般非线性仍不同于酉线性映射。
这些层归一化的是激活，并带增益等参数。
［[9](#ref-rmsnorm)，§§3–4］

> **编者适用条件注（理想归一化的分母）。** 无 $\epsilon$ 的 RMSNorm 仅在 RMS 非零的激活上定义，排除零向量；无 $\epsilon$ 的 LayerNorm 相应要求方差非零。正缩放不变性在这个非零分母域内成立。分母形式见 [RMSNorm §§3–4 的式 (3)–(4)](https://arxiv.org/html/1910.07467v1)；原文关于有 $\epsilon$ 时不能沿用精确尺度不变性的限定保留。


<a id="section-8-1"></a>
### 8.1. 项目中的一个直接反例：归一选择不补足训练证据

ML 白盒卷 §5 使用

$$
\phi(b)=(1,b_1,b_2,b_3,b_1b_3),\qquad
f_\theta(b)=\langle\theta,\phi(b)\rangle.
$$

训练点为 $000,100,010,001$ 时，所有末项特征为零；
故 $\theta$ 与 $\theta+t e_{13}$ 的全部训练输出、损失相同，
在联合点 $101$ 的输出却相差 $t$。
最小范数规则可选一个代表，但不能凭此证明真实交互系数已被识别。
［[7](#ref-ml)，§5］
这与上一节的摘要纤维是同一种恢复障碍，只是这里的纤维位于参数空间。

<a id="section-9"></a>
## 9. 提示、信息与误差：一个精确分解

<a id="statement-9-1"></a>
#### 定义 9.1（同一预测任务下的风险）

取有限内部随机变量：旧上下文 $X$、新提示记录 $Z$、固定目标 $Y$，
并固定联合律 $P(X,Z,Y)$。
实际模型在两种信息下输出 $q_0(y\mid x)$ 与 $q_1(y\mid x,z)$，
二者在真分布支持上为正。采用自然对数，定义

$$
\begin{aligned}
R_0&=\mathbb E[-\log q_0(Y\mid X)],&
R_1&=\mathbb E[-\log q_1(Y\mid X,Z)],\\
D_0&=\mathbb E_XD_{\mathrm{KL}}(P_{Y|X}\|q_0),&
D_1&=\mathbb E_{X,Z}D_{\mathrm{KL}}(P_{Y|X,Z}\|q_1).
\end{aligned}
$$

> **编者适用条件注（零质量条件纤维）。** 条件分布只在正质量的 $X=x$ 或 $(X,Z)=(x,z)$ 纤维参与有限期望；零质量纤维可任取版本而不改变风险。熵与 KL 求和中真概率为零的项按零计，正真概率处沿用定义 9.1 的 $q>0$。这是下述定理 9.2 逐纤维恒等式使用的约定。


<a id="statement-9-2"></a>
#### 定理 9.2（条件信息增益与模型失配分解）

<a id="thm:risk"></a>

$$
R_0=H(Y\mid X)+D_0,\qquad
R_1=H(Y\mid X,Z)+D_1,
$$

因而

$$
\boxed{R_1-R_0=-I(Y;Z\mid X)+(D_1-D_0).}
$$

**证明。**
在真分布正支持上写
$-\log q(Y)=-\log P(Y)+\log(P(Y)/q(Y))$。
按各条件纤维取期望，分别得到条件熵与 KL；
再用 $I(Y;Z\mid X)=H(Y\mid X)-H(Y\mid X,Z)$。

∎

KL 非负可由 $-\log u\ge1-u$ 求和得到。
若两模型均为相应信息下的真实 Bayes 预测，则 $D_0=D_1=0$，
新增信息使平均风险不增。
实际模型风险不增的充要条件则为

$$
D_1-D_0\le I(Y;Z\mid X).
$$

因此提示可能改善真实信息，也可能扩大或缩小模型失配；
归一化没有固定后者的符号。

<a id="statement-9-3"></a>
#### 命题 9.3（完全准确的提示也能被模型误用）

令 $X$ 常值，$Y$ 为公平位，$Z=Y$。
旧模型 $q_0=(1/2,1/2)$，新模型对正确答案 $Y=Z$ 只赋概率
$0<\varepsilon<1/2$。则

$$
R_0=\log2,\qquad H(Y\mid Z)=0,\qquad
R_1=-\log\varepsilon>\log2.
$$

**证明。**
直接代入风险定义。每个条件分布仍为 $(\varepsilon,1-\varepsilon)$
的适当排列，严格归一。

∎

该反例没有声称某个真实模型必会这样行动；
它证明仅有归一化与新提示，不足以推出误差下降。
条件熵的单调性还只对新增提示分支取平均成立，
不能外推为每一个特定提示分支都降低不确定性。
若提示改变目标或损失，或主动改变被预测系统的生成律，
应重新指定比较任务，不能直接套用同一联合律的定理。

<a id="statement-9-4"></a>
#### 推论 9.4（重述与自生成文本的作用）

若 $Z=h(X)$，则 $I(Y;Z\mid X)=0$，故风险改变完全由 $D_1-D_0$ 给出。
固定参数 $\theta$，若 $Z=g_\theta(X,S)$，
且 $S\perp Y\mid X,\theta$，则

$$
I(Y;Z\mid X,\theta)=0.
$$

**证明。**
前者是给定 $X$ 后 $Z$ 已确定。
后者中 $P(Z\mid X,\theta,Y)=P(Z\mid X,\theta)$，
所以条件独立，条件互信息为零。

∎

这允许计算、分步表达和自检降低有限实现的失配，
即使它们没有增加关于世界的新来源信息。
若系统实际读取整体内部的新证据，上述独立性前件可能不再成立。
不需要因此引入整体外部的信息源。

<a id="statement-9-5"></a>
#### 命题 9.5（摘要造成的最优 log 风险损失）

若 $M=h(X)$，则

$$
H(Y\mid M)-H(Y\mid X)=I(Y;X\mid M)\ge0.
$$

**证明。**
因为 $(X,M)$ 与 $X$ 携带相同信息，
$H(Y\mid X,M)=H(Y\mid X)$，代入条件互信息定义。

∎

关系余量若能消除这个条件互信息，就是该目标下的充分补充。
这给“商后遗失信息”的概率版本，但并未把互信息定义成可免费取得的寄存器。

<a id="section-9-1"></a>
### 9.1. 训练下降与固定参数推断应分别定理化

GPT-3 论文的 few-shot 评估明确通过文本上下文条件化，不作梯度更新或微调，
提供了“提示适应不必是参数更新”的公开实例。
［[10](#ref-gpt3)，摘要及 §1］
若要证明训练目标下降，应给出训练动力学：
例如当 $\nabla L$ 为 $L_s$-Lipschitz，$L_s>0$，
精确梯度步 $\theta'=\theta-\eta\nabla L(\theta)$、
$0<\eta<2/L_s$ 满足

$$
L(\theta')\le L(\theta)-
\eta(1-L_s\eta/2)\|\nabla L(\theta)\|^2.
$$

证明是在光滑性界
$L(\theta+s)\le L(\theta)+\langle\nabla L,s\rangle+(L_s/2)\|s\|^2$
中代入该步长；光滑性界由沿线积分梯度差得到。
这不自动覆盖随机梯度、分布外风险或固定参数的生成过程。
项目 ML 白盒卷 §14 对平方损失也分别列出标签噪声、表示遗漏、
读出类逼近与实际总体超额，不能把所有误差一概称为优化残差。
［[7](#ref-ml)，§14］

<a id="section-10"></a>
## 10. log、平方根与概率几何：可以成立的更强联系

<a id="statement-10-1"></a>
#### 命题 10.1（softmax 的平方表示不是量子性判据）

若 $q_i=e^{\ell_i}/Z$，$Z=\sum_j e^{\ell_j}$，
则 $a_i=e^{\ell_i/2}/\sqrt Z$ 满足 $\sum_i|a_i|^2=1$、
$q_i=|a_i|^2$。但任意经典概率表都可以如此平方提升。

**证明。**
直接代入；更一般地取 $a_i=\sqrt{q_i}$ 即可。

∎

加入任意相位后 $\psi_i=\sqrt{q_i}e^{i\theta_i}$ 仍有相同基概率，
这些相位没有被原概率表确定。
例如 $(\lvert 0\rangle+\lvert 1\rangle)/\sqrt2$ 与 $(\lvert 0\rangle-\lvert 1\rangle)/\sqrt2$
在该基上相同，经过 Hadamard 后却分别确定为 $\lvert 0\rangle$、$\lvert 1\rangle$。
经典混合 $\operatorname{diag}(q)$ 与纯平方提升
$|\sqrt q\rangle\langle\sqrt q|$ 也具有不同相干信息。

> **编者适用条件注（平方提升的退化支撑）。** 当至少两个 $q_i>0$ 时，所写纯提升有非零非对角元，而 $\operatorname{diag}(q)$ 没有；单点支撑时两矩阵相同。该区别直接按本段矩阵元 $\sqrt{q_iq_j}$ 判断，不把经典概率表本身当作额外相位的来源。


<a id="statement-10-2"></a>
#### 定义 10.2（Fisher 二次型）

在正单纯形 $\Delta_d^\circ=\{p_i>0,\sum_i p_i=1\}$ 上，
对切向量 $\sum_i v_i=0$，定义

$$
g_{F,p}(v,v)=\sum_i\frac{v_i^2}{p_i}.
$$

<a id="statement-10-3"></a>
#### 定理 10.3（KL 的局部平方与 Fisher 球面提升）

固定 $p\in\Delta_d^\circ$、$\sum_i v_i=0$，
对足够小的 $\epsilon$，

$$
D_{\mathrm{KL}}(p\|p+\epsilon v)
=\frac{\epsilon^2}{2}g_{F,p}(v,v)+O(\epsilon^3).
$$

映射 $\Phi(p)=2(\sqrt{p_i})_i$ 落在半径二球面上，并满足
$\|D\Phi_p v\|^2=g_{F,p}(v,v)$。

**证明。**
用 $-\log(1+u)=-u+u^2/2+O(u^3)$，
逐项令 $u=\epsilon v_i/p_i$ 并乘 $p_i$。
一阶项因 $\sum_i v_i=0$ 消失。
固定正 $p$ 和有限维保证余项；不声称该展开对趋零概率一致。
又 $D\Phi_p v=(v_i/\sqrt{p_i})_i$，且 $\sum_i(2\sqrt{p_i})^2=4$，
从而得到等距拉回。

∎

项目 V17 定理 6.5 已有五模式 Fisher 平方根几何。
本节说明 log 损失为何在正确模型附近出现平方误差，
同时保留它与全域精确 Born 平方律的不同前件。
［[4](#ref-v17)，定理 6.5］

<a id="statement-10-4"></a>
#### 定理 10.4（幂提升中，固定 Fisher 比例唯一选择平方根）

取 $d\ge2$、$r>0$，定义
$F_r(p)=(p_1^{1/r},\ldots,p_d^{1/r})$，
不再作额外 Euclidean 归一化。
若存在与 $p,v$ 无关的固定常数 $c>0$，使整个正单纯形上

$$
\|DF_r(p)v\|^2=c\,g_{F,p}(v,v)
\quad\text{对所有 }\sum_i v_i=0,
$$

则 $r=2$ 且 $c=1/4$；反之也成立。

**证明。**
拉回度量为
$r^{-2}\sum_i p_i^{2/r-2}v_i^2$。
令 $p_1=t,p_2=b-t$，其余正坐标固定；
$d=2$ 时 $b=1$。取 $v=e_1-e_2$，两度量比为

$$
R_r(t)=
\frac{t(b-t)}{r^2b}
\left[t^{2/r-2}+(b-t)^{2/r-2}\right].
$$

当 $t\downarrow0$，第二加项贡献趋零，第一贡献与
$r^{-2}t^{2/r-1}$ 同阶。
若 $r<2$，比值趋零；若 $r>2$，趋无穷。
均与有限固定 $c>0$ 冲突，故只能 $r=2$；
此时拉回直接为 $g_F/4$。

∎

全域固定比例是必要条件：在二元单纯形的一维切空间上，
允许比例依赖 $p$ 就不能选出指数；只在均匀点比较也不足够。
此定理选择规定幂族中的 Fisher 适配坐标，并未从裸归一化推导 Fisher 的选择。

<a id="statement-10-5"></a>
#### 定理 10.5（纯态几何分解为概率与相位关系）

在正支撑局部图册中令
$\psi_i=\sqrt{p_i}e^{i\theta_i}$，$\sum_i p_i=1$。
采用 $d_{\rm FS}([\psi],[\phi])=\arccos|\langle\psi,\phi\rangle|$ 的约定，
则

$$
\boxed{
ds_{\rm FS}^2=
\frac14\sum_i\frac{dp_i^2}{p_i}
+\sum_i p_i\,d\theta_i^2
-\left(\sum_i p_i\,d\theta_i\right)^2.
}
$$

**证明。**
微分为
$d\psi_i=e^{i\theta_i}(dp_i/(2\sqrt{p_i})+ i\sqrt{p_i}\,d\theta_i)$，所以

$$
\|d\psi\|^2=\frac14\sum_i dp_i^2/p_i+\sum_i p_i d\theta_i^2,
\quad
\langle\psi,d\psi\rangle=i\sum_i p_i d\theta_i.
$$

在 $ds_{\rm FS}^2=\|d\psi\|^2-|\langle\psi,d\psi\rangle|^2$ 中代入。

∎

相位部分是加权方差，消去共同相位方向。
固定相对相位时才剩 $g_F/4$；若相位随 $p$ 变，不能漏掉方差项。
对二态，令 $p_0=p,p_1=1-p$、相对相位为 $\varphi$，则

$$
ds_{\rm FS}^2=\frac{dp^2}{4p(1-p)}+p(1-p)d\varphi^2.
$$

再取 $p=\cos^2(\vartheta/2)$，得
$ds_{\rm FS}^2=(d\vartheta^2+\sin^2\vartheta\,d\varphi^2)/4$。
这给出概率、相位和 Bloch 球之间的精确桥梁；边界零概率处须更换坐标。

<a id="section-11"></a>
## 11. 统一为内生的关系递归，而不合并不同层次

上面的结构可以整理成以下相容链：

$$
\begin{gathered}
\text{内部关系与允许记录}
\ \longrightarrow\ \text{指定半环中的复合和推前},\\
\text{正相干核}
\ \longrightarrow\ \text{Hilbert 商与正交关系},\\
\text{相位不变、全正交可加、单位标定}
\ \longrightarrow\ \text{平方总权重与正交读出概率},\\
\text{任务相对的观察商}
\ \longrightarrow\ \text{充分关系余量与预测误差界}.
\end{gathered}
$$

每个箭头有自己的前件；它们不能只靠“都是关系”而自动相等。

<a id="statement-11-1"></a>
#### 命题 11.1（内部保留输入可使有限经典计算酉嵌入）

给有限位串函数 $f:\{0,1\}^n\to\{0,1\}^m$，
在同一整体内保留输入寄存器，定义

$$
U_f\lvert x,y\rangle=\lvert x,y\oplus f(x)\rangle.
$$

则 $U_f$ 为酉算子；从 $y=0$ 读出得到 $f(x)$。

**证明。**
该映射在计算基上是置换，且自身为逆，故其线性扩张酉。

∎

这使“经典读出可来自内部更大酉过程”成为有条件的数学表示。
它没有使局部丢弃输入、softmax、LayerNorm 或训练更新本身成为酉门，
也没有从表示定理推出实际宇宙采用某一指定模型。
若舍弃输入、记录和相关性，局部读出的不可逆性可以保留。

从用户直觉中可以保留并加强的，是以下四句话：

1. 加乘是多种关系递归的共同语法；标量域决定它在说存在、质量还是相干。
2. 概率在非负有限情形中有加权存在语义；支撑只记录可能性，不决定概率值。
3. 平方是相干几何与所有正交分解相容时的唯一权重；它不由“复平面可归一”单独决定。
4. 提示和推理可提供新关系、改进表达或减小模型失配；能否减误差取决于同一任务下的信息和解码条件。

其中可继续压缩的起源问题是：
为什么物理关系核应是正 Hermitian 核，为什么可操作分支满足全正交相容，
以及哪些内部记录足以支持实际读出。
这些问题比“归一化只能平方”更具体，也能够给出明确的反例与检验条件。

<a id="section-A"></a>
## A. 来源核查、完整性与证明范围

固定 GitHub 元数据与比较 diff，当前相关原文均取不可变提交。
匿名 API 的部分目录请求遇到限流，因此本轮增量依据官方固定比较 diff，
不宣称读取了当前完整 theory 树。
该 diff 共 103 个文件段，theory 路径只有正文所述两项。
对未变相关卷核对 Git blob 身份；当前 III 与上一轮同一完整 blob。

本轮相关实际阅读范围如下：

- RRO：全部新增 §§28–33 及其定义、证明和边界。
- V14：有限存在量词、半环支撑、正核与条件平方；量子存在接口和概率取得限制由有界审读核对。
- V17：Fisher 平方根及其五模式关系上下文；不重审全部融合和编织结论。
- ML 白盒卷：训练/使用区分、§5 未识别交互、§14 风险与表示细化，
   以及 softmax 合同的限定段；没有全文复核其全部 17710 行。
- 新 V44：开头归属说明及编者条件注；它是既有稿的转写，不作本轮独立新复证。
- 公开 ML 论文：Transformer §§3.1–3.4、RMSNorm §§3–4、
   GPT-3 摘要和 §1；不据此推断未公开模型机制。

本文的平方权重、半环、信息分解、幂提升及度量计算均给出纸面证明。
没有执行数学计算程序、枚举、CAS、模拟、门字搜索、Lean 构建或真实网络训练；
文件编排与 PDF 渲染只用于交付检查。
项目上游矩阵稠密性、实际制备、测量概率取得、未来闭合和物理实现，
仅在明确引用所需前件的范围内使用。

<a id="references"></a>
## 固定来源与适用范围

<a id="ref-head"></a>
**[1]**
the-omega-institute/trureturing.
[固定提交 6984386a601c1bed4fbc<wbr>c1e2885c1150b1138586](https://github.com/the-omega-institute/trureturing/commit/6984386a601c1bed4fbcc1e2885c1150b1138586)，
2026-10-31 10:57:55 UTC；PR #24749。

<a id="ref-compare"></a>
**[2]**
同仓库，
[v46 至本轮固定快照的官方比较](https://github.com/the-omega-institute/trureturing/compare/02c695f8c17e35965f80603427074b1dd434eed9...6984386a601c1bed4fbcc1e2885c1150b1138586)。
增量核查采用对应 `.diff`，未把部分目录读取当作完整树审计。

<a id="ref-v14"></a>
**[3]**
[V14《存在量词、电路半环与量子记录》](https://github.com/the-omega-institute/trureturing/blob/6984386a601c1bed4fbcc1e2885c1150b1138586/docs/develop/theory/AURIC_EXISTENTIAL_QUANTIFIERS_CIRCUIT_SEMIRINGS_AND_QUANTUM_RECORDS_V14.md)，
§§2–3、7、10、12。本文压缩了其平方定理的复对称前提；
不把已有 Hilbert 与读出条件说成由存在逻辑自动生成。

<a id="ref-v17"></a>
**[4]**
[V17《加乘、对数与量子勾股几何》](https://github.com/the-omega-institute/trureturing/blob/6984386a601c1bed4fbcc1e2885c1150b1138586/docs/develop/theory/AURIC_SUM_PRODUCT_LOGARITHMS_AND_QUANTUM_PYTHAGOREAN_GEOMETRY_V17.md)，
五模式概率、隐藏关系及定理 6.5 的 Fisher 平方根几何。

<a id="ref-rro"></a>
**[5]**
[《递归关系观察：Fibonacci 原生终端认证》](https://github.com/the-omega-institute/trureturing/blob/6984386a601c1bed4fbcc1e2885c1150b1138586/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FIBONACCI_NATIVE_TERMINAL_CERTIFICATION.md)，
本轮新增 §§28–33，特别定理 28.2、31.2、32.1 及命题 30.3。
只使用其固定来源与一个保留记录切口的前件，不移入全未来过程。

<a id="ref-iii"></a>
**[6]**
[《量子原则与相干重构续卷 III》](https://github.com/the-omega-institute/trureturing/blob/6984386a601c1bed4fbcc1e2885c1150b1138586/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md)，
§§173–176：与 v46 相同的固定原文身份；本轮不再宣称新增一次 Born 选律。

<a id="ref-ml"></a>
**[7]**
[《FIB 原子机器学习白盒》](https://github.com/the-omega-institute/trureturing/blob/6984386a601c1bed4fbcc1e2885c1150b1138586/docs/develop/theory/FIB_ATOM_MACHINE_LEARNING_WHITEBOX.md)，
§5 未识别关系，§14 风险分解与表示细化，§45 softmax 合同。
这些是有限模型的数学例子，不是实际大型网络实证。

<a id="ref-transformer"></a>
**[8]**
A. Vaswani et al.
[Attention Is All You Need](https://arxiv.org/html/1706.03762v7)，
arXiv:1706.03762v7，§§3.1–3.4。
这里只取投影矩阵、注意力 softmax、前馈与概率输出的架构事实。

<a id="ref-rmsnorm"></a>
**[9]**
B. Zhang, R. Sennrich.
[Root Mean Square Layer Normalization](https://arxiv.org/html/1910.07467v1)，
arXiv:1910.07467v1，§§3–4。
激活归一化、增益及尺度性质；正缩放与 $\epsilon$ 条件在正文单列。

<a id="ref-gpt3"></a>
**[10]**
T. B. Brown et al.
[Language Models are Few-Shot Learners](https://arxiv.org/html/2005.14165v4)，
arXiv:2005.14165v4，摘要及 §1。
文中 few-shot 推断不进行梯度更新，不将该事实推广为所有系统的内部机制。
