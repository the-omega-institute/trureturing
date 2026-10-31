# AURIC：约束递归、纯态对偶与内生静态历史

定义、定理与纸面证明　v51.0

2026 年 10 月 31 日　Asia/Singapore

原稿 PDF 元数据：标题「AURIC：约束递归、纯态对偶与内生静态历史」；作者「AURIC research continuation」；主题「Positive quadratic constraints, antipodal qubit duality, recursive atlases and spectral stability」。原稿页眉为「AURIC：约束递归、纯态对偶与内生历史」及「v51 / 2026-10-31」。

> 转写者说明：以下正文、证明及参考文献保留所供 v51.0 原稿的主张；其中“本文”“本轮”、获取与阅读范围、提交比较、未运行程序及未修改仓库等报告均归属原作者。另标“转写者校注”的文字为本次有限纸面核对所作的独立限定，不是原作者的改写。原稿身份：47,345 UTF-8 字节，SHA-256 <code>1c61568c975e4fab<wbr>48284e626f30edf9<wbr>599ef1aa40024fca<wbr>f25c37f1e09dab37</code>。原 TeX 注记要求 XeLaTeX 编译两次；未安装 Noto CJK OTF 时定义 `AURICFontPath`。这些排印指令不表示本 Markdown 已作 TeX 编译。

## 摘要

本文将“约束关系本身也可继续二元归一化”落实为可反复使用的数学构造。核心结论是：正半定二次残差的零条件等价于固定线性算子的核条件；可行密度态的支持恰落在共同核内，共同核为一维时才唯一选出纯态。对二维非零正约束，存在零罚归一态等价于约束秩一；约束态与唯一解态在 Bloch 球上互为对跖点，并满足精确的平方误差公式。约束矩阵、约束族与更高层关系可用带内部锚的纯态编码递归表示；每个有限编码态又可经全体二元主块接入项目已有的原生 AURIC 五模式等距编码。可数对象具有收敛的编码及严格截断界，但全局正性、闭路相容和解码精度仍须保留。进一步构造带内部起点约束的有限纯历史态，并证明显式谱隙下界；无限加权历史也可唯一为纯态，但给出的有界局部残差算子没有正谱隙。因此递归表达闭合、共同解存在、纯态唯一性与稳定性是四项可分别证明的性质。全文不使用数值试验或数学程序；项目既有结论、本轮推导和新增物理前提均明确分开。

## 1. 主结论与固定项目范围

用户直觉中最有力的命题可以精确写成：

> 在二元复空间，一条非零齐次线性关系的正平方残差为零，会把允许方向限制到一条复射线；归一化后得到唯一纯态。约束本身归一化后也是纯态，且与解态构成对跖对偶。约束的描述仍可进入同一种递归关系表示。

这条命题的关键是*正性、零水平与一维共同核*。“二次”不表示每个二次曲面都是线性的；“线性”也不是纯态的定义。纯态的有限维判据是正的迹一矩阵秩一，或等价地 $\rho ^2=\rho$。[[11](#bib-watrous2)]

本轮只冻结一次项目 `dev` 快照：<code>d2950bd36448c5d4<wbr>f6c4a3e5671ef734<wbr>185145c9</code>，提交时间 2026-10-31 21:19:22（新加坡）。相对 v50 的<code>a6ed97ef09691efe<wbr>d393942b6ae694c4<wbr>a44e5fc9</code>，theory 目录只有 <code>TOKEN_GRAPH_BLOW<wbr>UP_DEFECT_DECOMP<wbr>OSITION.md</code>追加了一个专门的图论段落；Ω 静态理论、V37、V42、V44 均未改变。本文所用的原生编码和历史核是项目既有结构，本轮对它们作新的组合推导。[[1](#bib-head)，[2](#bib-compare)，[7](#bib-token)]

采用同一内生整体的约定：观察者、相位参考、标签、记录、时钟、辅助槽位与环境均属于同一静态结构。数学上的张量因子或内部锚不引入整体之外的观察者。不过，规定它们内生并不会自动确定整体的状态、约束可满足性或所有内部接口的纯性。

| 对象 | 本文的准确含义 |
| --- | --- |
| 态 $\rho$ | 指定可观测代数上的正归一读出；有限维时用密度矩阵 |
| 正约束 $H$ | 通过 $\operatorname{Tr} (H\rho )=0$ 要求残差严格消失 |
| 约束编码 $\mathcal  C(H)$ | 保存 $H$ 的描述数据的另一状态；不等于原系统的状态 |
| 三轴接口 | 一个归一二阶正矩阵的三个实坐标；一般整体需要接口图册 |
| 纯态唯一性 | 全部合法零罚密度态构成一个秩一投影单点 |
| 稳定性 | 小残差可以定量控制到合法态的距离；通常还需谱隙 |

## 2. 二元正关系：三轴、平方约束与线性依赖

#### 定义 2.1（二元归一关系）

设

$$
G=\begin {pmatrix}A&C\\\overline  C&B\end {pmatrix}\succeq 0,
\qquad  S=A+B>0.
$$

令 $\rho =G/S$，并定义

$$
r=(x,y,z)=S^{-1}(2\operatorname {Re}C,-2\operatorname {Im}C,A-B).
$$

采用 $\sigma _y=\left (\begin {smallmatrix}0&-i\\i&0\end {smallmatrix}\right )$，其余 Pauli 矩阵为通常的 $\sigma _x,\sigma _z$。

<a id="thm:bloch"></a>

#### 定理 2.2（三轴球与秩一边界）

有

$$
\rho =\frac {I+r\cdot \sigma }{2},\qquad 
1-\|r\|^2=\frac {4(AB-|C|^2)}{S^2}\ge 0.
$$

每个闭单位球中的 $r$ 唯一给出一个二阶密度态。非零 $G$ 秩一当且仅当 $\|r\|=1$。

**证明。**

代入 Pauli 矩阵即可得到展开。$G$ 的正性等价于 $A,B\ge 0$ 及 $AB\ge |C|^2$；恒等式 $S^2-(A-B)^2-4|C|^2=4(AB-|C|^2)$ 给出球约束。反过来，$\rho$ 的两个特征值是 $(1\pm \|r\|)/2$。迹为一且行列式为零，恰等价于秩一。

∎

未归一化时可把 $G$ 写成

$$
G=\frac 12(SI+v\cdot \sigma ),\qquad  S\ge \|v\|.
$$

这是一条正锥条件。纯态射线位于 $S^2-\|v\|^2=0$ 的边界；归一化 $S=1$ 把它截成二维球面。因此“三个读出坐标”和“纯态具有两个连续自由度”相容。

<a id="thm:gram-linear"></a>

#### 定理 2.3（二元 Gram 纯态与线性依赖）

设 $u,v$ 为同一复 Hilbert 空间中的两个向量，不全为零。取第一变量共轭线性的内积并令

$$
G=\begin {pmatrix}\langle  u,u\rangle &\langle  u,v\rangle \\
\langle  v,u\rangle &\langle  v,v\rangle \end {pmatrix}.
$$

则以下条件等价：$G/\operatorname{Tr}  G$ 为纯态；$\|u\|^2\|v\|^2=|\langle  u,v\rangle |^2$；$u,v$ 线性相关；存在非零 $(\alpha ,\beta )$ 使 $\alpha  u+\beta  v=0$。

**证明。**

定义 $V(\alpha ,\beta )=\alpha  u+\beta  v$，则 $G=V^\dagger  V$，所以 $\ker  G=\ker  V$。非零二阶正矩阵秩一等价于核非零，亦等价于行列式为零。

∎

这里确实出现“纯态对应线性关系”。但系数 $(\alpha ,\beta )$ 可以随数据改变；全体秩一矩阵并不构成线性空间，两个不同纯态的凸组合通常为混态。下一节把*固定关系如何选出一个纯态*说清楚。

## 3. 正二次零约束的线性核定理

#### 定义 3.1（共同残差）

给定有限维 $\mathcal{H}$、线性算子 $L_j:\mathcal{H} \to \mathcal  K_j$ 与 $w_j>0$，定义

$$
H=\sum _{j=1}^m w_jL_j^\dagger  L_j\succeq 0,
\qquad  K=\bigcap _{j=1}^m\ker  L_j.
$$

对向量的残差为 $\langle \psi ,H\psi \rangle$；对密度态的残差为 $\operatorname{Tr} (H\rho )$。

<a id="thm:kernel"></a>

#### 定理 3.2（零二次型、线性核与允许支持）

对以上对象，有

$$
\langle \psi ,H\psi \rangle =0\iff \psi \in  K=\ker  H,
$$

$$
\operatorname{Tr} (H\rho )=0\iff \operatorname{supp} \rho \subseteq  K.
$$

因此全部归一零罚态恰为 $\mathcal{D} (K)$。若 $\dim  K=0$，没有解；若 $\dim  K=1$，唯一解为纯态；若 $\dim  K\ge 2$，可行集合包含纯态与混态。

**证明。**

由定义

$$
\langle \psi ,H\psi \rangle =\sum _jw_j\|L_j\psi \|^2.
$$

各项非负且系数严格正，因此和为零等价于每个 $L_j\psi =0$。另一方面，正算子满足

$$
\langle \psi ,H\psi \rangle =\|H^{1/2}\psi \|^2,
\quad 
\operatorname{Tr} (H\rho )=\|H^{1/2}\rho ^{1/2}\|_{\mathrm {HS}}^2.
$$

第二式为零恰表示 $\rho ^{1/2}$ 的像落在 $\ker  H$ 中。若核为一维，支持在其中的正迹一矩阵只能是该射线的正交投影。若核至少二维，任意两个正交核向量的投影之平均就是混合零罚态。

∎

各 $L_j^\dagger  L_j$ 不必交换。这里使用的是每一项的正性，所以没有正负项抵消所造成的伪零残差。

#### 说明 3.3（两项条件不能省略）

$\|\psi \|^2=1$ 是非零水平的二次条件，其解集为球面。$|a|^2-|b|^2=0$ 是非正的二次零条件，解集也不是线性空间：$(1,1)$ 与 $(1,-1)$ 满足，而它们的和不满足。因此定理说的是*正二次型的零集合*，而非任意二次方程。

一般线性读出约束同样不等于纯态。例如在二元空间，

$$
\operatorname{Tr} (\rho \sigma _x)=\operatorname{Tr} (\rho \sigma _y)=\operatorname{Tr} (\rho \sigma _z)=0
$$

唯一给出 $\rho =I/2$，这是严格混态。即使用正投影 $P_i=(I+\sigma _i)/2$ 来写 $\operatorname{Tr} (\rho  P_i)=1/2$，结论仍相同。非零水平的仿射约束不适用共同零核定理。

## 4. 核心对偶：约束纯态与解纯态互为对跖点

<a id="thm:antipodal"></a>

#### 定理 4.1（二元正约束的对跖对偶）

设 $H\in  M_2(\mathbb{C} )$、$H\succeq 0$ 且 $H\ne 0$，令

$$
\widehat  H=\frac  H{\operatorname{Tr}  H}=\frac {I+s\cdot \sigma }{2}.
$$

以下三项等价：存在归一零罚态；$\operatorname{rank}  H=1$；$\|s\|=1$。成立时零罚态唯一，且

$$
\boxed {\rho _*=I-\widehat  H=\frac {I-s\cdot \sigma }{2}.}
$$

约束方向 $s$ 与解方向 $r_*=-s$ 都在球面上。

**证明。**

非零二阶正矩阵只有秩一、秩二两种可能。秩二时核为零；秩一时核是一条复射线。归一秩一矩阵 $\widehat  H$ 是投影，$I-\widehat  H$ 正是其核投影。定理 [3.2](#thm:kernel) 给出唯一性；定理 [2.2](#thm:bloch) 给出球面条件。

∎

对具体线性行关系 $\ell =(\alpha ,\beta )\ne 0$，取 $H=\ell ^\dagger \ell$。一个归一解向量是

$$
\psi _*=
\frac {1}{\sqrt {|\alpha |^2+|\beta |^2}}
\begin {pmatrix}-\beta \\\alpha \end {pmatrix},
\qquad  \ell \psi _*=0.
$$

整体相位不改变其纯态投影。反过来，每个纯态投影 $P$ 都可由 $H=c(I-P)$、$c>0$ 唯一选出。

<a id="cor:antipodal-error"></a>

#### 推论 4.2（支持平面与精确误差）

设 $\rho =(I+r\cdot \sigma )/2$，取定理 [4.1](#thm:antipodal) 的约束。采用 $D(\rho ,\sigma )=\tfrac 12\|\rho -\sigma \|_1$，有

$$
\varepsilon =\operatorname{Tr} (\rho \widehat  H)=\frac {1+r\cdot  s}{2},
$$

$$
\boxed {D(\rho ,\rho _*)^2
=\varepsilon -\frac {1-\|r\|^2}{4}\le \varepsilon .}
$$

等号成立当且仅当 $\rho$ 为纯态。

**证明。**

Pauli 迹正交性给出第一式。二元差矩阵 $\rho _r-\rho _t$ 的特征值为 $\pm \|r-t\|/2$，故 $D(\rho _r,\rho _t)=\|r-t\|/2$。将 $t=-s$、$\|s\|=1$ 代入并展开平方即得。

∎

零罚条件 $r\cdot  s=-1$ 是球体的一个支持平面。它与球的唯一接触点就是 $-s$。这解释了为什么这里的*线性读出条件*会唯一选中*非线性纯态边界*上的一点。若输入也纯，且它与 $-s$ 的夹角为 $\delta$，则

$$
\varepsilon =\sin ^2(\delta /2),\qquad  D=|\sin (\delta /2)|.
$$

在该归一二元模型中，平方概率、几何角度和距离误差确实由同一个关系连接。

$H=0$ 必须作为零约束单独标记：此时所有态都合法，不能除以 $\operatorname{Tr}  H$。高维的对应条件是 $\dim \ker  H=1$，即 $\operatorname{rank}  H=d-1$；高维约束自身通常不是秩一，故“约束与解都纯”的对跖形式是二元接口特有的。

#### 命题 4.3（对跖对偶不是未知态的通用量子门）

将 $P\mapsto  I-P$ 线性延拓为

$$
\mathcal  N(X)=\operatorname{Tr} (X)I-X
$$

得到正且保迹的二元映射，但它不完全正。

**证明。**

对 Bell 投影 $P_\Phi$，

$$
(\mathcal  N\otimes \mathrm {id})(P_\Phi )=\frac {I_4}{2}-P_\Phi .
$$

该算子在 $\Phi$ 方向的特征值是 $-1/2$，所以不能是双系统的密度态。

∎

已知约束时选取其核态是一项数学构造；把任意未知输入都变成正交纯态则是另一项物理要求。所有辅助系统均内生，也不会改变完全正性条件。

## 5. 指数二究竟特殊在哪里

#### 命题 5.1（相同零集合不能单独选定指数二）

任意 $q>0$ 都有

$$
\|L\psi \|^q=0\iff  L\psi =0.
$$

因此仅从“残差为零给出线性关系”不能排除四次方或其他正指数。

<a id="thm:exponent"></a>

#### 定理 5.2（线性残差与正算子读出的二次闭合）

设 $L\ne 0$。若存在固定正算子 $H_L$ 使对所有 $\psi$ 都成立

$$
\|L\psi \|^q=\langle \psi ,H_L\psi \rangle ,
$$

其中 $q>0$，则 $q=2$。反之，$q=2$ 时可取 $H_L=L^\dagger  L$。

**证明。**

取 $L\psi \ne 0$，以 $c\psi$ 替换 $\psi$。两侧分别按 $|c|^q$ 和 $|c|^2$ 缩放，故对所有 $|c|>0$ 相等迫使 $q=2$。反向等式是伴随的定义。

∎

对于非平凡投影残差 $L=\lvert 0\rangle\langle 0\rvert$，即使只在单位向量上要求，仍得到 $q=2$。令 $\psi =\sqrt  p\lvert 0\rangle +e^{i\theta }\sqrt {1-p}\lvert 1\rangle$。若正算子 $H$ 的期望等于 $p^{q/2}$，两端 $p=1,0$ 迫使$H_{00}=1,H_{11}=0$；正性进一步迫使 $H_{01}=0$。于是该期望等于 $p$，对所有 $0<p<1$ 相等仍要求 $q=2$。

因此平方的精确特殊性是：

> 线性振幅关系的非负残差，能用同一个正算子表示，并且对统计混合按 $\rho \mapsto \operatorname{Tr} (H\rho )$ 仿射地传递。

这为“关系可以继续连接关系”提供二次闭合。它是一条给定复线性空间、内积及仿射状态读出后的兼容性定理；这些前提并未由“本体唯一”或“静态图”几个词独立推出。项目 Ω 文稿也明确把复 Hilbert 表示、正归一态和 CP 仪器作为新增结构。[[3](#bib-omega)]

任意高次多项式可以通过单项式坐标提升成线性读出，但新坐标仍需满足其像的相容方程。例如 $x^4+y^4=1$ 在 $(x^4,x^3y,x^2y^2,xy^3,y^4)$ 中是线性等式，这些五个坐标却不能独立指定。二次正型的优点是在*原变量*中直接成为固定线性映射的平方范数。

## 6. 与原生 AURIC 五模式的明确接合

本节重述并检验项目 V37 的固定编码；它是既有结果，不把重新阅读计为本轮新增。V44 已将同一编码用于高维接口。[[4](#bib-v37)，[5](#bib-v44)]

令

$$
\nu =\frac 1{1+2\sqrt 3+\sqrt {11}},\qquad 
a_\nu =\frac \nu 2(\sqrt 3+\sqrt {11}),\qquad  u_0=(a_\nu ,a_\nu ,\nu ).
$$

在数值模式 $s\in \{0,2,3,5,25\}$ 上定义五个二元正效果：

$$
\begin {aligned}
E_{25}&=\frac \nu 2(\sqrt 3 I-\sigma _x-\sigma _y-\sigma _z),& E_0&=3E_{25},\\
E_2&=\frac \nu 2(\sqrt {11}I+3\sigma _x+\sigma _y+\sigma _z),\\
E_5&=\frac \nu 2(\sqrt {11}I+\sigma _x+3\sigma _y+\sigma _z),&
E_3&=\nu (I+\sigma _z).
\end {aligned}
$$

每个效果的标量系数等于其 Pauli 向量长度，故正且秩一；直接相加得 $\sum _sE_s=I$。写 $E_s=\lvert \eta _s\rangle\langle \eta _s\rvert$ 并定义

$$
J\psi =\sum _s\lvert s\rangle \langle \eta _s,\psi \rangle .
$$

于是 $J^\dagger  J=I$，且 $J^\dagger \lvert s\rangle\langle s\rvert J=E_s$。它确实是进入原五模式的固定等距编码。

<a id="thm:native"></a>

#### 定理 6.1（原生三读出中的球与线性恒等式）

对 $G\succeq 0$ 定义 $w_s=\operatorname{Tr} (GE_s)$，以及同尺度量

$$
N=\operatorname{Tr}  G,\quad  X=w_2+w_{25},\quad  Y=w_5+w_{25},\quad 
Z=w_3,\quad \kappa =w_{25}.
$$

则

$$
\boxed {N-X-Y-Z-2\kappa =0.}
$$

其完整相容锥为

$$
\begin {gathered}
N\ge 0,\qquad  2\kappa =N-X-Y-Z,\\
\big \|(X-a_\nu  N,\,Y-a_\nu  N,\,Z-\nu  N)\big \|\le \nu  N.
\end {gathered}
$$

$N>0$ 时，球面等号恰对应 $G$ 秩一。

**证明。**

令 $v_i=\operatorname{Tr} (G\sigma _i)$，则

$$
G=\tfrac 12(NI+v\cdot \sigma ),\qquad  \|v\|\le  N.
$$

从效果公式得到

$$
(X,Y,Z)=Nu_0+\nu  v,
\qquad  \kappa =\tfrac \nu 2(\sqrt 3N-v_x-v_y-v_z).
$$

利用 $1-2a_\nu -\nu =\nu \sqrt 3$ 得到线性恒等式。反向从三读出恢复 $v$，锥不等式正好保证重建的 $G$ 正。$N=0$ 强迫全部量为零；$N>0$ 时用定理 [2.2](#thm:bloch) 判别秩。

∎

这给出同一固定编码中的“四推一”，但该线性关系对*所有混态*也成立。纯态需要额外的球面等号，不能只靠线性恒等式识别。归一态的原三均值为

$$
u(\rho )=u_0+\nu  r,
\qquad 
D(\rho ,\widetilde \rho )=\frac {\|u(\rho )-u(\widetilde \rho )\|}{2\nu }.
$$

这是一条明确的三轴稳定性公式，适用于该指定编码族。

数值模式与语义模式对应为$(0,2,3,5,25)\leftrightarrow (\varnothing ,1,2,3,13)$。这里 $X,Y$ 是含共同模式的占据读出，不能直接当成单独模式概率。在此编码中 $w_0=3\kappa$；$F[\varnothing ]$ 仍是一个事件，总归一化是 $\sum _sw_s=N$。V42 对一般原生五模式还保留额外的关系纤维；本节的 $J$ 选择了一个具体相容子类。[[6](#bib-v42)]

将定理 [4.1](#thm:antipodal) 接入 $J$，约束与解的三读出满足

$$
\boxed {u(\rho _*)=2u_0-u(\widehat  H).}
$$

因此对跖对偶在原 AURIC 三轴中变成以 $u_0$ 为中心的点反射。这就是本轮“约束自身也能提升”的一个可直接检验的原生实例。

## 7. 约束的描述可以再次编码：有限与可数递归

<a id="prop:scalar-chart"></a>

#### 命题 7.1（每个复关系系数的二元三轴图表）

任意有限复数 $c$ 都可用二元振幅 $(1,c)$ 编码，得到纯态

$$
P(c)=\frac 1{1+|c|^2}
\begin {pmatrix}1&\overline  c\\c&|c|^2\end {pmatrix},
\quad 
r(c)=\frac {(2\operatorname {Re}c,\,2\operatorname {Im}c,\,1-|c|^2)}{1+|c|^2}.
$$

有 $\|r(c)\|=1$，且可从三轴恢复

$$
c=\frac {r_x+ir_y}{1+r_z}.
$$

因此一列约束系数可以逐项成为一列带标签的球面图表，再逐项接入同一个原生 $J$。

**证明。**

$P(c)$ 是归一外积；恒等式$4|c|^2+(1-|c|^2)^2=(1+|c|^2)^2$ 给出球面等式。$1+r_z=2/(1+|c|^2)>0$，代入即可恢复 $c$。

∎

这是复平面与去掉一个极点的球面的射影坐标转换。它已经足以解释“关系自身也能三轴提升”；还须保留各图表的标签、类型和语义连接。将这些图表统一装入一个可归一对象，可用下面的锚定构造。

#### 定义 7.2（带内部锚的有限编码）

对有指定类型、形状与次序的复数据 $z=(z_1,\ldots ,z_M)$，令

$$
v(z)=(1,z_1,\ldots ,z_M)^{\mathsf  T},\qquad 
\mathcal  C(z)=\frac {v(z)v(z)^\dagger }{1+\sum _j|z_j|^2}.
$$

锚 $1$ 是编码中的一个指定内部坐标。

<a id="thm:finite-code"></a>

#### 定理 7.3（有限精确编码与递归闭合）

$\mathcal  C(z)$ 为纯态，且

$$
\boxed {z_j=\frac {\mathcal  C(z)_{j0}}{\mathcal  C(z)_{00}}.}
$$

因此有限矩阵、有限约束族以及更高层关系的全部复系数均可被无损编码。把编码矩阵再次排列成数据并重复构造，任意有限层都可逐层解码。

**证明。**

分母严格正，外积正且秩一，迹为一。锚对角元为 $1/(1+\|z\|^2)$，第 $j0$ 元为 $z_j/(1+\|z\|^2)$。相除即得逆式。逐层使用逆式给出有限归纳。

∎

零矩阵也有合法编码。没有锚的向量化纯投影会丢失整体尺度和整体相位，所以不能独自恢复完整约束矩阵。“混态描述有纯态编码”不表示原系统由此变纯；两者属于不同对象层。同样，矛盾约束的描述也有合法编码，编码存在不证明共同解存在。

> **转写者校注（空数据端点）。** 允许空数据列时，$M=0$ 给出一维编码 $[1]$。第 8 节图册要求 $d\ge2$；接入该图册前可作指定的零坐标嵌入 $[1]\mapsto\operatorname{diag}(1,0)$，其原一维数据由指定坐标取回。该端点不直接套用 $d=1$ 的成对主块公式。

#### 命题 7.4（纯态描述编码不等于任意输入的物理纯化）

若凸态域上的仿射映射 $\Phi$ 将每一个输入态（包括混合输入）都映到纯态，则 $\Phi$ 为常值。

**证明。**

若有两个不同纯输出 $P\ne  Q$，则

$$
\Phi ((\rho +\sigma )/2)=(P+Q)/2
$$

具有至少二维支持，与假设矛盾。

∎

因此知道矩阵描述后进行非线性编码，与对单份未知态施加同一个确定 CPTP 信道，不能混为同一操作。

#### 定义 7.5（可数锚定编码）

对可数复数据列 $c=(c_j)_{j\ge 1}$，每项均为有限复数，令

$$
f(z)=\frac {z}{1+|z|},\qquad 
v(c)=(1,2^{-1}f(c_1),2^{-2}f(c_2),\ldots )\in \ell ^2,
$$

$$
\mathcal  C_\infty (c)=\frac {\lvert v(c)\rangle\langle v(c)\rvert }{\|v(c)\|^2}.
$$

<a id="thm:countable-code"></a>

#### 定理 7.6（可数解码与严格截断界）

该编码满足 $1\le \|v(c)\|^2<4/3$，故 $\mathcal  C_\infty (c)_{00}>3/4$。其逆式为

$$
q_j=2^j\frac {\mathcal  C_\infty (c)_{j0}}{\mathcal  C_\infty (c)_{00}},
\qquad  c_j=\frac {q_j}{1-|q_j|}.
$$

令 $c^{\le  M}$ 把第 $M$ 项以后的数据置零，则

$$
D\bigl (\mathcal  C_\infty (c),\mathcal  C_\infty (c^{\le  M})\bigr )
=\sqrt {\frac {\sum _{j>M}4^{-j}|f(c_j)|^2}{\|v(c)\|^2}}
\le \frac {2^{-M}}{\sqrt 3}.
$$

**证明。**

$|f(z)|<1$，而 $\sum _{j\ge 1}4^{-j}=1/3$，所以范数有界。锚比值恢复 $f(c_j)$，其逆映射是 $q\mapsto  q/(1-|q|)$。写 $v=v_M+r_M$，两部分正交。两个归一向量的重叠模平方是 $\|v_M\|^2/\|v\|^2$。纯态迹距离的平方是该重叠模平方的补数；这可在两向量张成的二维空间直接求得。最后用 $\|v\|^2\ge 1$ 和 $\sum _{j>M}4^{-j}=4^{-M}/3$。

∎

有界算子在指定可分空间、指定基中由可数矩阵元唯一确定，因此可先排列矩阵元再用本编码。无限维恒等算子不是 Hilbert–Schmidt 算子，不能直接把它无权向量化；上述压缩及可求和权重正好避免这一错误。可数约束族、多层递归塔的全部标签和系数也仍可排列为一个可数列。

#### 命题 7.7（有限坐标的恢复稳定性）

记 $\varepsilon =\|\mathcal  C_\infty (c)-\mathcal  C_\infty (d)\|_1$。若 $|c_j|,|d_j|\le  M_0$，则

$$
|c_j-d_j|\le \frac 43(1+M_0)^2(2^j+1)\varepsilon .
$$

**证明。**

将两编码的锚对角元记为 $a,b>3/4$，对应非对角元记为 $x,y$。有 $|y|/b\le 2^{-j}$，因此

$$
2^j|x/a-y/b|\le \tfrac 43(2^j|x-y|+|a-b|)
\le \tfrac 43(2^j+1)\varepsilon .
$$

在 $|q|\le  M_0/(1+M_0)$ 上，逆映射的 Lipschitz 常数至多 $(1+M_0)^2$；用三角不等式展开两个分母即可得到该界。

∎

高位解码常数随 $2^j$ 增长，不能把编码态的快速截断收敛理解成有限精度下统一恢复全部无限数据。有限无界数据也有同样问题：$z=R$ 与 $z=2R$ 的编码迹距离为

$$
\frac {R}{\sqrt {(1+R^2)(1+4R^2)}}\longrightarrow 0,
$$

而原数据间距离为 $R$。精确注入、稳定逆映射与有限资源实现是不同要求。

## 8. 完整二元图册与关系之间的全局约束

### 8.1 全体主块提供精确高维表示

<a id="thm:atlas"></a>

#### 定理 8.1（带质量的二元主块重建）

给定 $d\ge 2$ 及 $\rho \in \mathcal{D} (\mathbb{C} ^d)$，设 $p_i=\rho _{ii}$，对每个 $i<j$ 定义主块

$$
B_{ij}=\begin {pmatrix}p_i&\rho _{ij}\\\overline {\rho _{ij}}&p_j\end {pmatrix},
\quad  N_{ij}=p_i+p_j.
$$

正质量时令 $r_{ij}$ 为 $B_{ij}/N_{ij}$ 的三轴。全体带标签、质量与零标记的接口精确决定 $\rho$，其中

$$
\rho _{ij}=\tfrac 12N_{ij}(r_{ij,x}-ir_{ij,y}),\qquad 
p_i=\tfrac 12N_{ij}(1+r_{ij,z}).
$$

质量满足 $\sum _{i<j}N_{ij}=d-1$。

**证明。**

每个主块正。若 $N_{ij}=0$，正性迫使整个块为零；无需定义条件态。正质量时由 Pauli 展开反解得到各矩阵元。每个 $p_i$ 在总质量中出现 $d-1$ 次，所以质量和为 $d-1$。亦可写

$$
\rho =\sum _{i<j}\iota _{ij}B_{ij}\iota _{ij}^\dagger 
-(d-2)\operatorname{diag} (p_1,\ldots ,p_d),
$$

其中 $\iota _{ij}$ 把二元块嵌回对应坐标。

∎

这些是*两振幅主块*，不是任意多体系统的两体约化态。接口是冗余的；在完整重叠信息和总迹已知时，某些质量可以从相容关系恢复。保留显式质量的目的，是让独立局部接口及零边界具有明确的解码规则。该构造已在 V44 给出。[[5](#bib-v44)]

取

$$
K_{ij}=\frac {\lvert 0\rangle \langle i\rvert +\lvert 1\rangle \langle j\rvert }{\sqrt {d-1}},
\quad 
V_d=\sum _{i<j}\lvert ij\rangle \otimes  K_{ij}.
$$

每个基投影出现 $d-1$ 次，故 $V_d^\dagger  V_d=I$。接上原 AURIC 编码得到

$$
\boxed {W_d=(I_{\mathrm {label}}\otimes  J)V_d.}
$$

这是等距映射，每个正质量分支的原三轴为 $u_0+\nu  r_{ij}$。标签、相干性和分支质量均在同一整体内部。若测量标签及相应读口，一次仪器执行给出一个分支或读数；完整图册需要相应统计资料，不能从单份未知态一次获得全部矩阵元。

若对 $V_d$ 的输出标签去相干，得到 $\bigoplus _{i<j}B_{ij}/(d-1)$；对 $W_d$ 的输出作同样操作，则每个块相应替换为 $JB_{ij}J^\dagger /(d-1)$。它仍可在数学上由矩阵元反演，但当 $d>2$ 时不存在对所有输入的共同 CPTP 左逆。取 $\psi _\pm =(\lvert 1\rangle \pm \lvert 2\rangle )/\sqrt 2$，输入迹距离为 $1$，只有 $12$ 分支的差保留，输出迹距离为 $1/(d-1)$。若有 CPTP 左逆，就违反迹距离收缩。保留相干的 $V_d$ 与去相干的分支表必须分开。[[5](#bib-v44)，[12](#bib-watrous3)]

### 8.2 局部纯关系何时能拼成一个整体

所有二元块各自合法，仍可能相互冲突。项目 V37、V44 的简单例子是

$$
M=\frac 13\begin {pmatrix}1&-1&-1\\-1&1&-1\\-1&-1&1\end {pmatrix}.
$$

每个二阶主块正且秩一，迹也全局归一；但

$$
M(1,1,1)^{\mathsf  T}=-\tfrac 13(1,1,1)^{\mathsf  T},
$$

所以不存在这个整体密度态。[[4](#bib-v37)，[5](#bib-v44)]

<a id="thm:cycle"></a>

#### 定理 8.2（饱和边关系的闭路判据）

给定连通图，每个顶点质量 $m_i>0$，每条定向边相位满足$|u_{ij}|=1$、$u_{ji}=\overline {u_{ij}}$。存在振幅 $a_i$ 使

$$
|a_i|^2=m_i,\qquad 
a_i\overline {a_j}=\sqrt {m_im_j}\,u_{ij}
$$

当且仅当每条有限闭路的相位乘积为 $1$。解在连通图上只差共同整体相位。

**证明。**

必要性由沿闭路的顶点相位逐项抵消得到。反过来，固定根点相位为 $1$，令从根到 $i$ 的路径相位乘积为 $q_i$，并取 $a_i=\sqrt {m_i}\,\overline {q_i}$。闭路条件保证 $q_i$ 与路径选择无关。若 $i\to  j$ 是边，则 $q_j=q_iu_{ij}$，因此$a_i\overline {a_j}=\sqrt {m_im_j}u_{ij}$。任意另一解的相位比沿边恒定，连通性给出共同相位。

∎

零质量点的所有相关矩阵元先由正性强制为零，相关相位没有定义；对剩余正质量连通分量使用上一定理。若图可数并要得到 $\ell ^2$ 中的归一向量，还需 $0<\sum _i m_i<\infty$。这些条件描述同一个内部整体的自洽性，并不依赖外部观察者。

更直接的线性残差例是

$$
z_1+z_2=0,\quad  z_2+z_3=0,\quad  z_3+z_1=0.
$$

每个单独关系在其两个局部变量构成的二元空间中，都选出一条纯态射线，但三者在共同的三变量空间中合起来只有零向量。对 $\|z\|=1$，

$$
|z_1+z_2|^2+|z_2+z_3|^2+|z_3+z_1|^2
=\|z\|^2+|z_1+z_2+z_3|^2\ge 1.
$$

因此“约束之间的关系”可以继续分析，并且能严格检出归一共同解不存在。

### 8.3 Schur 余量：逐层加入关系的精确判据

<a id="thm:schur"></a>

#### 定理 8.3（带奇异支撑的递归正性）

对有限维 Hermitian 块矩阵

$$
Q=\begin {pmatrix}A&b\\b^\dagger &c\end {pmatrix},
$$

有 $Q\succeq 0$ 当且仅当

$$
A\succeq 0,\qquad  b\in \operatorname{Ran}  A,\qquad 
s=c-b^\dagger  A^+b\ge 0.
$$

成立时 $\operatorname{rank}  Q=\operatorname{rank}  A+\mathbf 1_{s>0}$。

**证明。**

若 $Q\succeq 0$，取 $x\in \ker  A$，改变最后坐标的复相位和大小，正性迫使 $x^\dagger  b=0$，故 $b\in \operatorname{Ran}  A$。令 $y=A^+b$，则 $Ay=b$，且

$$
\begin {pmatrix}x\\t\end {pmatrix}^{\!\dagger }
Q\begin {pmatrix}x\\t\end {pmatrix}
=(x+ty)^\dagger  A(x+ty)+s|t|^2.
$$

这同时证明充要性。相应可逆合同变换把 $Q$ 化为 $A\oplus  s$，给出秩式。

∎

$s=0$ 表示新增方向没有增加秩，亦即相关 Gram 向量没有新增正交分量。只有已有块 $A$ 秩一时，这才继续保持纯态；若 $A$ 秩二，零余量仍保持秩二。这正是把“关系的约束”再次纳入递归所需的完整条件。[[5](#bib-v44)]

## 9. 算子值三轴：保留全部关系的另一种递归

对一个二元因子与其余内部系统的状态，写

$$
\rho =\begin {pmatrix}A&C\\C^\dagger &B\end {pmatrix},
\quad 
S=A+B,\ X=C+C^\dagger ,\ Y=i(C-C^\dagger ),\ Z=A-B.
$$

则恒等地

$$
\boxed {\rho =\tfrac 12(I\otimes  S+\sigma _x\otimes  X+
\sigma _y\otimes  Y+\sigma _z\otimes  Z).}
$$

下一层应继续分解 $S,X,Y,Z$ 四个算子。总归一化只给出 $\operatorname{Tr}  S=1$，不会确定整个 $S$；$X,Y,Z$ 是 Hermitian 系数，一般不是正态。若要把这些系数也当成正归一对象，应先使用第 7 节的描述编码，明确转换了类型。

对 $n$ 个二元因子，反复展开得到

$$
\rho =2^{-n}\sum _{\alpha \in \{0,x,y,z\}^n}
r_\alpha \,\sigma _{\alpha _1}\otimes \cdots \otimes \sigma _{\alpha _n},
$$

$$
r_\alpha =\operatorname{Tr} \bigl (\rho \,\sigma _{\alpha _1}\otimes \cdots \otimes \sigma _{\alpha _n}\bigr ).
$$

证明只需张量 Pauli 基的迹正交性；总迹固定一个系数，一般仍有 $4^n-1$ 个实自由度。这是递归使用同一二元格式的精确展开。

不能机械地把标量球条件改成 $X^2+Y^2+Z^2\preceq  S^2$。Bell 纯态给出 $S=I/2$、$X=\sigma _x/2$、$Y=-\sigma _y/2$、$Z=\sigma _z/2$，左侧为 $3I/4$，右侧为 $I/4$。正确约束始终是完整块矩阵正性。项目 V37、V44 已明确保留这一差别。[[4](#bib-v37)，[5](#bib-v44)]

## 10. 从递归残差到稳定性：共同核与谱隙

<a id="thm:countable-H"></a>

#### 定理 10.1（可数约束族的有界正残差）

设 $L_j:\mathcal{H} \to \mathcal  K_j$ 为可分空间之间的有界算子。令

$$
H=\sum _{j\ge 1}\frac {2^{-j}}{1+\|L_j\|^2}L_j^\dagger  L_j.
$$

级数在算子范数中收敛，$0\preceq  H\preceq  I$，且

$$
\ker  H=\bigcap _{j\ge 1}\ker  L_j.
$$

**证明。**

每项正且范数至多 $2^{-j}$，故绝对收敛。对任意 $\psi$，期望是严格正权重乘 $\|L_j\psi \|^2$ 的非负级数，为零当且仅当每项为零。

∎

这个 $H$ 保存共同解空间，未必保留每条约束的来源标签，也未必是迹类；若需完整描述，应连同原约束族一起编码，不能无条件写 $H/\operatorname{Tr}  H$。

<a id="thm:gap"></a>

#### 定理 10.2（一维核的谱隙误差界）

若 $H\succeq 0$、$\ker  H=\operatorname {span}\{\phi \}$、$\|\phi \|=1$，且

$$
H\succeq \Delta (I-\lvert \phi\rangle\langle \phi\rvert ),\qquad \Delta >0,
$$

则对任意密度态 $\rho$ 有

$$
\boxed {D(\rho ,\lvert \phi\rangle\langle \phi\rvert )\le \sqrt {\frac {\operatorname{Tr} (H\rho )}{\Delta }}.}
$$

**证明。**

令 $p=1-\langle \phi ,\rho \phi \rangle$。算子不等式给出 $\Delta  p\le \operatorname{Tr} (H\rho )$。将 $\rho$ 谱分解为 $\sum _j\lambda _j\lvert \psi _j\rangle\langle \psi _j\rvert$，迹范数凸性和 Cauchy 不等式给出

$$
D(\rho ,\lvert \phi\rangle\langle \phi\rvert )
\le \sum _j\lambda _j\sqrt {1-|\langle \phi ,\psi _j\rangle |^2}
\le \sqrt  p.
$$

两式合并即可。正常迹类态的可数谱分解给出同样证明。

∎

> **转写者校注（能量定义域）。** 本节谱隙误差界按有界正算子 $H$ 理解，此时任意正常迹类密度态的 $\operatorname{Tr}(H\rho)$ 均有定义。若扩展到非有界正自伴算子，须先以其正二次型定义扩展能量并注明有限能量域；这里不另作该域扩张。

在存在非零正交补方向时，取 $H=\Delta (I-\lvert \phi\rangle\langle \phi\rvert )$、$\psi =\sqrt {1-p}\phi +\sqrt  p\eta$，其中 $p\in [0,1]$、$\|\eta \|=1$、$\eta \perp \phi$，可以达到平方根界。若核至少二维，低能量只保证接近允许支持，不能指定一个唯一纯态。

> **转写者校注（多维核的稳定性条件）。** 上句“低能量只保证接近允许支持”仍需相对于核补空间的正谱隙：$H\succeq\Delta(I-P_K)$、$\Delta>0$，其中 $P_K$ 为核投影。没有该条件，一维核或多维核都不能仅由能量趋零推出到允许支持的距离趋零。

若没有正谱隙，甚至一维核也不够：在 $\ell ^2$ 上取

$$
He_0=0,\qquad  He_n=n^{-1}e_n\quad (n\ge 1).
$$

态 $\lvert e_n\rangle\langle e_n\rvert$ 的能量趋零，到 $\lvert e_0\rangle\langle e_0\rvert$ 的迹距离却恒为 $1$。

在二元正确／残差基中，若

$$
\rho =\begin {pmatrix}1-p&C\\\overline  C&p\end {pmatrix},
\quad  |C|^2\le  p(1-p),
$$

则

$$
D(\rho ,\lvert 0\rangle\langle 0\rvert )=\sqrt {p^2+|C|^2},\qquad  p\le  D\le \sqrt  p.
$$

相干关系为零时达到下界，纯态时达到上界。因此“误差的概率”和“状态的距离”需要注明是哪种量；归一化本身不会把所有误差统一成同一种收缩过程。

## 11. 内生静态历史：线性传播怎样唯一选出纯整体

项目 Ω 静态理论已有有限传播差分 $D_T$ 及 $K_T=D_T^\dagger  D_T$，并把其核与初始空间等距对应。[[3](#bib-omega)]以下在此基础上加入明确的内部起点约束，证明纯态唯一性和稳定界。

### 11.1 有限历史

给定有限维 $\mathcal{H}$、酉算子 $U_1,\ldots ,U_T$、单位向量 $\phi$，记$N=T+1$、$W_0=I$、$W_t=U_t\cdots  U_1$。时钟 $\lvert 0\rangle ,\ldots ,\lvert T\rangle$ 是内部记录坐标。对 $x=(x_0,\ldots ,x_T)$ 定义*未缩放*差分

$$
D_Tx=(x_1-U_1x_0,\ldots ,x_T-U_Tx_{T-1}),
$$

$$
H_T=D_T^\dagger  D_T+\lvert 0\rangle\langle 0\rvert \otimes (I-\lvert \phi\rangle\langle \phi\rvert ).
$$

<a id="thm:finite-history"></a>

#### 定理 11.1（唯一内生历史与显式谱隙）

有

$$
\ker  H_T=\operatorname {span}\{\Omega _T\},\qquad 
\Omega _T=\frac 1{\sqrt  N}\sum _{t=0}^T\lvert t\rangle \otimes  W_t\phi ,
$$

并且

$$
\boxed {H_T\succeq  N^{-2}(I-\lvert \Omega _T\rangle\langle \Omega _T\rvert ).}
$$

故

$$
D(\rho ,\lvert \Omega _T\rangle\langle \Omega _T\rvert )\le  N\sqrt {\operatorname{Tr} (H_T\rho )}.
$$

**证明。**

正零残差要求 $x_t=W_tx_0$，起点约束要求 $x_0\in \operatorname {span}\{\phi \}$，所以核恰为所示射线。

用内部受控酉 $\sum _t\lvert t\rangle\langle t\rvert \otimes  W_t$ 消去传播中的 $U_t$。对正交于平坦历史的向量写

$$
x_t=a_t\phi +b_t,\qquad  b_t\perp \phi ,\qquad \sum _ta_t=0.
$$

令

$$
E_a=\sum _{t=1}^T|a_t-a_{t-1}|^2,\qquad 
E_b=\|b_0\|^2+\sum _{t=1}^T\|b_t-b_{t-1}\|^2.
$$

能量恰为 $E_a+E_b$。由 $a_t=N^{-1}\sum _s(a_t-a_s)$ 及路径上的 Cauchy 不等式，

$$
|a_t|^2\le  N^{-1}\sum _s|a_t-a_s|^2\le  N E_a,
\quad  \sum _t|a_t|^2\le  N^2E_a.
$$

又由 $b_t=b_0+\sum _{j=1}^t(b_j-b_{j-1})$，

$$
\|b_t\|^2\le (t+1)\left (\|b_0\|^2+
\sum _{j=1}^t\|b_j-b_{j-1}\|^2\right )\le  N E_b.
$$

求和得到 $\|x\|^2\le  N^2(E_a+E_b)$，即谱隙不等式。最后使用定理 [10.2](#thm:gap)。

∎

若删去起点约束，$\ker (D_T^\dagger  D_T)$ 与整个 $\mathcal{H}$ 同维，允许不同历史射线的混合。若起点允许一个秩 $r$ 子空间，共同核也为 $r$ 维。因此“传播为酉且整体静态”并不独自选定纯初始射线。本节能量没有按 $\operatorname{Tr}  H_T$ 再归一；若改变残差尺度，谱隙也须同步改变。

### 11.2 无限加权历史的正构造与稳定性极限

<a id="thm:infinite-history"></a>

#### 定理 11.2（可归一无限纯历史及无谱隙性）

设 $w_t>0$、$\sum _{t\ge 0}w_t=1$；给定同一系统空间上的无限酉序列$(U_t)_{t\ge 1}$ 与单位向量 $\phi$，令 $W_0=I$、$W_t=U_t\cdots  U_1$。在内生时钟空间 $\ell ^2(\mathbb{N} _0)\otimes \mathcal{H}$ 上定义

$$
\Omega =\sum _{t\ge 0}\sqrt {w_t}\lvert t\rangle \otimes  W_t\phi ,
$$

$$
L_tx=\sqrt {w_t}\,x_{t+1}-\sqrt {w_{t+1}}U_{t+1}x_t,
$$

$$
H_\infty =\sum _{t\ge 0}2^{-t-1}L_t^\dagger  L_t
+\lvert 0\rangle\langle 0\rvert \otimes (I-\lvert \phi\rangle\langle \phi\rvert ).
$$

该正算子在范数中定义良好，核恰为 $\operatorname {span}\{\Omega \}$。在正常迹类态中，唯一零罚态是 $\lvert \Omega\rangle\langle \Omega\rvert$。但是这个具体 $H_\infty$ 没有正谱隙。

**证明。**

$L_tL_t^\dagger =(w_t+w_{t+1})I$，故 $\|L_t\|^2\le 1$，加权级数绝对范数收敛。零能量要求每个 $L_tx=0$，因此

$$
x_t=\sqrt {w_t/w_0}\,W_tx_0.
$$

起点关系将 $x_0$ 限制到 $\phi$ 射线；可求和权重保证所得向量可归一。

为证明无谱隙，对 $n\ge 1$ 取 $x_n=\lvert n\rangle \otimes  W_n\phi$。有 $\langle \Omega ,x_n\rangle =\sqrt {w_n}\to 0$，且

$$
\langle  x_n,H_\infty  x_n\rangle 
=2^{-n}w_{n-1}+2^{-n-1}w_{n+1}\longrightarrow 0.
$$

令 $y_n=(x_n-\sqrt {w_n}\Omega )/\sqrt {1-w_n}$。它是核的单位正交向量，能量等于上一式除以 $1-w_n$，仍趋零。这排除了任何正的统一谱隙。

∎

这里的 $w_t$ 是明确给出的归一化数据；没有从“静态”自动推出唯一的时间权重。可归一性、纯态唯一性和统一稳定性可以分别成立或失败。另一方面，任意已知纯态都可用非局部算子 $I-\lvert \Omega\rangle\langle \Omega\rvert$ 得到单位谱隙；该事实并不提供与上述局部传播残差相同的结构或实现成本。

无限均匀历史给出另一种边界。把有限 $\Omega _T$ 放进共同 $\ell ^2$ 时钟，对每个有限支撑测试向量其内积趋零，由稠密性得到 $\Omega _T\rightharpoonup 0$。其范数恒为一，所以没有范数极限。投影 $\lvert \Omega _T\rangle\langle \Omega _T\rvert$ 强算子趋零，但迹范数恒为一，故不在迹范数下趋零。极限时需要声明采用哪种拓扑，不能把弱局部极限直接当成归一密度态的迹范数极限。

## 12. 无限整体的状态相容与纯性边界

<a id="thm:quasilocal"></a>

#### 定理 12.1（一致局部态族决定准局部态）

给定每个有限前缀上的密度矩阵 $\rho _n\in \mathcal{D} ((\mathbb{C} ^2)^{\otimes  n})$，满足

$$
\operatorname{Tr} _{n+1}\rho _{n+1}=\rho _n.
$$

通过 $A\mapsto  A\otimes  I$ 嵌入局部矩阵代数，则存在唯一状态 $\omega$ 定义在其范数完成上，使$\omega (A)=\operatorname{Tr} (\rho _nA)$ 对每个局部 $A$ 成立。

**证明。**

部分迹一致性保证定义不依赖选择更大前缀。有限维正性给 $\omega (A^\dagger  A)\ge 0$、$\omega (I)=1$ 及 $|\omega (A)|\le \|A\|$。所以泛函唯一连续延伸到范数完成。若局部 $A_j\to  A$，则 $A_j^\dagger  A_j\to  A^\dagger  A$，保证延伸仍为正。唯一性来自稠密性。

∎

此处存在的是指定可观测代数上的状态，不自动是某个预先选择的无限 Hilbert 表示中可写为迹类矩阵的正常态。这为“极限静态整体”给出另一种精确定义。

#### 命题 12.2（纯态的局部极限可以为混态）

在可数比特链上，让前 $N$ 位为

$$
\mathrm {GHZ}_N=(\lvert 0^N\rangle +\lvert 1^N\rangle )/\sqrt 2,
$$

其后全部为 $\lvert 0\rangle$，所定义的状态记为 $\omega _N$。每个 $\omega _N$ 都纯，但在每个固定局部读出上

$$
\omega _N\longrightarrow \tfrac 12\omega _{0^\infty }+\tfrac 12\omega _{1^\infty },
$$

右侧是严格混合态。

**证明。**

对 $m\ge  N$，前 $m$ 位的状态是纯投影。若 $\omega _N$ 有非平凡凸分解，限制到每个这样的前缀都使分量相同，局部代数稠密性迫使全局分量相同，故 $\omega _N$ 纯。对固定 $m<N$，部分迹消去 GHZ 的交叉项，得到

$$
\tfrac 12\lvert 0^m\rangle\langle 0^m\rvert +\tfrac 12\lvert 1^m\rangle\langle 1^m\rvert .
$$

因此每个局部读出最终等于所示混合态的读出。两产品态在第一位 $\sigma _z$ 的期望不同，混合是严格的。

∎

支撑随 $N$ 增长的 $X^{\otimes  N}$ 在 $\omega _N$ 中期望为 $1$，在极限态中为 $0$。故这里不是状态范数收敛。在固定迹类空间中，纯态的迹范数极限仍纯：由$|\operatorname{Tr} (\rho _n^2)-\operatorname{Tr} (\rho ^2)|\le 2\|\rho _n-\rho \|_1$得 $\operatorname{Tr} \rho ^2=1$，再用正迹一特征值即可判别。被忽略的比特始终属于同一内生整体；局部混合不要求存在外部本体。

## 13. 递归闭合总命题与本轮项目进展的准确归属

<a id="thm:closure"></a>

#### 定理 13.1（可呈现内生结构的递归表示闭合）

规定对象由有限或可数复数据、类型、索引和内部参考约定呈现。则对象描述、其约束描述、约束之间关系的描述均可再次作正归一编码。任意有限编码态可由完整二元主块图册精确恢复，并经固定 $J$ 接入原 AURIC 三轴；可数编码可逐个恢复坐标，且具有定理 [7.6](#thm:countable-code) 的截断界。每个有限递归层均保持精确解码；一条可数递归塔也能作为可数描述整体编码。

若约束另具有有界线性残差表示，其共同向量解由正算子核刻画；在正常迹类密度态范围内，该核一维时唯一归一零罚态纯，具有正谱隙时小残差控制其迹距离。

**证明。**

先用定理 [7.3](#thm:finite-code) 或 [7.6](#thm:countable-code) 编码描述。有限态用定理 [8.1](#thm:atlas) 恢复全部矩阵元，再用定理 [6.1](#thm:native)对每个正质量分支编码。下一层仍是同一类数据，有限归纳给出递归闭合；可数层的可数索引可排列为单列。线性残差的结论分别由定理 [3.2](#thm:kernel)、[10.1](#thm:countable-H)、[10.2](#thm:gap) 得到。

∎

这允许将“没有例外”写成对*明确对象类*的全称命题。所有这些对象都有表示；表示中的全局相容判据仍然决定哪些约束同时有解。编码闭合本身不使一个三轴点容纳任意高维状态的全部稳定信息，也不证明无限递归自动具有自指固定点。任意非线性语义关系都能作为给定描述被编码，但要把它写成固定 $L\psi =0$仍需额外的线性表示或提升相容条件。

本轮固定快照中的实际增量应作如下限定。[[2](#bib-compare)，[7](#bib-token)，[8](#bib-history)，[9](#bib-kraus)，[10](#bib-anti)]

| 来源 | 本轮实际新增与本文使用范围 |
| --- | --- |
| Token Graph 文稿 | 新增第 14 节的专门图论谱约束；只阅读其开头定义、定理及证明起始，未把它推广为普适纯态定理。 |
| Coherent History Schmidt | 新增前后缀合法性 `legal_iff` 引理；Schmidt 分解主体已存在。固定寄存器纯态电路实现仍列为开放项。 |
| Diagonal Kraus Instrument | 新增对角输入的矩阵元展开；原有总 Kraus Gram 正交等价定理并非本轮新结论。 |
| Anticoherence Refutation | 整篇新增，否定 $n=8,t=7$ 情形一种特定的迹范数约化 anticoherence 单调性猜想；不等于一般 CPTP 迹距离收缩失效。 |

本文没有重跑 Lean、执行矩阵数值、枚举或数学程序，也未改动仓库。新蓝图的形式验证标签作为来源陈述记录；它们不能替代本文逐项写出的假设与证明。固定公开文本的哈希核对保证所读版本的身份，不保证每个命题均已独立形式认证。

在正常迹类密度态范围内，最终得到的核心链条是

$$
\boxed {
\begin {gathered}
\text {正平方残差为零}\ \Longleftrightarrow \ \text {固定线性核},\\
\text {共同核一维}\ \Longleftrightarrow \ \text {唯一归一零罚态纯},\\
\text {正谱隙}\ \Longrightarrow \ \text {小残差控制状态距离}.
\end {gathered}}
$$

其中二元接口进一步给出

$$
\boxed {\rho _*=I-\widehat  H,\qquad 
u(\rho _*)=2u_0-u(\widehat  H).}
$$

约束与结果因此可以在同一种三轴接口里递归表达；整体的相容性、归一尺度和稳定预算则由接口之间的关系共同承担。这为用户的直觉提供了可证明的统一结构，而量子态空间、复数相位、张量组成及物理可实现操作的选择仍是需要独立说明的前提。

## 固定来源、归属与阅读范围

<a id="bib-head"></a>

[1]

the-omega-institute/trureturing，固定提交[d2950bd36448c5d4<wbr>f6c4a3e5671ef734<wbr>185145c9](https://github.com/the-omega-institute/trureturing/commit/d2950bd36448c5d4f6c4a3e5671ef734185145c9)，2026-10-31 21:19:22 SGT，合并 PR #24771。

<a id="bib-compare"></a>

[2]

固定比较：[v50 基线至本轮冻结提交](https://github.com/the-omega-institute/trureturing/compare/a6ed97ef09691efed393942b6ae694c4a44e5fc9...d2950bd36448c5d4f6c4a3e5671ef734185145c9)。比较完整 theory 树（1109 项，未截断）与相关 Blueprint 文本差异；不据此声称审完全部仓库。

<a id="bib-omega"></a>

[3]

[AURIC Ω Static Compatibility Fiber Theory](https://github.com/the-omega-institute/trureturing/blob/d2950bd36448c5d4f6c4a3e5671ef734185145c9/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)。本轮使用开篇表示假设、第 5 节的相容性及第 7 节传播核；重点亲读 252–338 行。静态传播核是原有结论；本文加起点约束、显式谱隙和无限加权构造为本轮纸面推导。

<a id="bib-v37"></a>

[4]

[AURIC Binary Relations and Unitary Representation V37](https://github.com/the-omega-institute/trureturing/blob/d2950bd36448c5d4f6c4a3e5671ef734185145c9/docs/develop/theory/AURIC_BINARY_RELATIONS_UNITARY_REPRESENTATION_AND_GOLDEN_GATE_UNIVERSALITY_V37.md)。重点核对 150–283 行的固定 $J$、三轴球、同尺度线性恒等式；433–534 行的算子值递归。未独立审阅后续原生门编译成本。

<a id="bib-v44"></a>

[5]

[AURIC Boundary Extension and Higher Dimensional Relational Atlas V44](https://github.com/the-omega-institute/trureturing/blob/d2950bd36448c5d4f6c4a3e5671ef734185145c9/docs/develop/theory/AURIC_BOUNDARY_EXTENSION_AND_HIGHER_DIMENSIONAL_RELATIONAL_ATLAS_V44.md)。使用第 7–11 节的纯态图册、全体二元主块、全局正性、Schur 余量、$V_d$、$W_d$ 与算子值递归；具体亲读 633–994 行，并由来源审计补核 521–619 行。这些结构在本轮快照中未改变。

<a id="bib-v42"></a>

[6]

[AURIC F13 Relational Semantics V42](https://github.com/the-omega-institute/trureturing/blob/d2950bd36448c5d4f6c4a3e5671ef734185145c9/docs/develop/theory/AURIC_F13_RELATIONAL_SEMANTICS_QUANTUM_THREE_AXES_AND_RECURSIVE_COMPATIBILITY_V42.md)。来源复核 45–75、151–255、640–686、759–825、1243–1284 行：单位元归一化、null 事件、原生关系纤维与逻辑 qubit 约化态的适用范围。

<a id="bib-token"></a>

[7]

[Token Graph Blowup Defect Decomposition](https://github.com/the-omega-institute/trureturing/blob/d2950bd36448c5d4f6c4a3e5671ef734185145c9/docs/develop/theory/TOKEN_GRAPH_BLOWUP_DEFECT_DECOMPOSITION.md)。本轮真正追加第 14 节；只读 3552–3625 行的开头，不声称已审完后续证明。

<a id="bib-history"></a>

[8]

[Coherent History Schmidt](https://github.com/the-omega-institute/trureturing/blob/d2950bd36448c5d4f6c4a3e5671ef734185145c9/Blueprint/D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.md)。来源审计完整阅读并核对新旧差异；本轮只新增 `legal_iff` 相关前后缀引理。

<a id="bib-kraus"></a>

[9]

[Diagonal Kraus Instrument Factorization](https://github.com/the-omega-institute/trureturing/blob/d2950bd36448c5d4f6c4a3e5671ef734185145c9/Blueprint/D5/S3/Quantum/Measurement/DiagonalKrausInstrumentFactorization.md)。来源审计完整阅读；新添对角输入展开，原有正交性定理保持。

<a id="bib-anti"></a>

[10]

[Anticoherence Trace Distance Refutation](https://github.com/the-omega-institute/trureturing/blob/d2950bd36448c5d4f6c4a3e5671ef734185145c9/Blueprint/D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.md)。本轮新增；指定 $n=8,t=7$、SU(2) 协变通道和特定 Schatten-1 候选量。不能扩展为 $t\le  n/2$ 或 Schatten-2 的已定结论。

<a id="bib-watrous2"></a>

[11]

John Watrous，*The Theory of Quantum Information*，[第 2 章：Quantum Information Basics](https://jhwatrous.github.io/TQI.2.pdf)，作者公开章节。用于密度态、纯态、信道等标准定义；文中所需简短论证另行给出。

<a id="bib-watrous3"></a>

[12]

John Watrous，*The Theory of Quantum Information*，[第 3 章：Similarity and Distance among States and Channels](https://jhwatrous.github.io/TQI.3.pdf)，作者公开章节。标准迹距离与纯态重叠界；本文谱隙界另给自足证明。
