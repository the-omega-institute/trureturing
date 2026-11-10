# 正交时间场论 OTF-007：观察纤维、最小补全与维度阶梯

> 原稿中的示意图以文内文字和公式呈现，完整图注保留。

OTF RESEARCH SERIES / 007 / VERSION 1.0

正交时间场论

观察纤维、最小补全与维度阶梯

由投影歧义到可检验的结构扩展

Observation Fibres, Minimal Completion\
and Dimensional Hierarchies

**补全核心** 当前读出不可区分的状态，只有在任务上仍有差别时，才要求额外读出。 线性读出 $A$ 与任务 $F$ 的最少新增标量数为

$$
\boxed{s_{\min}=\operatorname{rank}(F|_{\ker A}).}
$$

**稳定核心** 若 $0<r=\operatorname{rank}A<d$，新增恰 $k=d-r$ 个标量， 其读出增益平方预算为 $\Gamma$，则

$$
\boxed{
 \max_{\left\|B\right\|_{\mathrm F}^2\le\Gamma}
 \sigma_{\min}\!\begin{pmatrix}A\\B\end{pmatrix}^{\!2} =
 \min\!\left\{\sigma_r(A)^2,\frac{\Gamma}{k}\right\}.
 }
$$

**范围** 区分物体维数、状态参数、观察秩、相位纤维与记录容量。 Hodge 对偶、联合读出与量子纯化各有不同类型； 本稿不以一幅投影图直接推出额外空间维度或无限层级。

2026 年 11 月 8 日 / Asia–Singapore

项目默认分支 dev，本轮不可变快照：

`c20a31d1caabd516a60f694f1a5799b7ae4e7bf3`

接续 OTF-006 的有效性、证书与全程资源要求。

## 摘要

本文将“点、线、面、球及更大球”的观察阶梯重述为观察映射的纤维、 任务相关的信息亏损与可恢复补全。 首先严格区分沿轴内积和屏幕投影， 证明子空间降维的充要条件，并计算球面投影中的前后双值纤维与赤道临界秩。 Hodge 星号始终相对于已给定的环境维数定义； 三维体积元的对偶为标量，不生成第四根轴。 随后给出双屏幕联合恢复、精确噪声放大常数， 以及完整对象或指定线性任务的最小补全定理。 在最少新增通道数固定时，证明 Frobenius 增益预算下的最优绝对抗噪界， 并单独求出相对条件数最优值。 动态部分复用项目已有的未来效果闭包，说明固定有限模型可以在有限步稳定。 量子部分明确采用复矩阵效果接口， 由归一化、正性和效果可加性得到密度矩阵及 Born 概率表示， 再区分 Bloch、Hopf、纯化及联合相关性。 内部观察者的完整历史受到记录容量界约束， 而其存在本身不迫使模型逐级增加一个欧氏坐标。 最后列出完整候选约束、逐项反例及与当前项目结果的来源关系。

**关键词：** 观察纤维；投影；Hodge 对偶；最小补全； 奇异值；未来观察商；纯化；内生观察者。

## 目录

- [1　研究对象、维数类型与 AX-007 候选约束](#section-1)
- [2　投影何时真的降低维数？](#section-2)
- [3　Hodge 对偶的维数前提与非唯一提升](#section-3)
- [4　同一空间中的联合观察与稳定恢复](#section-4)
- [5　最小补全、增益预算与抗噪最优性](#section-5)
- [6　未来观察闭包：有限模型何时可以停止提升](#section-6)
- [7　量子结构的条件桥接：球面、相位纤维与读出](#section-7)
- [8　纯化、相关纤维与内部参考](#section-8)
- [9　内生观察者：记录容量与自包含模型](#section-9)
- [10　新方向的证据与无穷提升的成立条件](#section-10)
- [11　结构提升的修订原则与反向检验](#section-11)
- [A　项目快照、沿用结果与核读范围](#section-A)

<a id="section-1"></a>

## 1　研究对象、维数类型与 AX-007 候选约束

本轮研究的问题是：若一个读出只呈现对象的部分结构， 怎样证明哪些信息被丢失、补充哪些读出足以恢复、何时需要更大的模型？ 用户提出的几何阶梯为这一问题提供直觉， 但每条升维箭头都须给出相应映射、类型与证据。

#### 定义 1.1：观察映射与纤维

设 $X$ 为允许状态集合，$q:X\to Y$ 为已声明读出。 对 $y\in q(X)$，集合

$$
q^{-1}(y)=\{x\in X:q(x)=y\}
$$

称为该读出的纤维。关系 $x\sim_qx'$ 当且仅当 $q(x)=q(x')$。 纤维可以是连续流形、有限点集、单点或更复杂的集合。

一个方向可表示为单位球面上的点， 也可表示为过原点的有向射线。 这两个表示之间一一对应， 并不因为一个叫“点”、另一个叫“线”就增加独立信息。 对外代数也必须区分元素的次数与其参数族的维数。

| 对象或量                        | 类型与维数        | 本轮含义                 |
|:--------------------------------|:------------------|:-------------------------|
| 球体 $B^3$ / 球面 $S^2$     | 分别为三维 / 二维 | 边界与实体不可混称       |
| 单位方向 $n\in S^2$           | 两个独立实参数    | 三个坐标受一个归一化约束 |
| $`*_3n\in\Lambda^2\mathbb R^3`$ | 与 $n$ 一一对应 | 次数变为二，不增加参数   |
| $\operatorname{rank}Dq$       | 局部可见秩        | 不等于物理空间的总维数   |
| 量子 Hilbert 维数 $d$         | 复线性维数        | 不等于纯态流形维数       |
| 有限记忆容量 $M$              | 可区分记录数      | 不等于连续坐标的个数     |

#### 结构约束 1.2：H1：整体与内部记录

每个固定有限协议给出包含对象、控制、参考、记录和未读自由度的整体模型。 实际状态可为其中一个固定 $\omega$； 用于辨识的允许状态族表示模型中的候选配置或制备。 记录为整体的内部接口，不能免费依赖未知目标。

#### 结构约束 1.3：H2：映射及维数有类型

每个“观察”“投影”“截面”“对偶”“补全”均声明定义域、值域和允许态域。 区分环境维数、流形维数、代数次数、读出秩和容量。 光滑结论另列正则性与常秩条件，不把任意集合编码当作稳定几何表示。

#### 结构约束 1.4：H3：相对参考与校准

几何模块使用已给定的内积、取向及相对校准。 共同正交变换不改变其可恢复性； 校准、坐标匹配及多个读出来自同一状态或同一制备律的条件， 均须由协议供应并计入成本。

#### 结构约束 1.5：H4：任务保真与未来一致

只保留任务 $f$ 时，$f$ 必须在被合并纤维上恒定。 若还要求递归预测，则全部允许后继与读出须保持该等价关系； 非法操作、失败标记及测量分支概率不能被消去。

#### 结构约束 1.6：H5：补全有构造与稳定合同

新增读出声明可实现性、输出类型、精度和恢复器。 区分局部恢复、全局恢复及仅恢复指定任务。 以奇异值或其他稳定界控制噪声，不能只用集合单射性替代实际可恢复性。

#### 结构约束 1.7：H6：量子接口及概率一致性

量子模块明确选取有限复 Hilbert 空间、效果域 $0\le E\le I$， 以及对全部该域适用的非语境、正性、归一化与有限可加概率规则。 复合采用所声明的张量积；可用仪器为可实现的 CP 分支。 效果结构、复数域和复合规则是本模块的输入， Born 表示将在这些条件下推导。

#### 结构约束 1.8：H7：有限实现与精度计费

准备、门、存储、记录、重复制备、校验及选择读出的成本全部计入。 称一个秩计算为算法时，给出确切有效算术或秩间隙证书。 仅知矩阵元可任意精度计算，不保证精确零判定有效。

#### 结构约束 1.9：H8：以可区分见证判定扩展

若声称现有模型不足，应给出当前不可分却对目标或允许未来不同的见证。 若声称必须增加物理自由度，还须有排除同空间补全的模型或实验依据。 容许有限闭合；不预先规定每层必须增加一维或必须出现无限层级。

这些是本轮完整候选接口约束，不是从“存在”一词单独推出的全部物理定律。 各条作用将在反例及恢复定理中逐项体现。

<a id="section-2"></a>

## 2　投影何时真的降低维数？

#### 定义 2.1：轴向读出与屏幕读出

取单位向量 $o\in\mathbb R^n$，定义

$$
q_o(x)=o^\top x,\qquad
 A_o(x)=(o^\top x)o,\qquad
 \Pi_o(x)=x-(o^\top x)o.
$$

三者依次为标量轴坐标、向轴投影和向屏幕 $o^\perp$ 的正交投影。

#### 命题 2.2：两种读出的核及正交分解

$$
x=A_o(x)+\Pi_o(x),\qquad
 \left\|x\right\|^2=|q_o(x)|^2+\left\|\Pi_o(x)\right\|^2,
$$

且

$$
\ker q_o=o^\perp,\qquad \ker\Pi_o=\mathbb Ro.
$$

**证明。**

$o$ 单位，故 $o^\top\Pi_o(x)=0$。 分解与 Pythagoras 恒等式随即成立； 分别令相应读出为零即可求得核。

$\square$

因此对迎面轴线 $x_0+to$，

$$
\Pi_o(x_0+to)=\Pi_o(x_0),\qquad
 q_o(x_0+to)=q_o(x_0)+t.
$$

把轴向深度压成一个屏幕点的是 $\Pi_o$； 内积 $q_o$ 恰保留该轴坐标。 这里讨论的是正交成像模型，不把它直接等同于透视光学或量子测量。

#### 定理 2.3：子空间投影的精确维数损失

若 $L\subseteq\mathbb R^n$ 为 $k$ 维线性子空间，则

$$
\dim\Pi_o(L)=k-\dim(L\cap\mathbb Ro) =
 \begin{cases}
 k-1,&o\in L,\\
 k,&o\notin L.
 \end{cases}
$$

相同结论适用于仿射空间 $x_0+L$ 的仿射维数。

**证明。**

限制映射 $\Pi_o|_L$ 的核为 $L\cap\mathbb Ro$， 应用秩–零化度定理即可；平移不改变方向子空间。

$\square$

这给“线投成点、面投成线”严格的条件： 观察方向须位于被投影子空间内。 否则线仍是线，面仍保留二维像。 “一个点可能来自一条线”与“一个点必定来自一条线”因此不同。

#### 定义 2.4：球体、球面与截面

$$
B^3=\{x\in\mathbb R^3:\left\|x\right\|\le1\},\qquad
 S^2=\{x\in\mathbb R^3:\left\|x\right\|=1\}.
$$

球体的平面中心截面为 $B^2$；球面的赤道为 $S^1$。 球面本身的内蕴维数是二，其环境坐标空间才是三维。

#### 命题 2.5：球面屏幕投影的双值纤维

对 $u\in o^\perp$，

$$
\Pi_o^{-1}(u)\cap S^2=
 \begin{cases}
 \{u+\sqrt{1-\left\|u\right\|^2}\,o,\ u-\sqrt{1-\left\|u\right\|^2}\,o\},
       &\left\|u\right\|<1,\\
 \{u\},&\left\|u\right\|=1,\\
 \varnothing,&\left\|u\right\|>1.
 \end{cases}
$$

**证明。**

满足屏幕读出的向量恰为 $x=u+to$。 因 $u\perp o$，归一化要求 $t^2=1-\left\|u\right\|^2$， 分别求解即得。

$\square$

**图示（文字版）。** 在球面 $S^2$ 的二维子午截面中，观察方向为 $o$，屏幕 $o^\perp$ 显示为水平直径。同一条平行于 $o$ 的虚线与球面相交于前后两点 $x_+$、$x_-$；两条投影箭头均指向屏幕上的同一点 $u$。其中 $x_\pm=u\pm\sqrt{1-\|u\|^2}\,o$。

**图 1。** 同一屏幕点可来自球面的前后两点。 为清晰起见，仅画二维子午截面，屏幕圆盘在图中对应水平直径。 纤维的双值性不是新增一条连续状态维度。

#### 命题 2.6：球面投影的正则区与临界区

$$
\operatorname{rank}D(\Pi_o|_{S^2})_x=
 \begin{cases}
 2,&x^\top o\ne0,\\
 1,&x^\top o=0.
 \end{cases}
$$

**证明。**

$T_xS^2=x^\perp$，故微分的核为 $x^\perp\cap\mathbb Ro$。 该交在第一种情形为零，在第二种情形为一维。

$\square$

球面的大多数点处，投影仍具有二维局部像。 赤道处秩为一，但邻域不恒秩； 实际纤维为单点，不能机械用“$2-1$”计算其维数。 这也说明必须区分连续维数损失与离散前后歧义。

#### 反例 2.7：同一个圆盘像不能选择唯一来源

对 $\Pi_{e_3}$，平面圆盘 $B^2\times\{0\}$、 球面 $S^2$ 和球体 $B^3$ 的像均为同一个 $B^2$。 它们的维数、拓扑与纤维不同，单个影像不能唯一反演来源。

<a id="section-3"></a>

## 3　Hodge 对偶的维数前提与非唯一提升

#### 定义 3.1：指定维数的 Hodge 星号

在已给定的 $n$ 维定向欧氏空间中，以内积识别向量和一形式， 令 $I_n=e_1\wedge\cdots\wedge e_n$。 线性映射

$$
*_n:\Lambda^kV\longrightarrow\Lambda^{n-k}V
$$

由 $`\alpha\wedge *_n\beta=\langle\alpha,\beta\rangle I_n`$ 定义。

#### 命题 3.2：体积元不自动生成新轴

在三维，

$$
*_3(e_1\wedge e_2)=e_3,\qquad
 *_3e_3=e_1\wedge e_2,\qquad
 \boxed{*_3I_3=1}.
$$

在已经给定的四维定向空间中，才有

$$
*_4(e_1\wedge e_2\wedge e_3)=e_4.
$$

**证明。**

把各基元素代入定义，其与所列对偶的外积均为相应维数的单位体积元。 三维的顶次元素必须映至 $\Lambda^0V$，四维的三次元素映至 $\Lambda^1V$。

$\square$

这里的下标不能省略后再改变环境维数。 公式 $`e_4=*_4I_3`$ 已使用第四个方向来定义 $`*_4`$， 不能反向作为第四维存在的证明。 $I_3$ 是外代数元素，不是一个球体或球面。 标准定义与三维例子见 Bouchard [\[12\]](#ref-bouchard)； 项目 OTF-005 已明确这一线面同构的类型 [\[2\]](#ref-repo_otf5)。

#### 命题 3.3：线面互译不增自由度

在三维，$`*_3:\Lambda^1V\to\Lambda^2V`$ 为线性同构。 若 $\left\|n\right\|=1$，则 $n$ 与 $`*_3n`$ 携带相同的两个独立方向参数。

**证明。**

对正交基逐项作用，星号把一组三个基映为另一组三个基， 并在一、二次元素上满足 $`*_3^2=1`$。 限制到单位球后仍为双射。

$\square$

该同构不另行指定平面内相位基、盘半径、旋转速度或 Hamiltonian。 因此它允许轴与面作两种描述， 不独自推出物理波动、自旋或时间演化。

#### 反例 3.4：非对易不能独自推出曲率

在平直 $\mathbb R^3$ 中，取绕坐标轴的旋转，有

$$
R_x(\pi/2)R_y(\pi/2)e_3=e_1,\qquad
 R_y(\pi/2)R_x(\pi/2)e_3=-e_2.
$$

旋转不对易，但欧氏空间的标准 Riemann 曲率为零。 由闭路平行移动讨论曲率，须另给联络及相应路径。

#### 命题 3.5：隐藏扩展的观察不可识别性

给定模型 $(X,q,\{F_a\})$，其中 $F_a:X\to X$ 是总映射。 对任意非空集合 $K$ 及任意 $h_a:K\to K$，令

$$
X'=X\times K,\qquad q'(x,k)=q(x),\qquad
 F_a'(x,k)=(F_a(x),h_a(k)).
$$

则从 $(x,k)$ 出发的全部允许有限读出历史只依赖于 $x$。

**证明。**

对操作词长度归纳，第一分量始终为原模型的 $F_w(x)$； $q'$ 删除第二分量。因此每一步记录均与原模型相同。

$\square$

$K$ 可以是单点、有限集合或任意维流形。 若使用定义域为 $D_a\subseteq X$ 的部分操作，扩展定义域须为 $D_a\times K$，从而操作合法性也不泄露隐藏分量。 若全部允许测试始终不耦合它，数据不能选择其大小。 这给“更大结构可能存在”与“数据迫使某个特定更大结构存在”划出界限。 当前项目 $\Omega$ 稿第 63 节已有相应量子直和扩展定理： 隐藏块可任意增大而保持指定接口的逻辑响应 [\[9\]](#ref-repo_omega)。 本轮沿用其不可识别性结论。

<a id="section-4"></a>

## 4　同一空间中的联合观察与稳定恢复

本节两个读出针对同一个未知向量，并使用同一可用的相对参考。 若对象已变化，必须给出状态运输模型； 若只知道两个没有对应关系的物体轮廓，以下逐向量定理并不直接适用。 项目的第二投影稿也明确要求同一概率律、时期与校准 [\[6\]](#ref-repo_occlusion)。

#### 定理 4.1：双屏幕恢复与精确稳定常数

设 $o,p\in\mathbb R^3$ 单位，$c=o^\top p$，

$$
Tx=(\Pi_ox,\Pi_px).
$$

则 $T$ 单射当且仅当 $|c|<1$。 在此情形令

$$
G=T^\top T=2I-oo^\top-pp^\top.
$$

其特征值为 $1-c,1+c,2$。 对 $u=\Pi_ox,\ v=\Pi_px$，

$$
\boxed{x=G^{-1}(u+v).}
$$

对带噪数据 $\widehat y=Tx+e$，最小二乘估计满足

$$
\boxed{
 \|\widehat x-x\|
 \le \frac{\|e\|}{\sqrt{1-|c|}},
 \qquad
 \kappa_2(T)=\sqrt{\frac{2}{1-|c|}}.
 }
$$

误差放大常数为确切的算子范数。

**证明。**

$\ker T=\mathbb Ro\cap\mathbb Rp$，故核为零当且仅当两方向不平行。 $\Pi_o,\Pi_p$ 为自伴随幂等投影，所以有给定的 $G$。 当 $|c|<1$ 时，非零向量 $o+p,o-p$ 分别为特征向量， 特征值为 $1-c,1+c$； 垂直于其张成平面的方向有特征值二。 故

$$
\sigma_{\min}(T)=\sqrt{1-|c|},\qquad
 \sigma_{\max}(T)=\sqrt2.
$$

因 $u,v$ 分别已经位于对应屏幕，$T^\top(u,v)=u+v$。 一般带噪数据使用 $\widehat x=(T^\top T)^{-1}T^\top\widehat y=T^+\widehat y$， 于是误差算子为 $T^+$，其范数等于最小奇异值的倒数。

$\square$

#### 例 4.2：正交视向不要求第四维

取 $o=e_3,p=e_1$，

$$
u=(x_1,x_2,0),\qquad v=(0,x_2,x_3).
$$

两个读出恢复全部三个坐标。 若有噪声，重复出现的 $x_2$ 可以平均； 相应 $G=\operatorname{diag}(1,2,1)$。 恢复仍在同一个 $\mathbb R^3$ 中完成。

#### 命题 4.3：相对校准的协变性

对任意共同正交变换 $R$，

$$
G_{Ro,Rp}=R G_{o,p}R^\top.
$$

因此共同转动后的数据恢复为 $Rx$。

**证明。**

将 $(Ro)(Ro)^\top=Roo^\top R^\top$ 等代入即可。

$\square$

该结论不需要绝对场外坐标，但需要关系 $o^\top p$ 和数据配准可用。 校准的取得与存储沿用 OTF-006 的成本要求 [\[3\]](#ref-repo_otf6)。 当两视向接近平行或反平行时， 唯一恢复仍可能成立，误差放大却趋于无穷。 这区分了可识别与稳定可识别。

#### 命题 4.4：三正交屏幕的各向同性最优性

对三个单位视向 $o_1,o_2,o_3\in\mathbb R^3$， 令 $T_3x=(\Pi_{o_1}x,\Pi_{o_2}x,\Pi_{o_3}x)$。 则

$$
T_3^\top T_3=3I-\sum_{j=1}^3o_jo_j^\top,\qquad
 \sigma_{\min}(T_3)^2\le2.
$$

三方向两两正交时，$T_3^\top T_3=2I$，达到该上界， 且条件数等于一。

**证明。**

每个屏幕投影的迹为二，故 Gram 矩阵迹为六， 最小特征值不大于平均值二。 正交基满足 $\sum o_jo_j^\top=I$，从而所有特征值为二。

$\square$

这是固定三维、固定三次单位增益屏幕读出的最优设计， 不构成所有物理系统必须三维的证明。

#### 命题 4.5：两个标量与归一化仍有侧向歧义

若只知

$$
\alpha=o^\top x,\qquad\beta=p^\top x,\qquad\left\|x\right\|=1,
 \qquad |c|<1,
$$

则 $x$ 在 $\operatorname{span}\{o,p\}$ 上的分量为

$$
x_\parallel=
 \frac{\alpha-c\beta}{1-c^2}o+
 \frac{\beta-c\alpha}{1-c^2}p,
 \qquad
 \left\|x_\parallel\right\|^2=
 \frac{\alpha^2-2c\alpha\beta+\beta^2}{1-c^2}.
$$

取已定向的单位法向 $n$，全部兼容状态为

$$
x=x_\parallel\pm\sqrt{1-\left\|x_\parallel\right\|^2}\,n.
$$

范数小于、等于、大于一时，候选数分别为二、一、零。

**证明。**

解二元 Gram 线性方程得到 $x_\parallel$； 剩余分量为 $tn$，归一化只确定 $t^2$。

$\square$

两个屏幕各输出两个实分量，不能与两个标量读出混为一谈。 手性固定法向 $n$ 的朝向，也不等于知道未知状态位于其正侧。 选取正号需要状态域约束或额外信息。

<a id="section-5"></a>

## 5　最小补全、增益预算与抗噪最优性

#### 定理 5.1：任务纤维判据，沿用已有恢复原则

设 $q:X\twoheadrightarrow Y$，任务 $f:X\to Z$。 存在唯一 $\bar f:Y\to Z$ 使 $f=\bar f\circ q$， 当且仅当 $q(x)=q(x')$ 蕴含 $f(x)=f(x')$。

**证明。**

必要性由复合得到。 充分性令 $\bar f(q(x))=f(x)$； 纤维常值保证定义良好，满射保证定义覆盖与唯一性。

$\square$

该原则在 OTF-003、V22 及恢复模块中已有 [\[1\]](#ref-repo_otf3), [\[4\]](#ref-repo_v22), [\[10\]](#ref-repo_recovery)。 存在性结论本身不供应可计算恢复器。 以下把它具体化为线性通道数量及噪声界。

#### 定理 5.2：完整对象的最少新增线性读出

设 $A:\mathbb R^d\to\mathbb R^m$ 的秩为 $r$。 若 $B:\mathbb R^d\to\mathbb R^s$ 使 $x\mapsto(Ax,Bx)$ 单射，则 $s\ge d-r$； 该下界可达到。

**证明。**

在 $\ker A$ 上，$B$ 必须单射，故 $s\ge\dim\ker A=d-r$。 反向，取 $\ker A$ 的正交基作为 $B$ 的行。 若 $Ax=Bx=0$，则 $x\in\ker A$ 且全部该核坐标为零，所以 $x=0$。

$\square$

#### 定理 5.3：指定线性任务的最小补全

另给线性任务 $F:\mathbb R^d\to\mathbb R^p$。 若新增 $s$ 个线性实读出，允许线性恢复 $F(x)=D(Ax,Bx)$，则最小 $s$ 恰为

$$
\boxed{s_{\min}=\operatorname{rank}(F|_{\ker A}).}
$$

**证明。**

令 $K=\ker A$。在 $K$ 上，$F|_K=D_2B|_K$， 所以 $\operatorname{rank}(F|_K)\le s$。 反向，把 $x=x_\parallel+x_K$ 分解到 $K^\perp\oplus K$。 由 $Ax$ 可唯一线性恢复 $x_\parallel$； 只将 $F(x_K)\in F(K)$ 的基坐标作为新增读出， 再输出 $F(x_\parallel)+F(x_K)$，即可达到该数量。

$\square$

这两个定理增加的是 *记录坐标或可用读出* ， 并未增加原对象的环境空间。 项目 N2 已从共享历史残差得到秩决定最小内部补足的结论 [\[5\]](#ref-repo_n2)；这里指定的是线性观察矩阵与任务恢复合同。

#### 定理 5.4：光滑常秩读出的局部最小补全

设 $M^d,Y$ 均为有限维无边界 $C^1$ 流形，$q:M^d\to Y$ 为 $C^1$ 映射， 在 $x_0$ 的邻域恒秩 $r$。 若增添 $s$ 个 $C^1$ 实读出 $z$ 后具有局部恢复器 $D$， 其中 $D$ 在 $(q(x_0),z(x_0))\in Y\times\mathbb R^s$ 的一个开邻域上为 $C^1$， 且 $D\circ(q,z)=\operatorname{id}$ 在 $x_0$ 附近成立， 则 $s\ge d-r$，且局部可取等号。

**证明。**

常秩正规形给局部坐标 $(u,v)\in\mathbb R^r\times\mathbb R^{d-r}$， 使 $q(u,v)=(u,0)$，新增 $v$ 即充分。 反向，若 $D\circ(q,z)=\operatorname{id}$，微分满足

$$
\mathrm dD\circ\mathrm d(q,z)=I_{T_xM},
$$

于是 $d=\operatorname{rank}\mathrm d(q,z)\le r+s$。

$\square$

正规形可由逆函数定理构造： 选非零 $r\times r$ Jacobian 子式， 将其输出与剩余输入坐标组合作源坐标； 恒秩迫使其他输出不依赖剩余坐标，再在目标端减去它们。 标准证明见 Conrad [\[13\]](#ref-conrad)。

#### 反例 5.5：局部一坐标不保证全局一坐标

对常映射 $q:S^1\to\{\mathrm{pt}\}$，局部只需一个实读出。 但不存在连续单射 $z:S^1\to\mathbb R$。 否则紧致性使它成为到某闭区间的同胚； 删去该区间内部一点会不连通，而圆周删去一点仍连通，矛盾。

允许多个坐标图、图册标签或圆周值输出会改变接口。 局部维数预算不能无条件替代全局拓扑恢复。

#### 定理 5.6：最少新增通道下的最优增益分配

设 $A:\mathbb R^d\to\mathbb R^m$，$0<r=\operatorname{rank}A<d$， $k=d-r$，$\Gamma\ge0$。 增加恰 $k$ 个标量线性读出，组成 $B\in\mathbb R^{k\times d}$， 并约束 $\left\|B\right\|_{\mathrm F}^2\le\Gamma$。 则

$$
\boxed{
 \max_{\left\|B\right\|_{\mathrm F}^2\le\Gamma}
 \sigma_{\min}\!\begin{pmatrix}A\\B\end{pmatrix}^{\!2} =
 \min\left\{\sigma_r(A)^2,\frac{\Gamma}{k}\right\}.
 }
$$

若 $K$ 的行为 $\ker A$ 的正交基， $B=\sqrt{\Gamma/k}\,K$ 达到该界。

**证明。**

记 $H=A^\top A$，其最底 $k$ 个特征值为零， 下一个为 $\sigma_r(A)^2$。 令 $E$ 是最底 $k+1$ 个特征向量的张成空间。 因 $\dim E=k+1$ 且 $\dim\ker B\ge d-k$， 存在单位向量 $v\in E\cap\ker B$。 于是

$$
v^\top(H+B^\top B)v=v^\top Hv\le\sigma_r(A)^2.
$$

故最小特征值不超过第一项。

另一方面，把 $B^\top B$ 压缩到 $k$ 维 $\ker A$。 其迹不超过 $\left\|B\right\|_{\mathrm F}^2\le\Gamma$， 所以其中某个单位向量的 Rayleigh 商不超过 $\Gamma/k$。 在这个子空间 $A$ 为零，故得到第二项上界。

取指定的 $B$，有 $B^\top B=(\Gamma/k)\Pi_{\ker A}$。 它与 $A^\top A$ 作用于互补的正交空间， 所以组合的特征值恰为 $A^\top A$ 的 $r$ 个正特征值， 以及 $k$ 个 $\Gamma/k$。由此达到两项最小值。

$\square$

#### 推论 5.7：最优绝对误差界与相对条件数

若 $\Gamma>0$，采用欧氏输出噪声与欧氏恢复误差， 在精确线性左逆恢复器中最小化算子范数 （由最小二乘伪逆达到），最优最坏恢复放大率为

$$
\left(\min\{\sigma_r(A)^2,\Gamma/k\}\right)^{-1/2}.
$$

若目标是相对条件数，约定秩亏组合矩阵的 $\kappa_2=\infty$，则

$$
\boxed{
 \min_{\left\|B\right\|_{\mathrm F}^2\le\Gamma}
 \kappa_2\!\begin{pmatrix}A\\B\end{pmatrix}^{\!2} =
 \frac{\sigma_1(A)^2}
 {\min\{\sigma_r(A)^2,\Gamma/k\}}.
 }
$$

第二个最优值由 $B=\sqrt{\min\{\Gamma/k,\sigma_r(A)^2\}}\,K$ 达到， 可能不必用完增益预算。

**证明。**

绝对误差界是最小奇异值的倒数。 对任意 $B$，组合最大特征值至少为 $\sigma_1(A)^2$， 而定理给最小特征值上界，故得到条件数下界。 第二个构造保持最大特征值为 $\sigma_1(A)^2$， 同时达到所需最小特征值，故取等号。

$\square$

#### 注 5.8：边界与量纲

$\Gamma=0$ 且 $r<d$ 时最小奇异值为零，不能恢复。 若 $r=0$，单列 $k=d$，最优平方奇异值为 $\Gamma/d$； 若 $r=d$，无需新增通道，保持 $\sigma_d(A)^2$。 $\Gamma$ 是固定坐标尺度下的 *读出增益平方预算* ， 并非没有能耗模型即可认定的物理能量。 最小通道数条件不可删： 允许更多新增通道后，还可以加固原本已可见的弱方向。

#### 例 5.9：两个缺失方向的预算饱和

令 $d=3$，$A=(1,0,0)$，于是 $r=1,k=2$。 最优最小奇异值平方为

$$
\min\{1,\Gamma/2\}.
$$

当 $\Gamma\le2$ 时，两个缺失方向平均分配增益最优； 当 $\Gamma>2$ 时，既有第一方向成为瓶颈。 对相对条件数，$\Gamma\ge2$ 已可达到一， 继续提高新增两方向的增益不再有益。

本定理在所核读的四篇相关项目稿中未发现相同的增益预算合同； 它作为本轮具体推导给出完整证明，不据此主张全库或全球首创。

<a id="section-6"></a>

## 6　未来观察闭包：有限模型何时可以停止提升

仅能解释当前读出，不等于能够预测下一次操作后的读出。 所需补全应同时对允许的未来操作稳定。 本节将 OTF-003 的未来效应闭包与 V22 的递归观察商， 写成适用于本轮维度问题的共同线性形式 [\[1\]](#ref-repo_otf3), [\[4\]](#ref-repo_v22)。有限闭包结论属于项目已有结果。

#### 定义 6.1：读出空间与未来闭包

设 $W$ 为 $D$ 维实线性空间，$L_a:W\to W$ 为有限组线性映射， 初始可用读出空间为 $E_0\subseteq W$，$\dim E_0=r$。 递归定义

$$
E_{j+1}=\operatorname{span}\left(E_j\cup\bigcup_a L_aE_j\right),
 \qquad E_\infty=\bigcup_{j\ge0}E_j.
$$

#### 定理 6.2：有限未来闭包

$E_\infty$ 是包含 $E_0$ 且对所有 $L_a$ 不变的最小子空间。 至多发生 $D-r$ 次严格扩张，并且

$$
E_{D-r}=E_\infty.
$$

若某次 $E_{j+1}=E_j$，此后不再扩张。

**证明。**

由定义 $E_j\subseteq E_{j+1}$，维数每次严格增加至少一，最多为 $D$。 一旦相等，所有 $L_a$ 已把该空间送回自身，因此下一步也相等。 包含 $E_0$ 的任意共同不变子空间由归纳包含每个 $E_j$， 所以包含它们的并；该并本身也是共同不变子空间。

$\square$

### 6.1　经典线性观察的解释

状态按 $x\mapsto A_ax$ 演化，读出协向量 $f$ 的未来拉回为 $f\mapsto A_a^\top f$。 若当前读出矩阵为 $C$，只在 $\operatorname{row}(C)$ 对所有 $A_a^\top$ 不变时， 当前记录才直接足以递归更新全部后续记录。 这里 $\operatorname{row}(C)$ 表示行向量所对应的协向量空间。

对单一转移 $A$，联合观察矩阵为

$$
{\cal O}=
 \begin{pmatrix}C\\CA\\ \vdots\\CA^{d-1}\end{pmatrix}.
$$

Cayley–Hamilton 定理保证更高幂不再增加行空间。 完整状态可由这些无噪声读出恢复，当且仅当 $\operatorname{rank}{\cal O}=d$；否则只能恢复相应观察商。 这与标准可观察性理论一致 [\[14\]](#ref-boyd)。 多个操作时不能只用同一个 $A$ 的幂，但定理 6.2 仍控制全部有限操作词。

### 6.2　量子分支、合法性与条件更新

设整体接口的希尔伯特空间为 $\mathbb C^d$， $W=\operatorname{Herm}_d$ 的实维数为 $d^2$。 一个被记录的操作分支由完全正、迹不增映射 $\Phi_a$ 表示； 更明确地，$a=(u,o)$ 表示动作 $u$ 及结果 $o$， 对每个动作 $u$，$\sum_o\Phi_{u,o}$ 为迹保持映射。 比较状态时使用同一个策略，该策略只依赖已有记录及公开随机量。 其 Heisenberg 拉回由

$$
\operatorname{tr}\!\left[\Phi_a(\rho)F\right]
 =\operatorname{tr}\!\left[\rho\,\Phi_a^*(F)\right]
$$

定义。取 $`L_a=\Phi_a^*`$，并令 $E_0=\operatorname{span}_\mathbb R(\{I\}\cup\mathcal F_{\rm read})$， 其中 $\mathcal F_{\rm read}$ 恰为可实现的终端读出效应集合。

#### 命题 6.3：所有有限未来统计的充分且必要表示

对状态 $\rho,\sigma$，以下两项等价：

1.  它们对所有允许有限操作词及终端效应给出相同的联合概率；

2.  $\operatorname{tr}[(\rho-\sigma)F]=0$ 对所有 $F\in E_\infty$ 成立。

该表述使用未归一化分支态，保留零概率分支与失败记录。

**证明。**

对词 $w=a_t\cdots a_1$，联合终端概率为

$$
\operatorname{tr}\!\left[\Phi_{a_t}\cdots\Phi_{a_1}(\rho)F\right] =
 \operatorname{tr}\!\left[\rho\,\Phi_{a_1}^*\cdots\Phi_{a_t}^*(F)\right].
$$

这些拉回效应张成 $E_\infty$，故线性性给出等价。 自适应方案的每个叶节点对应一个被记录的词； 事件概率是对应叶概率之和，所以同样成立。

$\square$

上述递归默认全部所列词合法； 若存在有限控制器限制，须把控制状态并入整体状态， 并将不可执行的分支及失败标记编码进操作。 不能在商空间化时删掉会区分原状态的合法性信息。 此处固定同一有限接口和控制状态；永久保存任意长的全部原始历史 需要另行扩充内部记忆，其容量将在第 9 节计入。

若 $E_\infty\ne\operatorname{Herm}_d$ 且允许全部密度矩阵， 取非零 $\Delta\in E_\infty^\perp$。 由于 $I\in E_\infty$，$\operatorname{tr}\Delta=0$。 选择 $0<\varepsilon<1/(d\left\|\Delta\right\|_{\mathrm{op}})$， 则

$$
\rho_\pm=I/d\pm\varepsilon\Delta
$$

是不同状态，却对全部允许未来不可区分。 因此闭包既给充分统计，也精确指出该接口永久保留的歧义。 若状态域受到额外承诺，必须在承诺域内重新寻找见证。

取 $E_\infty$ 的实基 $F_0=I,F_1,\ldots,F_{r_\infty-1}$， 令 $q_i=\operatorname{tr}(\rho F_i)$。 设 $`\Phi_a^*(F_j)=\sum_i c^{(a)}_{ji}F_i`$，则

$$
p_a=\sum_i c^{(a)}_{0i}q_i,\qquad
 q'_j=\frac{\sum_i c^{(a)}_{ji}q_i}{p_a}
 \quad (p_a>0).
$$

因此 $r_\infty-1$ 个自由实坐标足以预测并条件更新全部未来记录。 在包含全部密度矩阵的域上，这也是线性坐标表示的最小数目： 在 $I/d$ 附近，迹零方向的可见商维数恰为 $r_\infty-1$， 故更少的线性坐标不能单射表示该商。

#### 例 6.4：同一个量子比特中的读出扩展

令 $X,Y,Z$ 为 Pauli 矩阵， $H=(X+Z)/\sqrt2$，$S=\operatorname{diag}(1,\mathrm i)$。 起始只读 $Z$，则

$$
E_0=\operatorname{span}\{I,Z\},\qquad
 E_1=\operatorname{span}\{I,X,Z\},\qquad
 E_2=\operatorname{Herm}_2,
$$

因为 $H^\dagger ZH=X$，$S^\dagger XS=-Y$。 若只有 $H$，两个纯态 $(I\pm Y)/2$ 对全部该接口统计相同； 加入 $S$ 后，先 $S$、后 $H$、再读 $Z$ 即可区分。 扩张的是可用读出空间，希尔伯特维数始终为二。

#### 反例 6.5：预测坐标不是自动的物理压缩

将 $\operatorname{Herm}_2$ 正交投影到 $\operatorname{span}\{I,X,Z\}$， 得到 $\Psi(\rho)=(\rho+\rho^\top)/2$。 该映射正且保迹，但不完全正。 它的归一化 Choi 算符为

$$
J(\Psi)=\frac12|\Phi^+\rangle\langle \Phi^+|+\frac14\,\mathrm{Swap}.
$$

在反对称 singlet 向量上期望值为 $-1/4$， 所以它不能作为对任意纠缠参考均合法的量子通道。

#### 注 6.6：终止界不是免费算法

当已给出 $E_0$ 的有限基与全部 $L_a$ 的矩阵， 且其系数位于同一个可有效精确运算与判零的域中， 可通过反复生成与秩检验求闭包。 若只给可计算实数逼近程序，精确判零一般不能免费获得。 同时 $d=2^n$ 时 $d^2=4^n$，故该维数界不是关于量子比特数 $n$ 的多项式复杂度保证。该有效性边界沿用 OTF-006 [\[3\]](#ref-repo_otf6)。

<a id="section-7"></a>

## 7　量子结构的条件桥接：球面、相位纤维与读出

本节明确哪些结构是公理输入，哪些是其推论。 给定复希尔伯特空间、全体效应及一致概率响应， 可以推出 Born 形式；单凭“存在三条正交轴” 尚不足以推出这些输入。

### 7.1　由效应概率到密度算符

#### 定理 7.1：有限维效应概率表示，Busch 型

给定有限维复希尔伯特空间 $\mathcal H$。 设 $p$ 对每个效应 $0\le E\le I$ 赋值于 $[0,1]$， $p(I)=1$，且对 $E+F\le I$ 有

$$
p(E+F)=p(E)+p(F).
$$

同一个效应在不同可实现测量中使用同一个 $p(E)$。 则存在唯一密度算符 $\rho$，使

$$
p(E)=\operatorname{tr}(\rho E).
$$

**证明。**

有限可加性给 $p(E/n)=p(E)/n$，并给合法有理倍数的齐次性。 若 $E\le F$，由 $p(F)=p(E)+p(F-E)$ 得单调性。 用上下有理倍数夹逼，得到合法实数倍的齐次性。

对任意正算符 $A$，取 $t\ge\left\|A\right\|_{\mathrm{op}}$， 定义 $\ell(A)=t\,p(A/t)$。 齐次性保证该定义与 $t$ 无关；取共同足够大的尺度， 可得正锥上的可加性与非负性。 对 Hermitian 算符 $K=A-B$ 定义 $\ell(K)=\ell(A)-\ell(B)$： 若另有 $K=A'-B'$，则 $A+B'=A'+B$， 正锥可加性保证定义不依赖分解。 所以 $\ell$ 是 $\operatorname{Herm}(\mathcal H)$ 上唯一的实线性泛函。

有限维 Hilbert–Schmidt 对偶给唯一 Hermitian $\rho$ 使 $\ell(K)=\operatorname{tr}(\rho K)$。 对所有秩一投影非负意味着 $\rho\ge0$， 而 $\ell(I)=1$ 意味着 $\operatorname{tr}\rho=1$。

$\square$

这是已有量子概率表示定理的有限维版本 [\[15\]](#ref-busch)，不主张是本轮新结果。 概率非语境性是对 *全效应* 的合同， 不能偷偷减为仅正交投影而保留同样证明。 复标量域、效应集合、复合规则与允许操作也仍是输入。

### 7.2　Bloch 球的维数与半角

对量子比特，

$$
\rho=\frac12(I+\mathbf r\cdot\boldsymbol{\sigma}),\qquad
 \mathbf r\in\mathbb R^3.
$$

利用 $(\mathbf r\cdot\boldsymbol{\sigma})^2=\left\|\mathbf r\right\|^2I$， 可得 $\rho$ 的特征值为 $(1\pm\left\|\mathbf r\right\|)/2$。 故状态域是实三维闭球；纯态满足 $\left\|\mathbf r\right\|=1$， 构成 *内在二维* 的 $S^2$。

方向 $\mathbf n$ 的正结果效应为 $E_{\mathbf n}=(I+\mathbf n\cdot\boldsymbol{\sigma})/2$。 由定理 7.1，

$$
p_+(\mathbf n|\mathbf r)=\frac{1+\mathbf n\cdot\mathbf r}{2}.
$$

若两者单位长度且 Bloch 夹角为 $\theta$，则

$$
p_+=\frac{1+\cos\theta}{2}=\cos^2(\theta/2).
$$

因此 Bloch 球方向夹角不能直接代成 $\cos^2\theta$。 这是状态射线几何与三维方向表示之间的半角关系 [\[16\]](#ref-preskill)。

#### 命题 7.2：量子比特的真实相位提升

归一化振幅 $\psi=(\alpha,\beta)\in\mathbb C^2$ 构成 $S^3$。 映射

$$
h(\alpha,\beta)=
 \bigl(2\operatorname{Re}(\bar\alpha\beta),\,
       2\operatorname{Im}(\bar\alpha\beta),\,
       |\alpha|^2-|\beta|^2\bigr)
$$

落在 $S^2$，且其每根纤维为 $\{e^{\mathrm i\chi}\psi:\chi\in\mathbb R/2\pi\mathbb Z\}$。 因而

$$
S^3/\mathrm U(1)\cong\mathbb{CP}^1\cong S^2.
$$

**证明。**

直接展开得 $\left\|h(\psi)\right\|^2=(|\alpha|^2+|\beta|^2)^2=1$。 该映射就是秩一投影 $\psi\psi^\dagger$ 的 Bloch 坐标。 任一 Bloch 单位向量给一个秩一密度矩阵， 故映射满射。 若两个归一化向量给同一秩一投影，它们张成同一复一维像， 故只差单位模复因子；反向显然。

$\square$

这是 Hopf 纤维化的量子比特实例 [\[17\]](#ref-mosseri), [\[2\]](#ref-repo_otf5)。 其中 $S^3$ 的“三”是振幅归一化后的实参数维数， 不是已经发现了第四条物理空间轴。

#### 命题 7.3：不能全局连续选定同一个相位规范

不存在连续截面 $s:S^2\to S^3$ 使 $h\circ s=\operatorname{id}$。

**证明。**

若存在，则

$$
S^2\times S^1\longrightarrow S^3,\qquad
 (n,z)\longmapsto z\,s(n)
$$

为连续双射。源紧致、靶 Hausdorff，故是同胚。 但 $\pi_1(S^2\times S^1)\cong\mathbb Z$， 而 $\pi_1(S^3)=0$，矛盾。

$\square$

此处用了标准球面的基本群事实。 局部可以选相位，多个局部规范之间需保留过渡函数。 整体共同相位对所有效应均不可见； 引入参考可使 *不同分支之间的相对相位* 可测， 但整个复合态的共同相位仍被商去。 相位参考也须包含在整体资源账目中。

| 对象           | 参数空间                      | 实维数    |
|:---------------|:------------------------------|:----------|
| 未归一化复向量 | $\mathbb C^d$               | $2d$    |
| 归一化向量     | $S^{2d-1}$                  | $2d-1$  |
| 纯态射线       | $\mathbb{CP}^{d-1}$         | $2d-2$  |
| 满秩密度矩阵   | 正定迹一 Hermitian 矩阵的开集 | $d^2-1$ |

复合规则若取 $\mathcal H_{SO}=\mathcal H_S\otimes\mathcal H_O$， 维数相乘。两个量子比特的纯态空间为 $\mathbb{CP}^3$，实维数六； 归一化振幅为 $S^7$。 所以加入观察者也没有普遍的“从 $S^2$ 自动到 $S^3$”规则。

### 7.3　可检验读出与层析资源

#### 命题 7.4：二元方向读出的最小线性完整性

给定已校准方向 $\mathbf n_j$，令 $A$ 的第 $j$ 行为 $\mathbf n_j^\top$。概率满足

$$
p_j=\frac{1+(A\mathbf r)_j}{2}.
$$

这些概率在全部 Bloch 球上唯一确定状态，当且仅当 $\operatorname{rank}A=3$。若满列秩，最小二乘恢复满足

$$
\left\|\widehat{\mathbf r}-\mathbf r\right\|
 \le\frac{2\left\|\widehat{\mathbf p}-\mathbf p\right\|}{\sigma_{\min}(A)}.
$$

**证明。**

满秩时解线性方程并用伪逆范数。 秩亏时取非零 $v\in\ker A$，足够小的 $\pm\varepsilon v$ 均在 Bloch 球内且给相同概率，因此不单射。

$\square$

这些概率需要可重复制备与多次统计， 不能从一份未知量子态读取三个确定分量。 即使承诺纯态，两个独立方向一般仍保留 命题 4.5 的二值歧义。

这里的三个方向是 *二元投影设置* 的结论。 它不表示所有层析方案至少需要三种设置。 例如取正四面体的四个单位方向 $\mathbf n_j$， 满足 $\sum_j\mathbf n_j=0$、 $\sum_j\mathbf n_j\mathbf n_j^\top=(4/3)I$， 则单个四结果 POVM

$$
E_j=\frac14(I+\mathbf n_j\cdot\boldsymbol{\sigma}),\qquad
 \mathbf r=3\sum_{j=1}^4p_j\mathbf n_j
$$

也信息完备 [\[18\]](#ref-tetra)。 一个设置仍须重复取得频率。

一般有限 POVM $\{E_j\}$ 在全部 $d$ 维状态上信息完备， 当且仅当其效应实张成 $\operatorname{Herm}_d$。 充分性由迹配对的非退化性得到； 必要性由 $I/d\pm\varepsilon\Delta$ 的不可区分见证得到， 其中 $\Delta$ 正交于全部效应。 因此结果数至少为 $d^2$，但结果数、设置数和样本数是不同资源。

<a id="section-8"></a>

## 8　纯化、相关纤维与内部参考

#### 定理 8.1：最小纯化环境

设 $\rho$ 是 $\mathbb C^d$ 上秩为 $r$ 的密度矩阵。 存在 $\mathbb C^d\otimes\mathbb C^k$ 中的纯态 $|\Psi\rangle$， 使 $\operatorname{tr}_E|\Psi\rangle\langle \Psi|=\rho$， 当且仅当 $k\ge r$。

**证明。**

把 $\Psi$ 的系数写成 $d\times k$ 矩阵 $C$， 约化态为 $CC^\dagger$，故其秩不超过 $k$。 反向，若 $\rho=\sum_{i=1}^r\lambda_i|i\rangle\langle i|$， 取环境中正交向量 $e_i$，则

$$
|\Psi\rangle=\sum_{i=1}^r\sqrt{\lambda_i}|i\rangle\otimes|e_i\rangle
$$

给所需纯化。

$\square$

此结论是标准纯化定理的维数合同 [\[19\]](#ref-watrous)，也已明确出现在项目 V78 中 [\[8\]](#ref-repo_v78)。 它要求补入的是量子子系统及相关结构； 不直接给欧氏空间维数。 纯化的存在也不证明实际未知整体必为某个特定纯态。

#### 命题 8.2：固定约化态的纯化纤维

固定 $\rho$ 的一组谱基与 $k\ge r$。 所有归一化纯化向量构成复 Stiefel 流形

$$
V_r(\mathbb C^k)\cong \mathrm U(k)/\mathrm U(k-r),
 \qquad \dim_\mathbb RV_r(\mathbb C^k)=2kr-r^2.
$$

若只保留物理纯态射线，还须商去共同 $\mathrm U(1)$， 其维数减一。

**证明。**

在固定谱基展开纯化： $\Psi=\sum_i|i\rangle\otimes v_i$。 约化态恰为 $\rho$ 当且仅当 $\langle v_j,v_i\rangle=\lambda_i\delta_{ij}$， 且零特征方向对应零向量。 故 $v_i=\sqrt{\lambda_i}u_i$， 其中 $u_1,\ldots,u_r$ 为 $\mathbb C^k$ 中的有序正交标架。 $\mathrm U(k)$ 在标架上传递作用，其稳定子为 $\mathrm U(k-r)$，维数相减即得公式。 共同相位作用自由，因此射线商减少一个实维。

$\square$

可见补全纤维常是标架空间或其商， 没有统一的“更大球面”形状。

#### 例 8.3：相同局部状态，三种不同整体

取两个量子比特：

$$
\rho_{\rm ent}=|\Phi^+\rangle\langle \Phi^+|,\quad
 \rho_{\rm cl}=\frac12(|00\rangle\langle 00|+|11\rangle\langle 11|),\quad
 \rho_{\rm ind}=I_4/4,
$$

其中 $|\Phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2$。 三者的两个局部约化态都为 $I_2/2$，但

$$
\begin{array}{c|ccc}
 &\rho_{\rm ent}&\rho_{\rm cl}&\rho_{\rm ind}\\ \hline
 \langle X\otimes X\rangle&1&0&0\\
 \langle Z\otimes Z\rangle&1&1&0
\end{array}
$$

不同。联合读出补回的是相关性。

一般两比特状态可写为

$$
\rho=\frac14\left(
 I\otimes I+\sum_i a_i\sigma_i\otimes I+
 \sum_j b_jI\otimes\sigma_j+
 \sum_{i,j}T_{ij}\sigma_i\otimes\sigma_j\right).
$$

两个边缘态只给六个参数 $a_i,b_j$， 其余九个 $T_{ij}$ 描述相关性。 在 $I_4/4$ 附近，正性保留一个开邻域， 故固定边缘态的局部纤维确有九维； 在边界上正性约束可使纤维退化。 这个例子说明“局部已看清”不能替代“整体已确定”， 而差异的类型可以由实际联合实验检验。

<a id="section-9"></a>

## 9　内生观察者：记录容量与自包含模型

### 9.1　注意力作为内部可实现的接口选择

将“注意力”形式化为控制寄存器 $A$ 的状态， 并让它选择可实现的读出或操作族 $\{\mathcal I_a\}$。 目标、控制、参考、记录与未读部分都属于整体状态 $\omega$。 内部条件统计可写为

$$
\Pr(y|a)=
 \frac{\Pr(Y=y,A=a)}{\Pr(A=a)}
 \qquad(\Pr(A=a)>0).
$$

其中联合概率来自整体操作模型。 改变控制寄存器可以改变测量基、耦合强度或读出选择； 仅仅更改事后的描述，不会自动改变原有联合分布。

这个形式化允许注意力影响可见结构， 但不预设精神聚焦会无代价地产生物理坍缩。 记录、相位参考与操作序列都要由整体内部相互作用实现。 “焦点”是一个记录接口，不必是一条欧氏视线， 更不能把视线投影、统计条件化和量子仪器三种不同映射混同。

#### 定理 9.1：内部记录的可区分容量

设 $M$ 个可能历史被编码为 $q$ 维量子记忆上的状态 $\rho_1,\ldots,\rho_M$。 若存在一个固定解码 POVM $\{E_i\}_{i=1}^M$ （可另有失败结果），使每个历史的正确恢复率至少为 $1-\varepsilon$， $0\le\varepsilon<1$，则

$$
\boxed{q\ge M(1-\varepsilon).}
$$

完美恢复时 $q\ge M$； 若记忆由 $m$ 个量子比特组成，则 $m\ge\lceil\log_2M\rceil$。

**证明。**

每个密度矩阵满足 $0\le\rho_i\le I$，故

$$
M(1-\varepsilon)
 \le\sum_i\operatorname{tr}(E_i\rho_i)
 \le\sum_i\operatorname{tr}E_i
 \le\operatorname{tr}I=q.
$$

最后一步也允许 $\sum_iE_i<I$ 的失败效应。 完美情形取 $\varepsilon=0$，再用 $q=2^m$。

$\square$

若连续 $T$ 次二元记录确实允许所有 $2^T$ 条历史， 并要求以后无误恢复整个历史，则至少需要 $T$ 个记忆量子比特。 若动力学只允许 $M_T$ 条历史，正确下界是 $\lceil\log_2M_T\rceil$，而非默认 $T$。 若只保留足以预测未来的等价类，所需记录可能更小。

这也解释定理 6.2 的范围： 它固定了整体接口维数与允许操作。 若任务要求永久保留无限增长的逐次历史， 新增记忆必须进入整体维数账目； 不能同时宣称维数固定、无限历史全部可逆保存且不付资源。

#### 例 9.2：内部观察不必导致无穷外部观察者

取两个经典比特，整体承诺状态只有 $(s,m)=(0,0)$ 或 $(1,1)$。 第二比特是内部记录器，读取 $m$ 即确定承诺域中的整个状态。 该模型没有外部第三观察者，也无需新空间轴。 它只恢复这两个允许状态，不声称识别任意未知量子态。

#### 命题 9.3：全乘积状态域的自记录限制

若 $S,M$ 为有限非空集合且 $|S|>1$， 则不存在把全部 $S\times M$ 状态无损编码到同一个 $M$ 的单射。

**证明。**

$|S\times M|=|S||M|>|M|$，由抽屉原理即得。

$\square$

该命题与上例相容： 上例的允许整体状态是相关子集，不是整个自由乘积。 自包含理论必须说明实际状态、可允许状态族与可读记录分别是什么。

一个有限程序可以准确规定球面方程 $x_1^2+x_2^2+x_3^2=1$， 并不因此保存球面上任意未知点的无限精度坐标。 “描述规律”“识别当前状态”“保存全部历史” 是三个不同的任务合同。 所谓“看清整个球”，首先必须明确指的是哪一个。

<a id="section-10"></a>

## 10　新方向的证据与无穷提升的成立条件

### 10.1　由可检验关系判断是否多出独立方向

在实内积模型中，已有向量 $v_1,\ldots,v_n$ 的 Gram 矩阵为 $G_{ij}=\langle v_i,v_j\rangle$。 若加入候选向量 $w$，记录交叉内积 $b_i=\langle v_i,w\rangle$ 与 $c=\left\|w\right\|^2$， 便得到一个可验证的独立方向判据。 项目 V44 已用广义 Schur 补明确给出该判据 [\[7\]](#ref-repo_v44)。

#### 定理 10.1：Gram 补全的独立方向判据

设 $G\ge0$ 为实对称矩阵。则

$$
\widetilde G=\begin{pmatrix}G&b\\b^\top&c\end{pmatrix}\ge0
$$

当且仅当

$$
b\in\operatorname{ran}G,\qquad
 \delta=c-b^\top G^+b\ge0.
$$

成立时，

$$
\operatorname{rank}\widetilde G=\operatorname{rank}G+
 \begin{cases}0,&\delta=0,\\1,&\delta>0.\end{cases}
$$

**证明。**

若 $\widetilde G\ge0$，对 $z\in\ker G$ 与任意 $t$， 二次式 $2t\,z^\top b+t^2c$ 必须非负，因此 $z^\top b=0$， 即 $b\in(\ker G)^\perp=\operatorname{ran}G$。 令 $a=G^+b$，则 $Ga=b$。 可逆合同变换把 $\widetilde G$ 化为

$$
\begin{pmatrix}I&0\\-a^\top&1\end{pmatrix}
 \widetilde G
 \begin{pmatrix}I&-a\\0&1\end{pmatrix} =
 \begin{pmatrix}G&0\\0&c-b^\top G^+b\end{pmatrix}.
$$

正性和秩结论均立即成立。

$\square$

几何上，$\delta=\left\|w-\Pi_{\operatorname{span}\{v_i\}}w\right\|^2$。 所以 $\delta>0$ 迫使 *表示这些关系的最小内积维数* 增加一。 它仍可能使用原来已存在而尚未探测的方向； 还不能单凭此式判断物理空间新长出了一维。 从 Gram 数据到物理时空的解释，需要独立的测量与动力学合同。

存在噪声时，声称 $\delta>0$ 还需误差界与正裕量； 不能把一个数值近似的极小正数当成精确秩证据。 这一点与 H7 的可有效判别要求一致。

### 10.2　真正不能在有限层停止的例子

#### 命题 10.2：无限坐标观察的逐点收敛与非一致性

设 $X=\ell^2(\mathbb N)$，$P_nx=(x_1,\ldots,x_n,0,\ldots)$。 则每个有限 $n$ 都有 $\ker P_n\ne\{0\}$， 但

$$
\bigcap_{n\ge1}\ker P_n=\{0\},\qquad
 \left\|x-P_nx\right\|\longrightarrow0
 \quad\text{对每个固定 }x\in\ell^2.
$$

同时

$$
\sup_{\left\|x\right\|\le1}\left\|x-P_nx\right\|=1
 \quad\text{对每个有限 }n.
$$

**证明。**

$e_{n+1}\in\ker P_n$ 给出非零核。 若全部有限坐标为零，则每个分量为零，故交核为零。 平方误差为收敛级数的尾和 $\sum_{j>n}|x_j|^2$，对固定 $x$ 趋零。 在单位球上，上界一由正交投影给出， 而 $x=e_{n+1}$ 取得一。

$\square$

本例确有无穷观察阶梯，因为模型明确允许无限独立坐标， 每一步只测有限前缀。 要从误差目标 $\varepsilon$ 有效求出足够的 $n$， 还须知道相应尾界或有效收敛模。 它不是由“每个球后面还有一个球”推导而来。

### 10.3　逻辑层级与几何维数分属不同类型

Gödel 的原始不完备性定理，在有效给定且足够表达算术的系统中， 以 $\omega$ 一致性等条件得到不可判定命题。 原文第 VI 定理及其后对递归公理、规则与算术表达能力的说明， 讨论的是形式可证明性 [\[11\]](#ref-godel1931)。 它不推出欧氏空间必须增加一条坐标轴。

扩大公理系统可能证明原系统无法证明的命题； 但这需要给新公理、编码与一致性条件。 同样，扩大观察接口可能分开旧纤维中的状态； 这需要给新操作及资源。 两者可以比较“相对于接口的不可区分性”， 不能未经桥接便认作同一个物理升维定理。

<a id="section-11"></a>

## 11　结构提升的修订原则与反向检验

### 11.1　由固定阶梯改为任务驱动的补全程序

#### 定义 11.1：可检验的结构补全

给定状态域 $X$、旧接口 $q$、目标任务 $f$ 与允许资源， 一个补全是新增可实现接口 $z$ 及恢复器 $D$，使

$$
f=D\circ(q,z).
$$

若还要求预测未来，补全产生的等价关系必须对允许操作稳定。

这一程序按以下顺序落实：

1.  写清对象、状态族、整体内部控制、读出和目标任务。

2.  给出旧纤维中的两个见证 $x,x'$， 满足 $q(x)=q(x')$ 而 $f(x)\ne f(x')$； 找不到见证并不自动证明充分，但找到了就证明旧接口不足。

3.  先寻找已有整体中的新读出、联合相关或参考， 并证明补全的最小资源与稳定性。

4.  检验全部允许未来，明确是否达到闭包。 若仍不足，再提出能被检验的扩展，并把新增资源纳入整体。

线性情形的最小数量由定理 5.3 精确给出； 最少通道的抗噪极限由定理 5.6 给出； 有限未来闭包由定理 6.2 控制。 这三者分别回答“补什么”“补多少、补得多稳”“何时可以停止”。

### 11.2　四级叙述的严格修订

| 原有表述 | 可以成立的数学内容 | 仍须补充或纠正的条件 |
|:---|:---|:---|
| 点其实是线 | 沿轴观察会把轴上整条线送到同一屏幕点；一个记录标签也可指称丰富对象。 | 必须指定屏幕投影。内积读出保留轴向坐标；点标签本身不决定所指维数。 |
| 线其实是面 | 某些二维子空间在边缘视向下投成一维；外积记录两方向张成的有向面积。 | 不是每条线都来自面；非平行方向才张成二维，面积也不自动给波的动力学。 |
| 面其实是球 | 球面局部可表示为二维图；同一平面投影可对应多个高维模型。 | 球面本身内在二维。二维投影不唯一决定球、实心球或平盘。 |
| 看见球必进入更大球 | 量子相位纤维、纯化、联合相关可能要求更丰富表示。 | $\star_3 I_3=1$；第四轴必须事先存在于四维环境。补全形状不必是球，有限接口可以闭合。 |

### 11.3　AX-007 的反向检验

| 条目 | 试图删掉条件后的反例 | 保留的学术边界 |
|:---|:---|:---|
| H1 | 把未知目标状态作为免费测量基，或把相位参考放到系统外。 | 控制与参考须可制备；研究可能配置族不等于同时存在多个实际整体。 |
| H2 | 把 $S^2$ 称为三维流形，把三向量的 Hodge 对偶写成第四轴。 | 环境维数、内在维数、外代数次数与记录容量分开记账。 |
| H3 | 两个读出使用未知相对坐标，或实际针对不同对象。 | 联合恢复式需同对象、已知运输与相对校准；旋转协变不等于校准免费。 |
| H4 | 当前读 $Z$ 无法区分 $\pm Y$，后续加入 $S,H$ 后可区分。 | 当前商须对合法未来操作稳定，保留联合分支概率与失败标签。 |
| H5 | 近乎平行的双屏幕使最小奇异值趋零；$S^1$ 的局部坐标不能拼成单一全局实坐标。 | 区分存在、局部、全局、可构造与抗噪恢复。 |
| H6 | 把正的坐标投影当成完全正通道，或只用射线便声称已推出复合规则。 | Born 表示是条件定理；复结构、效应与复合输入明确保留。 |
| H7 | 把 $d^2$ 次维数界称为关于 $n=\log_2d$ 的多项式算法，或精确判零不收费。 | 列出维数、精度、样本、记忆及实现成本；已有证明不自动给有效程序。 |
| H8 | 任意追加永不耦合的隐藏因子，便宣称实验发现更高维。 | 扩展必须有旧模型不足的见证及新的可区分预测；允许有限闭合。 |

### 11.4　量子推导的输入与输出账目

| 明确输入 | 本文可证明的条件结论 |
|:---|:---|
| 有限复希尔伯特空间、全部效应、一致归一化可加概率 | 唯一密度算符与 $p(E)=\operatorname{tr}(\rho E)$。 |
| 上述结构，$d=2$ | Bloch 球、纯态 $S^2$、Born 半角与 $S^3/\mathrm U(1)$ 相位商。 |
| 张量积复合及纯化目标 | 最小环境维数为 $\operatorname{rank}\rho$；固定边缘态保留相关纤维。 |
| 固定有限维、给定合法完全正分支及终端效应 | 有限未来观察闭包与充分预测坐标。 |
| 已校准读出、已供应的独立同态重复制备及重复实验资源 | 秩判据、最小补全、误差界与层析可检验预测。 |

本文没有从各向同性或三维外积单独推导全部量子公理， 也没有从波面隐喻推出普遍时间本体。 “时间场”在本轮作为整体内部操作、关系与记录的组织语言保留； 若要成为独立物理理论，还需给出其专有状态空间、动力学、 量纲、可测量量及区别于现有理论的预测。

### 11.5　不用术语的说明

一张照片中的一个点，可能对应视线上的很多位置。 多看一个角度，常常能把原来混在一起的位置分开， 但房间没有因此增加一条空间轴。

同样，一个量子系统的局部记录可以漏掉相位参考或与其他部分的相关。 补上相应实验后，旧记录中的歧义可能消失。 需要补充多少，可以用秩、最小奇异值和可区分记忆容量计算。

有的任务经过有限补充就足够；有的任务随着新增记录持续扩大； 还有的模型一开始就包含无限独立信息。 理论应证明自己属于哪一种。 这比预先规定“永远还有更大的球”给出更多可以检查和反驳的内容。

<a id="section-A"></a>

## A　项目快照、沿用结果与核读范围

### A.1　不可变版本标识

本轮重新核查默认分支 `dev`，使用固定提交

$$
\texttt{c20a31d1caabd516a60f694f1a5799b7ae4e7bf3}.
$$

提交时间为 2026-11-08 14:43:54 UTC （Asia/Singapore：2026-11-08 22:43:54）。 元数据取得时间为 2026-11-08 14:49:51 UTC （Asia/Singapore：2026-11-08 22:49:51）。 所有项目引用固定到该提交，不以之后可能移动的分支头替代。

索引覆盖根目录、`docs`、`develop`、 `theory` 四个未截断树；其中理论树有 1,342 个条目。 本轮取得 21 篇相关理论稿及两份 Lean 源文件， 重点核读下列指定章节。 这不是对整个仓库全部内容的逐字审查。

| 材料 | 本轮核读与采用的结论 |
|:---|:---|
| OTF-003 | 第 2、10、11 节相关段：标签与所指维数不同； 有限观察划分与效应闭包；响应空间的正交投影甚至不保正。 |
| OTF-005 | 轴面 Hodge 类型、各向同性与三维条件、 Hopf 相位纤维及无全局规范相关段。 |
| OTF-006 | 当前快照第 5.5–5.6 节的精确判零与第 8.6–8.9 节的证明搜索限制； 另恢复上一轮 TeX，接续构造、精度资源与公理账目。 |
| V22 | 未来稳定观察商、联合分支记录与递归闭包相关段。 |
| N2 | 共享历史的残差秩最小内部补全， 以及维数预算下的奇异值残差控制。 本文的 Frobenius 增益预算合同与该残差预算区分。 |
| 第二投影稿 | 五态概率读出的显式联合恢复、归一化切空间核判据， 同一概率律、时期与校准要求。 |
| V44 | 广义 Schur 补的正性与秩增加， 以及稳定嵌入维数限制相关段。 |
| V78 | 复结构、效应概率及复合规则的输入， 定理 10.2 的最小纯化环境。 |
| $\Omega$ | 第 63 节定义 82.1、定理 82.2、推论 82.3： 隐藏块扩展保持指定接口响应的不可识别性。 |
| 恢复判据 Lean | 读取 `TargetRecoveryCriterion.lean` 的源定义与证明结构； 其中选择性恢复的存在性不自动给可执行解码器。 |

本轮未运行完整仓库的 Lean 构建，也未执行 `#print axioms`； 文中证明是可逐行审查的数学证明， 不标记为已经机械验证。 外部一手来源为课程作者讲义、原始论文与作者公开教材章节。

### A.2　本轮增量与可复核交付

本轮新增组织是： 用观察纤维统一四级叙述的歧义； 给出双屏幕的精确谱与噪声放大； 将指定任务的最小补全写成 $\operatorname{rank}(F|_{\ker A})$； 并证明最少新增通道、固定增益预算的最优稳定常数。 这些结论在本文均附假设与完整证明。 不以有限项目核读宣称全球首创。

有限未来闭包、Hopf 相位纤维、纯化环境秩、 共享历史残差补全及隐藏扩展不可识别性， 均明确衔接既有项目或标准文献。 全部图形为 TeX 内嵌 TikZ，源码不依赖外部图片。

## 参考文献

<a id="ref-repo_otf3"></a>

\[1\] trureturing 项目文稿.  *OTF-003：概念、存在与关系纤维* . §§2.1–2.6、10–11，尤其定理11.2. 固定提交同附录 A. [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c20a31d1caabd516a60f694f1a5799b7ae4e7bf3/docs/develop/theory/OTF_003_CONCEPTS_EXISTENCE_AND_RELATIONAL_FIBRES.md).

<a id="ref-repo_otf5"></a>

\[2\] trureturing 项目文稿.  *OTF-005：轴面几何、相位纤维与内生闭合* . §§1–2、7.3–7.5. 固定提交同附录 A. [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c20a31d1caabd516a60f694f1a5799b7ae4e7bf3/docs/develop/theory/OTF_005_AXIS_PLANE_GEOMETRY_PHASE_FIBRES_AND_ENDOGENOUS_CLOSURE.md).

<a id="ref-repo_otf6"></a>

\[3\] trureturing 项目文稿.  *OTF-006：内生计算、有效消去与证明搜索* . §§5.5–5.6、8.6–8.9. 固定提交同附录 A. [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c20a31d1caabd516a60f694f1a5799b7ae4e7bf3/docs/develop/theory/OTF_006_ENDOGENOUS_COMPUTATION_EFFECTIVE_CANCELLATION_AND_PROOF_SEARCH.md).

<a id="ref-repo_v22"></a>

\[4\] trureturing 项目文稿.  *相对门历史、观察商与递归闭合 V22* . §8.1–8.5. 固定提交同附录 A. [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c20a31d1caabd516a60f694f1a5799b7ae4e7bf3/docs/develop/theory/AURIC_RELATIVE_GATE_HISTORIES_OBSERVATION_QUOTIENTS_AND_RECURSIVE_CLOSURE_V22.md).

<a id="ref-repo_n2"></a>

\[5\] trureturing 项目文稿.  *共享历史充分性、最小内部补足与维数预算 N2* . §§5–7、9–10. 固定提交同附录 A. [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c20a31d1caabd516a60f694f1a5799b7ae4e7bf3/docs/develop/theory/AURIC_SHARED_HISTORY_SUFFICIENCY_MINIMAL_INTERNAL_COMPLETION_AND_DIMENSION_BUDGET_N2_V78_CONTINUATION.md).

<a id="ref-repo_occlusion"></a>

\[6\] trureturing 项目文稿.  *FIB 原子、遮挡、第二投影与局部恢复* . §4，连同附加适用条件注 Q1–Q2. 固定提交同附录 A. [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c20a31d1caabd516a60f694f1a5799b7ae4e7bf3/docs/develop/theory/AURIC_FIB_ATOM_OCCLUSION_SECOND_PROJECTION_AND_LOCAL_RECOVERY.md).

<a id="ref-repo_v44"></a>

\[7\] trureturing 项目文稿.  *边界延拓与高维关系图册 V44* . §§9.1–9.2、12.1. 固定提交同附录 A. [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c20a31d1caabd516a60f694f1a5799b7ae4e7bf3/docs/develop/theory/AURIC_BOUNDARY_EXTENSION_AND_HIGHER_DIMENSIONAL_RELATIONAL_ATLAS_V44.md).

<a id="ref-repo_v78"></a>

\[8\] trureturing 项目文稿.  *内生关系量子理论统一综合 V78* . §2、定理10.2. 固定提交同附录 A. [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c20a31d1caabd516a60f694f1a5799b7ae4e7bf3/docs/develop/theory/AURIC_ENDOGENOUS_RELATIONAL_QUANTUM_THEORY_UNIFIED_RELATIONAL_AXIOMS_V78_SYNTHESIS.md).

<a id="ref-repo_omega"></a>

\[9\] trureturing 项目文稿.  *AURIC Ω 静态相融纤维理论* . §§4、9、63. 固定提交同附录 A. [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c20a31d1caabd516a60f694f1a5799b7ae4e7bf3/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md).

<a id="ref-repo_recovery"></a>

\[10\] trureturing 项目文稿.  *TargetRecoveryCriterion Lean 源码* . target_recovery_criterion；本轮仅源码核读. 固定提交同附录 A. [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c20a31d1caabd516a60f694f1a5799b7ae4e7bf3/D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean).

<a id="ref-godel1931"></a>

\[11\] K. Gödel. *Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I*. Monatshefte für Mathematik und Physik 38 (1931), 173–198. 原印页187定理VI、190–191适用条件及191脚注48a. DOI: [10.1007/BF01700692](https://doi.org/10.1007/BF01700692). [原文扫描](https://www.w-k-essler.de/pdfs/goedel.pdf).

<a id="ref-bouchard"></a>

\[12\] V. Bouchard.  *MATH 215: Hodge dual* . University of Alberta course notes. [作者课程讲义](https://sites.ualberta.ca/~vbouchar/MATH215/section_hodge.html).

<a id="ref-conrad"></a>

\[13\] B. Conrad.  *Local structure theorem for $C^p$ maps* . Stanford University differential geometry handout. [常秩正规形及证明](https://virtualmath1.stanford.edu/~conrad/diffgeomPage/handouts/localstrthm.pdf).

<a id="ref-boyd"></a>

\[14\] S. Boyd and S. Lall.  *EE263: Observability and state estimation* . Stanford University. [可观察性课程讲义](https://ee263.stanford.edu/lectures/observ.pdf).

<a id="ref-busch"></a>

\[15\] P. Busch. Quantum states and generalized observables: a simple proof of Gleason’s theorem.  *Physical Review Letters*  91 (2003), 120403. [arXiv:quant-ph/9909073](https://arxiv.org/abs/quant-ph/9909073).

<a id="ref-preskill"></a>

\[16\] J. Preskill. *Lecture Notes for Physics 219: Chapter 2, Foundations I: States and Ensembles*. Caltech, 2015 version, §2.1 and §2.3.2. [作者讲义](https://www.preskill.caltech.edu/ph219/chap2_15.pdf).

<a id="ref-mosseri"></a>

\[17\] R. Mosseri and R. Dandoloff. Geometry of entangled states, Bloch spheres and Hopf fibrations.  *Journal of Physics A: Mathematical and General*  34 (2001), 10243–10252. [arXiv:quant-ph/0108137](https://arxiv.org/abs/quant-ph/0108137).

<a id="ref-tetra"></a>

\[18\] J. Řeháček, B.-G. Englert and D. Kaszlikowski. Minimal qubit tomography.  *Physical Review A*  70 (2004), 052321. [arXiv:quant-ph/0405084](https://arxiv.org/abs/quant-ph/0405084).

<a id="ref-watrous"></a>

\[19\] J. Watrous.  *The Theory of Quantum Information* . Cambridge University Press, 2018. Chapter 2, Definition 2.9 and Theorems 2.10, 2.12. [作者公开章节](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf).
