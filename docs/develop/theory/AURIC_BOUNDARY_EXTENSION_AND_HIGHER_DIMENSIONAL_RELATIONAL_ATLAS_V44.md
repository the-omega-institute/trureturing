<a id="manuscript-title"></a>
# AURIC：边界、体与维度提升

## 复平面展开及高维关系的相容重构

定义、定理与纸面证明　v44.0

2026 年 10 月 31 日　Asia/Singapore

**原稿元数据。** 文档标题：AURIC：边界延拓与高维关系图册；作者署名：AURIC research continuation；主题：Boundary-to-interior reconstruction, matrix Poisson extension, complex atlases, compatible qubit blocks and coherent encodings。原页眉：AURIC：边界延拓与高维关系图册；v44 / 2026-10-31。

**原作者陈述的归属。** 以下摘要、正文和文献中的“本文”“本稿”“本轮”、纸面证明及源码读取用途、历史快照与增量核对等陈述均保留原作者的说法；其中历史核对与取得权限的陈述不因转写而成为本 Markdown 的独立认证。另列的“编者适用条件注”不属原稿。

<a id="abstract"></a>
## 摘要

本文将“边界与体的关系可以递归升维”落实为四类有条件的构造：
星形体的锥填充、矩阵态值的 Poisson 调和延拓、多复变量的迭代 Cauchy 重构，
以及带索引和相容约束的 AURIC 二元关系图册。
其中，纯二能级边界的调和延拓准确填满 Bloch 球，保持正性和迹归一化，
并在任意固定矩阵范数的边界一致误差下不放大误差。
任意有限维密度态均可由全部二阶主块准确、稳定地重构；
全部纯态可用带共同参考的多个复比值图表示。
局部二元合法性还须通过全局正性、重叠和循环条件拼接。
给出奇异 Schur 递归、相干标签等距编码，以及经典化标签后不存在共同量子逆的反例。
高维态体的完整边界是所有降秩态，纯态仅在二能级时恰为整个边界。
项目既有 V24 的边界有效度量、V37 的算子值递归，与最新 RRO 的尖锐逆条件数分别对齐。
所有数学以纸面证明展开；源码读取、排版与渲染仅用于来源及交付检查。

<a id="section-1"></a>
## 1. 问题、来源与四种不同的重构

固定项目默认分支 `dev` 的提交
`3c22c32855cfb4640e445abede6ff2898c404800`，
 时间为 2026-10-31 16:53:55（新加坡）。
相对 v43 的 `268387eb9e31`，完整 theory 树仍有 1098 个 blob，
本轮仅三份理论文稿追加：Polygon、Root Positive Trace 及 RRO Native Terminal。
本稿直接使用的新进展是后一文稿的 §§18–21；
其余两个计数或来源守卫的追加不承担本轮解析延拓的前提。［[head](#ref-head)，[rro](#ref-rro)］

沿用单一静态本体 $(\mathcal A,\omega)$：参考、标签、观察者记录及允许控制均为内部结构。
本文的径向参数、混合参数和坐标图索引不自动解释为外部时间。
复线性空间、正定内积、已知边界、方程及原生控制合同，各在使用处明确给出。

| 构造 | 给定的数据与结构 | 准确得到的对象 |
| --- | --- | --- |
| 几何填充 | 连续正径向边界、中心、独立径向参数 | 与闭球同胚的星形体 |
| 调和延拓 | 完整边界态、内域、逐矩阵元调和条件 | 唯一正、归一且稳定的内部态场 |
| 全纯重构 | 多复变量模型及完整相容边界函数 | 由迭代 Cauchy 积分确定的内部函数 |
| 关系图册 | 多个二元块、索引、尺度与共同相容条件 | 完整高维态及其关系 |

本轮的主结论是：这些构造可以组合成高维关系的统一*表示与重构方案*。
维数信息保存在独立参数、边界函数、图册索引和交叉关系中。
存在性、唯一性、稳定性及共同酉实现是分别证明的性质。

<a id="section-2"></a>
## 2. 一般维数的球面提升与边界填充

<a id="thm:stereo"></a>
#### 定理 2.1（任意维数的逆立体投影）

对 $n\ge2$，定义

$$
\boxed{\mathsf S_{n-1}(x)=
\frac{(2x,1-\|x\|^2)}{1+\|x\|^2},\qquad x\in\mathbb R^{n-1}.}
$$

它是 $\mathbb R^{n-1}$ 到去南极球面 $S^{n-1}\setminus\{-e_n\}$ 的实解析双射，逆式为

$$
x=\frac{(u_1,\ldots,u_{n-1})}{1+u_n}.
$$

加入无穷远点后得到球面紧化。$n=3$、$x=(\Re w,\Im w)$ 时，
恰是上一轮复二通道的 Bloch 提升。

**证明。**

$4\|x\|^2+(1-\|x\|^2)^2=(1+\|x\|^2)^2$ 给单位范数；
$1+u_n=2/(1+\|x\|^2)$ 给逆式，范数趋于无穷时趋南极。

∎

这说明同一种几何公式确实可在任意维数使用。
输入仍有 $n-1$ 个实坐标；单个复平面只对应其中 $n=3$ 的情形。
一般公式不单独选择物理空间维数。

<a id="thm:cone"></a>
#### 定理 2.2（连续正径向边界的唯一锥填充）

给定连续函数 $R:S^{n-1}\to(0,\infty)$，置

$$
K_R=\{tR(\theta)\theta:\theta\in S^{n-1},\ 0\le t\le1\}.
$$

则 $\partial K_R=\{R(\theta)\theta\}$，且

$$
\boxed{
\bigl(S^{n-1}\times[0,1]\bigr)/(S^{n-1}\times\{0\})
\longrightarrow K_R,\qquad [\theta,t]\longmapsto tR(\theta)\theta
}
$$

为同胚。这里商掉的是全部零半径方向，即一个共同锥顶。

**证明。**

紧性给 $0<r_-\le R\le r_+<\infty$。
非中心点的逆为 $\theta=x/\|x\|$、$t=\|x\|/R(\theta)$。
所以显示映射为紧空间到 Hausdorff 空间的连续双射，故为同胚。
函数 $F(x)=\|x\|/R(x/\|x\|)$ 连续延拓为 $F(0)=0$。
$F<1$ 的点在内部，$F=1$ 的点沿同一射线稍向外即出域，故恰为边界。

∎

<a id="statement-2-3"></a>
#### 推论 2.3（边界误差的几何稳定性）

若 $\|R-\widetilde R\|_\infty\le\varepsilon$，则

$$
d_H(K_R,K_{\widetilde R})\le\varepsilon,
\qquad
d_H(\partial K_R,\partial K_{\widetilde R})\le\varepsilon.
$$

**证明。**

匹配相同 $(t,\theta)$，点间距离为 $t|R(\theta)-\widetilde R(\theta)|$。
边界取 $t=1$。同心球达到常数一。

∎

这个定理明确引入了独立径向参数 $t$。
它首先是拓扑和几何构造；即使 $R$ 很光滑，保射线映射
$x\mapsto R(x/\|x\|)x$ 也未必在中心可微。
若它在中心可微，其导数应把每个方向 $\theta$ 送到 $R(\theta)\theta$，
一个线性算子若每条直线都是特征方向，就只能为标量算子。
因此该特殊径向映射在中心可微要求 $R$ 为常数，不能把一般锥填充自动称为解析延拓。

<a id="section-3"></a>
## 3. 高维态体：完整边界不再只有纯态

<a id="statement-3-1"></a>
#### 定义 3.1（密度体与中心）

对 $d\ge2$，定义

$$
\mathcal D_d=\{\rho=\rho^\dagger\succeq0:\operatorname{Tr}\rho=1\},
\qquad C_d=I/d.
$$

以下边界与内部均相对于迹一 Hermitian 仿射超平面。

<a id="thm:densityboundary"></a>
#### 定理 3.2（降秩边界及唯一径向分解）

$\mathcal D_d$ 的实仿射维数是 $d^2-1$，其边界恰为所有降秩态。
对 $\rho\ne C_d$，令

$$
\boxed{
t=1-d\lambda_{\min}(\rho),\qquad
B=\frac{\rho-\lambda_{\min}(\rho)I}{1-d\lambda_{\min}(\rho)}.
}
$$

则 $0<t\le1$，$B\in\partial\mathcal D_d$，且

$$
\boxed{\rho=(1-t)C_d+tB.}
$$

这个中心到边界的分解唯一。中心对应 $t=0$，全部方向在此合并。

**证明。**

Hermitian 空间实维 $d^2$；固定迹减去一维。
正定态允许足够小的迹零 Hermitian 扰动，故是内部点。
若 $\rho v=0$、$\|v\|=1$，沿 $I/d-\lvert v\rangle\langle v\rvert$ 作任意小正扰动便在 $v$ 上给负期望，
故降秩态在边界。显示分子的最小本征值为零，迹为分母，所以 $B$ 是边界态。
反向若 $\rho=(1-t)C_d+tB$ 且 $\lambda_{\min}(B)=0$，
则 $\lambda_{\min}(\rho)=(1-t)/d$，唯一确定 $t$ 及 $B$。

∎

在迹零 Hermitian 单位方向 $U$ 上，$\lambda_{\min}(U)<0$，
边界的径向长度为

$$
R(U)=-\frac1{d\lambda_{\min}(U)}.
$$

它连续且严格正。由定理 [2.2](#thm:cone)，

$$
\mathcal D_d\simeq\overline B^{d^2-1},\qquad
\partial\mathcal D_d\simeq S^{d^2-2}.
$$

这是拓扑球体与拓扑球面，不断言高维态体是标准欧氏球或其边界处处光滑。

<a id="statement-3-3"></a>
#### 推论 3.3（纯态等于全部边界的准确范围）

在 $d\ge2$ 中，纯态恰为全部边界当且仅当 $d=2$。

**证明。**

$d=2$ 的迹一降秩态只能秩一。
$d\ge3$ 时 $\operatorname{diag}(1/2,1/2,0,\ldots,0)$ 是秩二混合边界态。

∎

因此只把纯态 $P$ 与一个参数组合为 $(1-t)I/d+tP$，在 $d\ge3$ 时不能给全部态。
一般径向分解还保留边界点自身的纯度：

$$
\operatorname{Tr}\rho^2=\frac1d+t^2\left(\operatorname{Tr} B^2-\frac1d\right).
$$

这些结论使用标准密度算符模型；本文给出了所需边界与径向公式的直接证明。［[watrous](#ref-watrous)］

<a id="section-4"></a>
## 4. 归一正核把完整边界态延拓到内部

<a id="statement-4-1"></a>
#### 定义 4.1（球上的归一 Poisson 核）

令 $n\ge2$，$\sigma$ 为 $S^{n-1}$ 上总质量一的面积测度。
对 $x\in B^n$、$\xi\in S^{n-1}$ 定义

$$
P_n(x,\xi)=\frac{1-\|x\|^2}{\|x-\xi\|^n}.
$$

<a id="statement-4-2"></a>
#### 命题 4.2（正性、调和性与总质量）

$P_n>0$，$\Delta_xP_n=0$，并且

$$
\int_{S^{n-1}}P_n(x,\xi)\,d\sigma(\xi)=1.
$$

**证明。**

令 $a=1-\|x\|^2$、$r=\|x-\xi\|$。
有 $\Delta a=-2n$、$\nabla a=-2x$、
$\nabla r^{-n}=-n(x-\xi)r^{-n-2}$、$\Delta r^{-n}=2nr^{-n-2}$，
所以

$$
\Delta(ar^{-n})=2nr^{-n-2}[-r^2+a+2x\cdot(x-\xi)]=0.
$$

核积分是旋转不变的光滑调和函数；径向方程
$(r^{n-1}F'(r))'=0$ 及原点光滑性使其为常数，$F(0)=1$ 给总质量一。

∎

<a id="thm:poisson"></a>
#### 定理 4.3（矩阵态值的唯一稳定调和延拓）

给定连续边界态 $g:S^{n-1}\to\mathcal D_d$，定义

$$
\boxed{\rho_g(x)=\int_{S^{n-1}}P_n(x,\xi)g(\xi)\,d\sigma(\xi).}
$$

则 $\rho_g(x)\in\mathcal D_d$，逐矩阵元调和，连续延拓到闭球且边界值为 $g$。
它是具有这些性质的唯一延拓。
任意固定矩阵范数下，

$$
\boxed{
\sup_{\overline B^n}\|\rho_g-\rho_h\|
\le\sup_{S^{n-1}}\|g-h\|.
}
$$

**证明。**

对任意 $v$，$v^\dagger\rho_gv=\int P_n v^\dagger g v\,d\sigma\ge0$；
迹等于核的总质量一。
内部紧集上可逐矩阵元交换微分与积分，给调和性。
对边界点 $\eta$，将积分分为 $\|\xi-\eta\|<\delta$ 及其补集。
近区由一致连续性控制；当 $\|x-\eta\|<\delta/2$ 时，远区核不超过
$(1-\|x\|^2)(2/\delta)^n$，故其质量趋零。得到边界连续性。
两解之差的每个实、虚矩阵元均调和且边界为零，最大值原理给唯一性。
最后由三角不等式及正核总质量一，逐点有
$\|\rho_g(x)-\rho_h(x)\|\le\int P_n\|g-h\|\,d\sigma\le\|g-h\|_\infty$。

∎

标量 Poisson–Dirichlet 原理是经典结果；这里将其直接用于矩阵态值，并逐项核对正性、
归一化与误差界。［[poisson](#ref-poisson)］
若不指定调和方程，$0$ 与 $1-\|x\|^2$ 在单位球边界相同而内部不同，
二者甚至都实解析。因此边界数据本身不是无条件的内部重构规则。

<a id="statement-4-4"></a>
#### 命题 4.4（内部秩由完整边界共同支撑决定）

对任意 $x\in B^n$，

$$
\ker\rho_g(x)=\bigcap_{\xi\in S^{n-1}}\ker g(\xi).
$$

**证明。**

$v^\dagger g(\xi)v$ 连续非负，且内部 Poisson 核处处正。
其积分为零当且仅当它在整个球面恒零；对正矩阵这等价于 $g(\xi)v=0$。

∎

<a id="cor:blochfill"></a>
#### 推论 4.5（纯二能级边界准确填满 Bloch 球）

取 $n=3,d=2$，$g(\xi)=(I+\xi\cdot\sigma)/2$。则

$$
\boxed{\rho_g(x)=\frac12(I+x\cdot\sigma),\qquad x\in\overline B^3.}
$$

结合定理 [2.1](#thm:stereo)，可写为

$$
\boxed{\rho(t,w)=\frac12(I+t\mathsf S_2(w)\cdot\sigma),\quad0\le t\le1.}
$$

其中 $w\in\widehat{\mathbb C}=\mathbb C\cup\{\infty\}$，
并约定 $\mathsf S_2(\infty)=-e_3$。

**证明。**

常数及线性坐标函数都调和；它们分别具有边界值 $1,\xi_1,\xi_2,\xi_3$。
由唯一性逐项得到公式。单位球中的全部 $x$ 给全部二能级密度态。

∎

这是“复平面参数化边界，再由指定模型恢复体”的准确正例。
其中 $t$ 是独立内部参数。一般边界场未必填满整个目标态体；
例如常量纯态边界只延拓成同一点。
调和平均也不自动是一个同载体酉门：非恒定纯边界可给混态，酉共轭则保纯。

<a id="prop:semigroup"></a>
#### 命题 4.6（径向延拓的递归相容与误差预算）

定义 $(\mathcal P_r g)(\theta)=\rho_g(r\theta)$，$0\le r<1$，并令 $\mathcal P_1=\operatorname{id}$。
则 $\mathcal P_r\mathcal P_s=\mathcal P_{rs}$，且每个 $\mathcal P_r$ 的一致范数至多一。
若每次递归另有误差 $\eta_k$，总误差满足

$$
e_m\le e_0+\sum_{k=1}^m\eta_k.
$$

**证明。**

$x\mapsto\rho_g(sx)$ 是边界值 $\mathcal P_sg$ 的调和延拓；由唯一性在 $r\theta$ 处等于
$\rho_g(sr\theta)$，给半群式。收缩性来自定理 [4.3](#thm:poisson)；
误差界逐步使用 $e_{k+1}\le e_k+\eta_{k+1}$。

∎

所以严格相容的内向延拓不放大已有误差，但不断注入的新误差仍需可求和预算。
这里没有把算子范数一误称为每步严格收缩。

<a id="section-5"></a>
## 5. 项目已有的边界重建：内部质量变成边界度量

项目 V24 定理 8.3 已有与本轮直觉直接对应的有限维结果。
这里的“边界/内部”首先是给定的索引分块，是否为空间几何边界还需另给模型。［[v24](#ref-v24)］

<a id="thm:boundaryschur"></a>
#### 定理 5.1（既有 Schur 边界重建及有效归一化）

设有限 Hermitian 算符

$$
L=\begin{pmatrix}L_{BB}&L_{BI}\\L_{IB}&L_{II}\end{pmatrix},
\quad \lambda\in\mathbb R\setminus\operatorname{spec} L_{II},
\quad R_\lambda=(L_{II}-\lambda I)^{-1}.
$$

全本征方程 $L(g,x)^{\mathsf T}=\lambda(g,x)^{\mathsf T}$ 等价于

$$
\boxed{
K_{\rm eff}(\lambda)g=\lambda g,\qquad
x=-R_\lambda L_{IB}g,
\quad K_{\rm eff}=L_{BB}-L_{BI}R_\lambda L_{IB}.
}
$$

完整态的归一化准确拉回为

$$
\boxed{
\|g\|^2+\|x\|^2=g^\dagger G(\lambda)g,
\quad G=I+L_{BI}R_\lambda^2L_{IB}=I-K_{\rm eff}'(\lambda)\succeq I.
}
$$

**证明。**

第二个分块方程解出内部向量，代入第一块即得有效边界方程。
由于 $R_\lambda$ 自伴，内部范数为

$$
\|x\|^2=g^\dagger L_{BI}R_\lambda^2L_{IB}g.
$$

再对逆算子求导，得到 $R_\lambda'=R_\lambda^2$，
从而得到所列 $G=I-K_{\rm eff}'$ 公式。

∎

这表明内部的范数预算没有消失，而是进入边界的正确度量 $G$。
把边界直接改为 $\|g\|=1$ 一般不等于完整态归一化。
令 $\gamma=\operatorname{dist}(\lambda,\operatorname{spec} L_{II})>0$，则重建映射满足

$$
\left\|\begin{pmatrix}\delta g\\-R_\lambda L_{IB}\delta g\end{pmatrix}\right\|
\le
\sqrt{1+\|L_{IB}\|^2/\gamma^2}\,\|\delta g\|.
$$

因此这条边界重建具有明确的谱间隔稳定条件。
当可逆条件失效时，内部可能有边界看不到的模。
例如 $L=\lambda I_3$、边界仅取第一坐标，内部的 $e_2,e_3$ 两个正交单位态给相同零边界。

V24 推论 8.4 的多步消元要求保留完整 $L-\lambda I$ 与全部重建映射。
在每次所需逆都存在的共同域上，分组无关性来自同一个线性方程解的唯一性。
若每步只保留归一化方向、删掉长度或重建算子，就不满足该前提。

<a id="section-6"></a>
## 6. 真正的复解析推广：多个复变量及完整边界函数

<a id="thm:cauchy"></a>
#### 定理 6.1（多复平面的迭代 Cauchy 重构）

设 $F$ 在闭单位多圆盘 $\overline{\mathbb D}^{\,m}$ 的某个邻域上全纯。
则对 $z\in\mathbb D^m$，

$$
\boxed{
F(z)=\frac1{(2\pi i)^m}
\int_{|\zeta_1|=1}\!\cdots\!\int_{|\zeta_m|=1}
\frac{F(\zeta_1,\ldots,\zeta_m)}
{\prod_{j=1}^m(\zeta_j-z_j)}\,
d\zeta_m\cdots d\zeta_1.
}
$$

完整 distinguished boundary $\mathbb T^m$ 上的数据唯一确定 $F$。
对两份满足前提的 $F,H$，

$$
\sup_{\overline{\mathbb D}^{\,m}}|F-H|
\le\sup_{\mathbb T^m}|F-H|.
$$

**证明。**

固定其余变量，对第一个变量使用一元 Cauchy 公式；
再对被积函数的第二个变量使用同一公式，依次迭代。
紧积分域上连续性允许交换积分顺序，得到公式及唯一性。
误差界对每个变量依次使用一元最大模原理。

∎

这是用户“高维关系逐个整理到复平面”的一个准确解析版本。
每步处理一个复变量，其余变量仍保留；边界数据是 $m$ 个角变量的完整函数，
不是有限个标量。上述结果是标准多复变理论，本轮采用较强的邻域全纯前件以保持证明简洁。［[cauchy](#ref-cauchy)］

<a id="statement-6-2"></a>
#### 命题 6.2（单切片不能决定新复维度）

给定一元全纯函数 $f(z_1)$，在 $z_2=0$ 上取相同值的二元全纯函数并不唯一。

**证明。**

对任意二元全纯 $H$，$F_H(z_1,z_2)=f(z_1)+z_2H(z_1,z_2)$
在该切片上都等于 $f$。取 $H=0,1$ 得不同延拓。

∎

任意边界函数也未必是全纯边界值。
例如单位圆上的 $g(\zeta)=\overline\zeta$ 有调和延拓 $\overline z$，
却没有连续到闭盘的全纯延拓：若存在 $f$，则 $zf(z)$ 的边界恒为一，
最大模原理给 $zf(z)=1$，与 $z=0$ 矛盾。

<a id="prop:illposed"></a>
#### 命题 6.3（精确解析唯一性不蕴含向外稳定性）

固定 $0<a<b<1$，在同一单位盘上取整函数
$f_N(z)=(z/b)^N$。它们满足

$$
\sup_{|z|\le a}|f_N(z)|=(a/b)^N\longrightarrow0,
\qquad f_N(b)=1.
$$

故从内子盘的一致数据向较大域作全纯延拓，在没有额外增长约束时并不连续稳定。

**证明。**

两个显示式由模长直接得到；在目标点的值没有趋零，排除该重构算子在零处的连续性。

∎

这个反例与完整外边界的 Poisson 或 Cauchy 内向稳定重构不冲突，
两者的数据区域与函数前提不同。

<a id="section-7"></a>
## 7. 高维纯态的复平面图册与循环相容

<a id="statement-7-1"></a>
#### 定义 7.1（共同参考的分量比值图）

对非零 $\alpha=(\alpha_1,\ldots,\alpha_d)\in\mathbb C^d$，
在 $\alpha_k\ne0$ 的图上定义 $w_j^{(k)}=\alpha_j/\alpha_k$，并置 $w_k^{(k)}=1$。

<a id="thm:pureatlas"></a>
#### 定理 7.2（多个二元球面读数完整表示高维纯态）

在一个共同参考图中，每个 $j\ne k$ 的条件二元态为

$$
\tau_{kj}=\frac1{1+|w_j^{(k)}|^2}
\begin{pmatrix}1&\overline{w_j^{(k)}}\\w_j^{(k)}&|w_j^{(k)}|^2\end{pmatrix}.
$$

其 Bloch 点是 $\mathsf S_2(w_j^{(k)})$。
这 $d-1$ 个带标签的球面点唯一决定全局纯态射线：

$$
\boxed{
\psi\sim\frac{(w_1^{(k)},\ldots,w_d^{(k)})^{\mathsf T}}
{\sqrt{\sum_i|w_i^{(k)}|^2}}.
}
$$

图间变换为

$$
\boxed{w_j^{(\ell)}=\frac{w_j^{(k)}}{w_\ell^{(k)}}}
$$

并在非零重叠域上全纯，满足三重重叠相容条件。

**证明。**

将 $(\alpha_k,\alpha_j)$ 除以共同非零因子 $\alpha_k$ 即得条件块。
上一轮逆立体投影的逆式恢复每个复比值。
全部比值确定全局射线，总归一化给显示向量。
更换参考仅是除以新参考比值，三次换图的分母依次消去。

∎

全局空间因此是 $\mathbb{CP}^{d-1}$，具有 $d-1$ 个复维、$2d-2$ 个实维。
它是多个复坐标图的相容系统，不是一个复平面。
标准射影图与 $S^{2d-1}/U(1)$ 描述可见原始课程来源；本节给了本轮具体二元读出公式。［[cp](#ref-cp)］
在 $d=3$、参考第一分量时，状态
$(1,w_2,w_3)/\sqrt{1+|w_2|^2+|w_3|^2}$
需要两个复关系或两个带共同参考的 AURIC 球面读数，仍有四个实自由度。

<a id="statement-7-3"></a>
#### 命题 7.3（可控的参考图）

每个纯态都可选择一个最大模分量作参考，使所有 $|w_j^{(k)}|\le1$。
若两态共用这样的图，令 $n_j=\mathsf S_2(w_j)$、$n'_j=\mathsf S_2(v_j)$，则

$$
\frac12\|\rho-\rho'\|_1
\le2\left(\sum_{j\ne k}\|n_j-n'_j\|^2\right)^{1/2}.
$$

**证明。**

最大模分量给比值上界。逆立体投影的精确弦长公式给
$|w_j-v_j|\le\|n_j-n'_j\|$。
带固定参考分量一的两个未归一向量范数均至少一，归一化后的距离至多未归一距离的两倍。
纯态迹距离不超过选定单位代表的向量距离，合并得到所述界。

∎

实际选图、换图仍需保留图标签和参考标定；几何上存在良好图不自动给实际取得权限。

<a id="thm:ratios"></a>
#### 定理 7.4（分量比值的树传播与循环判据）

在非零支撑上的连通图中，每条有向边给 $w_{ij}\ne0$，且 $w_{ji}=w_{ij}^{-1}$。
存在非零振幅使 $w_{ij}=\alpha_j/\alpha_i$，当且仅当每个有向闭路满足

$$
\boxed{\prod_{\rm cycle}w_{ij}=1.}
$$

存在时，归一化后的全局射线唯一。

**证明。**

必要性由比值连乘消去。充分性：选根及生成树，将根振幅设为一，
沿树路径的边比值乘积定义其余振幅。
任意非树边与树路径构成闭路，所给条件保证它也匹配。
任意另一解在相邻顶点的比例相同，连通性使全部只差共同标量；归一化只剩共同相位。

∎

若另给人口 $p_i>0$，还需 $|w_{ij}|^2=p_j/p_i$。
零分量不定义相位或逆比值，须按实际支撑分层。
这里是同一个态的分量比值循环，与沿不同纯态路径平行输运的 Berry 相位不同。
一般混态的相干关系也不能只由这个纯态比值判据决定。

<a id="section-8"></a>
## 8. 任意有限维正关系的二元块展开

固定 $d\ge2$ 和正交基 $e_i$。
令 $\iota_{ij}:\mathbb C^2\to\mathbb C^d$ 把基态送到 $e_i,e_j$，$i<j$。
对 $\rho\in\mathcal D_d$ 定义

$$
B_{ij}=\iota_{ij}^\dagger\rho\iota_{ij}
=\begin{pmatrix}p_i&\rho_{ij}\\\overline\rho_{ij}&p_j\end{pmatrix},
\qquad N_{ij}=p_i+p_j.
$$

$N_{ij}>0$ 时 $B_{ij}=N_{ij}(I+r_{ij}\cdot\sigma)/2$，其中

$$
r_{ij}=\frac{(2\Re\rho_{ij},-2\Im\rho_{ij},p_i-p_j)}{N_{ij}}.
$$

负号来自这里把 $\rho_{ij}$ 放在上非对角元的约定。
当 $N_{ij}=0$ 时，正性给 $B_{ij}=0$，只保留零块标记，不定义条件态。

<a id="thm:pairreconstruct"></a>
#### 定理 8.1（全部带标签二元块的准确重构）

全部 $(i,j,N_{ij},r_{ij})$ 及零块标记唯一决定 $\rho$，并有

$$
\begin{aligned}
p_i&=\frac{N_{ij}}2(1+r_{ij,3}),&
p_j&=\frac{N_{ij}}2(1-r_{ij,3}),\\
\rho_{ij}&=\frac{N_{ij}}2(r_{ij,1}-ir_{ij,2}),&
\sum_{i<j}N_{ij}&=d-1.
\end{aligned}
$$

嵌回全空间后的式子为

$$
\boxed{
\rho=\sum_{i<j}\iota_{ij}B_{ij}\iota_{ij}^\dagger
-(d-2)\operatorname{diag}(p_1,\ldots,p_d).
}
$$

**证明。**

每个非对角元出现一次，每个对角元出现 $d-1$ 次，减去重复的 $d-2$ 份即可。
质量和由每个 $p_i$ 被计数 $d-1$ 次及 $\sum p_i=1$ 得到。

∎

本节的二元块是同一固定基底中两个*振幅通道*的压缩，
不是多体系统的二体约化态集合。
例如 $(\lvert 000\rangle\pm\lvert 111\rangle)/\sqrt2$ 的任意二体约化态均为
$(\lvert 00\rangle\langle 00\rvert+\lvert 11\rangle\langle 11\rvert)/2$，因为被迹掉的一位使交叉项为零；
但本节在基通道 $000,111$ 上的二阶主块仍保留正负相干，故能区分两全局态。

单个条件态不决定其在全体中的质量。
例如 $\psi_t=\sqrt{t/2}e_1+\sqrt{t/2}e_2+\sqrt{1-t}e_3$，$0<t<1$，
其 $12$ 条件块不变，而 $N_{12}=t$。
不过，若保留全部带标签的条件块及零块信息，质量可利用完整重叠和总迹一推回。
选 $p_k>0$，由各条件块的对角比得到 $q_j=p_j/p_k$，置 $q_k=1$；则

$$
p_j=q_j/\sum_\ell q_\ell.
$$

所以质量可以由完整冗余关系*恢复*，不能宣称它在这种完整资料下必然不可恢复。
省略质量时必须保留这一恢复机制；局部独立接口、零质量守护及事件成本仍需实际质量。

<a id="thm:pairstability"></a>
#### 定理 8.2（块误差的全局稳定恒等式）

对两态之差 $\Delta=\rho-\widetilde\rho$，

$$
\boxed{
\sum_{i<j}\|\Delta B_{ij}\|_F^2
=\|\Delta\|_F^2+(d-2)\sum_i|\Delta_{ii}|^2.
}
$$

因而

$$
\frac1{d-1}\sum_{i<j}\|\Delta B_{ij}\|_F^2
\le\|\Delta\|_F^2\le\sum_{i<j}\|\Delta B_{ij}\|_F^2.
$$

令 $v_{ij}=N_{ij}r_{ij}$，零块置 $v_{ij}=0$，则

$$
\boxed{
\|\Delta B_{ij}\|_F^2
=\frac12\left((\Delta N_{ij})^2+\|\Delta v_{ij}\|^2\right).
}
$$

**证明。**

每块平方范数为 $|\Delta_{ii}|^2+|\Delta_{jj}|^2+2|\Delta_{ij}|^2$，
逐项计数给恒等式与两界。
最后一式由 $B=(NI+v\cdot\sigma)/2$ 及 Pauli 迹正交性得到。

∎

这个形式在零质量处无需除法。条件态本身在小质量处可能敏感，
带质量向量 $v=Nr$ 则直接进入线性的全局重构。

<a id="section-9"></a>
## 9. 从局部合法到全局相容：Gram 与 Schur 递归

<a id="prop:counterexample"></a>
#### 命题 9.1（局部三维块不能单独保证全局正性）

矩阵

$$
M=\frac13\begin{pmatrix}1&-1&-1\\-1&1&-1\\-1&-1&1\end{pmatrix}
$$

迹为一，所有二阶主块均非负、重叠对角一致，条件 Bloch 点均为 $(-1,0,0)$，
但 $M$ 不是密度态。

**证明。**

每个二阶块是 $\frac13\left(\begin{smallmatrix}1&-1\\-1&1\end{smallmatrix}\right)\succeq0$。
但对 $v=(1,1,1)^{\mathsf T}$，$Mv=-v/3$，故 $v^\dagger Mv=-1$。

∎

这一反例的未归一版本已在 V37 命题 6.5 中给出。［[v37](#ref-v37)］
其每边纯态比值为 $-1$，三环乘积为 $-1$，违反定理 [7.4](#thm:ratios)。
退化不是反例的必需前提：把非对角的 $-1$ 改为 $-a$，$1/2<a<1$，
所有二阶块严格正，但全一方向的本征值仍为 $(1-2a)/3<0$。

在正人口支撑上定义
$\Gamma_{ij}=\rho_{ij}/\sqrt{p_ip_j}$，
则 $\rho=\operatorname{diag}(\sqrt p)\Gamma\operatorname{diag}(\sqrt p)$。
所以完整正性等价于 $\Gamma\succeq0$；逐边正性只给 $|\Gamma_{ij}|\le1$。
对角为零的行列由正性强迫为零，另行保留其支撑标记。

<a id="thm:psdschur"></a>
#### 定理 9.2（含奇异边界的递归正性判据）

设 $M=\left(\begin{smallmatrix}A&b\\b^\dagger&c\end{smallmatrix}\right)$ Hermitian，
$A^+$ 为 Moore–Penrose 伪逆。则

$$
\boxed{
M\succeq0\iff
A\succeq0,\quad b\in\operatorname{Ran} A,\quad s:=c-b^\dagger A^+b\ge0.
}
$$

在上述正性条件成立时，还有 $\operatorname{rank} M=\operatorname{rank} A+\mathbf1_{\{s>0\}}$。

**证明。**

必要性先给 $A\succeq0$。
若 $h\in\ker A$ 且 $h^\dagger b\ne0$，二次型
$2\Re(h^\dagger bt)+c|t|^2$ 可选充分小且相位合适的 $t$ 变负，矛盾。
故 $b\perp\ker A$，即 $b\in\operatorname{Ran} A$。
令 $y=A^+b$，$Ay=b$，则

$$
(x,t)^\dagger M(x,t)
=(x+yt)^\dagger A(x+yt)+s|t|^2.
$$

取 $x=-yt$ 给 $s\ge0$，反向也由该式成立。
可逆三角合同将 $M$ 化为 $\operatorname{diag}(A,s)$，得到秩公式。

∎

若 $A=0$，必须 $b=0$，条件退化为 $c\ge0$。
在 Gram 向量解释下，$b^\dagger A^+b$ 是被已知张成空间解释的平方范数，
$s$ 是剩余正交分量的平方范数；$s>0$ 才需要新正交方向。
对命题 [9.1](#prop:counterexample)，前二阶块值域为 $\operatorname{span}(1,-1)$，
新列 $b=-(1,1)^{\mathsf T}/3$ 不在该值域，故拼接直接失败。

项目量子原则主卷 §27.1 还给完整双块版本：

$$
\begin{pmatrix}A&C\\C^\dagger&B\end{pmatrix}\succeq0
\iff C=A^{1/2}TB^{1/2}\quad\text{某个 }\|T\|\le1,
$$

其中 $A,B\succeq0$，核与支撑按奇异版本处理。
这说明两份内部资料之外，交叉关系是共同实现所需的额外数据。［[principles](#ref-principles)］

<a id="section-10"></a>
## 10. 二元展开的相干实现与原 AURIC 固定码

<a id="thm:coherent"></a>
#### 定理 10.1（带相干标签的普遍有限维等距展开）

对 $d\ge2$、$i<j$ 定义

$$
K_{ij}=\frac{\lvert 0\rangle\langle i\rvert+\lvert 1\rangle\langle j\rvert}{\sqrt{d-1}},
\qquad
V_d=\sum_{i<j}\lvert ij\rangle\otimes K_{ij}.
$$

则 $V_d^\dagger V_d=I_d$。
因此 $V_d$ 保持全部向量内积及归一化，是到
$\mathbb C^{\binom d2}\otimes\mathbb C^2$ 的等距编码。
对标签去相干后得到 CPTP 仪器

$$
\boxed{
\mathcal E_d(\rho)=\bigoplus_{i<j}\frac{B_{ij}}{d-1}.
}
$$

其标签概率为 $N_{ij}/(d-1)$；完整输出矩阵在数学上唯一决定输入态。

**证明。**

$K_{ij}^\dagger K_{ij}=(\lvert i\rangle\langle i\rvert+\lvert j\rangle\langle j\rvert)/(d-1)$。
每个基投影出现 $d-1$ 次，所以求和为 $I_d$，也即 $V_d^\dagger V_d=I_d$。
去相干只保留标签对角块 $K_{ij}\rho K_{ij}^\dagger=B_{ij}/(d-1)$。
Kraus 完备性给完全正、保迹；定理 [8.1](#thm:pairreconstruct) 给统计重构。

∎

所有标签都属于同一个整体的内部寄存器。
一次仪器执行只提供一个标签及其二元分支，不同时供应全部条件矩阵，
也不将分支变成可独立取用的未知态副本。

<a id="thm:nocptpinverse"></a>
#### 定理 10.2（统计完整与共同量子逆的差别）

当 $d>2$ 时，$\mathcal E_d$ 没有在全部输入态上成立的 CPTP 左逆。

**证明。**

取 $\psi_\pm=(e_1\pm e_2)/\sqrt2$、$\rho_\pm=\lvert \psi_\pm\rangle\langle \psi_\pm\rvert$。
两输入正交，故 $\|\rho_+-\rho_-\|_1=2$。
输出中仅 $12$ 块有差，因此

$$
\|\mathcal E_d(\rho_+)-\mathcal E_d(\rho_-)\|_1=\frac2{d-1}.
$$

若有 CPTP 左逆，迹范数收缩性要求 $2\le2/(d-1)$，矛盾。
所用收缩性可直接由 Hermitian 迹范数对偶式证明：
CPTP 映射的伴随为正且含幺，将 $-I\preceq H\preceq I$ 映回同一区间，
故 $\max_{-I\preceq H\preceq I}\operatorname{Tr}(H\Phi(X))\le\|X\|_1$。

∎

保留完整相干标签的 $V_d$ 没有该损失。
其正交像可补为一个更大内部空间的正交基，因而可作数学上的酉扩张。
统计线性反演与未知单态的物理通道恢复不能互换。

现在接回项目 V37 的*同一个*固定等距码 $J:\mathbb C^2\to\mathbb C^5$。
本稿的 $(E_N,E_1,E_2,E_3,E_{13})$ 按五个位置模式命名，
分别对应 V37 数值标签的 $(E_0,E_2,E_3,E_5,E_{25})$。
令

$$
\nu=\frac1{1+2\sqrt3+\sqrt{11}},\quad
a_\nu=\frac{\nu(\sqrt3+\sqrt{11})}{2},\quad
u_0=(a_\nu,a_\nu,\nu).
$$

其原占位轴及关系效果满足

$$
\begin{aligned}
E_1+E_{13}&=a_\nu I+\nu\sigma_x,&
E_3+E_{13}&=a_\nu I+\nu\sigma_y,\\
E_2&=\nu(I+\sigma_z),&
E_{13}&=\frac\nu2(\sqrt3I-\sigma_x-\sigma_y-\sigma_z),
\end{aligned}
$$

并且 $E_N=3E_{13}$，全部五效果之和为 $I$。
这些是既有固定编码，不重新定义原 $F[2]$。［[v37](#ref-v37)］

<a id="cor:auricatlas"></a>
#### 推论 10.3（高维态的原 AURIC 关系图册）

复合映射

$$
\boxed{
W_d=(I_{\rm label}\otimes J)V_d
}
$$

为保持全部内积的等距编码。
每个正质量分支的条件原三轴为

$$
\boxed{u_{ij}=u_0+\nu r_{ij},}
$$

其条件关系模式概率为

$$
\kappa_{ij}=\frac\nu2(\sqrt3-r_{ij,1}-r_{ij,2}-r_{ij,3}),
\qquad p_{N\mid ij}=3\kappa_{ij}.
$$

完整联合五模式概率还乘以标签质量 $N_{ij}/(d-1)$。
全部带标签数据及相容条件完整表示 $\rho$。

**证明。**

$J^\dagger J=I$ 与 $V_d^\dagger V_d=I$ 给 $W_d^\dagger W_d=I$。
条件块应用固定效果并取期望，得到三轴和关系公式。
联合质量总和为 $\sum_{i<j}N_{ij}/(d-1)=1$。
固定编码对每个二元态的三均值单射，故可先恢复全部块，再使用全局重构式。

∎

零质量标签不定义条件坐标，其全部联合模式质量为零。
每个局部 AURIC 单元满足同一个固定编码关系，但高维信息继续由标签、块间相容及相干承担。
数学等距构造本身不证明项目固定原生门菜单已编译该 $W_d$，更不供应字长或取得成本。

<a id="section-11"></a>
## 11. 项目已有的另一条高维路径：算子值三轴递归

V37 §6 已给出任意有限上下文的完整二元递归。
在 $\mathbb C^2\otimes\mathcal K$ 上写

$$
\rho=\begin{pmatrix}A&C^\dagger\\C&B\end{pmatrix}\succeq0,
\qquad \operatorname{Tr}(A+B)=1,
$$

并定义

$$
S=A+B,\quad Z=A-B,\quad X=C+C^\dagger,\quad Y=i(C^\dagger-C).
$$

则

$$
\boxed{
\rho=\frac12\bigl(I\otimes S+\sigma_x\otimes X+\sigma_y\otimes Y+\sigma_z\otimes Z\bigr).
}
$$

证明只需逐块展开：$A=(S+Z)/2$、$B=(S-Z)/2$、$C=(X+iY)/2$。
完整相容条件是重组矩阵正半定及 $\operatorname{Tr} S=1$。
高维的 $X,Y,Z$ 是上下文*算子*，不能只取三个迹而仍宣称保留完整态。［[v37](#ref-v37)］

特别地，不能把标量球面条件直接替换为
$X^2+Y^2+Z^2\preceq S^2$。
对合法 Bell 态 $\Phi^+=(\lvert 00\rangle+\lvert 11\rangle)/\sqrt2$，

$$
S=I/2,\quad X=\sigma_x/2,\quad Y=-\sigma_y/2,\quad Z=\sigma_z/2,
$$

左侧为 $3I/4$，右侧为 $I/4$，而完整矩阵仍是合法纯态。

逐因子递归后，完整 $m$ 量子位载体有 Pauli 展开

$$
\rho=2^{-m}\sum_{\alpha\in\{0,x,y,z\}^m}
r_\alpha\,\sigma_{\alpha_1}\otimes\cdots\otimes\sigma_{\alpha_m}.
$$

迹正交性保证唯一性，$r_{0\cdots0}=1$，一般态保留 $4^m-1$ 个实参数。
任意有限 $d$ 可先等距嵌入 $2^m\ge d$ 的基子空间，编码族仍有 $d^2-1$ 个自由度。
这与本轮的标量二元块图册互补：一种把上下文保留在轴算子中，另一种保留为多个带标签的局部块。

<a id="section-12"></a>
## 12. 单个三维点不能稳定承载任意高维自由度

<a id="thm:dimension"></a>
#### 定理 12.1（稳定压缩的维数下界）

设 $U\subseteq\mathbb R^k$ 含非空开集，且 $f:U\to\mathbb R^3$
在其中满足双向稳定界

$$
c\|x-y\|\le\|f(x)-f(y)\|\le C\|x-y\|,
\qquad 0<c\le C<\infty.
$$

则 $k\le3$。

**证明。**

取 $U$ 内一个闭小立方体，缩放为单位立方体。
其中步长 $1/N$ 的网格有 $(N+1)^k$ 个点，点间至少距 $1/N$。
像点彼此至少距 $c/N$，且由上界全部位于固定半径 $R$ 的球内。
以这些像点为中心、半径 $c/(3N)$ 的三维球两两不交，
并包含在半径 $R+c/(3N)$ 的球中。比较体积得

$$
(N+1)^k\le\left(1+\frac{3RN}{c}\right)^3.
$$

$N\to\infty$ 排除 $k>3$。

∎

对一般 $d$ 维混态，$k=d^2-1$；对纯态局部射影图，$k=2d-2$。
因此 $d\ge3$ 时，两者都不能以这种双向稳定方式压入单个三实数点。
本轮构造没有违反该下界：纯态保留 $d-1$ 个复比值，
一般态保留多块图册，或算子值上下文。

边界函数也可以携带无限多个自由度。
因此“边界的几何维数更低”不能直接换成“所需数据只是更少几个数”。
若使用有限精度或实际读口，资料数量、条件数与跨块取得条件仍须另外核算。

<a id="section-13"></a>
## 13. 最新项目进展：逐源唯一与统一稳定的分离

本轮新 RRO §§18–21 固定了来源内的实际正分支、共同切口、
整个块代数上的正代表、完整标签粗 Born 条件行及原纯更新。
在其固定实际纯源面上，令 $T$ 是中心权重差的总变差，
$N_u$ 是原有限事件字的区别差上确界；不要求某个有限字恰好取到它。
两个相关 $21$ 维纯尾块均占据且射线不同的情形给

$$
\boxed{
\delta_u T\le N_u\le T,
\qquad
\delta_u=\sqrt{1-|\langle\widehat u_{000},\widehat u_{010}\rangle|^2},
\qquad C_u^{\rm opt}=1/\delta_u.
}
$$

该公式是来源指定的纯源面结论，不移植为任意观测接口的普遍等式。［[rro](#ref-rro)］

新 §20 构造原 ready 的实际有限前缀族，使三个尾质量始终处于 $(1/4,1/2)$，
每个固定来源面上的原中心权重均具有有限的语义逆常数，
但 $\delta_u\to0$，所以这一来源族没有统一的有限逆常数。
因此失稳并不只来自罕见事件或零质量。
新 §21 的有限容限字典存在性也没有自动给字清单、编译算法、字长或执行可靠性；
原权重的源一致稳定仍需分离量的统一正下界，或改用适当可观察商。
本稿核对并使用其显示结论与来源范围，没有重新认证其全部上游原生控制密度证明。

对于本轮的递归，类似裕量具体表现为谱间隔 $\gamma$、参考图分母、
有效读口的最小分离量，以及所保留相干关系的条件数。
若第 $k$ 步有恢复常数 $C_k$ 与新增误差 $\eta_k$，则

$$
e_m\le
\left(\prod_{j=0}^{m-1}C_j\right)e_0+
\sum_{k=0}^{m-1}\eta_k\prod_{j=k+1}^{m-1}C_j.
$$

证明是将 $e_{k+1}\le C_ke_k+\eta_k$ 逐次代入。

<a id="note-recursive-error-domain"></a>
**编者适用条件注（不属原稿；递归误差预算的定义域）。** 上式取整数 $m\ge0$，初始误差及各步误差 $e_k,\eta_k\ge0$，恢复因子 $0\le C_k<\infty$；误差值取有限实数。空乘积约定为 $1$，空和约定为 $0$，所以 $m=0$ 时右端为 $e_0$。非负因子保证把各步不等式逐次代入时不反转方向。第 4 节命题 [4.6](#prop:semigroup) 的加法预算是 $C_k=1$ 的情形，同样使用非负误差及空和约定。

总归一化、逐步唯一及局部球面合法性，并不替代这个稳定预算。

<a id="section-14"></a>
## 14. 统一命题与可继续发展的对象

<a id="thm:unified"></a>
#### 定理 14.1（边界延拓与高维 AURIC 图册的条件统一）

给定明确的有限复 Hilbert 模型、内积、基标定及 V37 固定编码，成立以下结论：

1. 连续正径向边界与独立径向参数唯一给出星形体；
完整连续边界态与指定调和模型唯一给出正、归一且稳定的内部态场。
2. 二能级的全部纯态边界经该模型准确填成 Bloch 球；
高维态体须使用完整降秩边界，纯态只是其中一层。
3. 任意有限维纯态可展开成带共同参考的多个复平面关系，再提升为多个 AURIC 球面读数；
任意密度态可展开成带质量、标签和重叠条件的二元球体块。
4. 在索引与共享对角数据已经一致的前提下，这些局部块存在共同全局态，
当且仅当重组矩阵满足全局正性与归一化；
可用奇异 Schur 条件递归检验。纯态比值图则由实际支撑上的循环乘积条件拼接。
5. 完整相干标签等距 $W_d$ 保持整体内积；只保留经典标签与条件块时，
统计上仍可完整反演，但 $d>2$ 时没有全态 CPTP 逆。
6. 多复变量全纯关系可在完整相容边界数据下逐复平面作 Cauchy 重构；
单切片不决定新变量，无增长约束的向外延拓也不保证稳定。

**证明。**

依次应用定理 [2.2](#thm:cone)、[4.3](#thm:poisson)、
推论 [4.5](#cor:blochfill)、定理 [3.2](#thm:densityboundary)、
[7.2](#thm:pureatlas)、[8.1](#thm:pairreconstruct)、[9.2](#thm:psdschur)、
[7.4](#thm:ratios)、[10.1](#thm:coherent)、[10.2](#thm:nocptpinverse)、
推论 [10.3](#cor:auricatlas)、定理 [6.1](#thm:cauchy) 与命题 [6.3](#prop:illposed)。

∎

所以“高维展开到复平面，再提升到三维”可精确理解为
*带索引与相容条件的局部表示体系*。
边界、内部、尺度和法向之间确实有可证明的统一关系；
每一次提升保留其增加的参数，每一次整理保留其交叉信息，
每一次递归保留相应的有效度量与稳定裕量。
这给出有限数学关系的通用表示方案，不宣称已从裸归一化推出物理时空维数、
任意边界的全纯延拓或项目原生门的免费实现。
标准立体投影、Poisson、Cauchy、射影图册、Gram 与 Schur 结构均不主张原创优先权；
本稿的工作是将其明确条件、直接证明、量子态值版本和原 AURIC 编码合成。

<a id="references"></a>
## 固定来源与适用范围

<a id="ref-head"></a>
**[head]**
[trureturing，固定提交 3c22c32855cf](https://github.com/the-omega-institute/trureturing/commit/3c22c32855cfb4640e445abede6ff2898c404800)。
2026-10-31 16:53:55（新加坡）。本轮定向核对完整 theory delta 及相关固定文本。

<a id="ref-v24"></a>
**[v24]**
[AURIC 两基态、三通道、相位手性与递归平方律，V24](https://github.com/the-omega-institute/trureturing/blob/3c22c32855cfb4640e445abede6ff2898c404800/docs/develop/theory/AURIC_TWO_BASIS_STATES_THREE_CHANNELS_PHASE_CHIRALITY_AND_RECURSIVE_SQUARE_LAW_V24.md)。
§3：Hopf/Bloch；§8 定理8.3、推论8.4：边界 Schur 重建、有效归一化度量与多步消元。

<a id="ref-v37"></a>
**[v37]**
[AURIC 二元关系、酉表示与黄金门通用性，V37](https://github.com/the-omega-institute/trureturing/blob/3c22c32855cfb4640e445abede6ff2898c404800/docs/develop/theory/AURIC_BINARY_RELATIONS_UNITARY_REPRESENTATION_AND_GOLDEN_GATE_UNIVERSALITY_V37.md)。
§3：原五模式固定等距码；§6：算子值三轴、完整二元递归及全局 Gram 相容。

<a id="ref-principles"></a>
**[principles]**
[AURIC 量子原则与相干重构](https://github.com/the-omega-institute/trureturing/blob/3c22c32855cfb4640e445abede6ff2898c404800/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md)。
§27.1：两份正核的交叉收缩关系、奇异边界与相干比较的额外接口。

<a id="ref-rro"></a>
**[rro]**
[递归关系观察：Fibonacci 原生末端认证](https://github.com/the-omega-institute/trureturing/blob/3c22c32855cfb4640e445abede6ff2898c404800/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FIBONACCI_NATIVE_TERMINAL_CERTIFICATION.md)。
本轮新 §§18–21：固定纯源面的事件范数、尖锐恢复常数、实际前缀失稳族与有限容限字典。

<a id="ref-poisson"></a>
**[poisson]**
[UC Berkeley，Lecture 7: the Poisson integral formula](https://math.berkeley.edu/~avizeff/complex_analysis_S26/lecture_7.html)，2026。
标量单位盘的 Dirichlet 唯一性、正核及边界重构；本文自行证明一般球及矩阵态值版本。

<a id="ref-cauchy"></a>
**[cauchy]**
D. Chakrabarti，T. Gupta 记，
[MSRI 2018, Lecture 2](https://www.slmath.org/ckeditor_assets/attachments/1015/Day1-Lecture2.pdf)。
定理2.2及其证明：多圆盘迭代 Cauchy 公式；distinguished boundary 与最大模界。

<a id="ref-cp"></a>
**[cp]**
T. Ilmanen，
[ETH Zürich，Differential Geometry I，Exercise Sheet 10](https://metaphor.ethz.ch/x/2023/hs/401-3531-00L/ex/ex10.pdf)，2023，题5。
复射影空间、$2n$ 实维坐标图及 Hopf 商的标准定义；本文给具体比值重构证明。

<a id="ref-watrous"></a>
**[watrous]**
J. Watrous，
[The Theory of Quantum Information，Chapter 2](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)，2018。
§2.1.2：密度态、凸混合、纯态及带质量 ensemble 的标准模型。
