# 一处停住，一阶互定

> 参考输入：AI 撰写的工作稿，由用户提供于本会话（2026-11-04，Asia/Singapore）。Lean 是仓库的数学真源；本文仅为参考文稿，未作形式化认证。

QUANTUM ORIGINS / $\Omega Q$-008

从一个完整局部关系，回溯三维与有限量子理论

**本轮唯一候选：一处停住关系的全部横向微变，能够相互唯一补偿。**

在同一个完整原预测空间 $W$ 和原可逆作用闭包的 Lie 代数 $\mathfrak g$ 中，存在

$$
A\ne0,\qquad x\ne0,\qquad Ax=0,
$$

使完整线性关系

$$
\mathcal T_{A,x}
=\{([K],[y])\in(\mathfrak g/\mathbb R A)\times(W/\mathbb R x):Kx+Ay=0\}
$$

的两侧投影均为双射。

白话：**原来一份转向恰好把一份内容停住。任意一边稍微偏一点，另一边都恰好有一种横向偏法，能把这次变化补回来。**

上一轮在全部内容轴与全部转向轴上要求互定。本轮把这张全局表压缩为一个点上的完整一阶关系。保留有限完整预测、紧性、有效作用与原顺序闭合后，这一个点已经迫出整个三维旋转结构。

随后构造比较尺、复数、复二维振幅、原 Born 配对，以及由一阶补偿直接给出的平行搬运。最后明确发展全部有限矩阵量子理论所需的原复合、参考和过程接口。

 日期：2026-11-04。

固定来源：`dev@8e15c484cf5786fe69fef0627fd84a63cfeb5942`。

提交时间：2026-11-04 16:25:41 +0800。

承接：$\Omega Q$-007；本轮重新核查，仓库与理论正文增量均为零。

范围：普通数学定义、定理、证明与条件重建；本稿不是 Lean 认证。

“更简洁”有准确含义：全局条件缩为单点的一阶条件；没有声称背景前提消失、逻辑严格弱化或文献首创。

<a id="section-1"></a>

## 1. 本轮结论与项目接点

本轮的实质推进是

$$
\boxed{\text{一个停住点上的完整一阶互定}
\ \Longleftrightarrow\
\dim W=\dim\mathfrak g=3,\quad\mathfrak g=\mathfrak{so}(W,B).}
$$

因此，上一轮的全局轴互定会自动恢复。不是先画出三维再验证它，而是从原二元作用的一个一阶零关系推出三维。

另一个直接结果是：沿一条已给出的单位停住内容 $n(t)$，若原停住生成元为 $A(t)\ne0$，则

$$
\boxed{M_{\mathrm{hor}}(t)
=\frac{[A(t),\dot A(t)]}{-\tfrac12\operatorname{Tr}_W(A(t)^2)}}
$$

满足 $M_{\mathrm{hor}}n=\dot n$。它把“保持内容不动的生成元如何变化”，转成“怎样搬运这份内容”。该式不依赖 $A(t)$ 的非零重标，却不删除原转速与稳定子记录；复完成中的中心相位自由度也仍须单列。

**重新核查的仓库。**

本轮实际执行远端读取，`dev` 仍为 `8e15c484...`（完整哈希见封面）；其标题是合并 PR #26418 的 Bajnok–Beatty 阈值分布工作。相对 $\Omega Q$-007，提交、文件及理论正文均没有新增量。因此下文的新内容是候选及其证明的继续回溯，不是把旧仓库结论再次当作新进展。 [1](#ref-commit)

当前仍必须遵守两个已有边界。C117 §19 的立方响应虽有球面方向与完整旋转，完整预测容量仍为 $1+3+7=11$；可读二元记录反模型的容量为八。C127 §§35–40 使用的是事先给定的原 $D$、原中心、完整参考与原对象，其满足族可以只有 $3^k$ 大小的简单块而没有实际 $M_2$。本文不能缩掉原方向，也不能用后构造的 $R$ 替换原 $D$，或将数学支持角冒充实际对象。 [2](#ref-c117)、[3](#ref-c127)

<a id="section-2"></a>

## 2. 定义：整体内的完整内容与原转向

### 定义 2.1（完整原预测窗口）

在 $\Omega$ 内固定一个原归一准备。原总可逆控制含空词，接续封闭，并有同菜单内准确统计逆。共同未来域保留全部合法终端请求、结果标签、失败、可读旧记录及相关可用性区别。以全部未来概率定义实函数

$$
x_a(f,w)=p(a;f,w),\qquad p\ge0,\qquad \sum_w p(a;f,w)=1.
$$

置

$$
V=\operatorname{span}_{\mathbb R}\{x_a\},\quad u(x_a)=1,\quad
W=\ker u=\operatorname{span}_{\mathbb R}\{x_a-x_b\}.
$$

要求 $V$ 有限维且 $W\ne0$，不预置维数。原程序与日志继续存在；这里的预测表示不把它们的身份改写为相同。

### 引理 2.2（有界可逆接续给紧作用）

接续 $T_gx_a=x_{ag}$ 在 $V$ 上良定义。其矩阵闭包 $H$ 是紧群。令

$$
c=\int_H hx_\epsilon\,dh,\quad e=x_\epsilon-c,\quad
G=H|_W,\quad\mathfrak g=\operatorname{Lie}(G)\subseteq\operatorname{End}_\mathbb R(W).
$$

则 $V=\mathbb R c\oplus W$，$G$ 紧且忠实，$e\ne0$，并且 $W=\operatorname{span}(Ge)$。

**证明。**
若原行的线性组合在全部未来为零，它在以 $g$ 开头的未来也为零，故接续良定义。选有限实际行基与有限分离评价坐标。每个接续基行的所选坐标仍在 $[0,1]$，所以矩阵族一致有界。准确统计逆使逆矩阵也一致有界，闭包没有奇异矩阵，因而是紧群。

平均 $c$ 固定且 $u(c)=1$。若作用固定 $c$ 并在 $W$ 恒等，则在 $V$ 恒等，因此限制忠实。各 $x_a-c=T_ae$，而这些向量张成 $W$。若 $e=0$，全轨道不动，便有 $W=0$，矛盾。

### 定义 2.3（停住关系）

对 $A\in\mathfrak g$、$x\in W$，定义

$$
A\mathrel{\mathsf S}x\quad\Longleftrightarrow\quad Ax=0.
$$

它等价于 $\exp(tA)x=x$ 对所有 $t\in\mathbb R$ 成立。记
$\mathfrak g_x=\{K\in\mathfrak g:Kx=0\}$。

这里 $A\ne0$ 是*有效矩阵作用非零*。不能用作用为零的抽象控制中心制造非零见证。闭包中的 $A$ 也不自动是原菜单已经精确供应的连续器件：稠密可数旋转子群的闭包可以是 $SO(3)$，自身却没有非平凡连续路径。

原 $x\in W$ 是完整预测差的实线性内容，不要求每个差都是实际准备。因此候选必须覆盖完整 $W$，不能只覆盖来源轨道或可视化方向。C117 的

$$
p(\pm\mid n,m)=\frac{1\pm(m\cdot n)^3}{2}
$$

正好说明三维方向标签不保证三维完整预测空间。 [2](#ref-c117)

<a id="section-3"></a>

## 3. 唯一候选：一处关系的全方向一阶互补偿

### 定义 3.1（完整线性化零关系）

对 $A\ne0$、$x\ne0$、$Ax=0$，定义

$$
\boxed{\mathcal T_{A,x}
=\{([K],[y])\in(\mathfrak g/\mathbb R A)\times(W/\mathbb R x):Kx+Ay=0\}.}
\tag{Q8.0}
$$

用 $K+sA$ 或 $y+tx$ 替换代表元都不改变等式，所以定义良定。

它来自同一二元关系的展开：

$$
(A+\varepsilon K)(x+\varepsilon y)
=\varepsilon(Kx+Ay)+\varepsilon^2Ky.
$$

此时只称“线性化零关系”，尚未把全部一阶方向当作已存在的准确曲线。后面将证明本候选下确实可以局部积分。

**候选 $\Omega Q$-008。**

$$
\boxed{
\exists A\ne0,\ x\ne0,\ Ax=0:\quad
\pi_{\mathfrak g}:\mathcal T_{A,x}\to\mathfrak g/\mathbb R A,\quad
\pi_W:\mathcal T_{A,x}\to W/\mathbb R x
\text{ 均为双射}.}
\tag{Q8}
$$

也就是：在这一原停住对上，任意一边的横向微变，另一边都能且只能补偿一次。

$\mathcal T_{A,x}$ 是线性子空间，所以两侧双射自动把它变成一个线性同构的图；没有另输入一张线性对应表。必须使用*全部*满足等式的对，而不是从多值关系中挑一条好看的分支。

商空间只去掉此方程必然看不见的轴向重标。它没有删除原 $x,-x$ 的区别，也没有删除 $A,-A$ 的方向、大小与时钟信息。严格说，

$$
T_{[x]}\mathbb P(W)\cong\operatorname{Hom}(\mathbb R x,W/\mathbb R x);
$$

选定代表 $x$ 后，才识别为 $W/\mathbb R x$。将 $A\mapsto aA$、$x\mapsto bx$，其中 $ab\ne0$，会把补偿映射的坐标斜率乘以 $b/a$，而互定性质不变。

### 命题 3.2（候选的有限矩阵证书）

<a id="prop-rank"></a>

设 $n=\dim W$、$m=\dim\mathfrak g$，并定义

$$
E_x:\mathfrak g\to W,\qquad E_x(K)=Kx.
$$

在紧作用背景下，给定非零停住对满足 $Q8$，当且仅当

$$
\boxed{m=n,\qquad\operatorname{rank} A=n-1,\qquad\operatorname{rank} E_x=n-1.}
\tag{Q8.1}
$$

**证明。**
若 $Ay=0$，则 $(0,[y])\in\mathcal T_{A,x}$。单值性迫使 $[y]=0$，故 $\ker A=\mathbb R x$。同理 $Kx=0$ 迫使 $K\in\mathbb R A$，故 $\ker E_x=\mathbb R A$。两个商空间同构给 $m-1=n-1$，得到所列秩。

反向，紧性给正定 $G$-不变内积 $B_0$，使每个 $K\in\mathfrak g$ 斜对称。因此 $\operatorname{im}A$ 与 $\operatorname{im}E_x$ 都包含于 $x^\perp$。所列维数迫使两个像都恰为 $x^\perp$，两个核分别为 $\mathbb R x,\mathbb R A$。于是

$$
[y]\longmapsto Ay,\qquad[K]\longmapsto-Kx
$$

分别是到同一个 $x^\perp$ 的同构；复合其中一个的逆就给所需双射图。

这个证书是在已经识别的完整原 $W,\mathfrak g$ 中有限地计算。一个基点并不意味着只看一条概率或有限抽样就已排除全部未知未来方向。

<a id="section-4"></a>

## 4. 反着推：去掉哪份关系，会出现什么

### 4.1 五维：唯一停住对仍有补偿不到的内容方向

取 $W=\operatorname{Sym}_0(3,\mathbb R)$，让 $\mathfrak g=\operatorname{ad}\mathfrak{so}(3)$ 以 $K(z)=[\Omega,z]$ 作用。令

$$
x=\operatorname{diag}(1,1,-2),\quad
\Omega_z=\begin{pmatrix}0&-1&0\\1&0&0\\0&0&0\end{pmatrix},\quad
A=[\Omega_z,\cdot].
$$

有 $\ker A=\mathbb R x$、$\mathfrak g_x=\mathbb R A$。证明只需写出一般对称无迹矩阵：与 $\Omega_z$ 交换迫使其前两维为相同标量、交叉块为零；与 $x$ 交换的斜对称矩阵则只能在前两维旋转。

因此“一个互相唯一的停住对”本身还不够。取

$$
y=\operatorname{diag}(1,-1,0),\qquad Ay=2(E_{12}+E_{21}).
$$

任意原 $Kx$ 却只含 $13,23$ 对称分量，故 $Kx+Ay=0$ 无解。内容商空间四维，转向商空间只有二维。只留下可补偿的二维内容方向，会把这个反模型伪装成通过。

### 4.2 四维：没有改变转向，却有额外内容可以溜走

取 $W=\mathbb C^2$ 的实四维空间、$\mathfrak g=\mathfrak u(2)$。令

$$
x=e_1,\quad A=\operatorname{diag}(0,i),\quad y=ie_1.
$$

则 $Ax=Ay=0$，但 $y\notin\mathbb R x$。所以 $(0,[y])\ne(0,0)$ 仍在完整关系中，双向唯一性失败。被遗漏的是同一复直线里的第二个实方向。

### 4.3 七维：不保留顺序闭合，就会误认更高维叉积

在七维范数叉积中写 $D_ab=a\times b$，令 $\mathcal D=\{D_a\}$。对 $A=D_x,K=D_k$，

$$
Kx+Ay=D_x(y-k).
$$

因 $D_x^2y=\langle x,y\rangle x-\|x\|^2y$，有 $\ker D_x=\mathbb R x$，故裸算子族的关系就是 $[y]=[k]$，完全通过一阶互定。

但 $\mathcal D$ 不是 Lie 代数。明确采用三形式

$$
\varphi=e^{123}+e^{145}+e^{167}+e^{246}
-e^{257}-e^{347}-e^{356},
$$

由 $\langle D_ab,c\rangle=\varphi(a,b,c)$ 定义叉积。直接作用于基向量可得

$$
C=[D_1,D_2]-D_3,\qquad Ce_1=Ce_2=0,\quad Ce_4=3e_7.
$$

在*同一个*基点 $x=e_1,A=D_1$，$C\notin\mathbb R A$，但 $Cx=0$。完整顺序闭包因此新增 $([C],0)\ne(0,0)$，唯一补偿立即失败。无需先分类整个七维 Lie 闭包。

### 4.4 非紧二维：一阶互定通过，三维仍不会出现

令 $W=\mathfrak{aff}(1)=\operatorname{span}(h,e)$、$[h,e]=e$，采用忠实伴随作用。取 $x=h,A=\operatorname{ad}_h$，并写商代表

$$
K=k\,\operatorname{ad}_e,\qquad y=t e.
$$

则 $Kx+Ay=(t-k)e$，关系就是 $t=k$，却只有二维。该作用非紧；它不能来自上节完整有界可逆概率前端。这个反模型准确标出紧性的工作位置。

<a id="section-5"></a>

## 5. 主定理：一个一阶点已经迫出整个三维

<a id="sec-rigidity"></a>

### 定理 5.1（单点一阶刚性）

在非平凡有限实空间 $W$ 的紧有效矩阵群 $G$ 下，$Q8$ 等价于

$$
\dim_\mathbb R W=\dim_\mathbb R\mathfrak g=3,\qquad
\mathfrak g=\mathfrak{so}(W,B_0).
$$

并且

$$
G^\circ=SO(W,B_0),\qquad G=SO(W,B_0)\text{ 或 }O(W,B_0).
$$

**证明。**
**第一步：仅在见证点恢复两个一维核。**
命题 [3.2](#prop-rank) 已给

$$
\ker A=\mathbb R x,\qquad\mathfrak g_x=\mathbb R A,\qquad m=n.
\tag{5.1}
$$

由 Haar 平均取证明用正内积 $B_0$。它暂时不作为额外原比较输入。

**第二步：这个 $A$ 的中心化子只有一维。**
若 $[A,K]=0$，则

$$
A(Kx)=K(Ax)=0,
$$

所以 $Kx\in\mathbb R x$。斜对称性又给 $B_0(Kx,x)=0$，故 $Kx=0$，继而 $K\in\mathbb R A$。即

$$
Z_\mathfrak g(A)=\mathbb R A.
\tag{5.2}
$$

此处没有假设其它生成元也具有这一性质。

**第三步：一个伴随轨道填满转向球面。**
在 $\mathfrak g$ 上定义

$$
\kappa(K,L)=-\tfrac12\operatorname{Tr}_W(KL).
$$

有效斜对称矩阵使它正定，迹循环性使它伴随不变。归一化 $A$ 后，$G^\circ$ 的伴随轨道位于 $S^{m-1}$ 中；由 (5.2)，轨道维数为 $m-1$。紧群轨道是紧嵌入子流形，且与球面同维，故既开又闭。

若 $m=1$，则 $n=1$ 而 $\mathfrak g\subseteq\mathfrak{so}(1)=0$，与 $A\ne0$ 矛盾。因此 $m>1$，球面连通，整个球面就是这个轨道。

**第四步：这张球面只能是二维。**
在轨道上定义

$$
\omega_B([K,B],[L,B])=\kappa(B,[K,L]).
\tag{5.3}
$$

若改变 $K$ 的代表元，差与 $B$ 交换，迹不变性使右侧不变。若左侧对所有 $L$ 为零，同一不变性给 $[B,K]=0$，所以切向量为零；故 $\omega$ 非退化。

为说明闭性，令 $p(g)=\operatorname{Ad}_gA$，在群上取左不变一形式
$\eta_g(v)=\kappa(A,g^{-1}v)$。在单位元，

$$
d\eta(K,L)=-\kappa(A,[K,L])=-p^*\omega(K,L).
$$

$\kappa$ 的不变性与括号协变直接给 $\omega$ 的伴随不变性，所以两侧都左不变，等式全群成立；于是 $p^*d\omega=0$。$p$ 是满射下沉，得到 $d\omega=0$。这就是共伴随轨道的 KKS 辛形式。

非退化交替形式要求 $m-1=2r$。若 $r>1$，球面上 $H^2(S^{2r};\mathbb R)=0$，故 $\omega=d\alpha$。于是 Stokes 定理给

$$
\int_{S^{2r}}\omega^r
=\int_{S^{2r}}d(\alpha\wedge\omega^{r-1})=0,
$$

而辛体积在其自身取向下积分严格为正，矛盾。因此 $r=1$，即 $m=3$。这里用到的球面上同调可由两个可缩半球的 Mayer–Vietoris 序列直接得到：当球面维数大于二时，相交赤道的 $H^1$ 为零，故 $H^2$ 为零。紧秩一的同一辛球面论证也见 Donaldson 命题 15。 [4](#ref-donaldson)

**第五步：三维传回完整内容。**
由 $m=n$，得到 $n=3$。现在 $\mathfrak g\subseteq\mathfrak{so}(W,B_0)$ 两边都是三维，必相等。群的单位连通分支因此是 $SO(3)$；完整紧群包含它并包含于 $O(3)$，只能是所列两种。

反向，在标准三维旋转作用中，任一非零 $A$ 固定一条轴 $\mathbb R x$，$\mathfrak g_x=\mathbb R A$ 且 $m=n=3$。命题 [3.2](#prop-rank) 给 $Q8$。证毕。

### 5.1 与上一轮的严格等价及简化尺度

### 推论 5.2（恢复全局互定）

在相同前端，$Q8$ 等价于上一轮的

$$
Q7:\quad
\{([A],[x]):Ax=0\}
\text{ 是 }\mathbb P(\mathfrak g)\text{ 与 }\mathbb P(W)\text{ 的双射图}.
$$

**证明。**
$Q8$ 推出三维旋转，故全局互定成立。反向，若 $Q7$ 成立，每个非零 $A$ 的核线与每个非零 $x$ 的稳定子线均唯一。它们由固定秩矩阵的非零子式光滑给出，构成互逆的射影映射。因此两侧维数相同，$m=n$；一维核给命题 [3.2](#prop-rank) 的其余条件，故任何停住对都满足 $Q8$。

简化不是“又把原条件改了名字”。$Q7$ 要求*所有基点*上的零关系互定；$Q8$ 仅要求*存在一个基点*上的全方向一阶互定，其余所有基点由原紧群与顺序闭合传播出来。两者模型类相同，不存在“等价但逻辑严格更弱”的矛盾。

### 5.2 一阶条件可以积分，且不需要另列前提

### 命题 5.3（局部准确停住图）

$Q8$ 的线性补偿关系，是一片真实光滑停住对应的导数。

**证明。**
此论证甚至可放在主定理的球面步骤之前。由 (5.1)，斜对称 $A$ 的秩为 $n-1$，故 $n$ 为奇数。邻近 $A'\in\mathfrak g$ 的斜对称秩至多 $n-1$，而基点的一个非零 $(n-1)$ 阶子式持续非零，所以附近 $\ker A'$ 始终是一条光滑核线。

同样，对邻近非零 $z$，$E_z:\mathfrak g\to z^\perp$ 的秩至多 $n-1=m-1$，基点的最大秩也持续保持，所以 $\mathfrak g_z$ 是光滑变化的一条线。缩小邻域，这两个核线映射互逆。微分 $A(t)x(t)=0$ 正好给 $Kx+Ay=0$。因此原线性化没有留下不可积分的额外方向。

积分结论不等于从一个初始点确定唯一历史。给定一边的路径才有另一边的局部轴路径；候选没有挑选实验者后来采用哪条控制路径。

<a id="section-6"></a>

## 6. 三维有限提升与内生比较尺

<a id="sec-lift"></a>

### 6.1 显式的三维有限提升

取单位 $x$，取 $A\ne0$ 固定 $x$，再取 $y\perp x$、$y\ne0$。则 $Ay\ne0$，且

$$
x\perp y,\qquad x\perp Ay,\qquad y\perp Ay.
$$

所有原内容 $z\in W$ 都有准确分解

$$
\boxed{z=B_0(z,x)x+
\frac{B_0(z,y)}{B_0(y,y)}y+
\frac{B_0(z,Ay)}{B_0(Ay,Ay)}Ay.}
$$

也就是说，内容轴、一根偏离它的箭头、这根箭头被原转向送出的方向，已容纳完整窗口。

```latex
\begin{tikzpicture}[>=Latex,scale=0.92]
\fill[pale] (-2.1,-0.65)--(1.9,-1.1)--(2.5,0.55)--(-1.5,1.0)--cycle;
\draw[accent!65] (-2.1,-0.65)--(1.9,-1.1)--(2.5,0.55)--(-1.5,1.0)--cycle;
\draw[->,very thick,ink] (0,0)--(0,2.65) node[above]{固定轴 \(x\)};
\draw[->,very thick,accent] (0,0)--(2.0,-0.65) node[right]{\(y\)};
\draw[->,very thick,warm] (0,0)--(1.25,0.78) node[above right]{\(Ay\)};
\draw[->,thick,ink] (1.3,-0.25) arc[start angle=-15,end angle=120,x radius=1.1,y radius=0.35];
\node[ink] at (-1.5,0.15){\(A\)};
\node[align=left,text width=7.1cm,anchor=west] at (3.4,1.1)
{\textbf{两个元：}\(A\) 与 \(x\)。\\
原关系 \(Ax=0\) 指定一根轴。\\[3mm]
互定与原顺序闭合迫出三维后，\\
\(x,y,Ay\) 才成为完整正交三轴。};
\end{tikzpicture}
```

**图 1。**这幅图是主定理的结论；画出三个方向不是三维性的证明。

### 定义 6.1（线性提升）

称实线性同构 $\Phi:W\to\mathfrak g$ 为停住对应的线性提升，若

$$
\ker\Phi(x)=\mathbb R x\qquad(x\ne0).
$$

### 定理 6.2（线性提升的存在与唯一性）

$Q8$ 下存在这样的 $\Phi$。若 $\Phi_0$ 为一份，则所有线性提升恰为 $c\Phi_0$，$c\in\mathbb R\setminus\{0\}$。

**证明。**
主定理后，取证明用正内积 $B_0$ 与任一非零体积形式 $\nu$。由

$$
B_0(\Phi_0(x)y,z)=\nu(x,y,z)
$$

定义 $\Phi_0(x)$。它对 $x$ 线性，在 $y,z$ 上交替，所以是斜对称算子，属于 $\mathfrak g=\mathfrak{so}(W,B_0)$。非零 $x$ 的核恰为 $\mathbb R x$，维数给出同构。

若 $\Phi$ 是另一份，则 $M=\Phi_0^{-1}\Phi$ 保持每条直线。取基 $e_i$，有 $Me_i=c_ie_i$。再看 $e_i+e_j$ 的直线，得到 $c_i=c_j$。故 $M=cI$，证毕。

### 推论 6.3（见证对固定唯一的线性标定）

给定 $Q8$ 的原见证 $(A_0,x_0)$，存在唯一线性提升 $\Phi$ 满足 $\Phi(x_0)=A_0$。

**证明。**
对任一提升 $\Phi_0$，$\Phi_0(x_0)$ 与 $A_0$ 都张成 $\mathfrak g_{x_0}$，所以唯一非零常数 $c$ 使 $c\Phi_0(x_0)=A_0$。上一条唯一性给结论。

这用原见证作标定，没有从无向停住关系里凭空读出绝对手性或时钟。换原见证可以改变标定；下面的归一比较不受影响。

**准确的“地址即内容”。**

候选首先使一根内容轴唯一指定一根转向轴；定理进一步说明这种地址有一个相容的线性实现。它不是说任意选取的转速函数都会线性。例如
$\widetilde\Phi(x)=(1+\|x\|^2)\Phi_0(x)$
保留全部轴，却不保持加法。也没有把无限原历史与三维局部窗口直接等同。

### 定理 6.4（由原迹恢复唯一归一比较）

对任一线性提升，定义

$$
\boxed{B(x,y)=\frac{\kappa(\Phi(x),\Phi(y))}{\kappa(\Phi(e),\Phi(e))},
\qquad\kappa(A,K)=-\tfrac12\operatorname{Tr}_W(AK).}
\tag{6.1}
$$

则它与提升选择无关，是 $G$-不变正内积，且 $B(e,e)=1$。这也是唯一具有该归一条件的 $G$-不变正内积。

**证明。**
换提升只同时乘以 $c^2$，比值不变。正定性来自 $\kappa$ 与 $\Phi$ 的单射性。主定理下，三维所有 $SO(3)$-不变正内积相差正倍数：一份内积相对于另一份的正自伴算子与全部旋转交换，必须为标量。构造式是一份这样的内积；归一固定倍数。

为直接核对全部 $G$，在 $B_0$ 下写 $\Phi=cR$，其中 $R_xy=x\times y$。对 $g\in O(W,B_0)$，有
$gR_xg^{-1}=\det(g)R_{gx}$。迹配对的两个负号抵消，故 (6.1) 在反射下也不变。

这份比较的每个数来自同一原来源、同一原线性作用与其迹。若另定义旧轨道协方差

$$
\mathcal K\alpha=\int_G\alpha(ge)ge\,dg,
$$

则原轨道循环性使 $\mathcal K$ 正定可逆，且
$B(x,y)=\tfrac13(\mathcal K^{-1}x)(y)$。这是同一比较的等价表达；它不必作为本轮的额外前提。

### 6.2 归一后只剩两种手性

令 $s=\sqrt{\kappa(\Phi(e),\Phi(e))}$，$R_x=\Phi(x)/s$。则

$$
\kappa(R_x,R_y)=B(x,y),\qquad R_xx=0.
$$

相对于 $B$，它恰为两种单位叉积中的一种。因而

$$
\begin{aligned}
R_xR_yz&=B(x,z)y-B(x,y)z,\\
[R_x,R_y]&=R_{R_xy},\\
B(R_xy,R_xy)&=B(x,x)B(y,y)-B(x,y)^2.
\end{aligned}
\tag{6.2}
$$

三重积式可以在一个正向正交基上直接验证；其余两式由它得到。内容自身以 $\{x,y\}=R_xy$ 成为与原 $\mathfrak g$ 同构的紧 Lie 代数，Jacobi 不必另列为新公理。

### 命题 6.5（反射障碍）

对完整 $G\subset O(W,B)$，

$$
\operatorname{Ad}_gR_x=\det(g)R_{gx}.
$$

所以轴对应对全部 $G$ 协变，有向线性提升对 $G^\circ=SO(3)$ 协变。若 $G=O(3)$，不存在非零的、对全部 $G$ 无扭曲协变的线性 $W\to\mathfrak g$。

**证明。**
叉积的体积定义给公式。若存在后一种提升，对 $g=-I$ 有 $\operatorname{Ad}_g=I$，但线性性给 $\Phi(-x)=-\Phi(x)$，二者矛盾。

坐标无关的关系是 $\mathfrak{so}(W,B)\cong\Lambda^2W\cong W\otimes\operatorname{or}(W)$。选一个取向只是把一维取向因子平凡化。原生成元若为 $A=\lambda R_n$，停住关系看不见 $\lambda$ 的大小和符号。日志接续的先后序也不会自动挑选空间取向：对全部内容和控制作镜像运输，日志的前缀顺序可保持不变。把两种手性关联起来需要额外的原耦合关系。

<a id="section-7"></a>

## 7. 更大的结构：比较、转向与 Lorentz 锥

<a id="sec-lorentz"></a>

在 $E=\mathbb R1\oplus W$ 上定义

$$
(a,x)\circ(b,y)=(ab+B(x,y),ay+bx).
$$

单位为 $(1,0)$。谱投影 $(1,\pm x/\|x\|)/2$ 的谱值为 $a\pm\|x\|$，故正锥为

$$
C=\{(a,x):a\ge\|x\|\}.
$$

为直接验证 Jordan 恒等式，记乘法算子为 $L_{(a,x)}=aI+L_x$；而
$(a,x)^2=(a^2+B(x,x),2ax)$，所以
$L_{(a,x)^2}=(a^2+B(x,x))I+2aL_x$，与 $L_{(a,x)}$ 交换。这是由球及归一单位给出的自旋因子。

对 $x\in W$，记

$$
L_x(t,z)=(B(x,z),tx),\qquad
\mathcal R_x(t,z)=(0,R_xz).
$$

### 定理 7.1（关系的关系给六维比较代数）

这六个独立方向满足

$$
\begin{aligned}
[\mathcal R_x,\mathcal R_y]&=\mathcal R_{R_xy},\\
[\mathcal R_x,L_y]&=L_{R_xy},\\
[L_x,L_y]&=-\mathcal R_{R_xy}.
\end{aligned}
\tag{7.1}
$$

其 Lie 代数为 $\mathfrak{so}(1,3)$。定义

$$
J\mathcal R_x=L_x,\qquad JL_x=-\mathcal R_x,
$$

则 $J^2=-I$，且
$J[X,Y]=[JX,Y]=[X,JY]$。

**证明。**
前两式由 (6.2) 与 $B$-斜对称性得到。第三式作用于 $(t,z)$ 的向量部分为
$B(y,z)x-B(x,z)y=-R_{R_xy}z$。六个算子保持
$t^2-B(z,z)$，并线性独立，因此张成六维 $\mathfrak{so}(1,3)$。对三类括号代入 $J$ 定义即可核对所有恒等式。

### 定理 7.2（复数就是相容作用于全部括号的标量）

令 $\mathfrak h=\operatorname{span}\{\mathcal R_x,L_x:x\in W\}$，定义它的实重心代数为

$$
\operatorname{Cent}(\mathfrak h)
=\{T\in\operatorname{End}_\mathbb R\mathfrak h:T[X,Y]=[TX,Y]=[X,TY]\}.
$$

则

$$
\boxed{\operatorname{Cent}(\mathfrak h)=\{aI+bJ:a,b\in\mathbb R\}\cong\mathbb C.}
\tag{7.2}
$$

**证明。**
任何这样的 $T$ 与全部旋转的伴随作用交换。在
$\mathfrak h=\mathcal R(W)\oplus L(W)$ 的两个标准三维旋转模上，所有交换映射都是标量块，所以

$$
T\mathcal R_x=a\mathcal R_x+bL_x,\qquad
TL_x=c\mathcal R_x+dL_x.
$$

将 $[T\mathcal R_x,L_y]=T[\mathcal R_x,L_y]$ 代入 (7.1)，得到 $c=-b$、$d=a$。反向由 $J$ 的括号相容性直接成立。$J^2=-I$ 使这个二维实结合代数恰为复数。

于是复数可先在“保持所有关系的关系”的变换中被识别：比较与转向可以互换，互换两次得到负号。这是六维比较代数的复标量，不是对原三维内容强行安放一个复结构。后面的 Clifford 中心与振幅仍有独立的表示步骤。

归一截面是三维球；保正行列式的锥内截面是双曲三空间。这里 $t$ 是响应质量或未归一总量，并未被证明是物理时间。$L_x$ 给数学 boost 方向，不自动供应原滤片或精确控制。

| 几何对象 | 含义 | 不应混同的对象 |
|---|---|---|
| $\mathbb P(W)\cong\mathbb R P^2$ | 停住关系中的无向内容轴 | 完整纯态 |
| $S^2$ | 完成中的有向单位内容 | $x$ 与 $-x$ 不同 |
| $J_n=R_n\vert _{n^\perp}$ | 横向二维平面的复结构 | 完整三维空间的复结构 |
| $J$ 于 $\mathfrak{so}(1,3)$ | 比较 Lie 代数的六维复结构 | 物理时间、中心复数 |
| $\mathbb C^2$ 与 $\mathbb C P^1$ | 后续最小振幅与其复射线 | $\mathbb R P^2$ 轴商 |

<a id="section-8"></a>

## 8. 复数、复二维振幅与原 Born 概率

<a id="sec-born"></a>

### 8.1 复数作为最小结合完成的中心

定义 $(W,B)$ 的最小实含幺结合代数

$$
\mathcal A=\operatorname{Cl}(W,B),\qquad
xy+yx=2B(x,y)1,\qquad x^*=x.
$$

这是明确的普遍构造，不把复数输入为基础数域。选与 $R$ 相容的正交基 $e_1,e_2,e_3$，置 $\iota=e_1e_2e_3$。生成关系给

$$
\iota^2=-1,\quad\iota^*=-\iota,\quad
\iota x=x\iota,\quad xy=B(x,y)1+\iota R_xy.
$$

任意词约成八个实基词。把 $e_j$ 映到三个 Pauli 矩阵

$$
\sigma_1=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
\sigma_2=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad
\sigma_3=\begin{pmatrix}1&0\\0&-1\end{pmatrix}
$$

给八个实线性独立像，所以

$$
\boxed{\mathcal A\cong\operatorname{Cl}_{3,0}\cong M_2(\mathbb C).}
$$

取 $p_+=(1+e_3)/2$，则

$$
\mathcal H=\mathcal A p_+=\mathbb C p_+\oplus\mathbb C e_1p_+\cong\mathbb C^2.
$$

由 $\xi^*\eta=\langle\xi,\eta\rangle p_+$ 定义正 Hermitian 内积，范数平方为 $|z_1|^2+|z_2|^2$。

这里 $\iota$、$J_n$ 和比较代数上的 $J$ 是不同类型的对象。最小结合完成给出一份标准量子表示；它没有证明原装置已经实现每个完成元素。

**两种复数结构在同一表示中的对齐。**

比较代数 $\mathfrak h$ 与 $\mathfrak{sl}_2(\mathbb C)$ 的实 Lie 同构为

$$
\mathcal R_x\longmapsto-\frac{i}{2}x\cdot\sigma,\qquad
L_x\longmapsto\frac12x\cdot\sigma.
$$

Pauli 乘法核对三类括号，六维维数给同构。在这份表示中，$J$ 正好成为乘以中心 $i$。所以“比较与转向互换所得的复数”和最小结合完成的中心复数，可以在同一表示中准确对齐；这不是给原三维 $W$ 另安一份复结构。

### 8.2 原概率的数值保持

原准备轨道的闭包为 $c+S^2$，最小闭凸完成为 $c+\overline B^3$。任一原事件评价唯一写成

$$
f(tc+w)=\alpha t+B(b,w).
$$

原轨道上的 $0\le f\le1$ 给
$\|b\|\le\min(\alpha,1-\alpha)$。于是定义

$$
\rho_w=\frac{I+w\cdot\sigma}{2},\qquad
E_f=\alpha I+b\cdot\sigma,
$$

便有 $\rho_w\ge0$、$\operatorname{Tr}\rho_w=1$、$0\le E_f\le I$，且

$$
\boxed{f(c+w)=\operatorname{Tr}(\rho_wE_f).}
\tag{8.1}
$$

Pauli 迹恒等式直接证明等式。完整原测试的归一性给 $\sum_jE_{f,j}=I$，全部原标签与失败均保留。

对单位方向 $n,m$，数学锐效果 $P_m=(I+m\cdot\sigma)/2$ 满足

$$
\operatorname{Tr}(P_nP_m)=\frac{1+B(n,m)}2
=\cos^2\frac\theta2
=|\langle\psi_n,\psi_m\rangle|^2.
$$

因此平方律不是由“任何数都可平方”推出，而是完整原仿射评价、三维球与最小复振幅表示的同一配对。

相位几何是

$$
S^1\longrightarrow S^3\longrightarrow S^2\cong\mathbb C P^1,
$$

映射为

$$
(z_1,z_2)\mapsto
(2\Re(\bar z_1z_2),2\Im(\bar z_1z_2),|z_1|^2-|z_2|^2).
$$

整体相位改变振幅代表而保持内容；Bloch 对跖 $n,-n$ 对应不同且正交的纯态。

**哪些是实际已有的。**

(8.1) 对原事件逐项保真，但所有数学锐效果未必都在原菜单。例如仅有 $(I\pm\eta n\cdot\sigma)/2$、$0<\eta<1$，仍能分离全部方向而没有锐效果。闭凸完成也不自动供应实际随机混合准备。这些供应问题在下节的原过程接口中处理。

<a id="section-9"></a>

## 9. 本轮新增几何：从一阶补偿到平行搬运

<a id="sec-transport"></a>

### 9.1 补偿的正常形、尺度和准确曲线

现在采用已证明的归一 $B,R$。令 $B(n,n)=1$，并写

$$
A=\lambda R_n,\quad \lambda\ne0,\qquad K=R_b.
$$

那么

$$
K n+A y=R_n(\lambda y-b).
$$

所以在横向商空间上，

$$
\boxed{[y]=\frac1\lambda[b],\qquad
y=\frac{A K n}{\lambda^2}\quad(B(y,n)=0).}
\tag{9.1}
$$

后一式来自 $A^2=-\lambda^2 I$ 于 $n^\perp$。若 $K$ 选为 $\kappa$-正交于 $A$ 的代表，则

$$
\|y\|_B=\frac{\|K\|_\kappa}{|\lambda|}.
$$

因此候选保证补偿存在唯一，不计算原转速。靠近 $\lambda=0$ 时逆补偿会变得不稳定；非零条件具有真实作用。

写 $\beta=B(b,n)$、$v=b-\beta n$。对实际代数中的直线 $A(t)=A+tK$，准确的归一停住轴为

$$
n(t)=\frac{n+(t/\lambda)b}{\|n+(t/\lambda)b\|_B}.
$$

它满足 $A(t)n(t)=0$、$\dot n(0)=v/\lambda$。直接二阶展开得到

$$
\ddot n(0)=-\frac{2\beta}{\lambda^2}v-\frac{\|v\|^2}{\lambda^2}n.
$$

特别地，对横向 $v\perp n$，可以选择

$$
n(t)=\frac{n+tv}{\sqrt{1+t^2\|v\|^2}}
=\cos\theta(t)n+\sin\theta(t)\frac v{\|v\|},
\quad \theta(t)=\arctan(t\|v\|).
$$

这是一段重新参数化的大圆。它给准确积分实例，不意味着任意原历史都必须走大圆。

### 命题 9.1（二阶补偿）

设 $A(t)=A+tK+\frac12t^2N+O(t^3)$，
$n(t)=n+ty+\frac12t^2z+O(t^3)$，且 $\|n(t)\|=1$。一阶成立后，二阶条件为

$$
Az+2Ky+Nn=0,\qquad B(n,z)=-\|y\|^2.
$$

其唯一归一补偿为

$$
z=\frac{A(2Ky+Nn)}{\lambda^2}-\|y\|^2n.
$$

**证明。**
逐阶展开乘积与范数平方即可得到条件。由 $Kn=-Ay$ 与斜对称性，

$$
B(n,Ky)=-B(Kn,y)=B(Ay,y)=0;
$$

也有 $B(n,Nn)=0$。所以右端横向部分可用 $A|_{n^\perp}$ 的逆唯一解出，纵向部分由归一化固定。

### 9.2 停住生成元与搬运生成元不是同一对象

### 定理 9.2（内在的最小平行搬运）

给定光滑非零停住生成元 $A(t)$ 和一条归一的光滑核向量 $n(t)$，

$$
\boxed{M_{\mathrm{hor}}
=\frac{[A,\dot A]}{\kappa(A,A)}
=R_{n\times\dot n}}
\tag{9.2}
$$

满足 $M_{\mathrm{hor}}n=\dot n$。所有满足 $Mn=\dot n$ 的 $M\in\mathfrak g$ 恰为

$$
\boxed{M=R_{n\times\dot n}+\alpha(t)R_n.}
\tag{9.3}
$$

其中 $M_{\mathrm{hor}}$ 唯一正交于 $\mathfrak g_n$，也唯一最小化 $\kappa(M,M)$。将 $A(t)$ 换成任意光滑非零 $c(t)A(t)$，式 (9.2) 不变。

**证明。**
写 $A=\lambda R_n$，则

$$
\dot A=\dot\lambda R_n+\lambda R_{\dot n},\qquad
[A,\dot A]=\lambda^2R_{n\times\dot n},\qquad
\kappa(A,A)=\lambda^2.
$$

三重积给 $(n\times\dot n)\times n=\dot n$。两份搬运之差固定 $n$，所以必在 $\mathfrak g_n=\mathbb R R_n$。两项正交，且

$$
\kappa(M,M)=\|\dot n\|^2+\alpha^2,
$$

得到最小性。重标后，交换子中的 $c\dot c[A,A]$ 为零，分子分母同乘 $c^2$，所以比值不变。

这里 $A(t)n(t)=0$，而 $M(t)n(t)=\dot n(t)$。把这两个生成元混为一谈，就会把“内容正在改变”和“它被当前转向停住”写成矛盾。候选中的 $K=\dot A$ 也不是 $M$：它们的横向部分经

$$
M_{\mathrm{hor}}=\frac{[A,K]}{\lambda^2}
$$

联系。这个交换子正是一条“关系的关系”。

### 9.3 振幅平行搬运、曲率与路径记忆

在已经构造的复二维振幅中，令 $P=(I+n\cdot\sigma)/2$。对应的水平 Hamiltonian 为

$$
\boxed{H_{\mathrm{hor}}=i\hbar[\dot P,P]
=\frac\hbar2(n\times\dot n)\cdot\sigma.}
\tag{9.4}
$$

Pauli 乘法直接给这个等式。更一般地，

$$
H=h_0 I+\frac\hbar2(n\times\dot n+\alpha n)\cdot\sigma
$$

仍给同一条 Bloch 内容路径，因为
$\dot P=-i[H,P]/\hbar$。对满足 $P=\psi\psi^\dagger$ 及 $i\hbar\dot\psi=H\psi$ 的归一振幅 $\psi$，

$$
\psi^\dagger\dot\psi
=-i\left(\frac{h_0}{\hbar}+\frac\alpha2\right).
$$

因此水平条件是 $h_0/\hbar+\alpha/2=0$；取无迹代表 $h_0=0$ 时，等价于 $\alpha=0$。这里 $\alpha R_n$ 是原 $\mathfrak g$ 中的稳定子方向，$h_0I$ 则是复完成中的标量中心自由度。原内容轨迹不决定它们的数值，也不能据此将它们删除。

### 定理 9.3（球面曲率给半立体角相位）

在纯态完成 $S^1\to S^3\to S^2$ 上，局部归一振幅取

$$
\psi(\theta,\phi)=
\begin{pmatrix}\cos(\theta/2)\\ e^{i\phi}\sin(\theta/2)\end{pmatrix}.
$$

其连接与曲率为

$$
a=i\psi^\dagger d\psi=-\tfrac12(1-\cos\theta)d\phi,\qquad
F=da=-\tfrac12\sin\theta\,d\theta\wedge d\phi.
$$

沿闭合内容路径的水平振幅相位为

$$
\boxed{\gamma_{\mathrm{geom}}
=-\frac{\Omega_{\mathrm{solid}}}{2}\pmod{2\pi}.}
\tag{9.5}
$$

整个球面不存在一份连续光滑、处处定义的归一振幅代表。

**证明。**
对显示的 $\psi$ 直接微分即得 $a,F$。若水平提升为 $\Psi=e^{i\chi}\psi$，则

$$
0=\Psi^\dagger d\Psi=i\,d\chi+\psi^\dagger d\psi,
$$

所以 $d\chi=a$。对局部闭合路径用 Stokes 定理，
$\gamma=\oint a=\int F=-\Omega_{\mathrm{solid}}/2$。
跨图时加上相位过渡函数，结果仍模 $2\pi$ 良定；两份跨面相差整球面，$\int_{S^2}F=-2\pi$，不会改变相位。

若存在全局光滑振幅截面，其 $a$ 就是全局一形式，Stokes 定理将给 $\int_{S^2} da=0$，与 $-2\pi$ 矛盾。

这得到标准 Hopf 几何相位；Berry 的原论文研究了相应绝热量子相位。 [6](#ref-berry) 本文的等式由已构造的连接直接推出，不依赖绝热近似。把它实现为原干涉读数，还需要原相干参考与实际控制路径；这些供应条件不是 $Q8$ 单独保证的。

```latex
\begin{tikzpicture}[>=Latex,scale=.84]
\fill[pale] (0,0) circle(2.25);
\draw[ink!40] (0,0) circle(2.25);
\draw[dashed,ink!35] (0,0)--(0,1.837);
\draw[dashed,ink!35] (0,0)--(-1.591,-.919);
\draw[dashed,ink!35] (0,0)--(1.591,-.919);
\draw[very thick,->,accent,domain=0:90,samples=45,variable=\t]
 plot({-2.25*sin(\t)/sqrt(2)},{2.25*(-sin(\t)/sqrt(6)+sqrt(2/3)*cos(\t))});
\draw[very thick,->,warm,domain=0:90,samples=45,variable=\t]
 plot({2.25*(-cos(\t)+sin(\t))/sqrt(2)},{-2.25*(cos(\t)+sin(\t))/sqrt(6)});
\draw[very thick,->,ink,domain=0:90,samples=45,variable=\t]
 plot({2.25*cos(\t)/sqrt(2)},{2.25*(-cos(\t)/sqrt(6)+sqrt(2/3)*sin(\t))});
\node[above] at (0,1.86){\(e_3\)};
\node[left] at (-1.62,-.93){\(e_1\)};
\node[right] at (1.62,-.93){\(e_2\)};
\node at (0,.12){\(\Omega_{\mathrm{solid}}=\pi/2\)};
\node[anchor=west,align=left,text width=8cm] at (3.25,.5)
{\textbf{内容走完闭环，回到同一点。}\\[2mm]
三个大圆四分之一弧围住一个球面八分区。\\[2mm]
水平振幅却得到 \(e^{-i\pi/4}\)。\\[2mm]
局部补偿唯一，不等于只看终点就知道全部路径信息。};
\end{tikzpicture}
```

**图 2。**单位球的正交投影。闭环为 $e_3\to e_1\to e_2\to e_3$，有向立体角为 $\pi/2$。

该例也可完全代数核对。令

$$
U_1=e^{-i\pi\sigma_y/4},\quad
U_2=e^{-i\pi\sigma_z/4},\quad
U_3=e^{-i\pi\sigma_x/4}.
$$

沿各弧它们均为水平搬运，并且

$$
U_3U_2U_1=e^{-i\pi\sigma_z/4},\qquad
U_3U_2U_1\lvert0\rangle =e^{-i\pi/4}\lvert0\rangle .
$$

整个酉矩阵不是全局标量；显示的是所选纯态射线的相位。对一般 $h_0,\alpha$，闭路总相位还包含

$$
-\int\left(\frac{h_0}{\hbar}+\frac\alpha2\right)dt.
$$

因此几何相位、稳定子相位与中心相位都有明确的位置。

### 推论 9.4（球面长度、振幅距离与能量方差）

采用

$$
ds_{\mathrm{FS}}^2
=\langle d\psi,d\psi\rangle-|\langle\psi,d\psi\rangle|^2
$$

的 Fubini–Study 约定，则

$$
ds_{\mathrm{FS}}^2=\tfrac14\|dn\|_B^2,\qquad
(\Delta H)^2=\tfrac{\hbar^2}{4}\|\dot n\|_B^2.
$$

**证明。**
对上面的振幅坐标求导，得到
$ds_{\mathrm{FS}}^2=\frac14(d\theta^2+\sin^2\theta\,d\phi^2)$。
写 $H=h_0I+\frac\hbar2 b\cdot\sigma$，Pauli 恒等式给

$$
(\Delta H)^2=\frac{\hbar^2}{4}
\bigl(\|b\|^2-B(b,n)^2\bigr).
$$

代入 $b=n\times\dot n+\alpha n$ 即得。它是既定 Hamiltonian 的矩阵恒等式，不计算实际能标或 $\hbar$ 的数值。

<a id="section-10"></a>

## 10. 完整有限量子理论：定义、定理与接口

<a id="sec-quantum"></a>

本节把基本块发展为完整的有限数学理论，并列出它与原整体实际对象对应所需的关系。$Q8$ 只选择基本窗口，不重复施加于全部复合内容。

### 10.1 复合与任意有限维系统

### 定理 10.1（复张量的唯一性）

若 $M_m(\mathbb C)$、$M_n(\mathbb C)$ 以同一复中心含幺 $*$-嵌入联合代数，两个像交换，且乘积复线性张成联合代数，则联合代数同构于 $M_{mn}(\mathbb C)$。

**证明。**
$a\otimes b\mapsto\iota_A(a)\iota_B(b)$ 为满射含幺 $*$-同态。源 $M_m\otimes_\mathbb C M_n\cong M_{mn}$ 单，核为零或全体；含幺排除全体，故为同构。

量子位张量幂给 $M_{2^N}$，秩 $d\le2^N$ 的数学投影角给 $M_d$，再取有限直和，得到

$$
\mathcal A=\bigoplus_sM_{d_s}(\mathbb C).
$$

这给全部有限复矩阵代数的数学完成；实际支持角、实际复合与共用复中心仍须原接口供应。完整 C127 的某些满足族只有 $3^k$ 大小的块，并无实际 $M_2$ 对象；本文不能把数学角冒充原对象。 [3](#ref-c127)

### 10.2 状态、效果与观测量

### 定理 10.2（密度与迹配对）

标准正锥上的归一正线性泛函恰为

$$
\omega(a)=\sum_s\operatorname{Tr}(\rho_sa_s),\qquad
\rho_s\ge0,\quad\sum_s\operatorname{Tr}\rho_s=1.
$$

效果是 $0\le E\le I$，完整 POVM 满足 $\sum_kE_k=I$。自伴量 $H=\sum_kh_kP_k$ 的谱概率与均值分别为 $\operatorname{Tr}(\rho P_k)$、$\operatorname{Tr}(\rho H)$。

**证明。**
非退化迹配对给唯一自伴 $\rho_s$。在全部秩一正投影上非负等价于 $\rho_s\ge0$，单位评价给总迹一。反向直接成立。自伴谱分解给观测量结论。

### 10.3 完整参考推出 CP 与一般仪器

### 定理 10.3（参考保正与 Kraus 表示）

设同一原分支在自伴部分实线性，作唯一复线性延拓 $\mathcal E:M_d\to M_n$。若有实际完整矩阵参考 $M_r$、$r\ge d$，使 $\mathcal E\otimes\operatorname{id}_r$ 在完整联合标准正锥上保正，则

$$
\mathcal E(\rho)=\sum_\mu K_\mu\rho K_\mu^*.
$$

在全部归一态上迹不增，等价于 $\sum_\mu K_\mu^*K_\mu\le I$。完整仪器归一，等价于

$$
\sum_{k,\mu}K_{k\mu}^*K_{k\mu}=I.
$$

**证明。**
在参考中取 $d$ 维子空间，并取 $\lvert\Gamma\rangle =\sum_i\lverti\rangle \otimes\lverti\rangle$。联合保正使 Choi 矩阵
$C_{\mathcal E}=(\mathcal E\otimes\operatorname{id})(\lvert\Gamma\rangle \langle\Gamma\rvert )$
为正。将其谱分解向量重排为矩阵 $K_\mu$，比较矩阵单位即得表示。反向的共轭和在任意参考上保正。迹配对给所列不等式与等式。

这是标准有限维 Choi–Kraus 等价关系，参见 Watrous 定理 2.22。原参考条件必须覆盖全部联合正锥，单有经典参考、乘积态或线性分离不足。原标签 $k$ 与数学 Kraus 索引 $\mu$ 也不能自动合并为可访问的细记录。 [7](#ref-watrous)

### 推论 10.4（排除反射作为可附接的量子过程）

如果原反射也满足完整量子参考条件，就产生矛盾。

**证明。**
Bloch 的一个反射由转置代表。对 Bell 态的一半转置得到 $\tfrac12\operatorname{Swap}$，有特征值 $-1/2$。任意其它反射只相差旋转，结论不变。

这排除某类实际可附接过程，不选择一种绝对坐标手性。若原菜单真的有反射，则该原实例不满足后续完整参考接口，不能通过删去原门声称已经重建。

### 命题 10.5（仪器的有限酉扩张）

任一完整 Kraus 仪器都有一个数学等距扩张

$$
V\psi=\sum_{k,\mu}K_{k\mu}\psi\otimes\lvertk,\mu\rangle ,
\qquad V^*V=I.
$$

在环境读出投影 $Q_k=\sum_\mu\lvertk,\mu\rangle \langlek,\mu\rvert$ 后取偏迹，得到原分支
$\mathcal E_k(\rho)=\sum_\mu K_{k\mu}\rho K_{k\mu}^*$。

**证明。**
由完整性，
$V^*V=\sum_{k,\mu}K_{k\mu}^*K_{k\mu}=I$。
展开 $V\rho V^*$，投影 $Q_k$ 并对环境取迹即得分支。将输入、输出嵌入足够大的同维空间，补齐正交基，可将该等距映射延拓为一个酉算子。反向，任何这种酉扩张和环境读出都给 Kraus 仪器。

任一数学 POVM 也有实现：取 $K_k=\sqrt{E_k}$，便有 $\sum K_k^*K_k=I$。实际原设备是否供应该环境、耦合与读出，是同一原过程接口的实现问题。数学环境索引 $\mu$ 不因此成为实际可读标签。

### 10.4 Lüders 更新的准确前提

### 定理 10.6（理想投影更新）

CP 分支的效果为投影 $P$，并且不扰动每个支撑于 $P$ 的态，则

$$
\mathcal E(\rho)=P\rho P.
$$

**证明。**
$\sum_\mu K_\mu^*K_\mu=P$ 给 $K_\mu=K_\mu P$。对 $\psi\in P\mathcal H$，秩一正和
$\sum_\mu\lvertK_\mu\psi\rangle \langleK_\mu\psi\rvert =\lvert\psi\rangle \langle\psi\rvert$
迫使每项的向量与 $\psi$ 共线。对独立向量及其和用线性，得到 $K_\mu=c_\mu P$、$\sum_\mu|c_\mu|^2=1$。零投影和秩一情形直接包含。

成功概率非零时，条件态为 $P\rho P/\operatorname{Tr}(\rho P)$。只可重复、或仅保持某组基态，不足以推出此定理：支撑内退相干提供反例。

### 10.5 连续可逆过程与 Schrödinger 形式

### 定理 10.7（连续幺正演化）

同一简单块上的连续 CPTP 单参数群，若逆也 CP，则存在自伴 $H$，使

$$
\mathcal E_t(\rho)=U_t\rho U_t^*,\quad
U_t=e^{-itH/\hbar},\quad
i\hbar\dot\psi=H\psi.
$$

相应密度方程为 $\dot\rho=-i[H,\rho]/\hbar$。

**证明。**
令 $F$ 为 Heisenberg 对偶，$S=F^{-1}$。两者都保单位且 CP，故

$$
F(a)^*F(a)\le F(a^*a),\qquad
a^*a\le S(F(a)^*F(a)).
$$

把第一式施加 $S$，与第二式合并，迫使两式取等。$S$ 单射，故
$F(a)^*F(a)=F(a^*a)$。对 $a+b$ 与 $a+ib$ 极化，得到
$F(a)^*F(b)=F(a^*b)$，所以 $F$ 为 $*$-自同构。

有限维连续单参数矩阵群可写成指数，生成元 $\delta$ 是保持 $*$ 的导子。它必为内导子：对矩阵单位，置

$$
B=\sum_i\delta(E_{i1})E_{1i}.
$$

微分恒等式 $E_{kl}E_{i1}=\delta_{li}E_{k1}$，右乘 $E_{1i}$ 并求和，得到
$[B,E_{kl}]=\delta(E_{kl})$。故 $\delta(a)=[B,a]$。
保持 $*$ 又给 $[B+B^*,a]=0$，所以减去一个中心标量后可取 $B^*=-B$。写 $B=iH/\hbar$，即得 Heisenberg 指数式及其 Schrödinger 对偶。直和的有限中心不能被连续群非平凡置换，逐块论证。

该结论给定连续参数后的结构形式，不计算实际时钟、原生成元的速度、具体 $H$ 或 $\hbar$。

### 10.6 两个可检验的理论后果

完整局部 CPTP 操作并遗忘全部结果时，

$$
\operatorname{Tr}_B[(\operatorname{id}\otimes\mathcal E_B)(\rho_{AB})]=\operatorname{Tr}_B\rho_{AB},
$$

由 $\sum K_\mu^*K_\mu=I$ 直接推出无信号性。后选择不属于该命题。

正半内积 $\langle X,Y\rangle_\rho=\operatorname{Tr}(\rho X^*Y)$ 的 Cauchy–Schwarz 不等式给

$$
\operatorname{Var}_\rho(H)\operatorname{Var}_\rho(K)
\ge\left|\frac1{2i}\operatorname{Tr}(\rho[H,K])\right|^2.
$$

不确定性来自同一正比较与非交换乘法，不需要另立一条概率公理。

### 10.7 复合的实质后果：纠缠与 Bell 相关

在两个基本块的标准联合完成中，定义

$$
\lvert\Psi^-\rangle =\frac{\lvert01\rangle -\lvert10\rangle }{\sqrt2}.
$$

它的两个约化态都是 $I/2$，而联合态是秩一投影，不能是乘积态；也不能是乘积态的凸组合，因为秩一正和中的每项必须支撑在同一条射线上。

Pauli 矩阵直接给

$$
\langle\Psi^-|(a\cdot\sigma)\otimes(b\cdot\sigma)|\Psi^-\rangle=-B(a,b).
$$

取 $A_0=\sigma_z,A_1=\sigma_x$，
$B_0=(\sigma_z+\sigma_x)/\sqrt2$、
$B_1=(\sigma_z-\sigma_x)/\sqrt2$，得到

$$
\langle A_0B_0\rangle+\langle A_0B_1\rangle+
\langle A_1B_0\rangle-\langle A_1B_1\rangle=-2\sqrt2.
$$

对共同概率空间中预先给定的 $a_0,a_1,b_0,b_1\in\{\pm1\}$，相同组合
$a_0(b_0+b_1)+a_1(b_0-b_1)$ 的绝对值恒为二，平均后仍不超过二。因此标准联合完成包含超过该共同赋值模型的相关；同时上节已证明完整局部操作不发信号。

这是复合接口与联合正锥的结果，不是单个三维球或 $Q8$ 单独保证原环境中已经存在 Bell 实验。

<a id="section-11"></a>

## 11. 每条现有量子公理究竟在哪里出现

| 通常的量子表述 | 本文中的定义或证明 | 实际原对象仍需满足的条件 |
|---|---|---|
| 复 Hilbert 空间 | 三维刚性、归一比较、最小实 Clifford 完成及最小左理想给 $\mathbb C^2$ | 这是标准数学完成；原系统是否实现全部完成元素另判 |
| 纯态射线与相位 | $S^3/S^1=\mathbb C P^1=S^2$，曲率给半立体角相位 | 相位的原干涉比较须有相干参考 |
| 密度矩阵与 Born 律 | 球的闭凸完成、原完整仿射评价和迹恒等式 | 原概率逐项保持；全部混合态、锐效果不自动供应 |
| 张量积 | 同一复中心、交换嵌入及乘积张成迫出 $M_{mn}$ | 原联合对象及全联合正锥 |
| 一般测量与 CP | 足够矩阵参考上的保正给 Choi 正性与 Kraus 表示 | 必须检查全部联合正锥及全部原分支标签 |
| 投影更新 | CP、投影效果及对所有支撑态不扰动推出 $P\rho P$ | 仅重复性或保某组基态不够 |
| 薛定谔形式 | 连续 CPTP 群及 CP 逆给内导子与幺正群 | 实际连续调用、时钟、具体 $H$ 与能标 |
| 无信号与不确定性 | 完整仪器归一及非交换正比较的推论 | 保留失败与未选结果，不能以成功支路代替完整过程 |

**理论范围。**

本文给出一套封闭的*有限维*数学理论：所有有限复矩阵代数、状态、效果、联合系统、CP 仪器、理想更新、可逆连续演化及其几何。$Q8$ 识别的是最小三维量子位窗口，不是要求每个高维量子系统的全部内容空间都三维。标准 qutrit 也不必作为一个整体满足 $Q8$；C127 的实际对象族尤其不能因此被删改。

无限维 Hilbert 空间、连续位置与动量、无界算子定义域、具体时空和场论还需要拓扑极限及连续性等另行条件。有限矩阵甚至不可能严格满足 $[Q,P]=i\hbar I$，因为取迹后左侧为零而右侧非零。本轮没有将有限重建夸大为这些额外结构的证明。

<a id="section-12"></a>

## 12. “公理内生”的准确含义

所有候选对象都从同一个 $\Omega$ 的原数据定义：完整未来响应给 $W$，同一原接续给 $G,\mathfrak g$，同一作用给停住关系。再对这个关系取一次线性化，得到 $\mathcal T_{A,x}$。$Q8$ 只说这份已定义关系在一处是双向唯一的。

因此可以把“外部塞入一张内容到转向表”改成：

$$
\boxed{\text{同一个原作用定义出的两份横向变化读出，恰好互为同构。}}
$$

维数、比较尺、线性地址、叉积、复数和振幅均放到后续定理或明确的最小完成中。候选并未另造一个先验的 $D$ 让它冒名顶替原 $D$。

但必须区分三件事：一句约束的对象都在 $\Omega$ 内；某份原实例确实满足约束；整个宇宙必然选择这一约束。第一件事不证明后两件事。上面的反模型可以同样在一个整体里定义，却不满足同一关系合同。把约束改写成定义间关系，能够消除不明的外部结构输入，不能让一个有反例的性质自动变成逻辑恒真。

所以本轮已完成的是：*给出一个更局部、没有预输入维数或内容地址的候选；证明其精确模型类；从该模型类完整建立有限量子完成；把原对象实现这一完成的接口逐条列出。*

<a id="section-13"></a>

## 13. 一段白话，把本轮完整说清

在整体里找一份内容和一种转向：转向正在起作用，这份内容却恰好不动。现在让任意一边轻轻偏一点。如果另一边总能，而且只能用一种横向偏法，把这次偏移补回来，那么这一处就已经藏着整张对应表。把原有转向按先后接起来，把全部可区分的内容和记录都保留下来，这份对应便不能散成五维、七维或任意别的形状，它会展开成一根停住轴和一个能转动的平面，总共三维。三维里的比较和转向继续闭合，会出现复数和两分量振幅；同一个原概率就在这份振幅里写成平方模。再让内容沿路径移动，当前把它停住的转向怎样变化，就决定最省的搬运；内容绕一圈可以回到原处，振幅却留下这圈路径包住多少面积的相位。把这样的窗口用共同相位、完整联合正锥和完整参考连接起来，就得到有限量子理论。这里没有预先宣布空间三维，也没有先放进波函数；入口只是同一个整体内，一处原关系能否让两边的全部微小变化相互唯一补偿。

<a id="section-14"></a>

## A. 核查边界与可复用证书

本文的主定理使用线性代数、紧矩阵 Lie 群、Haar 平均、共伴随轨道的辛形式、球面上同调与 Stokes 定理。涉及这些成熟数学的步骤均已写出所需论证；没有使用未知的高维表示分类，也没有将三维来源轨道代替完整预测空间。

本轮对四维、五维反模型和七维交换子采用明确矩阵表达，对三段球面水平搬运的 Pauli 乘积作精确核对。核对只确认这些有限公式，不替代一般证明。独立证明审核确认：完整的一阶关系、有效非零算子、紧性及 Lie 闭合均不可在本稿论证中省略。

一个原实例的最小有限证书可以记录为

$$
(W,\mathfrak g,A,x;\ Ax=0,\ \dim W=\dim\mathfrak g,\
\operatorname{rank} A=\dim W-1,\ \operatorname{rank} E_x=\dim W-1),
$$

连同它确实来自完整原有界可逆窗口的证据。这比记录整张全局轴对应表简洁，但“完整原窗口”的来源证据仍不可由这组矩阵自行替代。

<a id="references"></a>

## 参考文献

<a id="ref-commit"></a>

### [1]

 trureturing，
[本轮重新读取的固定提交](https://github.com/the-omega-institute/trureturing/commit/8e15c484cf5786fe69fef0627fd84a63cfeb5942)，2026-11-04 16:25:41 +0800。相对 $\Omega Q$-007 无增量。

<a id="ref-c117"></a>

### [2]

 trureturing，
[C117 固定正文](https://github.com/the-omega-institute/trureturing/blob/8e15c484cf5786fe69fef0627fd84a63cfeb5942/docs/develop/theory/AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md)，尤其 §§17–24 与 §19 全容量反模型。

<a id="ref-c127"></a>

### [3]

 trureturing，
[C123–C127 固定正文](https://github.com/the-omega-institute/trureturing/blob/8e15c484cf5786fe69fef0627fd84a63cfeb5942/docs/develop/theory/AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md)，尤其 §§35–40。

<a id="ref-donaldson"></a>

### [4]

 S. K. Donaldson，*Lectures on Lie groups and geometry*，
[作者讲义](https://wwwf.imperial.ac.uk/~skdona/Liegroups/LIEGROUPSFINAL.PDF)，§2.2、命题 15。

<a id="ref-baez"></a>

### [5]

 J. C. Baez，*The Octonions*，Bull. Amer. Math. Soc. 39 (2002)，145–205，
[作者全文](https://math.ucr.edu/home/baez/octonions/)。七维反模型在正文另给明确三形式与交换子。

<a id="ref-berry"></a>

### [6]

 M. V. Berry，*Quantal phase factors accompanying adiabatic changes*，
Proc. R. Soc. Lond. A 392 (1984)，45–57，
[作者提供的原论文](https://michaelberryphysics.wordpress.com/wp-content/uploads/2013/07/berry120.pdf)，
[doi:10.1098/rspa.1984.0023](https://doi.org/10.1098/rspa.1984.0023)。

<a id="ref-watrous"></a>

### [7]

 J. Watrous，*The Theory of Quantum Information*，
[第 2 章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)，尤其定理 2.22，CP、Choi 与 Kraus 的有限维等价。
