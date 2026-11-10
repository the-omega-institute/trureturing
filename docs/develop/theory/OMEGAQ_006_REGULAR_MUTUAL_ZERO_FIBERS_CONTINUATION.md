# 一般位置，一轴一转

> 参考输入：AI 撰写的工作稿，由用户提供于本会话（2026-11-04，Asia/Singapore）。Lean 是仓库的数学真源；本文仅为参考文稿，未作形式化认证。

QUANTUM ORIGINS / $\Omega Q$-006

共停即共线的等价压缩、唯一复乘法与共同相位

保留同一个 $\Omega Q$-006 候选。把原二元作用写作

$$
\beta:\mathfrak g\times W\longrightarrow W,\qquad \beta(A,x)=Ax.
$$

令 $E_x(A)=Ax$，$W_{\rm reg}$ 是 $E_x$ 在完整 $W$ 中秩最大的点集。候选等价压缩为

$$
\boxed{\ \exists\,x\in W_{\rm reg}\setminus\{0\},\ A\ne0:
\quad\ker E_x=\mathbb R A,\qquad\ker A=\mathbb R x.\ }
$$

这里 $\mathfrak g$ 是同一原可逆接续作用的 Lie 代数；两个核是同一个二元作用的两个零纤维。

白话：在没有额外偶然对称的位置，一份内容只留下一种转向，这种转向也只留下一份内容；只差大小的，算同一方向。

这个陈述不含比较尺、预先指定的来源轴、共面、面积、复数或预给三维。先由最大秩处的双线性关系推出内容与转向同维，再由原动作的顺序闭合推出共同维数为三。一般位置的定义保留完整空间信息；它不是一次孤立采样。

 本会话新系列第六篇的继续稿；编号保持 $\Omega Q$-006。

日期：2026-11-04，Asia/Singapore。

固定版本：`dev@2c54932b6f9a7eb9a838e5be71e91d97e10027be`。

提交时间：2026-11-04 17:36:07，新加坡时间。

范围：普通数学证明、条件重建及原数据对应。

已只读核对项目；未修改仓库，未重新编译或认证 Lean。

简化指候选语言的压缩，不主张全球最小性或文献首创。

<a id="section-1"></a>

## 1. 本轮结论与最新项目的准确接点

在非平凡有限原预测窗口、紧且忠实的原可逆作用下，本轮候选等价于

$$
\dim_\mathbb R W=3,\qquad
\mathfrak g=\mathfrak{so}(W),\qquad G^\circ=SO(W).
$$

本继续稿把原来的全局二元条件压到一个一般位置上的两个零纤维。随后由原来源定义唯一归一正比较。任何保留自旋 Jordan 乘法、由原内容实生成的非零含幺结合实现，都被唯一确定为
$\operatorname{Cl}_{3,0}\cong M_2(\mathbb C)$；复数是其中心，而非先给的标量。再把“共同复中心”展开为局部虚单位之间的二元等式及闭环一致性，明确得到通常复张量积。在完整正锥、参考和过程接口下，继承有限量子理论的全部条件重建。

**冻结来源。**

相对 006 首稿的 `1764a0c7f33be6acf6dcaf4ad4007da021469ae9`，本次固定比较前进 23 个提交、涉及 30 条路径；完整差分为 218,622 字节、42 个 hunks。C123–C127 的 2,501 行及 C117 的 3,314 行均逐字未变；FIB 与 Fourpath 相关量子正文也未改变。本继续稿新增的双零纤维、唯一实结合实现与共同中心图定理，是本文的推导，不归因于仓库的新提交。 [1](#ref-repocompare)、[3](#ref-repo127)、[4](#ref-repo117)

本次新增理论是完整初值锥的无限 log-concavity 收缩：含零的齐次锥可沿 $x\mapsto(1-t)x$ 收到零点。这并不说明其去零、归一化或射影化后的空间可缩，也不构成本量子结构的前件。其余更新属于有限群、quandle 与阈值分布。
 [2](#ref-repog)

| 仍适用的项目背景 | 已推进的内容 | 不能由此省掉的条件 |
|---|---|---|
| C125–C127 | 从原零正配对接回原导子归属；一只指针固定原尺度；给完整中心反例 | 完整原中心、联合、正对偶、参考、协变及尺度 |
| C117 §§17–24 | 黄金四时关系导出全未来仿射性；逐原标签有符号 $L^\infty$ 误差 $\le5\varepsilon$ | 源文先给三维；有符号近似仍需共同正性 |
| FIB §§145–151 | 同一原集合精确实现 binary $B_8$；多项四标签共同匹配 | 完整 $F_{64}$ 尚未完成；不同存在见证不能拼成同一个 |
| Fourpath 新续卷 III | $0<\xi\le13/4$ 的全局最小者收紧为 pure phase | 极小参数、全部转变点及完整全域次序尚未求出 |

最直接影响本轮的是 C127 的反事实：全部单标签平方正确、原过程菜单丰富，并不保证两个标签的混合次序正确。本轮因此把转向放回完整 Lie 代数，不只检查一族孤立的漂亮算子。第 [10](#sec-project) 节给出准确对应；这些项目结果不是三维主定理的前提。

<a id="section-2"></a>

## 2. 定义：先固定同一个原预测窗口

### 定义 2.1（原全未来内容）

固定 $\Omega$ 内一个原归一准备与共同输入类型。原总可逆控制词菜单 $\mathcal L$ 含空词，封闭于接续，并供应同菜单的准确统计逆。所有原合法终端请求及完整标签，包括失败、旧记录和可用性区别，构成共同未来域。令

$$
x_a(f,w)=p(a;f,w),\qquad
p(a;f,w)\ge0,\quad \sum_w p(a;f,w)=1,
\quad p(ag;f,w)=p(a;gf,w).
$$

设

$$
V=\operatorname{span}_\mathbb R\{x_a\}
$$

有限维，维数未知。归一泛函 $u(x_a)=1$，内容差空间为

$$
W=\ker u=\operatorname{span}\{x_a-x_b\}.
$$

本轮研究非平凡窗口 $W\ne0$。

### 引理 2.2（原接续给紧忠实作用）

原接续 $T_gx_a=x_{ag}$ 良定义，其在 $GL(V)$ 中的闭包 $H$ 紧。以归一 Haar 平均定义

$$
c=\int_H hx_\epsilon\,dh,\qquad e=x_\epsilon-c,\qquad
V=\mathbb R c\oplus W.
$$

令 $G=H|_W$、$\mathfrak g=\operatorname{Lie}(G)$。则 $G$ 是紧矩阵群，作用忠实，且

$$
W=\operatorname{span}(Ge),\qquad e\ne0.
$$

**证明。**
若原行的线性组合在全部未来为零，它在以 $g$ 开头的全部未来也为零，故接续良定义。选有限实际行基及有限分离终端坐标；所有接续后的基行坐标仍在 $[0,1]$，故 $T_g$ 一致有界。统计逆使其逆也一致有界，闭包紧且不含奇异矩阵。平均 $c$ 固定，且 $u(c)=1$。固定 $c$ 且在 $W$ 上恒等的作用在 $V$ 上恒等，故限制忠实。每个 $x_a-c=T_ae$，这些差张成 $W$，得最后两式。

**类型与边界。**

$x,y\in W$ 是实线性内容差，不要求每个差都能单独作为归一准备。$A\in\mathfrak g$ 是完整原作用闭包的无穷小变化，

$$
Ax=0\quad\Longleftrightarrow\quad e^{tA}x=x\quad(t\in\mathbb R).
$$

它不等于一个有限门偶然回到起点，也不把闭包中的指数自动认作原菜单已供应的精确调用。Lie 代数的线性与交换子闭合来自同一可逆动作结构；不是候选另加一份任意旋转表。

<a id="section-3"></a>

## 3. 同一个候选：一般位置上的两个零纤维

<a id="sec-candidate"></a>

### 定义 3.1（一般位置）

令 $m=\dim\mathfrak g$、$n=\dim W$，并用同一原作用定义

$$
E_x:\mathfrak g\longrightarrow W,\quad E_x(A)=Ax,\qquad
r=\max_{y\in W}\operatorname{rank} E_y,\qquad
W_{\rm reg}=\{x:\operatorname{rank} E_x=r\}.
$$

$W_{\rm reg}$ 称为一般位置集：这里被动留下的转向数最少，因而没有额外的偶然稳定方向。

选定任意实基，$E_x$ 是关于 $x$ 线性的 $n\times m$ 矩阵。其最大非零子式不恒为零，所以 $W_{\rm reg}$ 非空、开且稠密；例外点由子式为零定义。当 $r=0$ 时它是整个 $W$。这个定义无需输入正比较、测度、“随机性”或特选来源轴。

等价地，一般位置就是作用秩在一个完整 $W$ 邻域内保持不变的位置。
最大秩点由非零子式保证局部不降；反向，若某开域上秩恒为 $r$，
所有更高阶子式在开域为零便作为多项式恒为零，所以这个 $r$ 已是全局最大。
直观上，轻微改变内容不会突然暴露更多可动方向；这里的邻域是在完整内容空间中，不仅在一个来源轨道上。

**$\Omega Q$-006 的唯一等价压缩：一般位置，一轴一转。**

$$
\boxed{\ \exists\,x\in W_{\rm reg}\setminus\{0\},\
0\ne A\in\mathfrak g:\qquad
\ker E_x=\mathbb R A,\qquad \ker A=\mathbb R x.\ }
\tag{Q6}
$$

$\ker E_x$ 与 $\ker A$ 是同一个二元关系
$\beta(A,x)=Ax=0$ 的两个纤维。它们分别说：留住这份内容的变化只有一个方向；这个变化留住的内容也只有一个方向。

非零是有效作用非零，作用恒零的抽象控制中心不能充当见证。这里的 $x,A$ 是在原结构中存在的同一对，不是外界指定的来源与动力学模板。倍数只识别方向，不识别原速度，也不把 $x$ 与 $-x$ 所代表的归一态混为同一个态。

后面的定理证明，这与 006 首稿的

$$
\exists\,0\ne A:\ Ax=Ay=0
\quad\Longleftrightarrow\quad
\mathbb R x=\mathbb R y\qquad(x,y\ne0)
\tag{共同固定形式}
$$

完全等价。本文只有一个结构候选及它的等价表达，不把这两行当作两条独立公理。

一般位置的真实性取决于完整原 $W$ 和完整原 $\mathfrak g$。写成一个存在量词，并未把全局信息变成一次孤立实验。内生的是载体、作用、一般位置与零纤维的定义；这些定义之间满足 Q6 仍是可被反模型否定的实质条件，不能仅因改称“定义”便自动成立。

<a id="section-4"></a>

## 4. 三维刚性：先同维，再由组合闭合锁成三维

<a id="sec-rigidity"></a>

### 引理 4.1（最大秩处的双线性相容）

若 $x\in W_{\rm reg}$，则对每个 $A\in\ker E_x$，

$$
A(W)\subseteq\operatorname{im}E_x.
$$

**证明。**
选 $B_1,\ldots,B_r\in\mathfrak g$，使 $B_jx$ 为 $\operatorname{im}E_x$ 的基。
对任意 $h\in W$，小 $t$ 时 $B_j(x+th)$ 仍独立；最大秩性使它们张成整个 $\operatorname{im}E_{x+th}$。
因为 $Ax=0$，

$$
tAh=A(x+th)\in\operatorname{span}\{B_j(x+th):1\le j\le r\}.
$$

除以非零 $t$ 并令 $t\to0$，得到结论。若 $r=0$，所有 $E_y=0$，结论直接成立。
等价的有限代数证明是对

$$
\bigwedge_{j=1}^{r}(B_jx+tB_jh)\wedge(tAh)=0
$$

取 $t$ 的一次项。这表明所用的相容性来自同一个二元线性作用。

### 定理 4.2（一般位置的双零纤维刚性）

设 $0\ne W$ 是有限实空间，$G\subset GL(W)$ 为紧矩阵群，$\mathfrak g=\operatorname{Lie}(G)$。
Q6 成立当且仅当相对于一份 $G$-不变正内积，

$$
\boxed{\dim_\mathbb R W=\dim_\mathbb R\mathfrak g=3,\qquad
\mathfrak g=\mathfrak{so}(W).}
$$

因此 $G^\circ=SO(W)$，且 $G=SO(W)$ 或 $O(W)$。

**证明。**
**第一步：同一对的两个核先迫出同维。**
紧群平均给 $G$-不变正内积 $B$，于是所有 $A\in\mathfrak g$ 斜对称。
取 Q6 的见证 $x,A$。由上一引理及斜对称性，

$$
x^\perp=\operatorname{im}A
\subseteq\operatorname{im}E_x\subseteq x^\perp.
$$

故 $\operatorname{rank} E_x=n-1$。另一方面 $\ker E_x=\mathbb R A$，故

$$
n-1=\operatorname{rank} E_x=m-1,\qquad n=m.
$$

非零斜对称 $A$ 的核一维，且其秩为正偶数，因此 $n=m\ge3$ 为奇数。

**第二步：关系的关系只剩一个中央化方向。**
若 $B_1\in\mathfrak g$ 与 $A$ 交换，则它保持
$\ker A=\mathbb R x$。斜对称性给 $B_1x=0$，Q6 的另一个零纤维随即给

$$
\mathfrak z_{\mathfrak g}(A)
=\{B_1:[B_1,A]=0\}
=\mathbb R A.
$$

这里用到了原转向的顺序比较 $[B_1,A]$，而非一份孤立的轴表。

**第三步：转向球面上的面积迫使维数为三。**
在 $\mathfrak g$ 上，

$$
\langle X,Y\rangle_{\mathfrak g}=-\operatorname{Tr}_W(XY)
$$

是正定、共轭不变的内积。将 $A$ 归一后，其 $G^\circ$ 伴随轨道维数为 $m-1$，与所在球面 $S^{m-1}$ 相同。紧轨道在连通球面内既开又闭，故恰为整个球面。

轨道有规范二元面积

$$
\omega_A([X,A],[Y,A])
=\langle A,[X,Y]\rangle_{\mathfrak g}.
$$

不变内积保证它与代表的选择无关；若对全部 $Y$ 为零，则 $[A,X]=0$，故非退化；Jacobi 恒等式给 $d\omega=0$。这是标准共伴随辛形式。 [8](#ref-donaldson)
于是 $m-1=2k$。若 $k>1$，球面的 $H^2(S^{2k};\mathbb R)=0$ 给 $\omega=d\eta$，从而

$$
\int_{S^{2k}}\omega^k
=\int_{S^{2k}}d(\eta\wedge\omega^{k-1})=0,
$$

与辛体积非零矛盾。因此 $k=1$，即 $m=n=3$。
$\mathfrak g\subseteq\mathfrak{so}(W)$ 两边同维，故相等。
这一辛球面步骤采用成熟的秩一紧群论证，Donaldson 命题 15 给出同一工具；不是另行宣称发现该分类。 [8](#ref-donaldson)

反向，三维中令 $R_xy=x\times y$。每个非零 $x$ 都为一般位置，
$\ker E_x=\mathbb R R_x$、$\ker R_x=\mathbb R x$，故 Q6 成立。

### 推论 4.3（与原“共停即共线”完全等价）

上述背景下，Q6 等价于对全部非零 $x,y$，

$$
\mathfrak g_x\cap\mathfrak g_y\ne0
\quad\Longleftrightarrow\quad \mathbb R x=\mathbb R y,
\qquad \mathfrak g_x=\ker E_x.
$$

**证明。**
Q6 已给三维全部旋转，故每根线都是轴，每个非零转向只留这一根轴。
反向，原条件先给每根线有非零固定转向，且任何非零转向的核至多一维。斜对称秩的偶性排除偶数 $n$，进而每个非零转向的核恰为一维，且 $n\ge3$。

若独立 $A,B\in\mathfrak g$ 交换，可同时正交谱分解，选一个共同实二维旋转平面 $P$，写
$A|_P=aJ,\ B|_P=bJ$，其中 $(a,b)\ne(0,0)$。
非零 $bA-aB$ 固定整个 $P$，矛盾。因此
$\mathfrak z_{\mathfrak g}(A)=\mathbb R A$。每根线的覆盖又排除 $m=1$；
复用主证明的辛球面步骤得 $m=3$。
选一般位置 $x\ne0$ 及固定它的 $A\ne0$。最大秩引理给

$$
n-1=\operatorname{rank} A\le\operatorname{rank} E_x\le m-1=2.
$$

于是 $n=3$，并恢复 Q6。

### 推论 4.4（任意一块完整开域已经足够）

如果原“共停即共线”只在某非空开集
$U\subset W\setminus\{0\}$ 的所有点对上成立，结论仍是全局 Q6。

**证明。**
取 $x\in U$ 及非零 $A$ 固定它。若另有独立 $h\in\ker A$，则
$x+th\in U$ 的小扰动与 $x$ 共停而不同线，矛盾。所以所有固定 $x$ 的非零转向核均为 $\mathbb R x$。
若 $B$ 与 $A$ 交换，斜对称性给 $Bx=0$；若 $B$ 与 $A$ 独立，上一推论中的共同旋转平面给一个非零组合，既固定 $x$ 又固定整个平面，仍矛盾。
因此中央化子为 $\mathbb R A$。

局部轴覆盖排除 $m=1$：唯一生成元若杀掉整个开集，就必须为零。
辛球面论证给 $m=3$，并使所有非零转向经缩放共轭，故它们全都有一维核。
另由 $U$ 上每个 $E_y$ 非单射，所有 $m\times m$ 子式在开集上为零，故作为多项式恒为零；若 $m>n$ 则这一点本已自动成立。
于是每个 $y$ 都有非零稳定子，得到全局共同固定形式。

**简洁几何。**

这条规则首先锁定一个二元零关系

$$
\mathcal Z=\{([A],[x])\in\mathbb P(\mathfrak g)\times\mathbb P(W):Ax=0\}.
$$

定理之后，$\mathcal Z$ 是两张实射影平面之间的一一对应；有向内容的单位代表则构成 $S^2$。
一般位置使“内容有多少方向”与“变化有多少方向”吻合，交换子与 Jacobi 再把二者锁成三维。这才是从关系到关系的关系，再到三维有限提升的顺序。

<a id="section-5"></a>

## 5. 反着推：删去什么，会具体发生什么

<a id="sec-counter"></a>

### 5.1 删去一般位置：特殊点会伪装成一轴一转

令 $W=\operatorname{Sym}_0(3,\mathbb R)$、$G=SO(3)$，作用为
$X\mapsto gXg^{\mathsf T}$，生成元为 $A_\Omega X=[\Omega,X]$。
取 $x=\operatorname{diag}(1,1,-2)$ 与第一、二坐标平面的旋转生成元 $\Omega$，则

$$
\ker E_x=\mathbb R A_\Omega,\qquad \ker A_\Omega=\mathbb R x.
$$

双零纤维都一维，然而 $\dim W=5$。原因是这个轴对称点的
$\operatorname{rank} E_x=2$，而三个特征值互异的 $y=\operatorname{diag}(1,0,-1)$ 满足
$\ker E_y=0$、$\operatorname{rank} E_y=3$。所以 $x\notin W_{\rm reg}$。
额外的偶然对称恰好冒充了所需稳定方向；“一般位置”不能删掉。

### 5.2 删去任意一个零纤维的唯一性

若只要求 $\ker A=\mathbb R x$，取 $W=\mathbb R^5,G=SO(5)$。
每个非零 $x$ 都在一般位置；在 $x^\perp$ 的两个正交平面上同时非零转动，
可使 $\ker A=\mathbb R x$，但
$\mathfrak g_x\cong\mathfrak{so}(4)$ 为六维。留住同一内容的变化并不唯一。

若只要求 $\ker E_x=\mathbb R A$，取

$$
W=\mathbb R^3\oplus\mathbb R^2,\qquad G=SO(3)\times SO(2).
$$

一般位置 $x=(v,w)$ 满足 $v,w\ne0$，其稳定子恰为
$\mathbb R A$，其中 $A=(R_v,0)$。但

$$
\ker A=\mathbb R v\oplus\mathbb R^2
$$

为三维。那一份变化还偷偷留住整个独立的二维部分。两例分别指出：同一二元作用的两个方向都须控制。

### 5.3 删去轴覆盖：五维也能让每个转向只有一根轴

取

$$
W=\operatorname{Sym}_0(3,\mathbb R),\quad \dim W=5,\qquad
G=SO(3),\quad g:X\mapsto gXg^{\mathsf T}.
$$

生成元作用为 $A_\Omega X=[\Omega,X]$。非零 $\Omega$ 经旋转化成绕第三轴的转向；直接解 $[\Omega,X]=0$ 得

$$
\ker A_\Omega
=\mathbb R\,\operatorname{diag}(1,1,-2)
$$

及其旋转像。所以“共停 $\Rightarrow$ 共线”成立。

但 $X=\operatorname{diag}(1,0,-1)$ 的三个特征值互异，与其交换的斜对称矩阵只有零，故这根内容线不能成为任何非零转向的轴。

更强地，取来源

$$
e=\operatorname{diag}(-1,-1,2)/\sqrt6.
$$

其整个原轨道上的每个点都有非零固定转向，轨道点两两测试也通过候选；轨道张成全部五维 $W$。所以只测实际纯轨道，不能代替对完整线性内容空间的量词。全部未来关系中的线性组合会揭露遗漏方向。

### 5.4 删去轴独占：四维每根线都有固定转向

取 $W=\mathbb R^4,G=SO(4)$。每个非零 $x$ 都有在 $x^\perp$ 内作用的非零转向固定它；但只转动一个坐标二维平面的生成元，会逐点固定它的二维正交补。因此“共线 $\Rightarrow$ 共停”成立，反方向失败。

### 5.5 删去原顺序闭合：七维伪块通过二元表，却过不了组合

在 $\mathbb R^7$ 的正交基上固定交替三形式

$$
\varphi=e^{123}+e^{145}+e^{167}+e^{246}
-e^{257}-e^{347}-e^{356},
$$

并定义 $B(a\times x,y)=\varphi(a,x,y)$、$D_ax=a\times x$。这是七维虚八元数叉积的一份符号约定。 [9](#ref-baez)
它给

$$
D_a^2=aa^{\mathsf T}-\|a\|^2I,\qquad
\ker D_a=\mathbb R a\quad(a\ne0).
$$

平方式可由基矩阵的
$D_i^2=e_ie_i^{\mathsf T}-I$ 与
$D_iD_j+D_jD_i=e_ie_j^{\mathsf T}+e_je_i^{\mathsf T}$
极化核对。因此仅在线性算子族 $L=\{D_a\}$ 中，共停恰为共线，维数却为七。

现在忠实补回原动作组合。令

$$
C=[D_1,D_2]-D_3.
$$

上述符号给

$$
Ce_1=Ce_2=0,\qquad Ce_4=3e_7\ne0.
$$

所以 Lie 闭包内出现一个非零变化，同时固定两个独立方向，直接违反候选。这里无需断言完整闭包是什么；这一个 Lie 闭包见证已经足够。

### 5.6 删去紧性：同一轴规则也允许双曲几何

令 $W=\mathfrak{sl}_2(\mathbb R)$、$G=\operatorname{Ad}PSL_2(\mathbb R)$。对任意非零无迹二阶实矩阵 $Z$，其二阶矩阵中心化子为 $\mathbb R I+\mathbb R Z$，取无迹部分得

$$
\ker(\operatorname{ad}_Z)=\mathbb R Z.
$$

故完整二元候选成立。但作用非紧，不存在不变正内积，出现的是不定型与双曲方向。原概率有界、统计逆和有限容量所给的紧性，确实承担普通球面几何的选择。

**局部范围。**

本候选选择局部基本窗口，不对整个 $\Omega$ 或所有复合对象重复施加。在 $M_d(\mathbb C)$ 的无迹自伴空间上，$d\ge3$ 时一个非零对角生成元固定至少 $d-1$ 维无迹对角内容，已经违反轴独占。这与高维量子理论相容：复合对象不再是本候选选出的基本块。

<a id="section-6"></a>

## 6. 这次回溯究竟缩短了什么

<a id="sec-simplify"></a>

005 使用给定比较与来源方向的三向量零响应；006 首稿将它压缩为共同固定关系与共线关系相等；本次继续将同一候选压成一般位置的一对双零纤维：

$$
\boxed{\text{006 首稿的全局点对关系}
\quad\Longleftrightarrow\quad
\text{本稿的一般位置双零纤维}.}
$$

在完整原前端中，它们也与已证的 005 三维结论等价。我们减少的是陈述需要直接提到的对象和量词，不是改变满足模型的集合。

| 比较 | 006 首稿 | 006 继续稿 |
|---|---|---|
| 直接检查的关系 | 任意两份内容能否共停 | 同一对内容与变化的两个零纤维 |
| 显式量词 | 所有 $x,y\ne0$ | 存在一个一般位置 $x$ 和对应 $A$ |
| 全局信息的承担处 | 全空间点对量词 | 完整作用中的最大秩定义 |
| 三维证明路径 | 先控制球面，再覆盖内容轴 | 最大秩引理先迫同维，再由辛球面迫三维 |
| 复数的进入 | 指定最小 Clifford 完成 | 所有实生成的结合实现唯一，中心内生 |
| 多个系统 | 共同复中心作为整体接口 | 二元中心识别与每个闭环的一致性 |

**精确有限证书。**

如果完整有限 $W,\mathfrak g$ 的矩阵作用已经识别，可用有限代数数据证明
$x\in W_{\rm reg}$：一个 $r\times r$ 子式在 $x$ 处非零，同时所有
$(r+1)\times(r+1)$ 子式作为 $W$ 上的多项式恒零。
再核验 $\ker E_x=\mathbb R A$、$\ker A=\mathbb R x$ 即可。若候选成立，则 $r=m-1$。
因此所谓“一个点”包含对完整原作用的最大秩证明，不能偷换成一次实验输出。

**有限误差不能替代完整未来。**

取同一原旋转菜单 $SO(3)$、来源方向 $r\in S^2$，完整末端二标签测试由
$n\in S^2$ 参数化。所有合法未来固定为有限旋转词后接终止读出，
其中旋转词只把 $r$ 换成 $gr$。对 $0<\varepsilon<1$ 定义

$$
p_\varepsilon(+\mid n,r)
=\frac12\left[1+(1-\varepsilon)n\cdot r+
\varepsilon P_2(n\cdot r)\right],
\qquad P_2(t)=\frac{3t^2-1}{2},
$$

$$
p_\varepsilon(-\mid n,r)=1-p_\varepsilon(+\mid n,r).
$$

$t,P_2(t)\in[-1,1]$，故这是合法、全标签归一的原概率族，且

$$
\sup_{n,r}|p_\varepsilon(+\mid n,r)-p_0(+\mid n,r)|\le\varepsilon.
$$

但是它的完整预测行空间满足

$$
\dim V_0=1+3=4,\qquad
\dim V_\varepsilon=1+3+5=9\quad(0<\varepsilon<1).
$$

证明只需把线性方向 $r_i$ 与无迹二次方向
$r_ir_j-\delta_{ij}/3$ 展开。它们分别给三维与五维旋转表示，两个系数均非零；
常数、线性项及无迹二次项在球面上线性独立，且全部读口 $n$ 分离这些方向。
因此 $W_\varepsilon$ 是三维表示与五维表示的直和。每个非零旋转生成元在这两个分量上各留一条轴，故

$$
\dim\ker A|_{W_\varepsilon}=2.
$$

任意小的逐标签误差，都可以掩盖一个完整的新二次扇区，使准确 Q6 失效。
这说明需要原全未来识别或额外的稳健维数条件；它不否定已给完整有限表示后的精确代数证书。此处 4 与 9 指线性预测维数，不是可完美区分的态数。这个反例针对上述固定原前端；未将它声称为满足 C127 全部仪器、参考与复合条件的模型。

<a id="section-7"></a>

## 7. 从同一来源重新取得比较、面积和复数

<a id="sec-geometry"></a>

### 7.1 比较不再是候选的输入

主定理后，所有 $G$-不变正内积只差一个正倍数：若两份内积之比对应自伴正算子，它与全部三维旋转交换，故为标量。原来源 $e$ 可把这一个倍数固定为 $B(e,e)=1$。

不需任选初始内积的显式定义仍为

$$
\mathcal K:W^*\to W,\qquad
\mathcal K\alpha=\int_G\alpha(ge)\,ge\,dg,
\qquad
B(x,y)=\frac13(\mathcal K^{-1}x)(y).
$$

原轨道张成 $W$，所以对 $\alpha\ne0$，
$\alpha(\mathcal K\alpha)=\int\alpha(ge)^2dg>0$。
故 $\mathcal K$ 可逆；不变性直接来自 Haar 运输。若记
$B_0(x,y)=(\mathcal K^{-1}x)(y)$，取迹得

$$
B_0(e,e)
=\int_G B_0(ge,ge)\,dg
=\operatorname{Tr}_W(\mathcal K\mathcal K^{-1})=3.
$$

因此上式准确归一且全部由原来源决定。Haar 平均是数学定义，不自动供应实际随机混合器。

### 7.2 两份内容的第三方向

选择一个取向作为坐标约定，定义 $R_xy=x\times y$ 为该 $B$ 与取向下的叉积。由于 $\mathfrak g=\mathfrak{so}(W)$，全部 $R_x$ 都属于原 Lie 代数，并且

$$
\begin{aligned}
R_xx&=0,&
-\tfrac12\operatorname{Tr}(R_xR_y)&=B(x,y),\\
R_xR_yz&=B(x,z)y-B(x,y)z,&
[R_x,R_y]&=R_{x\times y},\\
\|x\times y\|^2&=\|x\|^2\|y\|^2-B(x,y)^2.
\end{aligned}
$$

任意独立 $x,y$ 与 $x\times y$ 张成全 $W$：这才是候选之后的三维有限提升。固定单位 $e$，其横面上的 $J_e=R_e$ 满足

$$
J_e^2=-I\quad\text{于 }e^\perp.
$$

于是横向是一个复方向，轴加横面为 $\mathbb R\oplus\mathbb C$。

候选只固定轴和作用结构，不固定 $R$ 与 $-R$ 的选择，不固定原生成元 $A=\lambda R_e$ 的速度。后续的中央复单位也只确定到共轭约定；物理时间方向和 $\hbar$ 没有由固定关系给出。

```latex
\begin{tikzpicture}[>=Latex,scale=0.95]
\draw[fill=pale,draw=accent] (0,0) ellipse (2.3 and 0.75);
\draw[->,very thick,ink] (0,0)--(0,2.2) node[above]{原轴 \(e\)};
\draw[->,thick,accent] (0,0)--(1.85,0.25) node[above right]{\(x\)};
\draw[->,thick,accent] (0,0)--(-0.8,0.57) node[left]{\(J_ex\)};
\draw[->,thick,ink] (1.3,0.05) arc[start angle=0,end angle=115,x radius=1.3,y radius=0.4];
\node[align=center] at (0,-1.3) {横面：\(J_e^2=-I\)\\轴与横面合成完整三维内容};
\node[anchor=west,align=left,text width=7.2cm] at (3.0,0.65)
{候选没有先画这张图。\\
“每根线都是轴，非零转向只留一根轴”\\
加上原顺序复合，先迫出三维；\\
三维确定后，轴与横面的图才随之成立。};
\end{tikzpicture}
```

### 7.3 球锥与对称内容乘法

在 $E=\mathbb R1\oplus W$ 上，定义自旋 Jordan 乘法

$$
(a,x)\circ(b,y)
=(ab+B(x,y),\,ay+bx).
$$

其平方为 $(a^2+\|x\|^2,2ax)$。对 $x\ne0$，谱投影为
$(1,\pm x/\|x\|)/2$，谱值为 $a\pm\|x\|$，故其正锥为

$$
C=\{(a,x):a\ge\|x\|\}.
$$

$L_{v^2}$ 与 $L_v$ 交换可直接验证。将 $R$ 在单位方向延为零，叉积三重积恒等式又给

$$
[L_a,L_b]+[R_a,R_b]=0,\qquad
[R_a,L_b]=L_{R_ab}.
$$

这是同一球结构的对称比较与有向变化之间的三元相容性。

### 7.4 为什么结合性逼出平方为负一

先临时选择取向。设 $K$ 是非零实含幺交换代数，在自由 $K$-模
$K\otimes_\mathbb R E$ 上寻找含幺、$K$-双线性、$SO(3)$-等变乘法，保留

$$
\frac{x*y+y*x}{2}=B(x,y)1.
$$

这些是明确的表示要求，不宣称原内容之间已经供应了一项物理乘法。

### 命题 7.1（二元重括号校准）

上述乘法必且只可能写成

$$
x*y=B(x,y)1+\kappa(x\times y),\qquad \kappa\in K.
$$

它结合当且仅当 $\kappa^2=-1$。

**证明。**
反对称部分是从 $\Lambda^2W$ 到 $K\otimes(\mathbb R1\oplus W)$ 的等变映射。
三维旋转下不存在非零标量值不变交替二形式，而
$\Lambda^2W\to W$ 的等变映射只有叉积的标量倍数，故得到所示形式。
直接展开得

$$
(x*y)*z-x*(y*z)
=(1+\kappa^2)\bigl(B(x,y)z-B(y,z)x\bigr).
$$

其中标量三重积相消，向量部分只用叉积三重积恒等式。
特别地，只取两个正交单位方向 $u,v$，已有

$$
(u*u)*v=v,\qquad u*(u*v)=-\kappa^2v.
$$

自由模中的 $v$ 不会消去非零标量，故同一对方向的重括号一致性
迫使 $\kappa^2=-1$；反向代回全部结合差即为零。
若对合固定实 $E$，还由 $(x*y)^*=y*x$ 得 $\kappa^*=-\kappa$。

反着看，若坚持 $\kappa\in\mathbb R$，则同一对内容改变括号便改变结果。
如果先用外部 $i$ 写 $\kappa=i\lambda$、$\lambda\in\mathbb R$，相容性恰好要求
$\lambda^2=1$。这个校准约束的是所定义的结合表示；Q6 的轴关系本身对
$D_x\mapsto\lambda D_x$、$\lambda\ne0$ 不敏感，不能直接用它标定原物理速度。

### 7.5 不选左右手：取向线成为内生复中心

令 $L=\Lambda^3_\mathbb R W$ 携带 $B$ 诱导的一维内积，定义

$$
K=\mathbb R\oplus L,\qquad
(a,\ell)(b,m)
=\bigl(ab-\langle\ell,m\rangle,\;am+b\ell\bigr),
\qquad (a,\ell)^*=(a,-\ell).
$$

负号由上一节的重括号相容性决定。
因为 $L$ 一维，$\langle\ell,m\rangle n=\langle m,n\rangle\ell$，所以乘法结合。
且

$$
(a,\ell)^{-1}
=\frac{(a,-\ell)}{a^2+\|\ell\|^2}\qquad ((a,\ell)\ne0).
$$

故 $K$ 是实二维交换域。任取单位取向 $J\in L$，都有 $J^2=-1$；
选 $J$ 给坐标同构 $K\simeq\mathbb C$，选 $-J$ 给共轭坐标。这个域本身不需选定任一手性。

取任意正交单位基 $e_1,e_2,e_3$，定义无取向面积

$$
c(x,y)=\sum_{r=1}^3(x\wedge y\wedge e_r)\otimes e_r\in L\otimes W.
$$

换基的两个正交矩阵相互收缩，所以它与基无关。辅助选择 $J$ 后，

$$
c(x,y)=J\otimes(x\times_Jy).
$$

$J$ 与 $\times_J$ 同时反号时，这个乘积不变。
在
$\mathcal A=K1\oplus(K\otimes W)$ 上定义

$$
(\alpha,u)\bullet(\beta,v)
=\bigl(\alpha\beta+B_K(u,v),\
\alpha v+\beta u+c_K(u,v)\bigr),
$$

其中 $B_K,c_K$ 为 $K$-双线性延拓。上一命题给结合律。
对合对系数共轭、固定 $W$，从而

$$
\mathcal A_{\rm sa}=E,\qquad Z(\mathcal A)=K.
$$

中心的向量部分必须与所有 $x$ 的叉积为零，因而只能为零。
完成没有增加新的单系统自伴内容；新增的是容纳次序差所需的反自伴方向。

### 7.6 删去“最小”：实生成的结合实现其实唯一

### 定义 7.2（保留内容的实结合实现）

一个实现由非零实含幺结合 $*$-代数 $A$ 及实线性映射
$j:E\to A_{\rm sa}$ 组成，满足

$$
j(1)=1,\qquad
j(a\circ b)=\frac{j(a)j(b)+j(b)j(a)}2,
$$

且 $j(E)$ 作为实含幺结合代数生成 $A$。

“生成”限定我们正在实现这份内容的乘法，不把额外无关代数任意接入。
实标量与原预测内容的类型一致。这里不预设 $A$ 有限维、复标量或最小维数。

### 定理 7.3（唯一实结合实现）

任何上述实现都唯一同构于

$$
\boxed{A\cong\operatorname{Cl}_{3,0}\cong M_2(\mathbb C)}
$$

且同构保留给定的 $j$。这个同构类的中心是前节的内生域 $K$。

**证明。**
Jordan 关系给

$$
j(x)j(y)+j(y)j(x)=2B(x,y)1,\qquad j(x)^*=j(x).
$$

故有唯一满射实 $*$-同态 $\operatorname{Cl}_{3,0}\to A$。
取正交单位生成元 $e_1,e_2,e_3$。关系
$e_i^2=1,\ e_ie_j=-e_je_i$ 将每个词约成八个实单词

$$
1,\ e_1,\ e_2,\ e_3,\ e_1e_2,\ e_2e_3,\ e_3e_1,\ e_1e_2e_3.
$$

将 $e_i$ 分别送到 Pauli 矩阵

$$
\sigma_1=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
\sigma_2=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad
\sigma_3=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
$$

八个像为 $I,\sigma_1,\sigma_2,\sigma_3,i\sigma_3,i\sigma_1,i\sigma_2,iI$，
实线性独立并张成 $M_2(\mathbb C)$，所以这是同构。
任意实双边理想自动对中心 $iI$ 的乘法封闭，故也是复双边理想；
矩阵代数简单，因此上述非零含幺商只能是其本身。
同态由生成元决定，所以保留 $j$ 的同构唯一。

这也证明 $\mathcal A\cong M_2(K)$。自伴 $a1+x$ 的谱为
$a\pm\|x\|$，标准正锥准确恢复原球锥。
注意本文使用 $x^2=+\|x\|^2$ 的 Clifford 符号约定；
不能把负号约定的三维分类表直接挪来替代上述证明。

**为什么原操作闭包不能直接顶替这个实现。**

Jordan 左乘算子满足

$$
L_x(a,y)=(B(x,y),ax),\qquad
L_x^2(a,y)=(a\|x\|^2,B(x,y)x),
$$

通常不等于 $\|x\|^2(a,y)$。
所以 $x\mapsto L_x$ 不是这里的 Clifford 实现。
原动作可顺序复合，并不自动把原内容识别成该动作代数中的自伴元；
需要核验上面明确的保持关系。

**实生成与外部复生成的区别。**

在 $M_2(\mathbb C)\oplus M_2(\mathbb C)$ 中，$a\mapsto(a,a^{\mathsf T})$ 对自伴 $a$
是实 Jordan 嵌入。它实生成的仅是

$$
\{(M,\overline M):M\in M_2(\mathbb C)\}\cong M_2(\mathbb C),
$$

体积元为 $J=(iI,-iI)$。
若再加入外部复单位 $i_{\rm ext}=(iI,iI)$，则
$-i_{\rm ext}J=(I,-I)$，可分出两个中心投影。
所以外部复生成的普遍包变为

$$
\operatorname{Cl}_{3,0}\otimes_\mathbb R\mathbb C
\cong M_2(\mathbb C)\oplus M_2(\mathbb C).
$$

因此“复数内生”不能一边预先放入外部 $i$，一边沿用实简单包的唯一性。

### 推论 7.4（最小振幅与两分量 Hilbert 空间）

若 $p_+=(1+e_3)/2$，则

$$
\mathcal H=\mathcal A p_+\cong K^2\cong\mathbb C^2.
$$

其 $K$-基为 $p_+,e_1p_+$，内积由
$\xi^*\eta=\langle\xi,\eta\rangle p_+$ 定义，
范数平方为 $|z_1|^2+|z_2|^2$。

这里的“最小”只修饰矩阵代数的最小左理想，不再是用于挑选代数的额外假设。
二维复振幅由已证明唯一的实代数得到；它不从球面面积直接量子化出物理 $\hbar$。

<a id="section-8"></a>

## 8. 原始概率为何成为 Born 形式

<a id="sec-born"></a>

原归一准备轨道的闭包为 $c+S^2$，最小闭凸完成为 $c+\overline B^3$。每个原未来事件是 $V$ 上的线性评价，唯一写作

$$
f(tc+w)=\alpha t+B(b,w).
$$

在原轨道上的 $0\le f\le1$，经连续闭包给

$$
\|b\|\le\min(\alpha,1-\alpha).
$$

令

$$
\rho_w=\frac{I+w\cdot\sigma}{2},\qquad
E_f=\alpha I+b\cdot\sigma.
$$

则 $0\le E_f\le I$、$\rho_w\ge0$、$\operatorname{Tr}\rho_w=1$，并且

$$
\boxed{f(c+w)=\operatorname{Tr}(\rho_wE_f).}
$$

这是同一原评价的坐标表示。完整原测试的归一式给
$\sum_wE_{f,w}=I$，所有成功、失败、零标签及旧记录均保留。

纯方向 $n,m$ 对应秩一投影 $P_n,P_m$，因此

$$
\operatorname{Tr}(P_nP_m)=\frac{1+B(n,m)}2
=\cos^2\frac\theta2
=|\langle\psi_n,\psi_m\rangle|^2.
$$

相位几何为 Hopf 纤维

$$
S^1\longrightarrow S^3\longrightarrow S^2\cong\mathbb{CP}^1,
$$

其映射可写为

$$
(z_1,z_2)\longmapsto
(2\Re(\bar z_1z_2),\,2\Im(\bar z_1z_2),\,|z_1|^2-|z_2|^2).
$$

$SU(2)$ 到 $SO(3)$ 的提升
$U_n(\theta)=\exp(-\mathrm i\theta n\cdot\sigma/2)$
解释半角与振幅的 $4\pi$ 周期。

三维是原内容差维数，四维是含归一尺度的预测维数，都不是已推出的物理空间时间维数。若原效果只有
$(I\pm\eta n\cdot\sigma)/2$、$0<\eta<1$，仍能分离所有内容方向，却无原锐读口；最小凸完成也不供应每个实际混合准备。

<a id="section-9"></a>

## 9. 用候选继续发展完整有限量子理论

<a id="sec-full"></a>

下述定理发展的是上述块的有限数学完成，并把实际物理对象所需的接口逐项列明。它们不把“所有完备结构都在 $\Omega$”作为自动供应命题。

### 9.1 两个局部复数尚未对齐时，会多出什么

先把局部 $\mathcal A_A,\mathcal A_B\cong M_2(\mathbb C)$ 视为实 $*$-代数。
只要求其含幺像相互对易、并由这些像实生成联合代数。
普遍对象是实张量，而不是预先选定的复张量。

### 定理 9.1（两块之间的相对中心扇区）

$$
M_2(\mathbb C)\otimes_\mathbb R M_2(\mathbb C)
\cong M_4(\mathbb C)\oplus M_4(\mathbb C).
$$

令 $j_A=J_A\otimes1,\ j_B=1\otimes J_B$，则

$$
q=j_Aj_B,\qquad q^*=q,\quad q^2=1,
$$

$$
p_{\rm same}=\frac{1-q}{2},\qquad
p_{\rm opposite}=\frac{1+q}{2}
$$

是两个中心投影；前者上 $j_B=j_A$，后者上 $j_B=-j_A$。

**证明。**
实 $*$-代数同构

$$
\mathbb C\otimes_\mathbb R\mathbb C\longrightarrow\mathbb C\oplus\mathbb C,\qquad
z\otimes w\longmapsto(zw,z\overline w)
$$

在矩阵层面给

$$
a\otimes b\longmapsto
\bigl(a\otimes_\mathbb C b,\ a\otimes_\mathbb C\overline b\bigr).
$$

此时 $j_A=(iI,iI),j_B=(iI,-iI),q=(-I,+I)$，两个投影显式分离两块。
每块张成完整 $M_4(\mathbb C)$，维数吻合，故为同构。

这是从反面看“共同复中心”为什么不能省：两个局部球不识别彼此的复结构，
联合便允许一个相对正负的中心扇区。它首先是数学扇区；
若要把它当成可读取的经典记录，还需原效果实际供应该区分。
BGW 文献的相应 Jordan 复合范畴也出现两个复系统附带额外经典二值的现象；
这里的结论由上面的实张量分解直接证明。 [11](#ref-bgw)

### 9.2 全部生成型联合与二元中心识别

### 定理 9.2（实联合的全部扇区）

对 $N\ge1$，

$$
T_N=\bigotimes_{i=1}^{N}{}_\mathbb R M_2(\mathbb C)
\cong\bigoplus_{2^{N-1}}M_{2^N}(\mathbb C).
$$

相互对易的局部含幺像所实生成的任意非零联合，必为某个非空扇区子集的直和。

**证明。**
逐次用 $\mathbb C\otimes_\mathbb R\mathbb C\cong\mathbb C\oplus\mathbb C$ 即得分解。
显式地，选各局部内生中心的单位 $j_i$，令 $q_i=-j_1j_i$、$i\ge2$。
它们是相互对易的中心自伴对合，最小中心投影为

$$
p_\epsilon
=2^{-(N-1)}
\prod_{i=2}^N(1+\epsilon_iq_i),\qquad
\epsilon\in\{\pm1\}^{N-1}.
$$

在此扇区中 $j_i=\epsilon_i j_1$，剩余代数为通常的复矩阵张量积。
相互对易的局部像给 $T_N$ 到任意生成型联合的满射同态；
简单代数直和的理想只能删除整块，故商恰由非空扇区子集分类。

若原联合还含不由局部像生成的额外元素，这一分类只覆盖局部像生成的子代数；
局部中心未必与额外元素对易。生成条件因此须明说。

### 定义 9.3（同一个联合中的中心配对）

在 $N$ 个块组成的无向图上，为每条边指定
$\sigma_{ij}=\sigma_{ji}\in\{\pm1\}$，并要求

$$
\boxed{j_j=\sigma_{ij}j_i.}
$$

无坐标地，这是一条边上两个内生复域 $K_i,K_j$ 之间的实 $*$-同构，
而非外界统一塞入的一个 $i$。

### 定理 9.4（有限中心拼接）

设图有 $c$ 个连通分支，含孤立顶点。上述二元关系的普遍商非零，
当且仅当每个闭环都满足

$$
\boxed{\prod_{\text{环路边}}\sigma_{ij}=+1.}
$$

若相容，其普遍商为

$$
T_N/I_\sigma\cong
\bigoplus_{2^{c-1}}M_{2^N}(\mathbb C).
$$

具体生成型实现还可选择其中任意非空扇区子集。
特别地，图连通时，所有非零实现都唯一为 $M_{2^N}(\mathbb C)$。

**证明。**
沿一条环路反复代入边关系，会得到
$j_i=(\prod\sigma)j_i$。若乘积为负，则 $j_i=-j_i$，
进而 $j_i=0$；但 $j_i^2=-1$，所以 $1=0$，商退化。
若所有环路乘积为正，可在每个连通分支选一个根，沿路径传播正负号；
环路一致保证结果不依赖路径。每个分支内只剩一份中心，
不同分支之间还有 $c-1$ 个相对符号，故普遍商有 $2^{c-1}$ 块。
任意具体生成型实现为其非零商；当 $c=1$ 时简单性给唯一性。

一棵连接全部块的树只需 $N-1$ 条边，就可确定共同中心；
其余边检查相容性。三块的有限提升是

$$
\sigma_{12}\sigma_{23}\sigma_{31}=1.
$$

在完全图中，所有三角一致性足够；一般稀疏图则必须检查全部独立环路，
不能漏掉没有三角形的负四边环。

```latex
\begin{tikzpicture}[>=Latex,scale=0.9]
\node[draw=accent,fill=pale,circle,minimum size=11mm] (a) at (0,0) {\(K_1\)};
\node[draw=accent,fill=pale,circle,minimum size=11mm] (b) at (4,0) {\(K_2\)};
\node[draw=accent,fill=pale,circle,minimum size=11mm] (c) at (2,2.4) {\(K_3\)};
\draw[thick] (a)--node[below]{\(\sigma_{12}\)}(b);
\draw[thick] (b)--node[above right]{\(\sigma_{23}\)}(c);
\draw[thick] (c)--node[above left]{\(\sigma_{31}\)}(a);
\node[anchor=west,text width=6.7cm,align=left] at (5.3,1.1)
{每条边对齐两份内生复结构；\\
绕一圈必须回到原来的虚单位。\\
负环路会要求同一 \(J\) 同时等于 \(-J\)。};
\end{tikzpicture}
```

局部换坐标 $J_i\mapsto\eta_iJ_i$、$\eta_i=\pm1$，只使
$\sigma_{ij}\mapsto\eta_i\eta_j\sigma_{ij}$；闭环乘积不变。
这里对齐的是虚单位的相对共轭选择，不是把每个量子态的连续 $U(1)$ 相位钉住；
后者的 Hopf 纤维结构仍然保留。

### 推论 9.5（局部自伴乘积完整性）

若联合的全部自伴部分由局部自伴乘积实线性张成，则只保留一个中心扇区。

**证明。**
局部自伴乘积的张成维数至多 $4^N$，而 $s$ 个矩阵扇区的自伴维数为
$s\,4^N$。若张成完整自伴部分，则 $s=1$。
反向，单个复矩阵扇区中，局部 Pauli 张量基确实张成全部自伴部分。

这给共同中心的另一项等价联合检验；它仍是联合结构条件，局部 Q6 不自动保证。

### 9.3 局部反射与共同中心的实际兼容性

### 命题 9.6（独立反射必须保留全部相对扇区）

对局部 $g_i\in O(W_i)$，其 Clifford 实 $*$-自同构送
$j_i\mapsto\eta_i j_i$，其中 $\eta_i=\det g_i$。
因此相对扇区变为

$$
\epsilon_i\longmapsto\eta_1\eta_i\epsilon_i.
$$

一个局部控制族能延拓到保留扇区集合 $S$ 的生成型联合上，
当且仅当 $S$ 对上述置换不变。
若每一端的反射均能独立延拓，则 $S$ 必须包含全部 $2^{N-1}$ 个扇区。

**证明。**
体积元在 $g_i$ 下乘 $\det g_i$。代入
$q_i=-j_1j_i$ 与 $p_\epsilon$ 即得扇区置换。
自同构能下降到商，恰当且仅当被删除的中心理想不变。
各端独立反射给所有独立符号翻转，在扇区集上传递，因此非空不变集合只能是全集。

所以 Q6 本身允许的 $O(3)$ 离散反射，与单个共同中心扇区中的独立局部延拓并不相容。
若所有端同时反向，单扇区可以保持，但它仍是全局共轭型实对称；
标准量子过程是否允许它，要继续通过完整参考的 CP 条件检验。

### 9.4 从共同中心到全部有限矩阵块

### 命题 9.7（复张量）

若 $M_m(\mathbb C)$、$M_n(\mathbb C)$ 以同一复中心含幺 $*$-嵌入联合代数，
两个像交换且乘积复线性张成联合代数，则联合代数为 $M_{mn}(\mathbb C)$。

**证明。**
$a\otimes b\mapsto\iota_A(a)\iota_B(b)$ 是满射含幺 $*$-同态。
源 $M_m(\mathbb C)\otimes_\mathbb C M_n(\mathbb C)\cong M_{mn}(\mathbb C)$ 为单代数，
含幺排除全核，故必为同构。

张量幂先给 $M_{2^N}$。对 $d\le2^N$ 取秩 $d$ 的数学投影角，
再取有限直和，得到全部 $\bigoplus_sM_{d_s}(\mathbb C)$。
数学角不自动成为实际对象；原支持返回、标签与附接负责实际供应。
至此，旧接口“共同复中心”已经还原成同一个联合内的二元配对及有限闭环相容性。

### 9.5 状态、效果与可观测量

### 命题 9.8（密度表示）

有限直和 $\mathcal A$ 的自伴部分 $\mathcal A_{\rm sa}$ 上，
全部归一实线性正泛函（等价地，整个复代数上的归一复线性正泛函）恰为

$$
\omega(a)=\sum_s\operatorname{Tr}(\rho_sa_s),\qquad
\rho_s\ge0,\quad\sum_s\operatorname{Tr}\rho_s=1.
$$

效果为 $0\le E\le I$，完整测量为 $\sum_kE_k=I$。自伴元
$H=\sum_k h_kP_k$ 给均值 $\operatorname{Tr}(\rho H)$ 和谱概率
$\operatorname{Tr}(\rho P_k)$。

**证明。**
非退化实迹配对给唯一自伴 $\rho_s$；在每个秩一正投影上的正性给 $\rho_s\ge0$，在单位上的值给总迹一。反向直接成立。自伴谱分解给最后结论。

实际联合准备是否覆盖完整标准正锥是独立接口，单个局部球、代数张量同构或单纯线性分离不保证它。

### 9.6 完整参考推出 CP、Kraus 与仪器

### 定理 9.9（同一分支的完全正性）

设原分支在自伴部分实线性，作其唯一复线性延拓
$\mathcal E:M_d\to M_n$。若有实际完整矩阵参考块 $M_r$、$r\ge d$，使同一
$\mathcal E\otimes\operatorname{id}_r$ 在整个标准联合正锥上保正，则

$$
\mathcal E(\rho)=\sum_\mu K_\mu\rho K_\mu^*.
$$

对完整数学态空间迹不增，当且仅当
$\sum_\mu K_\mu^*K_\mu\le I$。完整仪器归一，当且仅当

$$
\sum_{k,\mu}K_{k\mu}^*K_{k\mu}=I,
$$

其中 $k$ 保留所有原记录。

**证明。**
在参考块内取 $d$ 维数学子空间，置
$\lvert\Gamma\rangle =\sum_i\lverti\rangle \otimes\lverti\rangle$。
完整联合保正使
$C_{\mathcal E}=(\mathcal E\otimes\operatorname{id})(\lvert\Gamma\rangle \langle\Gamma\rvert )\ge0$。
将其谱分解的向量重排为矩阵 $K_\mu$，比较矩阵单位系数即得 Kraus 式；逆向共轭和在任意参考上保正。迹配对给不等式与等式。

这使用标准 Choi–Kraus 判据，参考 Watrous 第 2 章定理 2.22。 [12](#ref-watrous)
经典参考的维数或只对乘积态的正性不足；数学 Kraus 指标也不是自动可访问的原细标签。

取向反射可由转置代表。其作用于 Bell 态的一半给

$$
(T\otimes\operatorname{id})(\lvert\Phi^+\rangle \langle\Phi^+\rvert )
=\tfrac12\,\operatorname{Swap},
$$

有特征值 $-1/2$。因此若同一原控制满足完整参考条件，就排除 $O(3)$ 中的反射。若原菜单确实有反射，该实例不满足这个后续接口，不能通过删门声称原实例已完成重建。

### 9.7 理想更新不是只由效果名称决定

### 定理 9.10（Lüders）

简单块上，CP 分支的效果若为投影 $P$，且它不扰动每个支撑于 $P$ 的态，则

$$
\mathcal E(\rho)=P\rho P.
$$

**证明。**
$\sum_\mu K_\mu^*K_\mu=P$ 给 $K_\mu=K_\mu P$。对每个
$\psi\in P\mathcal H$，正秩一和
$\sum_\mu\lvertK_\mu\psi\rangle \langleK_\mu\psi\rvert
=\lvert\psi\rangle \langle\psi\rvert$
迫使每个 $K_\mu\psi$ 与 $\psi$ 共线。对两个独立向量及其和用线性，得
$K_\mu=c_\mu P$、$\sum_\mu|c_\mu|^2=1$。秩一与零投影直接处理。

只有成功概率正时才归一成
$P\rho P/\operatorname{Tr}(\rho P)$。
仅可重复、或只保持某组基态，都不够：支撑内退相干就是反例。一般效果 $E$ 的选中无附加扰动滤片是
$\rho\mapsto\sqrt E\rho\sqrt E$，实际精确供应另由原指针与合法门词负责。

### 9.8 连续可逆过程与 Schrödinger 形式

### 定理 9.11（幺正动力学）

同一简单块上的连续 CPTP 单参数群，若逆也 CP，则存在自伴 $H$，使

$$
\mathcal E_t(\rho)=U_t\rho U_t^*,\qquad
U_t=e^{-\mathrm i tH/\hbar}.
$$

于是

$$
\mathrm i\hbar\,\dot\psi=H\psi,\qquad
\dot\rho=-\frac{\mathrm i}{\hbar}[H,\rho].
$$

**证明。**
对偶映射及其逆均保单位且 CP。两边的 Schwarz 不等式迫使
$T(a^*a)=T(a)^*T(a)$；极化给乘法保持，故为 $*$-自同构。矩阵单位的像由酉基变换实现，连续单参数的内导子给指数形式。标量相位不影响密度。有限离散中心不能被连续群置换，直和逐块处理。

这里是给定连续时间参数后的形式定理，不供应物理时钟、具体 Hamiltonian、精确连续调用或 $\hbar$ 的数值。

### 9.9 两个直接理论后果

局部完整 CPTP 操作并忘去全部结果时，

$$
\operatorname{Tr}_B[(\operatorname{id}\otimes\mathcal E_B)(\rho_{AB})]
=\operatorname{Tr}_B\rho_{AB},
$$

因为 $\sum_\mu K_\mu^*K_\mu=I$；这是无信号性，后选择与任意联合操作不在命题内。

状态半内积
$\langle X,Y\rangle_\rho=\operatorname{Tr}(\rho X^*Y)$
的 Cauchy–Schwarz 不等式，对中心化自伴 $H,K$ 给

$$
\operatorname{Var}_\rho(H)\operatorname{Var}_\rho(K)
\ge\left|\frac1{2\mathrm i}\operatorname{Tr}(\rho[H,K])\right|^2.
$$

因此不确定性来自同一正比较与非交换乘法，不需再单列为独立公理。

<a id="section-10"></a>

## 10. 接回最新 C127：同一原关系不能被重选

<a id="sec-project"></a>

本轮的 $\mathfrak g$ 来自原可逆接续。本轮构造的几何叉积 $R_x$ 并不自动等于项目事先给定的有向响应 $D_a$。例如 Pauli 约定下，
$\delta_ab=\mathrm i[a,b]/2$ 在无迹向量部分对应 $-R_ab$，符号与原尺度都须运输核对。

### 10.1 项目保留的零接触桥

C127 对每个原对象及实际联合对象、每个 $a\in E_A$、每个正元 $x$、每个原实际准备 $\alpha$，要求

$$
\alpha(x)=0\Longrightarrow\alpha(D_ax)=0.
$$

它仍保留全内协变和同一指针的原尺度式

$$
[K,D_a]=D_{Ka},\qquad
-\operatorname{Tr}_{\mathbb R,E_P}(D_{d_0}^{\,2})
=\operatorname{Tr}_{\mathbb R,E_P}(L_{d_0}^{\,2}),\qquad d_0=d-z_P(d).
$$

$z_P$ 是完整 Jordan 中心投影，不是只减去一个整体标量。
在其完整保留背景下，实际身份参考与原交叉零先给 $D_au=0$；实际准备的正锥包覆盖完整正对偶，再用零接触判据得到双向保锥指数，进而接回原导子。完整 C127 与 C126、C124 等价。 [3](#ref-repo127)、[10](#ref-niestegge)、[11](#ref-bgw)

这些是项目已经声明并证明的条件桥，本文只按原合同复用；没有把它们作为第二个本轮候选。C127 的全对象原同一性义务不会由局部 Q6 自动消失。

### 10.2 为什么每个平方正确仍不够：保留中心的反例

固定 $\varepsilon\in\mathbb R\setminus\{0\}$，项目给的全背景族可以在每个完整矩阵直和对象上写为

$$
D^\varepsilon_ab
=\delta_ab+\varepsilon
\bigl(t(a\circ b)-t(a)t(b)\bigr)u,\qquad
\delta_ab=\frac{\mathrm i}{2}[a,b],
$$

其中 $t$ 是完整直和的归一迹。记补项为 $M_ab$。迹循环性给

$$
\delta_aM_b=0,\quad M_aM_b=0,\quad
M_a\delta_a=0,\quad M_au=M_u=0.
$$

故逐个平方完全不变：

$$
(D^\varepsilon_a)^2=\delta_a^2.
$$

但两个顺序的差保留

$$
([L_a,L_b]+[D^\varepsilon_a,D^\varepsilon_b])x
=2\varepsilon\,t((\delta_ab)\circ x)u.
$$

在整个原指针 $\mathbb C\oplus M_3$ 中取 $p=0\oplus e_{11}$，
$\beta$ 的密度为 $0\oplus e_{22}$，归一迹满足 $t(p)=1/4$，则

$$
\beta(p)=0,\qquad
\beta(D^\varepsilon_pp)=3\varepsilon/16\ne0.
$$

这份差异实际沿完整单位方向输出；删去中心便看不见它。源文在同一个 tagged CP 域中核对了全部实际张量、原设备、失败、返回与历史均保留。 [3](#ref-repo127)

其对本轮的精确启示是：七维反例不能只保留单个叉积转向而漏掉交换子；原 $D$ 也不能只保留各自平方而漏掉混合中心输出。两者是不同载体上的障碍，不能互相冒充证明。

### 10.3 较大几何与实际供应

在复矩阵完成上，未归一正元满足

$$
X=\tfrac12(tI+w\cdot\sigma),\qquad
\det X=\tfrac14(t^2-\|w\|^2).
$$

正锥是未来 Lorentz 锥；$t$ 为概率质量坐标，不是时间。固定正行列式的二阶正定元形成
$SL(2,\mathbb C)/SU(2)$，即双曲三空间。一般有限直和的锥内部为

$$
C^\circ\cong
\prod_s\mathbb R_{>0}\times
\prod_{n_s\ge2}SL(n_s,\mathbb C)/SU(n_s).
$$

C125 的 $J$ 作用于比较 Lie 代数
$\mathfrak h=\mathfrak k\oplus L(E_0)$，不是三维球底空间的复结构。 [3](#ref-repo127)

C124–C127 的完整合同还保留原 P/G、AC、精确调用、X/Xs、全事件参考、F、原遗忘与具名支持返回。原确定原子指针配对使某非经典块内 $d=cp,\ 0<c\le1,\ \alpha(d)=1$ 迫出 $c=1,\rho_\alpha=p$。该块内两方向与

$$
U_E=
\begin{pmatrix}
\sqrt E&-\sqrt{I-E}\\
\sqrt{I-E}&\sqrt E
\end{pmatrix}
$$

配合，在其余指针方向与其余中心块上取恒等，可在完整原连线条件下供应选中平方根支及完整失败支。数学二维角不必是实际量子位对象；项目完整满足族可只有大小 $3^k$ 的块。

原成功率、返回尺度、正反手选择与物理钟速分别是不同数据。轴关系不能恢复它们；把成功分支归一化，也不能把原成功质量从历史中抹去。

<a id="section-11"></a>

## 11. 保留的量子研究背景如何约束这次回溯

**C117：几何方向不是完整预测内容。**

C117 的 §§17–24 先供应三维方向、旋转稠密、连续性与全未来充分性，再加所有上下文上的黄金四时选择关系，筛去高次球谐，非退化时导出预测容量四。其一致估计给同一仿射投影逐原标签的 $L^\infty$ 误差至多 $5\varepsilon$，但投影可为负；共同正修复另由整张原记录图的正锥可行性决定。这不是整条记录分布的 TV 误差。因此本文不能把其预给三维倒用作自己的三维证明，也不能以“近似看起来是球”替代完整 $W$。 [4](#ref-repo117)

**FIB：准确 binary 实现已经推进。**

FIB 的 §148.1 已在原完整来源及端点合同下，用同一个 Borel 集合准确实现三个时刻的独立 Bernoulli$(1/4)$ 八项联合律。§150.2 另有共同四标签分割匹配三对完整二时律；§151.1 有 binary 见证的细分匹配全部至少两个 B 的三时系数。后两份分割未证相同，剩余锚方程与完整 $F_{64}$ 仍未闭合。006 首稿已经纳入这一准确实现；本次继续保留其同一见证的边界。 [5](#ref-repofib)

**C113 与 Fourpath。**

C113 的结果在已给复矩阵及 CP 背景内，在同源三阶设计与记忆边缘正谱底条件下给联合误差界，另给未来新方向的有限误差秩五证书；canonical positive refinement 的 Lean 源也先给准确 canonical 粗滤片。Fourpath III 把 $0<\xi\le13/4$ 的全局最小者限制为 pure phase，仍未求出全部极小参数与转变点。这些结果推进校准、辨识和优化，不能替代本轮的量子起源条件。 [6](#ref-repo113)、[7](#ref-repofour)

<a id="section-12"></a>

## 12. 公理依赖账本与尚未推出的内容

| 目标 | 实际推导路径 | 仍需保留的接口 |
|---|---|---|
| 三维、全部旋转 | 原有限有界统计前端 $+\ Q6$ | 非平凡、全未来、原逆与顺序闭合 |
| 正比较与面积 | 原来源协方差；三维旋转及叉积 | 尺度归一与取向只是明确约定 |
| 复二维振幅 | 实生成的结合实现唯一；最小左理想给两分量 | 保 Jordan 的实现合同；实际门另供应 |
| 原 Born 概率 | 完整行评价线性 $+$ 原轨道闭包为球面 | 所有原标签须保留 |
| 全部有限维代数 | 相容二元中心图、交换生成、角与直和 | 同一个联合内的配对与实际支持返回 |
| CP 与一般仪器 | 同一原分支线性 $+$ 完整矩阵参考的联合保正 | 全联合正锥、原记录、全态归一 |
| Lüders 更新 | CP、投影效果、全部支撑态不扰动 | 理想不扰动不能省略 |
| 连续 Schrödinger 形式 | 连续 CPTP 群与 CP 逆 | 物理时间、$H$、$\hbar$ 数值 |
| 固定原 $D$ 的准确识别 | 项目 C127 原零配对、协变、单尺度与全背景 | 中心、参考、原对象与原过程不重选 |

本轮已给有限理论的完整数学构造和条件定理；没有推出任意无限维量子场、相对论时空、粒子谱、具体相互作用或现实实验满足所有前件。每个缺口在上表有具体对象，而非用一句“还有假设”笼统遮盖。

**与先前 $\zeta$ 零点问题的关系。**

本文的“零”是原线性作用的固定核，$\zeta(s)=0$ 是解析函数的零点。目前没有把本轮 $\mathfrak g,W$ 与 $\zeta$ 的解析延拓、谱或零点位置对应起来的定理。因此本候选没有推出临界线结论；离线零点也不能未经桥梁就称为它的反例。仓库首页仍明确区分未闭合的 O-5/O-6 与已证结论，并未宣称证明 RH。 [13](#ref-reporeadme)

## 一段完整白话

先把整体里能被未来问题区别的内容摆出来，再看整体自己允许哪些变化。在轻轻改动内容也不会突然多出可动方向的位置，找一份内容和一种非零变化：能不动这份内容的变化只有这一种，能被这变化留下的内容也只有这一份，只差大小的算同一方向。这一对关系先让内容和变化有同样多的方向；变化还必须能接着做、反着做，并比较交换先后的差，完整关系最后就只剩三个方向。两份内容接合时，重合的部分由点积记录，次序的差由面积记录；如果保留这份对称内容，又要求同一对东西反复接合时换括号不改结果，面积系数再作用一次就必须反号，复数便从三维结构自己的取向线中长出来。这个结合实现唯一，随后给出两分量振幅和平方概率。多个局部块接起来时，只需在连接它们的树上逐对对齐虚单位，沿其他闭环回来不能自相矛盾；相容后就得到共同的复矩阵结构。完整参考、全部记录与实际过程接上，便得到有限量子理论；哪些态真能制备、什么门真能实施、原来的变化转得多快，都继续由同一个整体中的原数据检验。

<a id="references"></a>

## 参考文献

<a id="ref-repocompare"></a>

### [1]

trureturing，固定比较，
[006 首稿至本继续稿](https://github.com/the-omega-institute/trureturing/compare/1764a0c7f33be6acf6dcaf4ad4007da021469ae9...2c54932b6f9a7eb9a838e5be71e91d97e10027be)。

<a id="ref-repog"></a>

### [2]

trureturing，Giacomelli 初值锥收缩，
[固定正文](https://github.com/the-omega-institute/trureturing/blob/2c54932b6f9a7eb9a838e5be71e91d97e10027be/docs/develop/theory/GIACOMELLI_INFINITE_LOG_CONCAVITY_CONE_CONTRACTION.md)，含零完整初值锥的准确范围。

<a id="ref-repo127"></a>

### [3]

trureturing，C123–C127，
[固定正文](https://github.com/the-omega-institute/trureturing/blob/2c54932b6f9a7eb9a838e5be71e91d97e10027be/docs/develop/theory/AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md)，尤其 §§21–40。

<a id="ref-repo117"></a>

### [4]

trureturing，C117，
[固定正文](https://github.com/the-omega-institute/trureturing/blob/2c54932b6f9a7eb9a838e5be71e91d97e10027be/docs/develop/theory/AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md)，尤其 §§17–24。

<a id="ref-repofib"></a>

### [5]

trureturing，FIB Appendix III，
[固定正文](https://github.com/the-omega-institute/trureturing/blob/2c54932b6f9a7eb9a838e5be71e91d97e10027be/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_III.md)，尤其 §§145–151。

<a id="ref-repo113"></a>

### [6]

trureturing，C113，
[固定正文](https://github.com/the-omega-institute/trureturing/blob/2c54932b6f9a7eb9a838e5be71e91d97e10027be/docs/develop/theory/AURIC_INTERNAL_BALANCED_CALIBRATION_AND_FILTER_COMPOSITION_GEOMETRY_C113.md)，尤其 §§36–48。

<a id="ref-repofour"></a>

### [7]

trureturing，Fourpath Continuation III，
[固定正文](https://github.com/the-omega-institute/trureturing/blob/2c54932b6f9a7eb9a838e5be71e91d97e10027be/docs/develop/theory/QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_III.md)。

<a id="ref-donaldson"></a>

### [8]

S. K. Donaldson，*Lectures on Lie groups and geometry*，
[作者讲义](https://wwwf.imperial.ac.uk/~skdona/Liegroups/LIEGROUPSFINAL.PDF)，§2.2 与命题 15。共伴随辛形式与秩一辛球面论证为成熟结果。

<a id="ref-baez"></a>

### [9]

J. C. Baez，*The Octonions*，Bull. Amer. Math. Soc. 39 (2002)，145–205，
[作者全文](https://math.ucr.edu/home/baez/octonions/)。

<a id="ref-niestegge"></a>

### [10]

G. Niestegge，*Dynamical Correspondence in a Generalized Quantum Theory*，
[arXiv:1402.0158v2](https://arxiv.org/html/1402.0158v2)，§4 引理 3。

<a id="ref-bgw"></a>

### [11]

H. Barnum、M. A. Graydon、A. Wilce，
*Composites and Categories of Euclidean Jordan Algebras*，
[arXiv:1606.09331v3](https://arxiv.org/pdf/1606.09331v3)，摘要、pp. 14–15 及复合结构讨论。

<a id="ref-watrous"></a>

### [12]

J. Watrous，*The Theory of Quantum Information*，
[第 2 章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)，尤其定理 2.22。

<a id="ref-reporeadme"></a>

### [13]

trureturing，
[固定 README](https://github.com/the-omega-institute/trureturing/blob/2c54932b6f9a7eb9a838e5be71e91d97e10027be/README.md)，“What is proved, and what is open”。
