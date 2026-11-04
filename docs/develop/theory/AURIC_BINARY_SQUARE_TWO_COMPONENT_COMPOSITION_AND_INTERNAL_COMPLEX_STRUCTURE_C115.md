**AURIC 量子关系研究续篇**

# 二元平方、两分量接续 与内生复结构

**候选 C115：同一关系的拆法与合法合成必须相容**

**本轮核心定理**

在明确的欧氏二元比较块中，若对称读出与有向变化必须在同一个两分量空间内结合地接续，则非经典方向空间只能是三维，连接两部分的中央标记必须平方为负。三个实方向的有序体积

$$
J=e_1e_2e_3,\qquad J^2=-1
$$

随后把复数、二分量振幅和泡利代数一起构造出来。概率由所有效果上的拆并一致性推出；复合系统的相位对齐用一个明确的双扇区反例检验。

**本轮推进的边界**

这是已有 Jordan–Lie、Clifford、效果概率及有限量子操作理论的一次局部化、重组和自足推导。我们给出完整的有限维候选及其承重条件，不声称自然界从“整体存在”一句话被唯一推出，也不把工作稿编号当作仓库已合并版本。

**项目核读范围**

2026 年 11 月 3 日重新核读仓库公开首页与局部相关盲区源码。首页指向 `dev`，但最新提交 SHA 与 AURIC 理论主卷端点未取得。故本稿承接已交付的 C113、C114，并使用本轮可见源码，不冒称已覆盖最新 HEAD 的全部内容。这里是纸笔证明，未运行 Lean 认证或提交仓库。

2026 年 11 月 3 日  C115 研究工作稿

## 目录

- [1. 从项目边界提出本轮问题](#section-1)
- [2. 二元原子的维数与复结构锁定](#section-2)
- [3. 由实关系闭包内生复数与二分量振幅](#section-3)
- [4. 关系的关系：复合系统必须对齐内部复中心](#section-4)
- [5. 由效果的二元拆并推出 Born 概率](#section-5)
- [6. 几何：有向球面、相位圆与内部运输](#section-6)
- [7. 从重构代数到完整的有限操作理论](#section-7)
- [8. 理想测量更新：把 C113 的选择条件补齐](#section-8)
- [9. 有限维后果：干涉、不确定性与 Bell 相关](#section-9)
- [10. 完整候选 C115 及有限维重构结论](#section-10)
- [11. 完整白话描述](#section-11)
- [参考文献](#references)

<a id="section-1"></a>

## 1. 从项目边界提出本轮问题

本轮可核读的仓库把“哪些对象在现有读口下不可区分”作为寻找下一条关系的出发点。其局部相关盲区源码给出 Bell 纯态与经典相关混合态：两者在两个子系统上具有相同边缘，却有不同整体相关；一般的 $m\times n$ 模型还给出相关子空间维数 $(m^2-1)(n^2-1)$ [1](#ref-repo)、[2](#ref-repo-blind)。这提示我们：不要只给局部形状，还要规定各关系怎样组成同一整体。

本轮与前稿的衔接很具体。C113 在同一效果与同一操作分支的约束下，用有限均衡比较选出平方根滤片；C114 证明递归二元正性与全体有限 Gram 矩阵正性等价，并用零空间商构造 Hilbert 实现 [3](#ref-c113)、[4](#ref-c114)。C114 仍明确使用共同复结构，并对制备的密度重心等价作了说明。本稿向前移动这两个接口：先由实的二元接续推出局部复结构，再由效果拆并推出线性概率和密度表示。

### 定义 1.1（本稿中“内生”的可检验含义）

以 $\Omega$ 表示包含对象、制备记录、效果记录和操作记录的总结构。观察者也在其中。选出的有限读口只访问其中一个带类型的子结构。说一条公理内生，意指它写成这些内部对象及内部操作之间的约束式，例如

$$
(xy)z=x(yz),\quad w(E+F)=w(E)+w(F),\quad J_A=J_B,
$$

并对同一有限实验中的两种表示给出可比较的结果。

**约束来自内部对象，不等于约束无需选择。** 把一组条件合称一个定义，可以消除含混术语，却不能证明每个任意的 $\Omega$ 都满足它。交换代数、实矩阵代数及本稿的复矩阵代数都能成为自洽整体。我们的任务是给出一个量子子结构的准确定义，证明它推出什么，再逐条检查删掉条件会放进什么反模型。物理世界是否实现它，属于额外的经验与建模问题。

本稿只提出一个完整候选 C115。它的局部核心可以先用一句话表达：

> 同一对内容的比较，分成交换顺序不变的相合部分和交换顺序反向的变化部分；两部分必须在同一个有限比较空间中封闭接续，而且括号、效果拆并及独立参考的加入，不能使同一关系获得互相矛盾的结果。

接下来每个词都有定义、定理或反例；最后会列明完整候选仍含哪些独立条件。

### 1.1 把“圆”放到准确的关系坐标中

原二次式 $q_x(a,b)=a^2+xab+b^2$ 满足

$$
q_2=(a+b)^2.
$$

所以在实 $(a,b)$ 系数平面中，$q_2=1$ 是两条平行线。真正适合本轮几何的圆是

$$
(a^2-b^2)^2+(2ab)^2=(a^2+b^2)^2.
$$

写 $s=a^2+b^2$、$Z=a^2-b^2$、$X=2ab$，则

$$
q_x=s+\frac{x}{2}X,
$$

即原交叉项在关系坐标 $X$ 中成为线性读出。复振幅再提供

$$
s=|a|^2+|b|^2,\quad
 X=2\Re(\bar a b),\quad Y=2\Im(\bar a b),\quad
 Z=|a|^2-|b|^2,
$$

并满足 $X^2+Y^2+Z^2=s^2$。本轮不把复振幅当作最初输入，而是在后文先构造代数，再得到这张三维关系球。

**白话。**圆不是凭一个系数取特殊值就出现的。先把“两份内容各有多少”与“它们怎样相合”分开，原来弯曲的平方关系就变成更高一层关系空间里的直读口。下一步要追问：这张关系图除了能被读，还能否按顺序接续；正是接续的相容性进一步固定了三维和复数方向。

<a id="section-2"></a>

## 2. 二元原子的维数与复结构锁定

从对称读出与有向变化恢复结合乘法，属于已有的 Jordan–Lie 与动力学对应研究路线 [5](#ref-alfsen)。本节给出它在一个二元比较块上的初等约化：不预设关系球的维数，也不先选择复数，而让明确的合成闭合条件同时约束二者。该结论的范围是下面定义的二元块，并不把任意高维系统都假定成一个球。

### 2.1 把合成条件完整写出来

### 定义 2.1（二元比较块与有向变化）

令 $W$ 为有限维实内积空间，$n=\dim W$，并令

$$
V=\mathbb R 1\oplus W,\qquad
 V_+=\{\alpha1+a:\alpha\ge\|a\|\}.
$$

取对称双线性运算

$$
S(\alpha1+a,\beta1+b)
 =(\alpha\beta+\langle a,b\rangle)1+\alpha b+\beta a.
$$

因此 $S(1,x)=x$，且 $S(a,a)=\|a\|^2 1$。正锥、单位元与这项平方运算是本节的结构前提；仅说“有一个球”不能省去对运算的规定。

有向变化为双线性映射 $D:W\times W\to W$，写作 $D_ab=D(a,b)$，满足

$$
\langle D_ab,d\rangle=-\langle b,D_ad\rangle,\qquad D_aa=0.
$$

将它延伸到 $V$ 时规定 $D(1,x)=D(x,1)=0$。

第一条表示固定标签产生的无穷小变化保持内积；第二条表示该变化不改变自己的生成方向。这里包含对标签的线性性。对 $D_{a+b}(a+b)=0$ 极化，得到

$$
D_ab=-D_ba.
$$

结合反对称算子条件，$T(a,b,d)=\langle D_ab,d\rangle$ 是完全交替三形式。特别地，$D_ab$ 同时正交于 $a,b$。

这里 $S$ 的公式也可由“对称双线性、单位作用、纯方向平方”三项定义极化得到，而无需逐个给定乘法表。固定标签的 $D_a$ 反对称，等价于线性流 $e^{tD_a}$ 保持欧氏内积；这不是仅要求任意非线性轨迹留在球面上。代入 $S$ 的公式还可验证

$$
D_a S(x,y)=S(D_ax,y)+S(x,D_ay),
$$

因为两个标量内积项相消。所以有向变化自动是对称比较的导子。

### 定义 2.2（同一空间中的二分量闭合）

对暂未确定的 $s\in\mathbb R$，令

$$
F_s=\mathbb R[j]/(j^2-s),\qquad
 \mathcal A_s=V\otimes_{\mathbb R}F_s=V\oplus jV.
$$

$j$ 与全部对象交换。规定有序比较乘法在实对象上为

$$
x\star y=S(x,y)+jD(x,y),
$$

再按 $F_s$ 双线性延伸到 $\mathcal A_s$。要求实际纳入模型的有序比较合成由这个乘法表示，并且

$$
(x\star y)\star z=x\star(y\star z)
 \qquad(x,y,z\in\mathcal A_s).
$$

这项要求同时含有**表示、闭合、结合**三层内容：反对称部分必须是同一个中央标记 $j$ 乘同一个比较空间中的对象。一般过程复合具有结合律，并不自动证明新定义的 $S+jD$ 就是该复合。允许进入任意更大的结合包络，也不足以替代这里的闭合要求。标量 $s<0,s=0,s>0$ 分别覆盖复数型、对偶数型与分裂复数型；此时尚未选择其中任何一种。

这份实两分量结构还自带一个伴随运算：

$$
(x+jy)^*=x-jy,\qquad x,y\in V.
$$

它在实比较对象上为恒等，在中央标记上取负。由于 $S$ 对称、$D$ 反对称，实对象满足
$(x\star y)^*=S(x,y)-jD(x,y)=y\star x$；按两分量展开后，同式推广为 $(ab)^*=b^*a^*$，且 $(a^*)^*=a$。所以后面使用自伴方向无需另加一次选择。

### 2.2 两个方向迫出第三个，第四个又被排除

### 定理 2.3（二元块的维数与标量类型锁定）

<a id="thm-c115-dimension"></a>

在上述条件下，若 $n\ge2$，则

$$
\boxed{n=3,\qquad s<0.}
$$

选定三维取向后，存在非零实常数 $c$，使

$$
D_ab=c\,a\times b,\qquad sc^2=-1.
$$

反之，三维叉积与 $sc^2=-1$ 给出满足这些条件的结合代数，且该代数同构于 $M_2(\mathbb C)$。若 $n=0$ 或 $1$，则 $D=0$，不由本定理强迫复数型标量。

**证明。**
以下为简洁省略乘号 $\star$。任选正交单位向量 $u,v\in W$，令 $w=D_uv$。前述交替性给 $w\perp u,v$，而乘法定义给

$$
u^2=v^2=1,\qquad uv=jw,\qquad vu=-jw.
$$

结合律使同一四项合成满足

$$
1=u(v^2)u=(uv)(vu)=-s\,w^2=-s\|w\|^2 1.
$$

因此 $-s\|w\|^2=1$，从而 $s<0$、$w\ne0$。两个独立方向确实带出第三个独立方向，且此后 $j$ 可逆。

若 $z\in W$ 同时正交于 $u,v,w$，其对称乘积为零，因而

$$
zu=-uz,\qquad zv=-vz,\qquad zw=-wz.
$$

但结合律又给

$$
z(uv)=(zu)v=-u(zv)=u(vz)=(uv)z.
$$

代入 $uv=jw$ 并约去可逆的中央 $j$，得到 $zw=wz$。两式合并得 $zw=0$。由于 $w^2=\|w\|^2 1$ 可逆，故 $z=0$。所以 $W=\operatorname{span}\{u,v,w\}$，维数恰为三。

在三维空间中，交替三形式只有一维，因此
$\langle D_ab,d\rangle=c\,\langle a\times b,d\rangle$，即 $D_ab=c\,a\times b$。对正交单位 $u,v$，刚才的等式变为 $-sc^2=1$。后续命题给出完整结合子公式，直接证明反向结合性。映射 $1\mapsto I_2$、取向正交基 $e_k\mapsto\sigma_k$、$j\mapsto iI_2/c$ 保持乘法；其像实线性张成 $M_2(\mathbb C)$，两边实维数均为八，故为代数同构。

当 $n\le1$，交替双线性映射 $D$ 为零；$S$ 分别给出平凡标量块或经典二元块的结合乘法。因而前述非经典结论不能扩展到这两个边界。

### 说明 2.4（无需再加旋转协变）

三维分类只用了标签线性、内积保持和自身不变。它已经推出同一个常数 $c$，因此对保持取向的旋转之协变是结果。若删掉标签线性，则
$D_ab=(1+\|a\|^2)a\times b$ 仍逐标签保持内积、自身方向并满足旋转协变，却不具有统一的线性生成律。

### 2.3 尺度由一个准确的结合子锁定

### 命题 2.5（完整乘法与结合子）

在三维中，对任意实数 $s,c$ 使用上述叉积运算，则

<a id="eq-c115-product"></a>

$$
(\alpha1+a)\star(\beta1+b)
 =(\alpha\beta+\langle a,b\rangle)1+\alpha b+\beta a+jc(a\times b).
\tag{1}
$$

其结合子精确等于

$$
(x\star y)\star z-x\star(y\star z)
 =(1+sc^2)\bigl(\langle a,b\rangle d-\langle b,d\rangle a\bigr),
$$

其中 $x=\alpha1+a$、$y=\beta1+b$、$z=\gamma1+d$。因此结合性当且仅当 $sc^2=-1$。

**证明。**
含单位元的结合子为零，故只需计算 $a,b,d\in W$。两边的 $j$ 标量项分别为
$jc\,\langle a\times b,d\rangle$ 与 $jc\,\langle a,b\times d\rangle$，相等而抵消。其余差为

$$
\langle a,b\rangle d-\langle b,d\rangle a
 +sc^2\bigl((a\times b)\times d-a\times(b\times d)\bigr).
$$

向量三重积恒等式使括号等于前面两项之差，得到公式。选取正交单位 $a=b=e_1,d=e_2$，结合子为 $(1+sc^2)e_2$，故必要性与充分性同时成立。

锁定之后，中央元素 $cj$ 的平方为负一；若先选 $j^2=-1$，则 $c=\pm1$，其符号表示取向。这里固定的是**对称读出与有向变化的相对尺度**，没有推出物理时间单位或 $\hbar$ 的数值。对于单位方向 $a,b$，还有

$$
\langle a,b\rangle^2+\|a\times b\|^2=1.
$$

所以同一个有序二元关系的对称部分与有向部分组成精确的圆；交换顺序只改变有向部分的符号。

### 2.4 删除条件后会发生什么

### 例 2.6（更大的结合包络不能代替二分量闭合）

实对称二阶矩阵构成一个 $n=2$ 的比较块。取

$$
A=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
 B=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

它们在 $M_2(\mathbb R)$ 中当然可以结合地相乘，但
$AB=\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$ 是额外的反对称矩阵。它不属于原比较空间，也不能由该二维空间内的 $D$ 按上述中央二分量形式封闭表示。因此本定理没有声称实量子理论不存在结合矩阵表示。

### 例 2.7（错误标量符号给出明确括号矛盾）

固定三维 $D_ab=c\,a\times b$。若 $s=0$ 或 $s>0$，则

$$
(e_1\star e_1)\star e_2=e_2,
 \qquad e_1\star(e_1\star e_2)=-sc^2e_2,
$$

不可能相等。对偶数型与分裂复数型被排除的是这一组正定比较和闭合条件；结论不涉及任意其他代数模型。

### 例 2.8（只保留对称读出不能选定有序乘法）

同一个三维正锥和 $S$ 同时容许 $S+i(a\times b)$ 与 $S-i(a\times b)$ 两个相反乘法。它们的平方与对称读出完全相同，顺序却相反。若连有向部分都删去，只剩 $S$，仍有合法 Jordan 比较结构，却有
$S(S(e_1,e_1),e_2)=e_2$、$S(e_1,S(e_1,e_2))=0$。所以有向信息承担真实内容，不能只用对称读出重新命名出来。

**白话。**两份内容既有相合多少，也有按哪个方向接过去。要求所有接续始终只用这两部分，而且先合哪两项不能改变最终结果，两个独立方向就必须带出第三个方向；再加第四个独立方向却会让接续规则互相冲突。对称份量和有向份量的尺度也被同时锁定，连接它们的标记必须平方为负一。这是在明确闭合条件下得到的二元量子原子；更大整体如何拼接，仍要继续满足 C114 的递归相容条件。

<a id="section-3"></a>

## 3. 由实关系闭包内生复数与二分量振幅

本节取前节得到的三维欧氏方向空间，并固定正向基
$e_1,e_2,e_3$。我们先只使用实数：设 $\mathcal A$ 是由这些方向生成的非零含幺实结合代数，
方向元自伴，且对称乘积满足

<a id="eq-c115-clifford"></a>

$$
e_i^*=e_i,\qquad
 e_ie_j+e_je_i=2\delta_{ij}1.
\tag{2}
$$

这里的结合律作用于包含有序关系的乘法闭包；它并不要求可观测量的对称乘积本身结合。
式 [(2)](#eq-c115-clifford) 是三维欧氏对称关系的准确表达，
其中尚未放入复数矩阵或二维复向量。

### 定理 3.1（实关系闭包的唯一代数）

<a id="thm-c115-algebra"></a>

在上述条件下，$J=e_1e_2e_3$ 是中心元，
$J^2=-1$、$J^*=-J$。
子代数 $\mathbb C_J=\mathbb R[J]$ 是内生的复数域，每个元素唯一写成

$$
a=\alpha1+z_1e_1+z_2e_2+z_3e_3,\qquad
 \alpha,z_i\in\mathbb C_J.
$$

因此 $\mathcal A$ 的实维数为八，并作为实结合 $*$-代数同构于
$M_2(\mathbb C)$。其自伴部分恰为
$\mathbb R1\oplus\mathbb R^3$。

**证明。**
不同方向元反交换，而 $e_i^2=1$。把任意 $e_i$ 穿过其余两个方向元，
符号改变两次，故 $J$ 与每个生成元交换，从而属于中心。直接换序得到

$$
J^2=(-1)^3e_1^2e_2^2e_3^2=-1,\qquad
 J^*=e_3e_2e_1=-J.
$$

还必须证明这个复数方向不会在代数中塌缩。若 $r+sJ=0$，
乘以 $r-sJ$ 得
$(r^2+s^2)1=0$。非零含幺实代数中的非零实标量可逆，
因此 $r=s=0$。于是

$$
\mathbb R[t]/(t^2+1)\longrightarrow\mathcal A,\qquad t\longmapsto J
$$

是单射；其像 $\mathbb C_J$ 确实是一个复数域，而非仅有形式名称的符号。

任意生成词都能先按下标排序，再用 $e_i^2=1$ 消去重复方向。
剩下的八种词又满足

$$
e_1e_2=Je_3,\qquad e_2e_3=Je_1,\qquad e_3e_1=Je_2.
$$

所以每个元素具有定理中的形式。这只证明了张成，尚须证明独立性。
对该形式直接计算，有

$$
\sum_{i=1}^{3}e_i a e_i
 =3\alpha1-\sum_{i=1}^{3}z_ie_i.
$$

因此可从元素本身提取它的标量系数：

<a id="eq-c115-scalar-extraction"></a>

$$
\alpha1=\frac14\left(a+\sum_{i=1}^{3}e_i a e_i\right).
\tag{3}
$$

令 $v=a-\alpha1$，再利用反交换关系，得到逐项提取公式

<a id="eq-c115-vector-extraction"></a>

$$
z_i1=\frac12(e_iv+ve_i),\qquad i=1,2,3.
\tag{4}
$$

若某个上述展开等于零，式 [(3)](#eq-c115-scalar-extraction)
先给出 $\alpha=0$，式 [(4)](#eq-c115-vector-extraction)
再给出全部 $z_i=0$；这里使用了已经证明的 $\mathbb C_J$ 单射性。
故四个复方向独立，实维数恰为八。

现在才把内部的 $J$ 记作通常的 $i$。映射

<a id="eq-c115-pauli-map"></a>

$$
\alpha1+z\cdot e\longmapsto
 \begin{pmatrix}
  \alpha+z_3&z_1-iz_2\\
  z_1+iz_2&\alpha-z_3
 \end{pmatrix}
\tag{5}
$$

由
$e_ie_j=\delta_{ij}1+\epsilon_{ijk}Je_k$
可知保持乘法。任意复二阶矩阵都能唯一拆成右边的形式，
所以这是双射。它也保持伴随：

$$
(\alpha1+z\cdot e)^*=\bar\alpha1+\bar z\cdot e.
$$

唯一展开遂表明，自伴元恰是 $\alpha,z_i$ 都为实数的元素。

这一定理说明复结构能由闭包中的关系构成。它没有证明实际自然界必定选择这种闭包；
三维欧氏对称关系与结合的有序乘法仍是候选的实质条件。
反转三维取向会把 $J$ 换成 $-J$，对应复共轭约定。

### 3.1 从最小左理想构造振幅空间

令

$$
p=\frac{1+e_3}{2},\qquad q=e_1p,\qquad H=\mathcal A p.
$$

则 $p^2=p=p^*$。由反交换关系，

$$
pe_1p=0,\qquad
 e_1p=q,\qquad e_2p=Jq,\qquad e_3p=p.
$$

定理的唯一展开说明 $H$ 由 $p,q$ 在 $\mathbb C_J$ 上张成。
对于
$x=\alpha p+\beta q$ 与 $y=\gamma p+\delta q$，直接相乘得到

<a id="eq-c115-left-ideal-inner"></a>

$$
x^*y=(\bar\alpha\gamma+\bar\beta\delta)p.
\tag{6}
$$

定义
$\langle x,y\rangle=\bar\alpha\gamma+\bar\beta\delta$。
它在第一变量共轭线性，在第二变量线性，且
$\langle x,x\rangle=|\alpha|^2+|\beta|^2$。
这里 $p\ne0$：否则 $e_3=-1$，由
$e_1e_3+e_3e_1=0$ 得 $e_1=0$，与 $e_1^2=1$ 矛盾。
因此若 $\alpha p+\beta q=0$，
式 [(6)](#eq-c115-left-ideal-inner) 迫使 $\alpha=\beta=0$。
这同时证明了基的独立性和内积的正定性，故

$$
H\cong\mathbb C^2.
$$

代数通过左乘作用于 $H$。这一作用忠实：若 $aH=0$，
则 $ap=0$、$ae_1p=0$；而
$1-p=e_1pe_1$，所以 $a(1-p)=0$，最终 $a=0$。
在基 $p,q$ 中，左乘 $e_1,e_2,e_3$ 的矩阵分别是

$$
\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
 \begin{pmatrix}0&-J\\J&0\end{pmatrix},\qquad
 \begin{pmatrix}1&0\\0&-1\end{pmatrix}.
$$

因此二分量复振幅与泡利矩阵是从实代数关系构造出的表示。
任意非零向量可由某个二阶矩阵送到任意目标向量，
故 $H$ 没有非平凡左子模，确为最小左理想。

### 3.2 正锥、球与平方读出

对于自伴元 $a=s1+x\cdot e$，有
$(x\cdot e)^2=\|x\|^2 1$。若 $r=\|x\|>0$，设

$$
p_\pm=\frac12\left(1\pm\frac{x\cdot e}{r}\right).
$$

它们是互相正交的自伴投影，且

$$
a=(s+r)p_++(s-r)p_-.
$$

在刚刚构造的忠实 Hilbert 表示中，两项系数就是特征值，
因此

$$
a\ge0\ \Longleftrightarrow\ s\ge\|x\|,
 \qquad
 \det(a)=s^2-\|x\|^2.
$$

$r=0$ 时同样由 $a=s1$ 得到该结论。
正性也可在代数内检查：系数非负时
$\sqrt{s+r}\,p_++\sqrt{s-r}\,p_-$ 是自伴平方根；
反之任何 $b^*b$ 的 Hilbert 读出都非负。

定义通常的迹 $\operatorname{Tr}(\alpha1+z\cdot e)=2\alpha$，
则归一化状态元恰为

$$
\rho_r=\frac12(1+r\cdot e),\qquad \|r\|\le1.
$$

单位球面上的 $p_n=(1+n\cdot e)/2$ 是纯状态和秩一锐效应。
自伴空间 $\mathcal A_{\mathrm{sa}}$ 上正的归一化实线性状态泛函具有形式

$$
\omega_r(s1+x\cdot e)=s+r\cdot x,\qquad \|r\|\le1.
$$

证明很直接：自伴空间上的任意归一化线性泛函都具有左式形式；
在正元 $1+n\cdot e$ 上非负迫使 $\|r\|\le1$，
而这个界与 $s\ge\|x\|$ 又保证所有正元的读出非负。
所以

$$
\omega_r(p_n)=\frac{1+r\cdot n}{2}
              =\operatorname{Tr}(\rho_rp_n).
$$

把纯状态和秩一效应写入 $H$，便得到

$$
\operatorname{Tr}\!\left(
 \lvert \psi\rangle\langle \psi\rvert\,\lvert \phi\rangle\langle \phi\rvert
 \right)=|\langle \phi,\psi\rangle|^2.
$$

平方律由表示中的秩一分解推出；把正的归一化线性泛函解释为实验概率，
仍须明确作为理论的操作性要求。

**五模式的候选翻译。**

可以暂将 $F[\mathrm{null}]$ 对应单位及归一化角色，
$F[1],F[3],F[2]$ 分别对应 $e_1,e_3,e_2$，
而有序关系 $F[1,3]$ 对应
$e_1e_3=-Je_2$。
这只是待核的候选编码，并非仓库原生定义已认证的等价；
尤其最后一项属于有序乘法闭包，不能直接当作另一独立自伴轴。

<a id="section-4"></a>

## 4. 关系的关系：复合系统必须对齐内部复中心

局部构造完成后，还存在一个可精确展示的整体问题：
每个子系统各自拥有 $J$，并不自动意味着它们共享同一个复数方向。

### 定理 4.1（实复合的双扇区及其消除）

<a id="thm-c115-center"></a>

把 $\mathcal A=\mathcal B=M_2(\mathbb C)$ 视为实代数，则

$$
\mathcal A\otimes_\mathbb R\mathcal B
 \cong M_4(\mathbb C)\oplus M_4(\mathbb C).
$$

令 $J_A=J\otimes1$、$J_B=1\otimes J$，
则 $Z=-J_AJ_B$ 是满足 $Z^2=1$ 的中心自伴元。
要求 $J_A=J_B$，等价于选择 $Z=1$ 的扇区，
其商代数恰为通常的复张量积 $M_4(\mathbb C)$。

**证明。**
在已构造的矩阵表示中，定义实线性映射

<a id="eq-c115-real-tensor-split"></a>

$$
\Phi(a\otimes b)=
 \bigl(a\otimes_\mathbb C b,\ a\otimes_\mathbb C\bar b\bigr),
\tag{7}
$$

其中横线表示逐项共轭。共轭保持实线性、乘法及伴随，
因此 $\Phi$ 是含幺实 $*$-同态。计算得

$$
\Phi(J_A)=(iI,iI),\qquad
 \Phi(J_B)=(iI,-iI),\qquad
 \Phi(Z)=(I,-I).
$$

$J_A,J_B$ 交换且各自平方为 $-1$、伴随为其负值，
故 $Z^*=Z$、$Z^2=1$。于是

$$
P_\pm=\frac{1\pm Z}{2}
$$

是中心投影，其像分别为 $(I,0)$ 与 $(0,I)$。
复矩阵张量 $a\otimes_\mathbb C b$ 张成全部 $M_4(\mathbb C)$；
乘以 $P_+$ 可独立取得第一分量，乘以 $P_-$
可独立取得第二分量。因此 $\Phi$ 满射。
其源实维数为 $8\cdot8=64$，目标实维数为
$32+32=64$，所以它也是单射。

在此分解下，$J_A-J_B$ 对应 $(0,2iI)$。
它生成的理想恰为第二个直和分量，故令 $J_A-J_B=0$
得到的商代数就是第一个 $M_4(\mathbb C)$。
由 $J_A^2=-1$ 还可直接验证：
$J_A=J_B$ 当且仅当 $-J_AJ_B=1$。

### 4.1 删去中心对齐后，所有局部乘积读出仍可能相同

在直和代数的自伴元上，定义两个状态

$$
\omega_+(X,Y)=\frac{\operatorname{Tr} X}{4},\qquad
 \omega_-(X,Y)=\frac{\operatorname{Tr} Y}{4}.
$$

它们都是正的归一化泛函；若需写在一般元上，可取迹的实部作实线性延拓。
对任意局部自伴元 $a,b$，

$$
\begin{aligned}
 \omega_+\!\left(\Phi(a\otimes b)\right)
 &=\frac{\operatorname{Tr}(a)\operatorname{Tr}(b)}4,\\
 \omega_-\!\left(\Phi(a\otimes b)\right)
 &=\frac{\operatorname{Tr}(a)\operatorname{Tr}(\bar b)}4
  =\frac{\operatorname{Tr}(a)\operatorname{Tr}(b)}4.
 \end{aligned}
$$

最后一步使用自伴矩阵的迹为实数。
所以两个状态在全部局部乘积读出及其线性组合上完全相同。
然而

$$
\omega_+(Z)=1,\qquad\omega_-(Z)=-1,
 \qquad
 \omega_+(P_+)=1,\quad\omega_-(P_+)=0.
$$

整体中心效应可以完美区分它们。这个反例准确指出：
局部量子球及实结合乘法，尚未保证整体能由全部局部乘积统计确定。
统一内部复中心，消除的正是这里显式出现的额外扇区。
这一操作性问题与复合系统的局部层析要求相呼应，
但这里的双扇区结论由上面的代数计算独立证明。 [6](#ref-barnumwilce)

### 4.2 有限复合的范围

若各子系统在联合代数中相互交换、共享同一个 $J$，
且联合代数由这些子系统生成，乘法就给出复张量积到联合代数的满同态。
对 $N$ 个上述二元系统，其源为

$$
M_2(\mathbb C)^{\otimes_\mathbb C N}\cong M_{2^N}(\mathbb C).
$$

这是单代数，含幺同态的核不可能为整个代数，也就只能为零。
这里的单性可用矩阵单位直接验证：
任一非零双边理想中的非零矩阵，经左右乘矩阵单位可取得一个非零标量倍的矩阵单位，
再缩放及左右相乘即可取得全部矩阵单位。
因此联合代数确实是标准复矩阵张量积。

这一结论直接覆盖维数 $2^N$。要覆盖任意有限维数 $d$，
还需允许取投影支持的受限子系统：
当 $d\le2^N$、投影 $p$ 的秩为 $d$ 时，

$$
pM_{2^N}(\mathbb C)p\cong M_d(\mathbb C),
$$

其单位是 $p$。允许这种角代数作为系统是一项明确的闭包要求；
无限维完备化、连续时间及具体动力学仍不由本节的有限代数结论自动给出。

<a id="section-5"></a>

## 5. 由效果的二元拆并推出 Born 概率

<a id="sec-c115-effects"></a>

前面的代数计算说明何种对象可以充当效果，但尚未假设实验概率是迹配对。本节给出这一环节的独立条件与完整有限维证明。它属于在所有广义效果上赋概率的 Gleason 型路线，二维系统也适用 [7](#ref-busch)。

### 定义 5.1（效果与拆并一致的状态）

在已构造的 $\mathcal A=M_d(\mathbb C)$ 中，效果集合为

$$
\mathcal E_d=\{E=E^*:0\le E\le I\}.
$$

一次有限测量是一组效果 $E_k$，满足 $\sum_kE_k=I$。
把互斥的两个结果合并，表示为效果之和 $E+F$；此操作只在 $E,F\ge0$ 且 $E+F\le I$ 时定义。

一个状态首先仅是函数 $w:\mathcal E_d\to[0,1]$，满足

<a id="eq-c115-effect-add"></a>

$$
w(I)=1,\qquad w(E+F)=w(E)+w(F)
 \quad(E,F\ge0, E+F\le I).
\tag{8}
$$

同一代数效果在不同测量分解中使用同一个 $w(E)$。我们明确要求这一效果表示与实验读口一致，而不只要求各个二结果实验分别归一化。

最后一句是承重条件：$E,F$ 可以是三结果测量
$\{E,F,I-E-F\}$ 的前两个结果。原始合并始终是二元操作，但必须允许这种较大上下文。仅有 $w(E)+w(I-E)=1$ 不足。定义也没有假设各次测量预先拥有确定的结果值。

### 定理 5.2（二元效果拆并确定密度表示）

<a id="thm-c115-born"></a>

满足式 [(8)](#eq-c115-effect-add) 的函数，与密度矩阵一一对应：存在唯一

$$
\rho\ge0,\qquad \operatorname{Tr}\rho=1
$$

使得对所有效果 $E$，

$$
\boxed{w(E)=\operatorname{Tr}(\rho E).}
$$

该结论对每个有限 $d\ge1$ 成立，不需另加连续性假设。

**证明。**
取 $E=F=0$ 得 $w(0)=0$。若 $0\le E\le F\le I$，则
$F=E+(F-E)$，所以 $w(E)\le w(F)$。
将效果 $E$ 分成 $n$ 份给出
$w(E/n)=w(E)/n$，继而对 $r\in[0,1]\cap\mathbb Q$ 有
$w(rE)=rw(E)$。对任意实数 $t\in[0,1]$，用趋近 $t$ 的上下有理数夹逼，借助单调性得

$$
w(tE)=t\,w(E).
$$

对任意正矩阵 $A$，选 $u>0$ 且 $u\ge\|A\|$，定义

$$
W(A)=u\,w(A/u).
$$

若改选较大的 $v$，由 $A/v=(u/v)(A/u)$ 的齐次性知定义不变；两个任意选择可与共同更大者比较，所以 $W$ 良定义。
给 $A,B\ge0$ 选择 $u\ge\|A+B\|$，则

$$
W(A+B)=u\,w(A/u+B/u)=W(A)+W(B).
$$

同理 $W(tA)=tW(A)$，$t\ge0$。

每个自伴矩阵都能写成 $X=A-B$，$A,B\ge0$。定义
$L(X)=W(A)-W(B)$。若还有 $X=C-D$，则 $A+D=C+B$，正锥上的可加性保证两种定义相同。故 $L$ 是自伴空间上的实线性正泛函，$L(I)=1$。

实双线性形式 $(X,Y)\mapsto\operatorname{Tr}(XY)$ 在自伴空间上正定且非退化；选一个正交基即可构造唯一自伴矩阵 $\rho$，使 $L(X)=\operatorname{Tr}(\rho X)$。
对于任意单位向量 $v$，

$$
\langle v,\rho v\rangle=L(\lvert v\rangle\langle v\rvert)\ge0,
$$

故 $\rho\ge0$；$L(I)=1$ 给出 $\operatorname{Tr}\rho=1$。
反过来，这样的 $\rho$ 显然在每个效果上给出 $[0,1]$ 内的值，并满足拆并规则。唯一性来自迹配对的非退化性。

### 推论 5.3（纯态、混合与平方律）

全部状态的极点恰为秩一投影。纯制备 $\rho=\lvert \psi\rangle\langle \psi\rvert$ 对锐效果 $P_\phi=\lvert \phi\rangle\langle \phi\rvert$ 的概率为

$$
p(\phi\mid\psi)=|\langle \phi,\psi\rangle|^2.
$$

随机混合状态的概率函数，对应相同权重的密度矩阵混合；两种制备分解若密度重心相同，则所有效果读出相同。

**证明。**
若密度矩阵秩至少二，可在其两个正特征值之间加减同一个充分小的 $\epsilon$，把它写成两个不同密度矩阵的平均，因此不极端。
若 $P_\psi=t\rho_1+(1-t)\rho_2$，$0<t<1$，对所有 $v\perp\psi$ 的非负二次型相加为零，故两矩阵均只支持在 $\mathbb C\psi$ 上；归一化于是迫使 $\rho_1=\rho_2=P_\psi$。
平方律直接由秩一矩阵相乘和取迹得到。混合与制备等价由定理的唯一迹表示得到。

这使 C114 中显式的密度重心制备等价变成当前效果条件的后果。我们没有先把纯态上的任意概率分布按密度重心商掉，再声称从“仿射”推出这个商；那样会把关键条件藏在状态定义里。

### 例 5.4（只归一化仍允许错误的三次读出）

写一个二阶效果为 $E=\alpha I+b\cdot\sigma$。
效果条件等价于

$$
\|b\|\le\min(\alpha,1-\alpha)\le\tfrac12.
$$

定义

$$
\widetilde w(E)=\alpha+4b_z^3.
$$

因为 $|4b_z^3|\le|b_z|\le\min(\alpha,1-\alpha)$，它确实位于 $[0,1]$；又有

$$
\widetilde w(I-E)=1-\widetilde w(E),\qquad
 \widetilde w(tI)=t.
$$

但令 $P_z=(I+\sigma_z)/2$，则

$$
\widetilde w(P_z)=1,\qquad
 \widetilde w(P_z/2)=\frac5{16},\qquad
 2\widetilde w(P_z/2)=\frac58\ne1.
$$

同一效果拆成两份再合并就改变概率。这精确指出二元拆并条件排除了什么。

**白话。**概率不能因为记账时把同一结果拆成两格而改变。只要每个合法效果都遵守这件事，概率就被迫对效果线性。前面从关系接续得到的复代数，再把这种线性评价表示成密度矩阵与效果的配对；对两个纯方向，这个配对自然就是振幅内积的模平方。平方律因此有了完整的来路，但“同一效果跨分解同读”仍是明确承担内容的条件。

<a id="section-6"></a>

## 6. 几何：有向球面、相位圆与内部运输

<a id="sec-c115-geometry"></a>

前文的三轴闭合给出一个最小二能级代数。本节使用已经证明的效果赋值形式，说明它的球面、切向、相位和滤片几何；这些结论不另为 Born 证明增加前提。量子理论的这种几何表达与 Hamiltonian、Killing 结构的联系已有系统研究 [8](#ref-ashtekar)，以下系数和符号均按本稿约定直接计算。

### 6.1 球面与切平面的四分之一转动

写

$$
\rho_r=\frac{I+r\cdot\sigma}{2},\qquad
 P_n=\frac{I+n\cdot\sigma}{2},\qquad |n|=1.
$$

$\rho_r$ 的本征值为 $(1\pm|r|)/2$，故状态对应闭球 $|r|\le1$，纯态对应球面 $S^2$。由前文效果赋值定理和 Pauli 迹恒等式，

<a id="eq-c115-bloch-born"></a>

$$
\boxed{p(n\mid r)=\operatorname{Tr}(\rho_rP_n)=\frac{1+r\cdot n}{2}.}
\tag{9}
$$

这条公式先来自效果的相容赋值，再成为球面上的几何读数。

### 命题 6.1（内生的切平面复结构）

在有向单位球面上，对 $v\in T_rS^2$ 定义

$$
\mathcal J_rv=r\times v,\qquad
 \omega_0{}_r(v,w)=r\cdot(v\times w).
$$

则 $\mathcal J_r^2=-I$，且对单位球度量 $g_0$ 有
$\omega_0(v,w)=g_0(\mathcal J_rv,w)$。

**证明。**
切向条件为 $r\cdot v=0$，故
$r\times(r\times v)=r(r\cdot v)-v=-v$。
第二式是标量三重积恒等式。

这里 $\mathcal J_r$ 作用在各点的二维切平面上。它把一个微小变化转为同一切平面内的正交变化；球面上的三坐标仍只有两个独立自由度。

### 命题 6.2（归一化振幅与相位圆）

归一化振幅 $\psi\in\mathbb C^2$ 构成 $S^3$，映射
$\psi\mapsto\psi\psi^*$ 的像为上述纯态球面。每条纤维恰为
$\{e^{i\chi}\psi:\chi\in\mathbb R\}$，因此

$$
S^3/U(1)\cong\mathbb{CP}^1\cong S^2.
$$

**证明。**
同一秩一投影的两个单位生成向量必然相差单位复数。反过来，每个

$$
r=(\sin\theta\cos\phi,\sin\theta\sin\phi,\cos\theta)
$$

都由

$$
\psi_N(\theta,\phi)=
 \begin{pmatrix}\cos(\theta/2)\\e^{i\phi}\sin(\theta/2)\end{pmatrix}
$$

实现，直接代入外积即可验证。

### 6.2 距离、曲率与概率的平方

### 定理 6.3（固定归一约定下的射影度量）

对 $r,n\in S^2$，定义

$$
ds_{\mathrm{FS}}^2=\langle d\psi,d\psi\rangle
                   -|\langle \psi,d\psi\rangle|^2.
$$

则

<a id="eq-c115-fs"></a>

$$
\boxed{ds_{\mathrm{FS}}^2
 =\frac14\bigl(d\theta^2+\sin^2\theta\,d\phi^2\bigr).}
\tag{10}
$$

其 Gaussian 曲率为 $4$。两条射线的最短距离满足

$$
d_{\mathrm{FS}}(r,n)=\frac12\arccos(r\cdot n)
 =\arccos|\langle \psi_r,\psi_n\rangle|,
 \qquad p(n\mid r)=\cos^2 d_{\mathrm{FS}}(r,n).
$$

**证明。**
由显示的 $\psi_N$，
$\langle \psi,d\psi\rangle=i\sin^2(\theta/2)d\phi$。
代入度量定义，$d\phi^2$ 系数为
$\sin^2(\theta/2)\cos^2(\theta/2)=\sin^2\theta/4$，得到式
[(10)](#eq-c115-fs)。度量为单位圆球度量的四分之一，距离减半、曲率变为四倍。最后结合式 [(9)](#eq-c115-bloch-born) 和半角恒等式。

相应的 Kähler 形式是 $\omega_{\mathrm{FS}}=\omega_0/4$。因此必须区分单位 Bloch 球的角距离和射影距离；后者是前者的一半。

**同一有向代数中的半角转动。**

以内部 $J$ 写出

$$
U_n(\theta)=\cos(\theta/2)1-J(n\cdot e)\sin(\theta/2).
$$

因为 $(n\cdot e)^2=1$、$J^*=-J$，直接相乘得 $U_n^*U_n=1$。
代入 $e_ie_j=\delta_{ij}1+\epsilon_{ijk}Je_k$，有

$$
U_n(r\cdot e)U_n^*
 =\bigl(r\cos\theta+(n\times r)\sin\theta
       +n(n\cdot r)(1-\cos\theta)\bigr)\cdot e.
$$

这就是三维轴角转动。所有行列式为一的二阶酉矩阵都写成
$a1-Jb\cdot e$，$a,b$ 实且 $a^2+|b|^2=1$，故构成 $S^3$。
上面的共轭给出 $SU(2)\to SO(3)$ 的满同态；其核必须同时与三个轴交换，故是标量 $\pm1$。
因此 $2\pi$ 转动把振幅算子变号，$4\pi$ 才回到自身。
这里的旋转双覆盖、固定一个纯态的旋转稳定子，以及作用在振幅上的中央整体相位圆，是相关但不同的对象，不能混成同一个动作。

### 6.3 局部相位、曲率通量与回路

本节固定实联络的符号约定

$$
A=-i\psi^*d\psi.
$$

在上述北规范中直接得到

<a id="eq-c115-berry"></a>

$$
\boxed{A_N=\frac{1-\cos\theta}{2}d\phi,\qquad
 F=dA_N=\frac12\sin\theta\,d\theta\wedge d\phi
       =\frac12\omega_0=2\omega_{\mathrm{FS}}.}
\tag{11}
$$

南规范取 $\psi_S=e^{-i\phi}\psi_N$，于是
$A_S=A_N-d\phi=-(1+\cos\theta)d\phi/2$；两者的曲率一致。

### 命题 6.4（相位不能在全球平滑选成同一截面）

上述曲率满足 $\int_{S^2}F=2\pi$，因而该相位圆丛没有全局光滑截面。

**证明。**
积分式 [(11)](#eq-c115-berry) 得通量 $2\pi$。若存在全局光滑归一化向量截面，$A=-i\psi^*d\psi$ 就是球面上的全局一形式，Stokes 定理将给 $\int_{S^2}dA=0$，矛盾。

这是同一整体内各个局部相位坐标之间的接续性质，并不要求本体之外另有一个相位来源。

对提升 $\Psi=e^{i\gamma}\psi$，联络变为 $d\gamma+A$。水平运输要求
$d\gamma=-A$。因此沿闭环 $C$，在跨越曲面上相容地使用局部规范，得到

<a id="eq-c115-holonomy"></a>

$$
\boxed{\operatorname{Hol}(C)
 =\exp\left(-i\int F\right)
 =\exp(-i\mathcal A_C/2),}
\tag{12}
$$

其中 $\mathcal A_C$ 为有向立体角。跨越曲面改变所带来的 $4\pi$ 立体角差不改变该相位。

结合律保持同一有序乘积的括号等价；改变实际路径或先后顺序则改变了流程。因而非零回路相位与同一流程的内部相容性同时成立。

### 例 6.5（三条关系的方向检查）

取
$\psi_z=(1,0)^T$、$\psi_x=(1,1)^T/\sqrt2$、
$\psi_y=(1,i)^T/\sqrt2$。有

$$
B_{zxy}=\langle \psi_z,\psi_x\rangle\langle \psi_x,\psi_y\rangle
          \langle \psi_y,\psi_z\rangle=\frac{1+i}{4}.
$$

沿大圆短弧 $z\to x\to y\to z$ 行走，有向立体角为 $\pi/2$，故
$\operatorname{Hol}=e^{-i\pi/4}=e^{-i\arg B_{zxy}}$。
因此在本稿的回路次序和联络约定下，Bargmann 积的相位与水平运输相位符号相反。

### 6.4 同一读口也是转动方向

令归一化二元平均读数为 $f_n(r)=2p(n\mid r)-1=n\cdot r$，
单位角速度场为 $X_n(r)=n\times r$。对任意切向变化 $v$，

$$
\omega_0(X_n,v)
 =r\cdot[(n\times r)\times v]
 =n\cdot v=df_n(v).
$$

所以已经推导的读数满足

<a id="eq-c115-reciprocity"></a>

$$
\boxed{df_n=\iota_{X_n}\omega_0
 =2\iota_{X_n}F=4\iota_{X_n}\omega_{\mathrm{FS}}.}
\tag{13}
$$

式 [(13)](#eq-c115-reciprocity) 是效果赋值与球面结构的后果。若反过来把它当作候选条件，连同一个端点标定，也能在连通球面上唯一确定 $f_n=n\cdot r$；那是另一条条件重构路线。仅要求同轴和自守恒则不够，例如 $(n\cdot r)^3$ 也在绕 $n$ 的转动中不变。

若 $H=h_0I+h\cdot\sigma$，则

$$
\dot r=\frac2\hbar h\times r,\qquad
 \Omega_{\mathrm{phys}}=\hbar F=\frac\hbar2\omega_0,
 \qquad \iota_{X_H}\Omega_{\mathrm{phys}}=d(h_0+h\cdot r).
$$

这同时固定了读数、角速度与物理时间的系数；$F$、$\omega_0$ 和
$\omega_{\mathrm{FS}}$ 各自保留上述尺度。

### 6.5 滤片的 Lorentz 几何与圆的投影

未归一化正表写为 $Q=(sI+r\cdot\sigma)/2$，其正性等价于
$s\ge|r|$。在这个四实维锥上，定义线性生成算子

$$
\mathsf L_n(s,r)=(n\cdot r,sn),\qquad
 \mathsf J_n(s,r)=(0,n\times r).
$$

它们分别由正滤片 $e^{tn\cdot\sigma/2}$ 的合同作用，以及酉转动
$e^{-itn\cdot\sigma/2}$ 的共轭作用产生。直接代入并用向量三重积得到

$$
[\mathsf J_u,\mathsf J_v]=\mathsf J_{u\times v},\qquad
 [\mathsf J_u,\mathsf L_v]=\mathsf L_{u\times v},\qquad
 [\mathsf L_u,\mathsf L_v]=-\mathsf J_{u\times v}.
$$

这是线性生成算子的交换子。它把 C113 中不同方向滤片接续所产生的极酉转动，放到一个明确的无穷小几何结构中。正滤片作为实际成功分支时，还须乘上满足 $K^*K\le I$ 的尺度；锥上的一般增益并不都能作为确定过程。

沿 $\mathsf L_n$ 的流，$\frac{d}{dt}(s^2-|r|^2)=2s(n\cdot r)-2r\cdot(sn)=0$，所以它保持 Lorentz 二次型与未来正锥；归一化截面 $s=1$ 则一般不保持。转动 $\mathsf J_n$ 同时保持 $s$ 与 $|r|$。这准确区分滤片和归一化球内的可逆运动。

对于 $|n|=1$、$|r(0)|=1$，固定方向 $n$ 的转动满足

$$
r(t)=cn+u\cos(\nu t)+(n\times u)\sin(\nu t),\quad
 c=n\cdot r(0),\quad u=r(0)-cn.
$$

轨迹是平面 $n\cdot r=c$ 中的圆；除不动点外，仅 $c=0$ 时为球面测地线。任意线性二维读出把该圆变为椭圆，允许退化成线段或点。因此椭圆可以是圆在受限读口中的像。仅有历史切线、平滑性和任意目标态，还不能唯一选定轨迹或推出椭圆；需要进一步给定生成元、控制规律或变分准则。

**白话。**一个二元纯态对应球面上的一点。选定一个方向，既能读出它沿该方向的份量，也能沿同一方向组织内部转动。局部相位像贴在球面上的坐标，绕一圈以后可以留下可计算的相位差；所有接续仍在同一个整体内。圆和椭圆的差别取决于运动规律与读口。

<a id="fig-c115-circles"></a>

```latex
\begin{tikzpicture}[>=Latex, font=\small]
\begin{scope}[shift={(2.4,0)}]
  \node[font=\bfseries] at (0,2.2) {有序关系中的圆};
  \draw[teal!75!black,thick] (0,0) circle (1.38);
  \draw[->,gray] (-1.65,0)--(1.8,0) node[right] {$C$};
  \draw[->,gray] (0,-1.65)--(0,1.73) node[above] {$T$};
  \coordinate (p) at (0.887,1.057);
  \draw[->,very thick,teal!75!black] (0,0)--(p);
  \draw[dashed,gray] (p)--(0.887,0) (p)--(0,1.057);
  \fill[teal!75!black] (p) circle (0.045);
  \draw[->] (0.43,0) arc (0:50:0.43);
  \node at (0.57,0.23) {$\theta$};
  \node[align=center,text width=6cm] at (0,-2.22)
    {$C=a\cdot b=\cos\theta$\quad $a\times b=Tn$\par
     $C^2+T^2=1$，\quad $AB=C1+JT(n\cdot e)$};
\end{scope}
\begin{scope}[shift={(10.1,0)}]
  \node[font=\bfseries] at (0,2.2) {归一化关系中的球};
  \fill[teal!5] (0,0) circle (1.38);
  \draw[teal!75!black,thick] (0,0) circle (1.38);
  \draw[dashed,gray] (-1.38,0) arc (180:0:1.38 and 0.42);
  \draw[gray] (-1.38,0) arc (180:360:1.38 and 0.42);
  \draw[->,gray] (0,-1.58)--(0,1.74) node[above] {$n$};
  \draw[teal!75!black,dashed] (-1.071,0.829) arc (180:0:1.071 and 0.326);
  \draw[teal!75!black,thick,->] (-1.071,0.829) arc (180:345:1.071 and 0.326);
  \coordinate (r) at (1.071,0.829);
  \draw[->,thick] (0,0)--(r) node[right] {$r$};
  \fill[black] (r) circle (0.045);
  \node[align=center,text width=6cm] at (0,-2.22)
    {$|r|=1$，\quad $p(n\mid r)=(1+n\cdot r)/2$\par
      同轴转动保持读数；图示为球面的投影。};
\end{scope}
\end{tikzpicture}
```

**图 1。**左：单位方向的对称份量与有向份量组成圆。右：纯态关系球上，固定读口的等读数集合是纬圆。两个圆来自不同对象，分别由代数乘法和归一化状态几何确定。

<a id="section-7"></a>

## 7. 从重构代数到完整的有限操作理论

本节在已经重构的有限复矩阵扇区 $\mathcal A=M_d(\mathbb C)$ 上工作；复合系统沿用前节给定的独立合成接口。以下把读出、过程、记录与运动的承重条件分别写明。它们构成完整的有限操作模型，而具体实验实际供应哪些准备、效果和过程，仍由其操作菜单确定。

定理 [5.2](#thm-c115-born) 已给出全部效果的概率表示。其自伴实线性泛函有唯一复线性延拓
$\omega(X+iY)=L(X)+iL(Y)$，$X,Y$ 自伴；在矩阵表示中即 $\omega(A)=\operatorname{Tr}(\rho A)$。
自伴量 $A=\sum_k a_kP_k$ 对应以谱投影 $P_k$ 为效果、以 $a_k$ 为结果值的测量，期望为 $\operatorname{Tr}(\rho A)$。
以下不再重证 Born 形式，而补齐过程与连续时间的条件。

### 7.1 内部参考正性决定允许过程的形式

确定过程保持经典混合。若其在归一化状态上为仿射映射 $\Phi$，则对 $X\ge0$ 定义

$$
\widehat\Phi(X)=(\operatorname{Tr} X)\Phi\bigl(X/\operatorname{Tr} X\bigr)\quad(X\ne0),
 \qquad \widehat\Phi(0)=0.
$$

用 $\operatorname{Tr}(X+Y)$ 分解混合权重可知该映射加性、正齐次，因而唯一延伸为 Hermitian 矩阵上的实线性映射，再复线性延伸。以下仍记为 $\Phi$。有结果分支时，要求仿射的是**保留成功权重的输出**，不能先把每个成功分支归一化再要求其线性。

### 定义 7.1（任意有限内部参考下的正性）

物理过程 $\Phi:M_d(\mathbb C)\to M_m(\mathbb C)$ 为线性映射，并要求对每个有限 $r\ge1$，

$$
(\Phi\otimes\operatorname{id}_{M_r})(X)\ge0\qquad(X\ge0).
$$

参考与被操作部分同属内部模型；量词包含它们的全部联合正态，不只包含积态。确定过程保迹，选择性分支不增迹。这就是完全正性及其相应归一条件。

### 定理 7.2（内部参考正性与 Kraus 表示）

<a id="thm-c115-kraus"></a>

上述完全正性当且仅当存在有限矩阵 $K_\mu:\mathbb C^d\to\mathbb C^m$，使

$$
\Phi(X)=\sum_\mu K_\mu X K_\mu^*.
$$

过程的效果为 $E_\Phi=\sum_\mu K_\mu^*K_\mu$。保迹等价于 $E_\Phi=1$，不增迹等价于 $E_\Phi\le1$。

**证明。**
固定未归一化向量 $\lvert \Omega_d\rangle=\sum_{i=1}^d\lvert i,i\rangle$，并采用输出因子在前的约定：

$$
C_\Phi=(\Phi\otimes\operatorname{id}_{M_d})(\lvert \Omega_d\rangle\langle \Omega_d\rvert)
 =\sum_{i,j}\Phi(\lvert i\rangle\langle j\rvert)\otimes\lvert i\rangle\langle j\rvert\ge0.
$$

将其谱分解写成 $C_\Phi=\sum_\mu\lvert v_\mu\rangle\langle v_\mu\rvert$，把本征值平方根吸收进 $v_\mu$，并定义

$$
\lvert v_\mu\rangle=\sum_{a=1}^m\sum_{i=1}^d(K_\mu)_{ai}\lvert a,i\rangle.
$$

比较每个输入矩阵单位的系数，得到
$\Phi(\lvert i\rangle\langle j\rvert)=\sum_\mu K_\mu\lvert i\rangle\langle j\rvert K_\mu^*$，从而得到公式。反向，接上任意参考后每项仍是 $K_\mu\otimes1$ 的正合同变换。最后
$\operatorname{Tr}\Phi(X)=\operatorname{Tr}(XE_\Phi)$；对全部正 $X$ 检验便得到迹条件。

### 例 7.3（单系统正性漏掉的负权重）

转置 $\Theta(X)=X^{\mathsf T}$ 在一个系统上正且保迹。对 Bell 投影
$P=\lvert \beta\rangle\langle \beta\rvert$、$\lvert \beta\rangle=(\lvert 00\rangle+\lvert 11\rangle)/\sqrt2$，却有

$$
(\Theta\otimes\operatorname{id})(P)=\frac12\mathsf F,
 \qquad
 \mathsf F\frac{\lvert 01\rangle-\lvert 10\rangle}{\sqrt2}
 =-\frac{\lvert 01\rangle-\lvert 10\rangle}{\sqrt2},
$$

其中 $\mathsf F$ 交换两个因子。因此扩展后的矩阵有本征值 $-1/2$。这说明为什么参考延伸是有内容的相容条件。

### 7.2 仪器、条件化与内部记录

### 定义 7.4（量子仪器）

仪器是有限完全正分支族 $\{\mathcal I_k\}$，其和为保迹映射。写

$$
\mathcal I_k(X)=\sum_\mu K_{k\mu}XK_{k\mu}^*,\qquad
 E_k=\sum_\mu K_{k\mu}^*K_{k\mu},\qquad \sum_kE_k=1.
$$

则结果概率和成功后态分别为

$$
p_k=\operatorname{Tr}(\rho E_k),\qquad
 \rho_k=\frac{\mathcal I_k(\rho)}{p_k}\quad(p_k>0).
$$

概率为零的分支不定义条件后态。

合并一组结果时使用 $\mathcal I_B=\sum_{k\in B}\mathcal I_k$；经典随机选择两个过程时使用 $t\Phi+(1-t)\Psi$。二者都保持完全正性。合并已记录结果是分支映射的和，不把不同记录的 Kraus 振幅直接相加为一个相干分支。

全部结果可以用内部正交记录实现。算子

$$
V\psi=\sum_{k,\mu}K_{k\mu}\psi\otimes\lvert k,\mu\rangle
$$

满足 $V^*V=1$，故为等距映射。读取记录 $k$ 得到相应分支，忽略记录得到总通道。有限多个这样的步骤可继续接续，所需结果和未读信息都保留在更大的内部描述中。

**概率不唯一决定后态。** 对同一个效果 $E$，$K=U\sqrt E$ 对任意酉 $U$ 都满足 $K^*K=E$，却通常改变成功后态。因此本节没有从正性推出唯一的 Lüders 更新。平方根实现 $\sqrt E\rho\sqrt E$，以及投影时的 $P\rho P$，仍须由 C113 的附加理想滤片选择条件指定。

### 7.3 双向合法的运动必为酉运动

### 定理 7.5（同维可逆通道的唯一形式）

设 $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ 为保迹完全正映射，且有保迹完全正逆 $\Psi$。则存在酉矩阵 $U$，使

$$
\Phi(X)=UXU^*.
$$

**证明。**
设两个通道的 Kraus 算子为 $K_a,L_j$。复合 $\Psi\Phi=\operatorname{id}$ 的 Kraus 算子为 $L_jK_a$。恒等通道的 Choi 矩阵是秩一矩阵 $\lvert \Omega_d\rangle\langle \Omega_d\rvert$；正的秩一矩阵的每个向量和分解都使用同一条射线。因此

$$
L_jK_a=c_{ja}1.
$$

至少有一项 $c_{j_0a_0}\ne0$，所以同维方阵 $L_{j_0},K_{a_0}$ 均可逆。固定 $j_0$ 后，全部 $K_a$ 都与 $K_{a_0}$ 成比例，故可把 $\Phi$ 合成单 Kraus 形式 $AXA^*$。保迹给 $A^*A=1$，同维使 $A$ 为酉矩阵。

### 定理 7.6（连续群的 Hamiltonian 形式）

若这些可逆通道构成连续单参数群 $\Phi_{t+s}=\Phi_t\Phi_s$、$\Phi_0=\operatorname{id}$，则存在自伴 $H$，使

$$
\Phi_t(X)=e^{-itH/\hbar}Xe^{itH/\hbar}.
$$

因此 $\dot\rho=-i[H,\rho]/\hbar$；选择相容的纯态代表后，$i\hbar\dot\psi=H\psi$。

**证明。**
有限维连续单参数线性群可在单位元附近取矩阵对数，再由群律扩展，写为 $\Phi_t=e^{t\mathcal L}$。每个 $\Phi_t$ 都是保持乘法和伴随的自同构，求导得到

$$
\mathcal L(XY)=\mathcal L(X)Y+X\mathcal L(Y),\qquad
 \mathcal L(X^*)=\mathcal L(X)^*.
$$

令 $E_{ij}=\lvert i\rangle\langle j\rvert$，并取
$A=\sum_i\mathcal L(E_{i1})E_{1i}$。对
$E_{kl}E_{i1}=\delta_{li}E_{k1}$ 求导，再右乘 $E_{1i}$ 并求和，得

$$
\mathcal L(E_{kl})=AE_{kl}-E_{kl}A.
$$

所以 $\mathcal L=[A,\cdot]$。伴随相容性迫使 $A+A^*$ 与全部矩阵交换，故 $A+A^*=\lambda1$，$\lambda\in\mathbb R$。令 $A_0=A-\lambda1/2$，则 $A_0^*=-A_0$。任取正的单位换算常数 $\hbar$，$H=i\hbar A_0$ 自伴，并有 $\mathcal L=-i[H,\cdot]/\hbar$。积分即得结论。

这是运动*形式*的重构。连续群、具体生成元和时间标尺仍是运动结构；证明没有给出 $\hbar$ 的数值。$H$ 加上实常数倍单位元不改变通道，对纯态只改变共同相位。

### 7.4 C114 的关系核成为同一内部模型的推论

原始历史标签保留在 $\Omega$ 中，每个标签具有操作表示；以下为简洁将其表示仍写作 $h\in\mathcal A$。对同一正归一读出 $\omega$ 定义

$$
K(h,k)=\omega(h^*k).
$$

任意有限系数 $z_i$ 都满足

$$
\sum_{i,j}\bar z_i z_jK(h_i,h_j)
 =\omega\left(\left(\sum_i z_i h_i\right)^*
                    \left(\sum_j z_j h_j\right)\right)\ge0.
$$

因此该关系表自动半正定。这正好接回 C114 的递归相容结构 [4](#ref-c114)：任意已合成历史与新历史继续比较时，仍属于同一个正核。

具体地，两个合成 $u,v$ 给出

$$
G=\begin{pmatrix}p&c\\\bar c&q\end{pmatrix}\ge0,
 \quad p=\omega(u^*u),\ q=\omega(v^*v),\ c=\omega(u^*v).
$$

当 $t=p+q>0$ 时，它的归一化三维关系为

$$
\mathbf r=\frac{(2\Re c,-2\Im c,p-q)}t,
 \qquad \|\mathbf r\|\le1.
$$

这里按 Gram 表的上右项定义 $c$，故第二坐标取负号；与振幅外积坐标比较时要同时转换这个约定。当 $t=0$ 时正性迫使整块为零。任意有限二元合成都继承同一规则，而不是只验证原始标签的两两比较。

令 $N=\{u:\omega(u^*u)=0\}$。二阶正性给
$|\omega(u^*v)|^2\le\omega(u^*u)\omega(v^*v)$，故 $N$ 中对象与所有比较对象的关系为零。于是比较空间商去 $N$ 后具有正定内积

$$
\langle [u],[v]\rangle=\omega(u^*v).
$$

本节是有限矩阵情形，该商有限维并且完备；有限标签表的最小实现维数为 $\operatorname{rank}K$。商去的是这一比较结构看不见的差异，**不是删除 $\Omega$ 中的原始来源或合成历史**。不同历史仍可有不同标签与接续信息，只是在所给读出接口下暂时不可区分。

**白话。**同一份内容可以产生结果，也可以带着结果继续接下去。结果合并时概率必须相加；把过程接到任何内部参考上，都不能出现负的份量。这两项要求把允许的过程固定成 Kraus 形式。若过程连逆过程都合法，就只能整体酉转动；连续接续时便写成 Hamiltonian 运动。每条历史与其他历史的比较则自动组成正核，因此之前逐层检查的三维球约束成为同一个模型内持续成立的关系。理想测量怎样更新内容，仍由额外的滤片选择规定，不能只从结果概率猜出来。

<a id="section-8"></a>

## 8. 理想测量更新：把 C113 的选择条件补齐

概率本身不能选定测后状态。即使效果 $E$ 相同，
$\rho\mapsto\sqrt E\rho\sqrt E$ 与
$\rho\mapsto U\sqrt E\rho\sqrt E U^*$ 也可给出相同的成功概率。
因此候选必须另行说明哪一种实现叫“理想滤片”。以下重述并证明 C113 使用的有限均衡比较条件 [3](#ref-c113)。

### 定义 8.1（有限均衡比较与理想滤片）

令 $P_s=\lvert \psi_s\rangle\langle \psi_s\rvert$ 为有限组纯态，$w_s>0$、$\sum_sw_s=1$，满足

$$
\sum_sw_s P_s\otimes P_s=\frac{I+F}{d(d+1)},
$$

其中 $F(u\otimes v)=v\otimes u$。给定同一个效果 $E$，在满足
$\sum_aK_a^*K_a=E$ 的同一个 CP 分支
$T(X)=\sum_aK_aXK_a^*$ 中，定义平均保留量

$$
R(T)=\sum_sw_s\operatorname{Tr}[P_sT(P_s)].
$$

称达到这个约束下最大 $R$ 的分支为本候选的理想实现。

这是一项精确的选择准则，不是将“最少扰动”当作未经定义的形容词。
有限比较组总能构造：以总权重 $1/(d+1)$ 均匀取标准基向量，再以总权重 $d/(d+1)$ 均匀取所有

$$
\frac1{\sqrt d}(z_1,\ldots,z_d),\qquad z_k\in\{1,i,-1,-i\}.
$$

令 $D_0=\sum_i\lvert ii\rangle\langle ii\rvert$。独立四次单位根平均使平坦向量组的二阶矩为 $(I+F-D_0)/d^2$，基向量组的二阶矩为 $D_0/d$；代入这两个总权重，$D_0$ 项抵消，恰得 $(I+F)/[d(d+1)]$。重复的同一射线可以合并权重，不影响该等式。

### 定理 8.2（同一效果的理想滤片唯一为平方根分支）

<a id="thm-c115-luders"></a>

对 $0\le E\le I$，上述最大保留量为

$$
\max R(T)=\frac{\operatorname{Tr} E+(\operatorname{Tr}\sqrt E)^2}{d(d+1)},
$$

且达到最大值的 CP 映射唯一为

$$
\boxed{T_E(X)=\sqrt E\,X\sqrt E.}
$$

若 $E=P$ 为投影，条件化后的状态是 $P\rho P/\operatorname{Tr}(\rho P)$；分母为零时不定义这一条件分支。

**证明。**
二阶矩公式给出

$$
R(T)=\frac{\operatorname{Tr} E+\sum_a|\operatorname{Tr} K_a|^2}{d(d+1)}.
$$

设 $L=\sqrt E$，在其非零支持上选正交特征基 $\lvert i\rangle$，特征值为 $\lambda_i>0$。
因为 $\sum K_a^*K_a=E$，每个 $K_a$ 在 $\ker E$ 上为零，可写
$K_a=A_aL$，其中 $\sum A_a^*A_a=P_{\operatorname{Ran} E}$。
定义向量 $v_i=(\langle i,A_a i\rangle)_a$。则

$$
\|v_i\|^2\le\sum_a\|A_a\lvert i\rangle\|^2=1,
 \qquad (\operatorname{Tr} K_a)_a=\sum_i\lambda_i v_i.
$$

三角不等式于是给出

$$
\sum_a|\operatorname{Tr} K_a|^2
 =\left\|\sum_i\lambda_i v_i\right\|^2
 \le\left(\sum_i\lambda_i\right)^2.
$$

取 $K_1=L$ 达到此界。

若达到等号，由全部 $\lambda_i>0$，每个 $v_i$ 必须是同一个单位向量 $c=(c_a)_a$。
投影不等式也必须取等号，所以
$A_a\lvert i\rangle=c_a\lvert i\rangle$，从而 $K_a=c_aL$。
$\sum_a|c_a|^2=1$，故这些 Kraus 算子给出的映射恰是 $X\mapsto LXL$。
若 $E=0$，所有 $K_a=0$，同一结论仍成立。

**白话。**同样亮起一个结果，并不说明内部做了同样的事。把一组有限且均衡的纯方向逐个送进去，在成功概率固定的前提下比较它们还能保留多少；唯一保留最多的实现，就是平方根滤片。这样，读出规则和理想更新规则各有自己的约束，不会把测量后的变化偷偷混进概率公式。

<a id="section-9"></a>

## 9. 有限维后果：干涉、不确定性与 Bell 相关

<a id="sec-c115-consequences"></a>

前面的结构条件还给出可以直接计算的预测。本节只使用已经构造的状态、效果、复合和正过程，不再增加概率规则。

### 命题 9.1（干涉由内部记录的重叠控制）

取归一化内部记录 $\eta_0,\eta_1$，以及 $|a|^2+|b|^2=1$，令

$$
\lvert \Psi\rangle=a\lvert 0\rangle\otimes\lvert \eta_0\rangle
            +b\lvert 1\rangle\otimes\lvert \eta_1\rangle,\qquad
 \gamma=\langle \eta_0,\eta_1\rangle.
$$

只对路径系统读取
$\lvert +_\phi\rangle=(\lvert 0\rangle+e^{i\phi}\lvert 1\rangle)/\sqrt2$，则

$$
\boxed{p_+(\phi)
 =\frac12\left[1+2\Re\left(e^{-i\phi}\bar a b\gamma\right)\right].}
$$

同一记录给出完整交叉项；正交记录使该局部读数恒为 $1/2$。

**证明。**
将 $\langle +_\phi\rvert\otimes I$ 作用于联合向量，得到
$(a\eta_0+e^{-i\phi}b\eta_1)/\sqrt2$。成功概率是它的平方范数，展开即得公式。

因此可读干涉对比度为 $2|ab\gamma|$。当 $\gamma=0$ 时，联合态仍可保持纯态；局部读口缺少了读取联合交叉关系的能力。这里两份记录都位于同一个整体内，无需另设本体之外的环境。

### 定理 9.2（同一二元正性给出不确定关系）

对密度矩阵 $\rho$ 和自伴 $A,B$，记

$$
\Delta A=A-\operatorname{Tr}(\rho A)I,\qquad
 \Delta B=B-\operatorname{Tr}(\rho B)I.
$$

则

$$
\begin{aligned}
\operatorname{Var}_\rho(A)\operatorname{Var}_\rho(B)
 \ge{}&
 \left(\frac12\operatorname{Tr}\rho\{\Delta A,\Delta B\}\right)^2
 +\frac14\left|\operatorname{Tr}\rho[A,B]\right|^2.
\end{aligned}
$$

**证明。**
在 Hilbert–Schmidt 内积中取
$u=\Delta A\sqrt\rho$、$v=\Delta B\sqrt\rho$。
二元 Gram 正性，即 Cauchy–Schwarz 不等式，给出

$$
\operatorname{Var}_\rho(A)\operatorname{Var}_\rho(B)
 \ge|\operatorname{Tr}(\rho\Delta A\Delta B)|^2.
$$

右侧复数的实部是对称协方差，虚部是
$\operatorname{Tr}\rho[A,B]/(2i)$；分开平方即得结论。证明对奇异 $\rho$ 和零方差也成立。

### 定理 9.3（CHSH 界与可达例）

设局域锐二值可观测量满足
$A_i=A_i^*$、$A_i^2=I$，以及 $B_j=B_j^*$、$B_j^2=I$。
定义

$$
C=A_0\otimes(B_0+B_1)+A_1\otimes(B_0-B_1).
$$

对每个联合态 $\rho$ 都有 $|\operatorname{Tr}(\rho C)|\le2\sqrt2$，且两个二元系统已经能达到此界。

**证明。**
直接展开，利用不同系统的算子交换，得到

$$
C^2=4I-[A_0,A_1]\otimes[B_0,B_1].
$$

各局域算子范数为一，故两个交换子的范数各不超过二。因此
$\|C\|^2=\|C^2\|\le8$，从而得到任意状态上的上界。

取

$$
\lvert \Phi\rangle=\frac{\lvert 00\rangle+\lvert 11\rangle}{\sqrt2},\qquad
 A_0=\sigma_z,\quad A_1=\sigma_x,\qquad
 B_{0,1}=\frac{\sigma_z\pm\sigma_x}{\sqrt2}.
$$

此时 $C=\sqrt2(\sigma_z\otimes\sigma_z+\sigma_x\otimes\sigma_x)$，
而 $\Phi$ 同时是括号内两项本征值为一的本征态，故读数为 $2\sqrt2$。

若四个局域输出可以同时预赋为数 $a_i,b_j\in\{-1,1\}$，对应表达式的绝对值恒为二，随机混合后仍不超过二。上述可达值展示了候选的联合读出与这种局域数值模型的具体差别。

同时，对另一侧的保迹局域过程
$\Lambda_B(X)=\sum_\mu K_\mu XK_\mu^*$，不按其结果筛选时，

$$
\operatorname{Tr}\!\left[(E_A\otimes I)
       (\operatorname{id}\otimes\Lambda_B)(\rho_{AB})\right]
 =\operatorname{Tr}\!\left[\rho_{AB}
       \left(E_A\otimes\sum_\mu K_\mu^*K_\mu\right)\right]
 =\operatorname{Tr}[\rho_{AB}(E_A\otimes I)].
$$

因此这种操作不改变另一侧的局部概率。联合相关、条件分支的变化与未筛选局部统计之间的区别，都由同一套正性和归一化条件保留。

<a id="section-10"></a>

## 10. 完整候选 C115 及有限维重构结论

<a id="sec-c115-candidate"></a>

把本稿的条件收成一组，才能称为一份完整候选。表中的四层是一条关系一致性原则的不同接口；将它们放进一个名称，不代表已经证明四层逻辑独立性或最小性。

本候选的有限系统范围，定义为下述二元原子经有限独立复合及投影角代数生成的系统。关于 $\Omega$ 中每一个其他可能的子结构是否也属于这个生成范围，本稿不作无条件断言。

| 接口 | 明确约束 |
|---|---|
| 局部接续 | 非经典二元块满足 $\dim W\ge2$ 并具有欧氏平方规则 $S$；有向变化 $D$ 对标签线性、保持内积且不改变自身标签；同一两分量表示 $S+jD$ 在原空间内封闭且结合。 |
| 概率拆并 | 模型中的每个效果、每个有限效果分解都有同一上下文无关概率；二元互斥合并可加，单位效果概率为一。全部正归一化评价作为模型状态。 |
| 整体拼接 | 独立系统以相互交换的含幺子代数嵌入，由它们生成联合代数，并共享内生复中心 $J$。允许任意有限个二元系统及投影角代数；采用全部正状态和正效果，任何有限聚合必须保正。 |
| 操作与时间 | 采用全部尊重随机混合、成功分支不增总概率、加入任何内部有限参考后对完整联合正锥仍保正的操作。时间平移为这类操作及其同类逆组成的连续单参数群。理想滤片按定理 [8.2](#thm-c115-luders) 的有限比较准则指定。 |

所谓“采用全部”是可用性约定。若实际设备只实现其中一部分状态、效果或过程，所得是此数学理论的受限子理论；从结构定理不能自动推断某台设备有任意控制能力。

### 定理 10.1（C115 的有限维量子表示）

满足上述候选的每个有限系统，具有通常复 Hilbert 空间量子理论的表示：

1. 二元原子为 $M_2(\mathbb C)$，其最小振幅空间为 $\mathbb C^2$；有限独立复合及允许的角代数给出 $M_d(\mathbb C)$ 与 $H=\mathbb C^d$。

2. 状态为 $\rho\ge0,\operatorname{Tr}\rho=1$；效果为 $0\le E\le I$；测量为 $\sum_kE_k=I$，概率为 $\operatorname{Tr}(\rho E_k)$。

3. 独立复合为复张量积。局部态由部分迹表示；整体可具有纠缠态。

4. 允许的有限分支为 Kraus 映射；归一化总过程为量子信道；可逆信道为酉共轭，连续一参数可逆流具有 Hamiltonian 生成元。

5. 所指定的理想效果分支为平方根更新，锐测量为 Lüders 更新。

反过来，通常的有限维复量子模型，在二元块中取泡利乘法，并按本候选指定理想滤片，满足这些条件。

**证明。**
第一项由定理 [2.3](#thm-c115-dimension)、[3.1](#thm-c115-algebra)、[4.1](#thm-c115-center) 及角代数构造给出。
第二项是定理 [5.2](#thm-c115-born)。
第三项的张量结论已经证明；对任意联合态 $\rho_{AB}$，部分迹由唯一满足

$$
\operatorname{Tr}[\rho_{AB}(E\otimes I)]=\operatorname{Tr}[(\operatorname{Tr}_B\rho_{AB})E]
$$

的局部矩阵定义，它在正效果上非负、迹为一，故正是局部状态。
例如 $\lvert \Phi\rangle=(\lvert 00\rangle+\lvert 11\rangle)/\sqrt2$ 给出纯联合态，而局部矩阵为 $I/2$；若是乘积纯态其局部应为秩一，因此该态并非乘积。
第四项由定理 [7.2](#thm-c115-kraus) 及其后可逆与连续流论证给出。
第五项即定理 [8.2](#thm-c115-luders)。
逆向验证逐项使用矩阵乘法、正锥、迹的线性及张量延伸即可。

这里重构的是完整的**有限维运动学和一般操作结构**，连同连续可逆动力学的形式。具体 Hamiltonian、耦合常数、$\hbar$ 的数值、空间维数、相对论场论与引力并未被选出。任意有限关系一致性也不自动给出无限维表示所需的拓扑、连续性、定义域与完备性。

### 10.1 把每个承重条件反着检查

| 删去什么 | 留下什么具体后果 |
|---|---|
| 两分量中的闭合 | 实 qubit 仍能在 $M_2(\mathbb R)$ 里结合相乘；不能据此推出三维或中央复数。 |
| 结合相容或正确尺度 | $(e_1e_1)e_2$ 与 $e_1(e_1e_2)$ 不同；相对尺度被括号选择改变。 |
| 有向关系 | 同一球和同一 Jordan 平方无法区分乘法与反向乘法；顺序信息遗漏。 |
| 跨分解的效果拆并 | $\widetilde w(E)=\alpha+4b_z^3$ 仍合法归一化，却使一个效果拆成两份时总概率改变。 |
| 全体有限聚合正性 | 四元表对角为 $1$、非对角为 $-2/5$；全部三元主块正定，整体沿 $(1,1,1,1)$ 却有负二次型。 |
| 复中心对齐 | 实张量积保留两个中心扇区；$\omega_\pm$ 对全部局部乘积读出相同，却对 $P_+$ 给出 $1$ 与 $0$。 |
| 任意参考延伸保正 | 转置在单系统上正且保迹，但其与恒等过程并用会把 Bell 态送成有负特征值的矩阵。 |
| 理想滤片选择 | 同一成功效果容许许多不同测后状态，平方根更新不再唯一。 |
| 时间流与连续性 | 状态空间和概率仍存在，但不会自行选择某个时间演化，更不决定 Hamiltonian。 |

表中四元反例可直接计算：$k$ 元主块的特征值为 $7/5$（重数 $k-1$）与 $1-2(k-1)/5$。$k=3$ 时后者为 $1/5$，$k=4$ 时为 $-1/5$。因此“三维有限提升”必须反复作用于已经合成的对象，不能解释成只检查每组三个原始元。

### 10.2 下一条真正开放的命题

本轮最有价值的后续问题不是再给 $J$ 起一个名字，而是进一步削弱“同一两分量结合闭合”这个条件。具体目标可以写成：在不先规定 $V\oplus jV$ 的条件下，由项目原生二元比较协议、可恢复性、有限接口供给与可检验的顺序等价，构造这一表示，并证明其反对称部分恰需一个共同中央方向。该步骤若完成，才把当前仍是候选输入的闭合要求变成更原始定义间的定理。当前证明不冒充完成了这一步。

<a id="section-11"></a>

## 11. 完整白话描述

整体里先有能够互相比较、能够按顺序接起来的内容。两份内容相遇，会留下两种关系：它们有多相合，以及从前一份接到后一份时朝哪边变化。交换顺序，相合不变，变化反向。我们要求这两种关系一直够用：接了再接，也不用突然从外面补一类新东西，而且先接哪两份不能改变最后结果。于是两个独立方向必须带出第三个方向，再添第四个独立方向又会与接法冲突；三维的有向体积就在内部承担了那个“平方等于负一”的角色。复数由此有了一个具体位置，而不是先写在外面的规则。

这时，一个二元系统可以画成一个球：球内是混合状态，球面是纯方向。一次二元读出就是沿某个方向看这个球；有向变化则沿球面转动。同一个效果拆成两份再合并，读数必须保持一致，这迫使概率对效果线性，写进刚刚构造出的振幅空间便成为模平方。球面上的每个点还挂着一圈整体相位；这一圈不能被单次读出，但沿不同关系接续一周，可能留下可比较的相位差。几个系统接成整体时，还要认同同一个复数方向，否则会多出局部乘积读口看不见的整体扇区。任何操作拿着内部参考一起检验，都不能产生负概率；理想测量则在固定成功效果下，保留最多的均衡比较信息。这一组内部相容条件，给出有限维量子理论的状态、概率、复合、操作和连续可逆运动。

它的简洁之处，在于把很多规则放回同一种问题：**同一关系换一种合法拆法或接法，会不会得到矛盾的结果？** 它仍是一份有明确前提的量子候选。每条前提被删去时都有具体的不同模型或失败现象；这正让它有机会继续被项目中的更原始关系证明、削弱或反驳。

<a id="references"></a>

## 参考文献

<a id="ref-repo"></a>

### [1]

 the-omega-institute. *trureturing*, public repository, `dev` page consulted 2026-11-03. [https://github.com/the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing).

<a id="ref-repo-blind"></a>

### [2]

 the-omega-institute. *LocalMarginalCorrelationBlindSpot.lean*, public source consulted 2026-11-03. [Repository source](https://github.com/the-omega-institute/trureturing/blob/dev/D5/S3/Quantum/Entanglement/LocalMarginalCorrelationBlindSpot.lean). Source inspection here is not a new Lean build.

<a id="ref-c113"></a>

### [3]

 AURIC C113. *Finite balanced calibration and canonical square-root filters*. Prior delivered research manuscript and source, 2026-11-03. Used as a prior-work record; the filter statement needed here is reproved in this manuscript.

<a id="ref-c114"></a>

### [4]

 AURIC C114. *从二次读出到递归关系相容*. Prior delivered research manuscript and self-contained TeX, 2026-11-03. Its finite positivity interface is restated here.

<a id="ref-alfsen"></a>

### [5]

 E. M. Alfsen and F. W. Shultz. Orientation in operator algebras. *PNAS* 95 (1998), 6596–6601. [https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/](https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/).

<a id="ref-barnumwilce"></a>

### [6]

 H. Barnum and A. Wilce. Local tomography and the Jordan structure of quantum theory. *Foundations of Physics* 44 (2014), 192–212. [https://arxiv.org/abs/1202.4513](https://arxiv.org/abs/1202.4513). The general result has composite hypotheses beyond the phrase “local tomography.”

<a id="ref-busch"></a>

### [7]

 P. Busch. Quantum states and generalized observables: a simple proof of Gleason's theorem. *Physical Review Letters* 91 (2003), 120403. [https://arxiv.org/abs/quant-ph/9909073](https://arxiv.org/abs/quant-ph/9909073).

<a id="ref-ashtekar"></a>

### [8]

 A. Ashtekar and T. A. Schilling. Geometrical formulation of quantum mechanics. [https://arxiv.org/abs/gr-qc/9706069](https://arxiv.org/abs/gr-qc/9706069). Geometric conventions in this manuscript are given explicitly.
