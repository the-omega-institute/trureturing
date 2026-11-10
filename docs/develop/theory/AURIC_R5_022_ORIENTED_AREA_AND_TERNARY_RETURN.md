# AURIC R5-022：有向面积与三元返回

> 理论参考输入：本稿为用户提供的研究正文，包含普通数学证明，未作本候选的 Lean/kernel 认证。仓库数学真值以经 Lean 内核核验的声明及其公理闭包为准。

AURIC / R5-022

有向面积与三元返回

一条关系如何恢复三维量子比特几何

定义、完整证明、反例与外部输入账本

2026年11月7日（Asia/Singapore）

**本轮核心。** 在一个至少含两个独立方向的实内积空间上，给任意二元总映射 $D$，只要求

$$
\boxed{\quad D(D(a,b),c)=\langle a,c\rangle b-\langle b,c\rangle a
\qquad(a,b,c\in V).\quad}
\tag{R}
$$

则空间自动为三维，$D$ 自动成为某一手性的标准叉积。 有限维、完备、连续、双线性、反对称、面积范数律和完整旋转协变都不用独立加入。

**最短几何读法。** 先把两个方向组成有向面积，再把它与第三个方向比较；结果必须回到原来两方向的平面，且其两个分量恰由原二元比较决定。 第三个量是同一载体中的通用测试元，不是从模型外指定的特殊点。 关系对全部原元素、和、缩放与已生成输出成立，因而覆盖递归代入。

**精简的准确范围。** 这是 R5-021 已恢复比较层的几何压缩。这里把正定内积作为明确输入，并把 $D$ 的输出类型固定为比较空间 $V$。 因此它不宣称：把旧世界中的五组关系直接删成一组、已经消除了旧中心输出、或从零公理得到了量子力学。 真正证明的是，在这个明列入口上，有限性与全部转向正则性是冗余假设。

**线与面积的严格统一。** 单位态 $n$ 的切平面上有同一个正核

$$
Q_n(v,w)=\frac14\bigl(\langle v,w\rangle+i\langle n,D(v,w)\rangle\bigr),
\quad v,w\perp n.
$$

其对称部分给长度，反对称部分给有向面积，且二元正性界精确饱和。 它不单独提供物理时间、完整历史或任意复合系统。

固定项目快照：`5d356c7b7e9b0fc64a3c88286402d43ecb54f4a5`，当次可取得的默认分支为 dev。

源提交时间：2026-11-07 20:38:23（新加坡）。源码核读与普通数学证明分列；本轮未新建或重新编译 Lean 定理。

本稿续已取得的 R5-021 工作稿；编号不表示它已进入仓库或取得文献优先权。

## 目录

- [1　研究标杆、项目现状与本轮归属](#section-1)
- [2　唯一候选：三元返回律](#section-2)
- [3　最简几何：一条轴与一个转动平面](#section-3)
- [4　正存在、内生读出与标准单比特形式](#section-4)
- [5　两个态究竟决定哪一种面积](#section-5)
- [6　线与面积来自同一个正核](#section-6)
- [7　面积、时间与内生观察者的边界](#section-7)
- [8　三元相容不能只解释成逐对没有冲突](#section-8)
- [9　不动点、正交返回与有限线性提升](#section-9)
- [10　从单比特到完整有限量子过程：哪些还需外部输入](#section-10)
- [11　反向删除、闭合账本与白话描述](#section-11)

<a id="section-1"></a>

## 1　研究标杆、项目现状与本轮归属

### 1.1　与问题最匹配的已核研究

没有一项研究同时把球面几何、完整量子重构、测量过程和物理时间全部从无前提推出。 本轮按结论范围选择下列标杆，而不作无统一指标的“全球最好”排名。

| 研究 | 已确立的结构 | 必须保留的输入边界 |
|:---|:---|:---|
| Ashtekar–Schilling [\[1\]](#ref-ashtekar) | 射线空间的相容度量、辛形式和复结构；Hamilton 流表示 Schrödinger 演化。 | 是量子形式的等价几何表达，不从裸“存在”推出。 |
| Mitscherling 等，2025 [\[2\]](#ref-projector) | 投影算子给规范不变的量子度量、Berry 曲率和多态几何。 | 基于已有态投影及参数依赖；还存在超出二阶几何的信息。 |
| Tamate 等，2011 [\[3\]](#ref-bargmann) | 三顶点相位与球面测地三角形立体角相联。 | 两个端点不能替代任意内部路径。 |
| Barnum–Hilgert [\[4\]](#ref-jordan) | 强对称、谱分解的紧凸态空间被分类为简单 Euclidean Jordan 态空间或单纯形。 | 仍需额外关系选择复量子；“各向同性”本身更弱。 |
| Selby–Scandolo–Coecke，2021 [\[5\]](#ref-selby) | 由过程图式公设重构有限维经典–量子复合及其相互作用。 | 过程组合、经典接口、纯化等都是明确结构。 |
| Nakahira，2026 预印本 [\[6\]](#ref-nakahira) | 在其 OPT 框架中，局部等价与等价系统纯化给态、效果、复合和 CP 过程。 | Appendix A.2 另有框架要求；不是全部只付两个输入，也不覆盖量子场论。 |
| Hausmann 等，2025 [\[7\]](#ref-clock) | 内生时钟下不同测量实现的等价性及有限资源失效边界。 | 非理想钟的某些实现可能失酉或失去确定时序；不能泛化为所有有限钟必如此。 |

### 1.2　固定项目快照的实质内容

本次对 1,334 份 theory 路径进行名称及关键词检索，并定点读取相关正文和 Lean 声明。 这不是全库逐行证明认证。以下四个接口直接参与本轮判断。

1.  **C128 已到 §§468–478。** 最新候选保留原实载体、分离线性评价、原序单位锥、同一旧 $S,D$ 和实际来源。 仅查全部二标签正表及指定相加／近邻三表的受限系数正性，加相加零平方、$S(u,u)=u$、 小效果 $S(e,e)\le e$ 和一条实部三元式；正文据此恢复旧双线性、全有限正表、原单位、虚部式和结合星结构。 其 §473 明确：一般正核只给 $`J^*=-J,\|J\|\le1`$， *不给*  $J^2=-I$。 §476 给总平方正性不能代替原效果边界的四维反例。[\[12\]](#ref-c128)

2.  **面积与方向同型已经在库。** 稳定关系边界卷 §4.4 证明 $\Lambda^2V\simeq V$ 的有限维非平凡情形必须是三维； §3 区分完整三槽 $SO(V)$ 不变性与裸球面传递性。 这些结论不能重新计为本轮首创。[\[13\]](#ref-boundary)

3.  **三点相位已有精确 Lean 声明。** `triple_bargmann_bloch` 给本稿第 5.2 节的三点公式。 源码还含 $(1+i)/4$ 与 $(1-i)/4$ 的明确例子。 本轮仅读取该文件；其逃逸登记审计注记关联 issue \#27571，未在此消除。[\[14\]](#ref-repobargmann)

4.  **整体内生不等于历史可压成端点。** 静态相融纤维卷区分事件历史、算子乘积与内生时钟； 目标恢复判据则要求目标在同读出纤维上常值。 它们为检验“面积就是时间”提供现成的准确标准。[\[15\]](#ref-omega), [\[16\]](#ref-recovery)

R5-021 原稿的入口包括有限实载体 $E=\mathbb Ru\oplus V$、完整标架、原双线性 $M$ 和任意总 $D$， 以及五组关系。它恢复比较尺并用固定输出条件消去中心余项。 本稿改在已经分出的比较空间上工作，不把这一类型限制算作从无条件自动得出。

<a id="section-2"></a>

## 2　唯一候选：三元返回律

### 2.1　全部外部输入

#### 定义 2.1：候选 $\mathcal Q_{22}$

给定以下三类结构：

- **B1.** 实向量空间 $V$，至少有两个线性独立向量。 *不要求有限维或完备。*

- **B2.** 正定对称实双线性形式 $g(a,b)=\langle a,b\rangle$。

- **B3.** 任意总映射 $D:V\times V\to V$。 *不要求任何线性、反对称、连续或可测性。*

唯一附加关系族是对全部 $a,b,c\in V$ 的恒等式

$$
D(D(a,b),c)=g(a,c)b-g(b,c)a.
\tag{1}
$$

**计数约定。** 这是“三类结构输入加一个全称关系族”的分组计数。 实数、向量空间和正定双线性形式的公理内容没有被删除。 $D$ 的输出属于 $V$，不允许再附加一个不可见标量槽。 式 (1) 的全称量词包括零、缩放、和及 $D$ 的输出；只查单位态或有限三元样本不等价。

### 2.2　分类定理及完整证明

#### 定理 2.2：任意总操作的三维刚性

候选 $\mathcal Q_{22}$ 当且仅当 $\dim_\mathbb RV=3$，且相对于某个正交定向，

$$
D(a,b)=\kappa\,a\times b,\qquad\kappa\in\{1,-1\}.
$$

尤其 $D$ 自动双线性、交替、连续，满足面积律、Jacobi 恒等式及全部正向正交变换协变。

**证明。**

记 $R_z(c)=D(z,c)$，此时尚不假设 $R_z$ 线性。

**第一步：零行恰为零。** 令 $z_0=D(0,0)$，(1) 给 $R_{z_0}=0$。 于是 $D(z_0,z_0)=0$，再对 $(z_0,z_0,c)$ 用同一式，得 $D(0,c)=0$。 若 $R_z=0$，则对 $(z,a,c)$ 用式 (1) 得

$$
0=g(z,c)a-g(a,c)z\qquad\forall a,c.
$$

若 $z\ne0$，取非零 $a\perp z$、$c=z$，得到 $0=\|z\|^2a$，矛盾。 故

$$
R_z=0\quad\Longleftrightarrow\quad z=0.
\tag{2}
$$

**第二步：零比较准确检测共线。** 由正定性，线性算子 $c\mapsto g(a,c)b-g(b,c)a$ 为零，当且仅当 $a,b$ 线性相关。 利用 (1) 和 (2)，

$$
D(a,b)=0\quad\Longleftrightarrow\quad a,b\text{ 线性相关}.
\tag{3}
$$

特别地，$D(a,a)=0$。

**第三步：两方向的全部正交补只能有一维。** 取独立 $a,b$，令 $w=D(a,b)\ne0$。 由于 $D(w,w)=0$，式 (1) 给

$$
0=g(a,w)b-g(b,w)a.
$$

独立性给 $w\perp a,b$。 若 $z\perp a,b$，同式给 $D(w,z)=0$，故由 (3)，$z\in\mathbb Rw$。 所以

$$
\operatorname{span}\{a,b\}^{\perp}=\mathbb Rw.
$$

任意向量都可正交投影到有限维平面 $\operatorname{span}\{a,b\}$；余量属于 $\mathbb Rw$。 故 $V=\operatorname{span}\{a,b,w\}$， *自动* 得到 $\dim V=3$。 这个投影只解一个可逆二阶 Gram 方程，不使用空间完备性。

**第四步：所有行的线性与斜性自动恢复。** 对非零 $v$，取单位 $e\perp v$，令 $p=D(e,v)$。 由 (1)，$D(p,e)=v$；于是

$$
D(v,c)=g(p,c)e-g(e,c)p.
$$

右侧是关于 $c$ 的线性斜对称算子。 式 (3) 又给 $\ker R_v=\mathbb Rv$。

**第五步：只有共同的两个手性选择。** 选一个临时正交定向。三维中每个核为 $\mathbb Rv$ 的非零斜对称算子唯一写成

$$
D(v,c)=\kappa(v)\,v\times c,\qquad\kappa(v)\ne0.
$$

给非零 $x\perp v$，可选 $b$ 使 $D(v,b)=x$。 此时 (1) 及通常的三重积公式给

$$
D(x,c)=(v\times b)\times c=\frac1{\kappa(v)}x\times c.
$$

故 $\kappa(x)\kappa(v)=1$。 任意非零 $v,w$ 都有共同非零垂线 $x$，所以 $\kappa(v)=\kappa(w)$。 该常数平方为一。 因此原 $D$ 在全部原向量上就是 $\pm\times$；其双线性等性质随即成立。 反向是标准三维叉积恒等式，且两次出现的符号相乘为一。

$\square$

### 2.3　真正减少了什么

| 项目 | 本轮位置 | 是否已经删除独立输入 |
|:---|:---|:---|
| 有限维、完备 | 维数由三元返回自动推出 | 有限维无需输入；完备随三维成立 |
| $D$ 双线性、反对称、连续 | 分类定理结论 | 均无需输入 |
| 面积律、Jacobi、完整 $SO(3)$ 协变 | 分类定理推论 | 均无需输入 |
| 原正定比较尺 $g$ | B2 明列 | 仍是入口；可由已给 $D$ 唯一回读不等于存在性免费 |
| 旧标量尾项已被消除 | B3 的类型 $D:V^2\to V$ | 不能冒称自动解决 R5-021 的固定输出义务 |
| 原世界、全部实际过程和时钟 | 本候选未给 | 不得把局部三维当作整个 $\Omega$ 的维数 |

在检索到的项目近邻中，已有版本通常先给有限维或转向的线性／斜性，或由更大的原代数候选推出返回式。 本轮提供的是上述任意总映射入口的直接证明。 这不是全球优先权声明，也没有证明比成熟完整量子重构的总输入更少。

<a id="section-3"></a>

## 3　最简几何：一条轴与一个转动平面

以下选择 $D$ 自身确定的定向，使 $D(a,b)=a\times b$。

#### 命题 3.1：方向、面积和比较尺的条件互恢复

对全部 $a,b\in V$，

$$
\begin{aligned}
g(D(a,b),a)&=g(D(a,b),b)=0,\\
\|D(a,b)\|^2&=\|a\|^2\|b\|^2-g(a,b)^2,
\end{aligned}
\tag{4}
$$

$$
\begin{aligned}
[L_a,L_b]&=L_{D(a,b)},\qquad L_a(v)=D(a,v),\\
g(a,b)&=-\frac12\operatorname{Tr}_V(L_aL_b).
\end{aligned}
\tag{5}
$$

**证明。**

前三式由分类后的叉积直接展开。具体地 $L_aL_b(v)=b\,g(a,v)-v\,g(a,b)$， 故其迹为 $g(a,b)-3g(a,b)=-2g(a,b)$。 这也表明若同一个 $D$ 满足两个正定尺的返回律，则两个尺必相同。

$\square$

#### 命题 3.2：一次正交、两次正交与内生复结构

给单位 $n$，令 $T_n=\{v:g(n,v)=0\}$ 及 $J_nv=D(n,v)$。则

$$
J_n^2v=n\,g(n,v)-v,
\qquad J_n^2|_{T_n}=-I_{T_n}.
$$

因此 $J_n$ 在切平面上是等距四分之一转动；两次作用回到反向。

**证明。**

用反对称性把 $D(n,D(n,v))$ 改为 $-D(D(n,v),n)$，再用返回律。 范数与正交性由 (4) 得到。

$\square$

原稿的两幅几何示意图在此用文字和公式呈现：

- 左图“有向面积的法向读出”：两个方向 $a,b$ 张成面积平面，法向读出为 $D(a,b)$，对应 $\Lambda^2V\simeq V$。
- 右图“$n$ 处的切平面”：依次转动 $v\mapsto J_nv\mapsto-v$，对应 $J_n^2=-I$。

左图为三维关系的平面示意投影；它不把示意图中所画距离当作量值。 右图展示同一内部态 $n$ 所确定切平面上的精确转动关系。

#### 推论 3.3：固定点与正交投影

定义

$$
\Pi_n(v)=v+D(D(v,n),n)=g(v,n)n.
$$

则 $\Pi_n^2=\Pi_n$，$\operatorname{Fix}\Pi_n=\mathbb Rn$。 若 $n\perp m$，则 $\Pi_n\Pi_m=0$。

这里的 $-v$ 是比较方向反转。正对象的端点没有消失，也没有引入负概率。 在正态空间上的物理非选择测量要使用第 4 节的含单位扩张。

### 3.1　面积向量与全部面积记录

反对称双线性使 $D$ 唯一诱导线性映射 $\widetilde D:\Lambda^2V\to V$，$a\wedge b\mapsto D(a,b)$。 在导出的三维中，它把一组正交面积基送到一组正交向量基，因此是等距同构。 这是已知的 Hodge 对偶结构，项目中已有对应定理。[\[13\]](#ref-boundary)

七维也存在满足正交与面积范数条件的二元叉积，但它不满足本返回律。 这正说明只有式 (4) 还不够；经典向量积分类可参照 Brown–Gray 或 Walsh。[\[9\]](#ref-cross)

完整各向同性在此指 $SO(3)$： $D(Ra,Rb)=RD(a,b)$。 若把反射也包括进来，正确关系是

$$
D(Ra,Rb)=\det(R)\,R D(a,b),\qquad R\in O(3).
$$

故手性不能与“普通向量的全部反射不变”同时无条件要求。

<a id="section-4"></a>

## 4　正存在、内生读出与标准单比特形式

### 4.1　从比较量建立正对象

#### 定义 4.1：含单位的比较代数

从已得 $V,g,D$ 定义 $E=\mathbb R\oplus V$、$u=(1,0)$，以及

$$
\begin{aligned}
(\alpha,a)\circ(\beta,b)
&=(\alpha\beta+g(a,b),\alpha b+\beta a),\\
\delta((\alpha,a),(\beta,b))&=(0,D(a,b)).
\end{aligned}
\tag{6}
$$

正对象定义为平方锥 $C=\{A\circ A:A\in E\}$。 这定义了本候选的数学扩张；不声称恢复了某个尚未提供的旧 $M$ 的身份。

#### 定理 4.2：正锥、谱与负号的准确含义

$$
C=\{(t,a):t\ge\|a\|\},\qquad C\cap(-C)=\{0\},\qquad E=C-C.
$$

若 $a\ne0$，$n=a/\|a\|$、$p_{\pm n}=(u\pm n)/2$，则

$$
(t,a)=(t+\|a\|)p_n+(t-\|a\|)p_{-n}.
$$

**证明。**

平方为 $(\alpha^2+\|b\|^2,2\alpha b)$，第一坐标不小于第二坐标的范数。 反向，给 $t\ge\|a\|$，上述谱式的系数非负； $\sqrt{t+\|a\|}p_n+\sqrt{t-\|a\|}p_{-n}$ 的平方恰为 $(t,a)$。 $a=0$ 直接取 $\sqrt t\,u$。 尖性显然。对任何 $A=(t,a)$，取足够大的 $s\ge0$，有 $A+su,su\in C$， 从而 $A=(A+su)-su$。

$\square$

每个有向比较都可表示为两个正对象的差；反向比较只交换两个正端点。 如果额外要求每个比较及其负值也都为正，尖性会迫使全部比较为零。

### 4.2　内生数学观察者与 Born 形式

令

$$
h((t,a),(s,b))=ts+g(a,b),\qquad\tau(t,a)=t.
$$

#### 定义 4.3：数学读出

数学读出是正归一实线性泛函 $\omega:E\to\mathbb R$： $\omega(C)\ge0$，$\omega(u)=1$。效果是 $0\le e\le u$。 全部这类数学读出的实际可实施性，是额外的操作性主张，不从定义自动推出。

#### 定理 4.4：对象与读出使用同一正锥

每个数学读出唯一写成

$$
\omega_r(t,a)=t+g(r,a),\qquad\|r\|\le1.
$$

等价地，每个非零 $o\in C$ 给读出 $\omega_{[o]}(A)=h(o,A)/\tau(o)$，正比例的 $o$ 给同一读出。

**证明。**

线性与归一化给 $\omega(t,a)=t+g(r,a)$。 在全部 $(1,n)$、$\|n\|=1$ 上测试正性，得到 $1+g(r,n)\ge0$，即 $\|r\|\le1$。 反向由 Cauchy–Schwarz 成立。这也证明 $C$ 对 $h$ 自对偶。

$\square$

若 $c=(t,a)\in C\setminus\{0\}$，则 $t>0$，内部读出 $\omega_0(c)=t$ 可区分它与零。 但某个特定观察者可能读到零，例如 $\omega_{-n}(1,n)=0$。 所以“存在可被读出”在这里是正对象的可分离性，不是每个观察者都必须看到它。

选择与 $D$ 相容的 Pauli 三轴，定义

$$
\Phi(t,a)=tI+a\cdot\sigma,
\qquad\rho_r=\frac12(I+r\cdot\sigma).
$$

Pauli 恒等式给

$$
(a\cdot\sigma)(b\cdot\sigma)=g(a,b)I+iD(a,b)\cdot\sigma.
$$

因此在 $E_\mathbb C$ 上定义的 $A\star B=A\circ B+i\delta(A,B)$ 是结合星乘法， 且 $\Phi:E_\mathbb C\simeq M_2(\mathbb C)$。这里引入 $i$ 是复化表示；其局部几何已经由 $J_n^2=-I$ 构造。

由两个特征值 $t\pm\|a\|$ 得 $\Phi(C)=M_2(\mathbb C)_+$，而

$$
\omega_r(A)=\operatorname{Tr}(\rho_r\Phi(A)).
\tag{7}
$$

对单位方向 $m$ 的二元效果 $p_m=(1,m)/2$，

$$
p(m\mid r)=\frac{1+g(r,m)}2.
\tag{8}
$$

若 $\|r\|=\|m\|=1$ 且夹角为 $\theta$，则 $p=\cos^2(\theta/2)$。

#### 注 4.5：平方读数不是各向同性单独给的

对纯方向定义 $p_k(a,b)=(1+(a\cdot b)^{2k+1})/2$，$k\ge1$。 它们旋转不变、非负、互补归一且同态读数为一，却不是 (8)。 本稿 Born 形式依赖明确的正线性读出定义；若读出也必须从原始关系推出，需回接项目 C128 的原评价／混合接口。

### 4.3　酉演化、测量与不确定性

#### 命题 4.6：导出的数学动力学与测量

给 $a\in V$，$e^{sL_a}\in SO(V)$。其矩阵实现为

$$
U_a(s)=e^{-is(a\cdot\sigma)/2},\qquad
\rho_{e^{sL_a}r}=U_a(s)\rho_rU_a(s)^\dagger.
$$

给投影 $P_m=(I+m\cdot\sigma)/2$，分支映射 $\mathcal I_m(\rho)=P_m\rho P_m$ 为完全正，权重为 $\operatorname{Tr}(\rho P_m)$。 权重正时归一输出为 $P_m$。 非选择测量为

$$
\mathcal E_m(\rho_r)=P_m\rho_rP_m+P_{-m}\rho_rP_{-m}
=\rho_{(r\cdot m)m}.
$$

**证明。**

$L_a$ 斜对称给旋转指数；Pauli 交换子验证矩阵形式。 夹心在任意参考系统上仍保持正，故完全正。秩一投影满足 $P_m\rho P_m=\operatorname{Tr}(\rho P_m)P_m$。 两个分支相加消去横向 Bloch 分量。

$\square$

这个构造证明了标准投影仪器的 *存在* ，不证明给定概率唯一指定该仪器。 同一效果可先用平方根分支、再对输出施加不同酉变换，获得不同状态更新而保持同一权重。

对可观测量 $A=a\cdot\sigma,B=b\cdot\sigma$，直接计算还有

$$
\operatorname{Var}_r(A)\operatorname{Var}_r(B)
-\operatorname{Cov}_r(A,B)^2-
\bigl(r\cdot D(a,b)\bigr)^2
=(1-\|r\|^2)\|D(a,b)\|^2\ge0.
$$

协方差取对称化乘法。这是单比特的 Robertson–Schrödinger 关系及其精确余项。

<a id="section-5"></a>

## 5　两个态究竟决定哪一种面积

### 5.1　三种面积必须分开

给单位 Bloch 方向 $a,b$，$t=a\cdot b=\cos\theta$、$0\le\theta\le\pi$。 它们决定

$$
\text{平行四边形面积 }A=\|a\wedge b\|=\sin\theta,
\qquad
\text{单位圆小扇形面积 }S=\theta/2.
$$

第一项的共同原点是归一化 Bloch 球的中心，它在所定义的凸结构内对应最大混合态，并非新增纯态 $C$。 非共线时，第二项使用两态张成的平面、选定的小弧和半径归一化。 共线时数值 $S=\theta/2$ 仍确定；反极点间的半圆所在平面还需要选择。 球面回路所围有向面积则依赖路径；两个端点本身没有确定这个回路。

#### 命题 5.1：面积单独丢失二态概率

令 $F=\operatorname{Tr}(P_aP_b)=(1+t)/2$，则

$$
A^2=1-t^2=4F(1-F).
$$

所以只有 $A$ 时无法区分 $F$ 与 $1-F$。 尤其 $a=b$ 和 $a=-b$ 都给 $A=0$，但转移概率分别是一与零。

用圆扇形可以得到 $F=\cos^2 S$，但这是已经选择几何和 Born 配对后的恒等改写， 并不使“概率由面积唯一决定”的物理解释自动成立。

另一个精确区别：

$$
a\perp b\Longrightarrow F=1/2,
\qquad F=0\Longleftrightarrow b=-a.
$$

三条 Bloch 正交轴对应三个互补的二元测量，不是二维 Hilbert 空间内三个两两正交的纯态。

### 5.2　第三态的回路信息不能由两个端点替代

#### 命题 5.2：二态规范与三态不变量

独立重定相 $|A\rangle\mapsto e^{i\alpha}|A\rangle$、$|B\rangle\mapsto e^{i\beta}|B\rangle$ 使

$$
\langle A|B\rangle\mapsto e^{i(\beta-\alpha)}\langle A|B\rangle.
$$

因此两射线的内积相位不是独立规范不变量。 三态乘积

$$
\Delta_3(A,B,C)=\langle A|B\rangle\langle B|C\rangle\langle C|A\rangle
$$

则不随三个相位选择改变。

**证明。**

三个相位因子在乘积中逐个抵消。

$\square$

对 qubit，Pauli 乘法直接给

$$
\operatorname{Tr}(P_aP_bP_c)=
\frac{1+a\cdot b+b\cdot c+c\cdot a+i\,a\cdot D(b,c)}4.
\tag{9}
$$

这是项目已有精确声明，本文引用其结构并给出相同的直接计算意义。[\[14\]](#ref-repobargmann)

取内部正交标架 $a=e_z,b=e_x,c_\pm=\pm e_y$。 两组三个二态概率全为 $1/2$，但

$$
\Delta_3(a,b,c_+)=(1+i)/4,
\qquad\Delta_3(a,b,c_-)=(1-i)/4.
$$

其相位分别为 $\pi/4$ 与 $-\pi/4$。 两个候选第三态均为原二元关系的内部输出 $\pm D(a,b)$，并没有用外部世界的点。  *内生* 不意味着两份相反的内部回路信息必须相同。

若令 $C=A$ 或 $C=B$，则 $\Delta_3=F\ge0$。 $F>0$ 时相位成为零；$F=0$ 时相位未定义。 这说明端点基足够读出二态概率，但把第三点并到端点会删去非平凡环信息。

对有指定闭路的 qubit，Berry 几何相位为有向立体角的一半，符号取决于连接和路径顺序； 本稿统一用 $\mathcal A=i\langle\psi|d\psi\rangle$，则 $\gamma_B=-\Omega/2\pmod{2\pi}$。 上述 $\Delta_3$ 顺序对应的三角形相位是其相反号；不把两种约定混写。[\[3\]](#ref-bargmann)

#### 命题 5.3：局部选基不能消除全局相位拼接

对本稿约定的 Berry 曲率，$\int_{S^2}F=-2\pi$。 不存在全局光滑的一形式 $\mathcal A$ 满足 $F=d\mathcal A$。 因此态向量的单一全局光滑相位规约不存在；局部规范仍需在重叠区域通过相位关系拼接。

**证明。**

将第 6 节的曲率式积分得 $-2\pi$。 若全局 $F=d\mathcal A$，球面无边界，Stokes 定理会给积分为零，矛盾。 一个全局光滑归一态向量将产生全局 $i\langle\psi|d\psi\rangle$，也被排除。

$\square$

这个障碍来自同一内部射线几何的 Hopf 线丛，不要求加入模型之外的参照点。

### 5.3　起点和终点也不确定量子门

#### 命题 5.4：同端点门的稳定子自由度

若 $U_0P_aU_0^\dagger=P_b$，则对全部 $\eta\in\mathbb R$，

$$
U_\eta=e^{-i\eta b\cdot\sigma/2}U_0
$$

都有相同的态端点。 这些门对其他输入一般不同，因此端点不足以恢复门。

**证明。**

$e^{-i\eta b\cdot\sigma/2}$ 与 $P_b$ 对易，故固定 $P_b$。 对不平行于 $b$ 的另一个 Bloch 方向，它一般执行非平凡旋转。

$\square$

选择最短旋转是一条额外的选取规则；反极点间连最短大圆都不唯一。 给定实际纯态轨迹 $r(t)$，使它满足 Schrödinger 演化的 Hamiltonian 仍可写成

$$
H(t)=h_0(t)I+\frac\hbar2
\bigl(r(t)\times\dot r(t)+\lambda(t)r(t)\bigr)\cdot\sigma.
$$

任意 $h_0,\lambda$ 不改变 Bloch 轨迹；后者的纵向分量可改变所选态向量的相位。

<a id="section-6"></a>

## 6　线与面积来自同一个正核

### 6.1　完全内生的切平面关系

#### 定理 6.1：切平面正核与面积饱和

给单位 $n$、$v,w\in T_n$，定义

$$
Q_n(v,w)=\frac14\bigl(g(v,w)+i g(n,D(v,w))\bigr),
\quad g_n=\operatorname{Re}Q_n,\quad\omega_n=\operatorname{Im}Q_n.
$$

对任意有限个切向量，$[Q_n(v_i,v_j)]$ 半正定，复秩至多一。 并且

$$
\begin{aligned}
g_n(J_nv,w)&=\omega_n(v,w),
\end{aligned}
\tag{10}
$$

$$
\begin{aligned}
g_n(v,v)g_n(w,w)-g_n(v,w)^2&=\omega_n(v,w)^2.
\end{aligned}
\tag{11}
$$

**证明。**

取单位切向量 $e$，令 $f=J_ne$。$(e,f,n)$ 为相容正交标架。 写 $v=v_1e+v_2f$，$z_v=v_1+iv_2$。 由叉积公式

$$
Q_n(v,w)=\tfrac14\overline{z_v}z_w.
$$

故对任意复系数 $c_j$， $\sum_{ij}\overline c_iQ_n(v_i,v_j)c_j=|\sum_j c_jz_{v_j}|^2/4\ge0$。 核只有一个复特征方向。 $g(J_nv,w)=g(n,D(v,w))$ 给 (10)； 二维实 Gram 行列式等于有向面积平方，给 (11)。

$\square$

这与投影算子公式完全一致：

$$
P_n=\tfrac12(I+n\cdot\sigma),\qquad
Q_n(v,w)=\operatorname{Tr}(P_n\,dP_n[v]\,dP_n[w]).
$$

因而不需要选取一个绝对相位，甚至不需要先写一个态向量。 投影算子几何的系统发展可见近期一手研究。[\[2\]](#ref-projector)

### 6.2　更大结构中的正性界

在任意已有复 Hilbert 射线模型中，给归一态的参数化 $|\psi(x)\rangle$，

$$
Q_{\mu\nu}=\langle\partial_\mu\psi|(I-P)|\partial_\nu\psi\rangle.
$$

这是投影后切向量的 Gram 核，故正。 记 $g=\operatorname{Re}Q$、$\omega=\operatorname{Im}Q$，任意二参数满足

$$
\det\begin{pmatrix}g_{11}&g_{12}\\g_{12}&g_{22}\end{pmatrix}
\ge\omega_{12}^2.
$$

qubit 切空间只有一复维，因而恰好饱和。 一般更高维子流形可以有严格缺口，缺口记录两复切向量未共线。

取

$$
|\psi(\theta,\phi)\rangle=
\cos(\theta/2)|0\rangle+e^{i\phi}\sin(\theta/2)|1\rangle,
$$

直接微分得到

$$
Q=\frac14
\begin{pmatrix}
1&i\sin\theta\\-i\sin\theta&\sin^2\theta
\end{pmatrix},
\quad
ds^2=\frac14(d\theta^2+\sin^2\theta\,d\phi^2),
$$

$$
\omega=\frac14\sin\theta\,d\theta\wedge d\phi,
\qquad
F=d\mathcal A=-2\omega=-\frac12\sin\theta\,d\theta\wedge d\phi.
$$

极点处参数坐标退化，几何张量本身仍良好。 这是“同一关系的线与面积读出”的精确数学内容。

### 6.3　波粒读出的准确二元关系

固定两条路径基，把 $\rho$ 写成

$$
\rho=\frac12
\begin{pmatrix}
1+r_z&r_x-ir_y\\r_x+ir_y&1-r_z
\end{pmatrix}.
$$

路径先验偏置 $\mathcal P=|r_z|$；在平衡重合及相位扫描下，

$$
p(\phi)=\frac12(1+r_x\cos\phi+r_y\sin\phi),
\quad\mathcal V=\sqrt{r_x^2+r_y^2}.
$$

正性给

$$
\boxed{\mathcal P^2+\mathcal V^2=\|r\|^2\le1.}
\tag{12}
$$

纯态取等号。这里一轴读出路径偏置，正交平面读出相干；它们属于同一个正态。 这与波粒互补性的成熟定量研究相接，但 $\mathcal P$ 不是一般路径探测器的可区别度。 后者需要包含探测器相关，不能无条件替换。[\[10\]](#ref-englert)

<a id="section-7"></a>

## 7　面积、时间与内生观察者的边界

#### 命题 7.1：单个各向同性方向不能自发选出非零流

设 $X(n)\in T_nS^2$ 且 $X(Rn)=RX(n)$ 对全部 $R\in SO(3)$ 成立。 则 $X\equiv0$。

**证明。**

固定 $n$，全部绕 $n$ 的旋转都必须固定 $X(n)$。 它们在切平面上唯一的共同不动向量为零。

$\square$

因此非平凡转向至少还需要一个内部关系，例如控制轴、历史切向或 Hamiltonian。 这个第二对象可以属于同一整体，但不能从一个没有其他标记的方向自动恢复。

### 7.1　同一几何不确定时间尺度

#### 命题 7.2：时间缩放不可由态空间几何恢复

给 $H$、持续时间 $T>0$ 与 $\lambda>0$，

$$
e^{-i(\lambda H)(T/\lambda)/\hbar}=e^{-iHT/\hbar}.
$$

两实现有同一门、同一未参数化轨迹、同一长度与几何面积，但持续时间不同。 因此这些几何数据不能单独唯一确定时间。

**证明。**

指数中的乘积相同；中间轨迹由 $t\mapsto\lambda t$ 重参数化。

$\square$

若已有 Hamiltonian 与时间校准，纯态满足

$$
\frac{ds}{dt}=\frac{\Delta H}{\hbar}.
$$

对 qubit，$H=h_0I+h\cdot\sigma$， $\dot r=(2/\hbar)h\times r$，故 $|\dot r|/2=\sqrt{|h|^2-(h\cdot r)^2}/\hbar$，即上式。 这需要能量与 $\hbar$ 的校准；不是“有面积”本身给出秒。 几何相位与球面面积无量纲，乘以 $\hbar$ 是作用量尺度，仍不是时间。

### 7.2　静态整体的内生关系时间

下面给出一个 *附带明确输入* 的内生钟模型，不把它并入 $\mathcal Q_{22}$ 的已证结论。 给共同空间 $\mathcal H_C\otimes\mathcal H_S$、两个 Hamiltonian、静态整体 $|\Omega\rangle$，满足

$$
(H_C\otimes I+I\otimes H_S)|\Omega\rangle=0.
$$

给协变钟态 $|t\rangle=e^{-iH_Ct/\hbar}|0\rangle$，定义条件态

$$
|\psi(t)\rangle=(\langle t|\otimes I)|\Omega\rangle.
$$

在这些微分与条件化合法的范围内，

$$
i\hbar\frac{d}{dt}|\psi(t)\rangle
=-(\langle t|H_C\otimes I)|\Omega\rangle
=H_S|\psi(t)\rangle.
$$

因此静态整体和内生相对演化可以共存。 张量分解、约束、钟协变及共同尺度仍是输入。 有限资源钟与连续测量的实现还需要额外核查，近期研究已给出不同实现不等价的明确情形。[\[7\]](#ref-clock)

### 7.3　同一个读出能否承担全部历史

#### 定理 7.3：目标恢复的纤维判据

设非空来源集 $X$，读出 $O:X\to Y$，目标 $T:X\to Z$。 存在 $R:Y\to Z$ 满足 $T=R\circ O$，当且仅当

$$
O(x)=O(y)\Longrightarrow T(x)=T(y)\quad\forall x,y\in X.
$$

**证明。**

必要性直接代入。充分性在 $O(X)$ 上令 $R(O(x))=T(x)$；纤维条件保证良定义。 取一个 $x_0\in X$，在 $Y\setminus O(X)$ 上令 $R=T(x_0)$。

$\square$

此为项目已有正式接口。[\[16\]](#ref-recovery) 取空历史和 $g g^{-1}$，算子读出都为 $I$，状态端点相同，但操作计数是 $0$ 与 $2$。 沿同一路径往返还能使有向面积相消，正耗时依然不为零。 所以保留端点或有向面积，都不自动保留完整时间历史。[\[15\]](#ref-omega)

### 7.4　所有新过程可以内生，但不能全塞进同一三维类型

有限表达式由 $D$ 和实线性组合构成时，结构归纳保证其值仍在 $V$，且返回律可递归代入。 但表达式值相同不保证表达式、来源历史或证明相同。

在 $E=\mathbb R\oplus V$ 上，全部实线性过程的空间为

$$
\operatorname{End}_\mathbb R(E)\simeq E\otimes_\mathbb RE,
\qquad\dim\operatorname{End}_\mathbb R(E)=16>4=\dim E.
$$

因此不存在把全部线性过程忠实线性编码为同型元素的单射。 它们仍可从内部二元关系构造：

$$
T_{a,b}(x)=h(b,x)a,
\quad
T_{a,b}T_{c,d}=h(b,c)T_{a,d}.
$$

三次接续两种括号都给 $h(b,c)h(d,e)T_{a,f}$。 这满足二元构造与三元相容，同时保留对象与过程的类型差异。 一般线性过程不都保持正，不能直接称为可执行量子操作。

若把观察者的有限记录也纳入模型，可以另取记录空间、联合态和条件化。 它使用第 10 节所声明的复合扩张；“观察者内生”不赋予未知过程免费识别或无限记忆。

<a id="section-8"></a>

## 8　三元相容不能只解释成逐对没有冲突

### 8.1　三阶正表仍不控制全表

#### 命题 8.1：四元反例

令

$$
G=\frac75I_4-\frac25\mathbf1\mathbf1^{\mathsf T}.
$$

每个不超过三阶的主子矩阵正定，但整个 $G$ 不半正定。

**证明。**

一个 $m$ 阶主子矩阵的特征值为 $7/5$（重数 $m-1$）及 $(7-2m)/5$。 $m\le3$ 时都正；$m=4$ 时后者为 $-1/5$。

$\square$

这不反驳本稿的三元返回律，因为它对全部线性组合及生成输出量化， 不是仅给有限原标签表的三阶子块作检查。 项目 C128 正在解决的也正是原加法、受限三表与全部有限表之间的恢复问题，而非省略这个桥。[\[12\]](#ref-c128)

### 8.2　任取两测量可读也不等于三个共同可读

已知量子例子为

$$
E_k(\pm)=\tfrac12(I\pm\eta\sigma_k),\quad k=x,y,z.
$$

任意两者联合可测当且仅当 $\eta\le1/\sqrt2$；三者共同联合可测当且仅当 $\eta\le1/\sqrt3$。 取 $\eta=3/5$ 就落在二者之间。对锐投影测量，这一反例不适用：两两可共同测量等价于两两对易， 并可得到共同联合。[\[11\]](#ref-joint)

因此“可在一个模型中共同描述”“两两比较值存在”“有共同测量”“旧关系无损延拓”是不同条件。 改变原测量精度或删除约束可以改变相容性，但那是新的关系任务。 同在 $\Omega$ 内不能消除原任务的真实矛盾。

<a id="section-9"></a>

## 9　不动点、正交返回与有限线性提升

### 9.1　任意不动点是关系交点，不自动是量子态

对任意 $f:X\to X$，

$$
x=f(x)\quad\Longleftrightarrow\quad (x,x)\in\Gamma_f\cap\Delta_X.
$$

这一形式没有蕴含正性、线性、面积、概率或维数。

#### 命题 9.1：$\cos x=x$ 的固定点

该方程有唯一实解 $c\approx0.7390851332$，每个实初值的迭代 $x_{k+1}=\cos x_k$ 都趋于 $c$。

**证明。**

一次迭代进入 $[-1,1]$；该区间在 $\cos$ 下保持，且导数绝对值至多 $\sin1<1$。 压缩性给唯一固定点和收敛。

$\square$

在此固定点，$f'(c)=-\sin c\approx-0.6736120292$，是交替衰减。 本稿 $J_n^2=-I$ 则是保长度的两次正交返回。 两者都出现负号，但前者为收缩，后者为可逆旋转，不能互换。

### 9.2　精确提升的闭合条件

#### 定义 9.2：保留原读数的有限线性提升

给 $f:X\to X$ 与原读数 $h:X\to\mathbb R$。 若存在有限 $N$、$K\in M_N(\mathbb R)$、$\Theta:X\to\mathbb R^N$、线性 $\ell$，满足

$$
\Theta(f(x))=K\Theta(x),\qquad h(x)=\ell\Theta(x),
$$

称其为精确有限线性提升；仿射常数由加入特征 $1$ 处理。

#### 命题 9.3：必要且充分条件

上述含常数的提升存在，当且仅当 $\operatorname{span}_\mathbb R\{1,h,h\circ f,h\circ f^2,\ldots\}$ 有限维。

**证明。**

前向所有 $h\circ f^k=\ell K^k\Theta$ 落入有限特征张成。 反向对这个有限维、被 $g\mapsto g\circ f$ 保持的空间选基，即得 $K$ 与 $\Theta$。

$\square$

#### 命题 9.4：$\cos$ 不容许保留原 $x$ 的有限精确线性提升

在任意非空开区间，$1,x,\cos x,\cos(\cos x),\ldots$ 线性无关。 故在非空前向不变开区间，保留 $h(x)=x$ 时不存在任何有限维精确提升。

**证明。**

若有限线性关系成立，解析恒等原理使其延拓到全实轴。 $x$ 无界而所有正次迭代有界，先得 $x$ 的系数为零。 令 $y=\cos x$，其像包含开区间，再次解析延拓便使下一层的线性 $y$ 项系数为零。 重复至所有系数为零。有限提升将由 Cayley–Hamilton 给一个非零常系数关系，与此矛盾。

$\square$

这些固定点边界已在 R5-021 原稿中出现；本轮保留它们而不重计为新发现。 真正新增的核心不是一个吸引点，而是对全部关系和关系输出成立的返回恒等式。

<a id="section-10"></a>

## 10　从单比特到完整有限量子过程：哪些还需外部输入

### 10.1　标准结构的恢复表

| 标准量子内容 | 本轮状态 | 精确条件 |
|:---|:---|:---|
| 二维复 Hilbert 表示 | 数学上已构造 | $\mathcal Q_{22}$ 的三维定向与 Pauli 代数 |
| 纯态与混态 | 数学上已构造 | 正平方锥、归一正线性读出定义 |
| Born 配对与 POVM 数学形式 | 已得到 | 用全部正线性泛函与 $\sum e_i=u$；实际全可实施性未给 |
| 酉群与连续旋转 | 已得到 | 指定生成方向给数学参数 $s$；具体 $H,t,\hbar$ 另给 |
| 投影／平方根仪器 | 存在构造 | 原效果不唯一规定实际状态更新 |
| 任意多系统张量积 | 未由单体唯一推出 | 需要复合关系与整体正锥 |
| 所有 CP、CPTP 过程 | 条件构造 | 需要参考系统层级与可用过程规则 |
| 测量记录、内生钟、全历史 | 条件构造 | 需要记录类型、联合、钟约束及来源供应 |
| 量子场论、物理时空与作用量尺度 | 未推出 | 没有从本局部几何给出这些输入 |

### 10.2　同一单体有不同复合正锥

已经恢复两个 qubit 后，线性张量空间上至少可考虑

$$
\begin{aligned}
C_{\min}&=\operatorname{cone}\{A\otimes B:A,B\ge0\},\\
C_q&=\{X\in\operatorname{Herm}_4(\mathbb C):X\ge0\},\\
C_{\max}&=\{X:\langle a\otimes b|X|a\otimes b\rangle\ge0\quad\forall a,b\}.
\end{aligned}
$$

有 $C_{\min}\subsetneq C_q\subsetneq C_{\max}$。 归一 Bell 投影在 $C_q$ 中，其部分转置为交换算子 $F/2$，在反对称方向有负特征值， 故它不属于 $C_{\min}$。 另一方面 $\langle a\otimes b|F/2|a\otimes b\rangle=|\langle a,b\rangle|^2/2\ge0$， 故 $F/2\in C_{\max}\setminus C_q$。 单体态、单体概率与乘积效果没有唯一选出 $C_q$。

Jordan 结构加合适复合、局部层析和 qubit 的成熟重构定理，正是填补这个层级的研究， 而不是把“整体”一词当作已给张量正锥。[\[8\]](#ref-wilce)

### 10.3　一个明确付费的标准完成

若 *另选* 以下数学扩张，可以构造完整有限维标准量子过程：

- **C1.** 允许有限张量积 $M_2(\mathbb C)^{\otimes k}$ 及其投影支撑角 $P M_{2^k}(\mathbb C)P$，并使用其矩阵正锥。

- **C2.** 过程取复线性映射，要求与每个允许参考系统旁接后仍保正；确定过程保迹，分支过程不增迹。

第一项已经选择复合结构，第二项已经选择完全正的操作性要求。它们不是从返回律推出。

任意 $d$ 可取 $2^k\ge d$ 及秩 $d$ 投影，得到 $P M_{2^k}(\mathbb C)P\simeq M_d(\mathbb C)$。 在该模型中，完全正映射的 Kraus 形式可以直接证明：

$$
C_\Phi=\sum_{ij}|i\rangle\langle j|\otimes\Phi(|i\rangle\langle j|)\ge0.
$$

谱分解 $C_\Phi=\sum_\alpha|v_\alpha\rangle\langle v_\alpha|$， 将 $v_\alpha$ 重排为矩阵 $K_\alpha$，逐矩阵单位比较给

$$
\Phi(\rho)=\sum_\alpha K_\alpha\rho K_\alpha^\dagger,
\qquad
\Phi\text{ 保迹}\Longleftrightarrow\sum_\alpha K_\alpha^\dagger K_\alpha=I.
$$

反向任意此类夹心和在旁接参考后保持正。 因此完全正要求与 Kraus 表示等价，保迹给标准确定过程。

测量分支取有限标签集 $i$ 时，另要求共同归一化 $\sum_{i,\alpha}K_{i\alpha}^\dagger K_{i\alpha}=I$。 不完整仪器可取小于等于 $I$，并显式保留未记录的剩余权重。 每个分支各自不增迹不能代替这条总预算。此时

$$
\mathcal I_i(\rho)=\sum_\alpha K_{i\alpha}\rho K_{i\alpha}^\dagger,
\quad E_i=\sum_\alpha K_{i\alpha}^\dagger K_{i\alpha},
\quad p_i=\operatorname{Tr}(\rho E_i).
$$

把标签写入内部记录空间，得到

$$
\rho\longmapsto\sum_i\mathcal I_i(\rho)\otimes|i\rangle\langle i|.
$$

这是观察者记录的一个内生构造。任意数学过程的实际设备可实现性，仍不是表示定理的结论。

本节给一个自洽完成，并证明其中标准形式的对应；它没有证明完成唯一。 若任务要求从更原始操作公设唯一推出这整个完成，应使用完整过程重构的额外前件， 而不能把 C1–C2 的定义选择隐藏起来。[\[5\]](#ref-selby), [\[6\]](#ref-nakahira)

<a id="section-11"></a>

## 11　反向删除、闭合账本与白话描述

### 11.1　删除条件会发生什么

| 拟删除或替换的内容 | 明确反例／缺口 | 被影响的关系 |
|:---|:---|:---|
| 至少两个独立方向 | $V=\mathbb R,D=0$ 满足返回式 | 无非零面积，不能得三维 |
| 正定可分离比较 | 零半内积、$D=0$ 可在任意维满足返回式 | 所有区别均不可读 |
| 三元返回律 | $D=0$ 可在任意实内积空间定义 | 二元正尺没有选出转向 |
| 全域量词 | 零、输出和线性组合可能不在测试域 | 本定理的递归闭合证明失去前件 |
| 三元相容仅保留至三阶正表 | 第 8 节四阶 Gram 反例 | 局部正性不能保证整体正性 |
| 正线性读出改为只有旋转不变 | $p_k=(1+t^{2k+1})/2$ | Born 仿射配对不再唯一 |
| 第三态或实际路径一概删掉 | $\Delta_3=(1\pm i)/4$ | 同二态概率仍有不同环相位 |
| 时间由长度或面积唯一恢复 | $H\mapsto\lambda H,T\mapsto T/\lambda$ | 相同几何留下时间尺度纤维 |
| 把所有过程压回同型对象 | $\dim\operatorname{End}(E)=16>4$ | 过程的忠实线性记录丢失 |

### 11.2　本轮最终输入与输出

**外部数学结构：** B1 实线性载体及非退化维数范围；B2 正定双线性比较；B3 比较输出同类型的总映射。

**独立关系族：** 仅式 (1)，对所有原元素和所有生成输出量化。

**定义选择：** 含单位扩张、平方正锥、全部正归一线性数学读出、复化表示、指定数学仪器。 这些定义给一个具体理论，但没有证明它们全部等于尚未提供的原设备或实际来源。

**闭合推出：** 三维、原 $D$ 的完整正则性、共同手性叉积、面积律、Jacobi、$SO(3)$、 内生切平面复结构、正锥自对偶、单比特的 Born 形式和酉形式、投影仪器存在、切平面正核及面积饱和。

**完整有限过程的新增扩张：** C1 张量／支撑角及矩阵正锥；C2 全参考正性与迹预算。 内生钟另需联合分解、Hamiltonian 约束、钟协变和尺度。 没有证明这些扩张族独立且最少，也没有证明只靠正性便唯一选出它们。

若用一个新名称“相融”定义返回式，再要求全部关系相融，模型筛选条件仍是同一返回式。 定义性改写可以缩短语言，但不自动减少逻辑输入。

**本轮没有推出：** 所有物理场等于时间、所有波等于面积、所有粒子等于线、宇宙全历史可压入一个三维球、 一个共同本体态唯一决定全部实际观察者的具体读出、或数学输入总数已经为零。

### 11.3　完整白话

两种存在可以比较；比较产生的关系还必须接受同一种比较。 先由两个方向组成有向面积，再用任何内部方向去比较它，所得结果必须回到原两方向的平面， 而且保留原来的投影关系。这一条返回约束足够把比较空间锁成三维，并让转向自动成为线性的叉积。 固定一个内部态，它周围的两种正交变化组成一个平面：转一次得到正交方向，转两次得到反向， 长度和面积因此成为同一正性关系的两种读出。 正对象没有负概率；负号描述比较的反向。 观察者可以用同一正锥表示，但观察者的记录、过程与时钟仍须在整体中保留各自信息。 线与面积可以统一，任意回路与完整时间却不能只从两个端点恢复。

## 参考来源

<a id="ref-ashtekar"></a>

\[1\] A. Ashtekar, T. A. Schilling.  *Geometrical Formulation of Quantum Mechanics*  (1997). [arXiv:gr-qc/9706069](https://arxiv.org/abs/gr-qc/9706069).

<a id="ref-projector"></a>

\[2\] J. Mitscherling, A. Avdoshkin, J. E. Moore.  *Gauge-invariant projector calculus for quantum state geometry and applications to observables in crystals* . Phys. Rev. B 112, 085104 (2025). [arXiv:2412.03637v2](https://arxiv.org/html/2412.03637v2); [DOI:10.1103/qscv-qxqt](https://doi.org/10.1103/qscv-qxqt). 核对表 1 与投影几何部分。

<a id="ref-bargmann"></a>

\[3\] S. Tamate, K. Ogawa, M. Kitano.  *Bloch sphere representation of three-vertex geometric phases* . Phys. Rev. A 84, 052114 (2011). [arXiv:1107.5447](https://arxiv.org/pdf/1107.5447). 本稿与原文三点乘积的环路顺序相反，符号已分别标明。

<a id="ref-jordan"></a>

\[4\] H. Barnum, J. Hilgert.  *Strongly symmetric spectral convex bodies are Jordan algebra state spaces* . [arXiv:1904.03753](https://arxiv.org/abs/1904.03753). 强对称、谱性与有限紧凸背景均保留。

<a id="ref-selby"></a>

\[5\] J. H. Selby, C. M. Scandolo, B. Coecke.  *Reconstructing quantum theory from diagrammatic postulates* . Quantum 5, 445 (2021). [DOI:10.22331/q-2021-04-28-445](https://quantum-journal.org/papers/q-2021-04-28-445/).

<a id="ref-nakahira"></a>

\[6\] K. Nakahira.  *Two Operational Principles Single Out Quantum Theory* . [arXiv:2605.23217v1](https://arxiv.org/html/2605.23217v1) (2026，预印本). 核对 Theorem 51 与 Appendix A.2；本次未独立认证全文证明。

<a id="ref-clock"></a>

\[7\] L. Hausmann, A. Schmidhuber, E. Castro-Ruiz.  *Measurement events relative to temporal quantum reference frames* . Quantum 9, 1616 (2025). [DOI:10.22331/q-2025-01-30-1616](https://quantum-journal.org/papers/q-2025-01-30-1616/).

<a id="ref-wilce"></a>

\[8\] H. Barnum, A. Wilce.  *Local tomography and the Jordan structure of quantum theory* . Foundations of Physics 44, 192–212 (2014). [arXiv:1202.4513](https://arxiv.org/abs/1202.4513). 结论依赖其复合、因子化、局部层析等前件。

<a id="ref-cross"></a>

\[9\] B. Walsh.  *The Scarcity of Cross Products on Euclidean Spaces* . American Mathematical Monthly 74, 188–194 (1967). [DOI:10.2307/2315620](https://www.jstor.org/stable/2315620). 本稿三元返回分类采用自足证明，不把范数叉积分类的前件偷换为任意总映射。

<a id="ref-englert"></a>

\[10\] B.-G. Englert.  *Fringe Visibility and Which-Way Information: An Inequality* . Phys. Rev. Lett. 77, 2154 (1996). [DOI:10.1103/PhysRevLett.77.2154](https://doi.org/10.1103/PhysRevLett.77.2154). 本稿 $\mathcal P$ 是先验路径偏置，未冒称一般探测器可区别度。

<a id="ref-joint"></a>

\[11\] T. Heinosaari, D. Reitzner, P. Stano.  *Notes on Joint Measurability of Quantum Observables* . [arXiv:0811.0783v2](https://arxiv.org/pdf/0811.0783) (2008). 核对 Propositions 1–2 与 Example 1。

<a id="ref-c128"></a>

\[12\] 固定项目快照：[C128：正交迹与角关系续卷](https://github.com/the-omega-institute/trureturing/blob/5d356c7b7e9b0fc64a3c88286402d43ecb54f4a5/docs/develop/theory/AURIC_C128_ORTHOGONAL_TRACE_AND_CORNER_RELATIONS_CONTINUATION.md)，§§468–478。理论正文，非本轮机器认证。

<a id="ref-boundary"></a>

\[13\] 固定项目快照：[FIB-ATOM：稳定关系边界与三维闭合](https://github.com/the-omega-institute/trureturing/blob/5d356c7b7e9b0fc64a3c88286402d43ecb54f4a5/docs/develop/theory/AURIC_FIB_STABLE_RELATION_BOUNDARY_THREE_DIMENSIONAL_CLOSURE.md)，§§1–5，尤其命题 3.1、4.4、5.2。

<a id="ref-repobargmann"></a>

\[14\] 固定项目快照：[C129QubitBargmann.lean](https://github.com/the-omega-institute/trureturing/blob/5d356c7b7e9b0fc64a3c88286402d43ecb54f4a5/D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.lean)，`triple_bargmann_bloch` 与 `explicit_state_orientation`。源码注记的未完审计：[issue \#27571](https://github.com/the-omega-institute/trureturing/issues/27571)；本轮未重编。

<a id="ref-omega"></a>

\[15\] 固定项目快照：[AURIC OMEGA 静态相融纤维理论](https://github.com/the-omega-institute/trureturing/blob/5d356c7b7e9b0fc64a3c88286402d43ecb54f4a5/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)，历史／操作／时钟区分、回路共同不动点与观察者内生部分。

<a id="ref-recovery"></a>

\[16\] 固定项目快照：[TargetRecoveryCriterion.lean](https://github.com/the-omega-institute/trureturing/blob/5d356c7b7e9b0fc64a3c88286402d43ecb54f4a5/D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean)，`target_recovery_criterion`。本稿给首项等价的普通证明，未声称本轮重新编译该声明。

## 12　全域平面返回与代数不共线的无尺入口

### 12.1　定义与整个原空间上的结论

**定义 12.1（同一关系的两个条件）。** 设 $V$ 为任意实向量空间，$D:V\times V\to V$ 为非零交替双线性总映射。记 $L_a b=D(a,b)$。要求

$$
D(D(a,b),c)\in\operatorname{span}_{\mathbb R}\{a,b\}
\qquad\forall a,b,c\in V,
\tag{12.P}
$$

以及

$$
D(a,D(a,b))\in\mathbb R D(a,b)
\ \Longrightarrow\ D(a,b)=0
\qquad\forall a,b\in V.
\tag{12.N}
$$

这里 $\mathbb R0=\{0\}$。条件 N 排除非零响应再次与原输入作用后仍落在该响应的一条线上，包括再次作用为零的情形。P 与 N 对整个原 $V$ 量化，因而也适用于任意和、实倍数及任意有限次生成的输出；没有另选测试域。入口不含有限维、比较尺、范数、拓扑、连续参数、Jacobi、生成性、商空间或共同有界群。

**定理 12.2（无尺入口的三维正定刚性）。** 定义 12.1 蕴涵整个原 $V$ 三维。只在此有限性结论之后定义

$$
g_D(a,b)=-\frac12\operatorname{Tr}_V(L_aL_b).
\tag{12.1}
$$

它是正定对称实双线性形式，并且对全部原向量有精确返回

$$
D(D(a,b),c)=g_D(a,c)b-g_D(b,c)a.
\tag{12.2}
$$

这是同一个原 $D$ 的唯一返回比较尺。每个非零原向量都是实际二元输出；对每个 $a\ne0$，

$$
\ker L_a=\mathbb Ra,\qquad
\operatorname{im}L_a=a^{\perp_{g_D}},\qquad
\operatorname{rank}L_a=2.
\tag{12.3}
$$

原 $D$ 相对于其自身确定的定向是 $g_D$ 的单位叉积，满足 Jacobi。所有原行的指数生成的代数子群恰为 $SO(V,g_D)$，无需取闭包。反向，三维正定空间上任一手性的单位叉积都满足定义 12.1。下面分别证明入口桥与这些结论。

### 12.2　输出平面、中心与维数

**引理 12.3（实际非零输出唯一确定原输入平面）。** 若 $w=D(a,b)\ne0$，则 $a,b,w$ 线性独立，且

$$
\operatorname{im}L_w=\operatorname{span}\{a,b\},\qquad
L_w|_{\operatorname{span}\{a,b\}}\text{ 为线性同构}.
\tag{12.4}
$$

因此同一个非零输出，甚至它的任一非零实倍数，不能来自两个不同的输入平面。

**证明。** 交替双线性首先使 $a,b$ 独立。若 $w=sa+tb$，则 $D(a,w)=tw\in\mathbb Rw$，N 会使 $w=0$，矛盾。因此 $w$ 不在原平面 $F=\operatorname{span}\{a,b\}$。

P 给 $L_w(V)\subseteq F$。对任意 $0\ne x=sa+tb\in F$，可选 $y=ua+vb$，使 $sv-tu=1$，从而 $D(x,y)=w$。若 $L_wx=0$，交替性给 $D(x,w)=0$；对 $(x,y)$ 用 N 又得到 $w=0$。所以 $L_w|_F$ 单射。二维 $F$ 上的单射是满射，故它的像恰为 $F$，同时也是整个 $L_w$ 的像。若 $D(a',b')=\lambda w$，$\lambda\ne0$，则同样的结论给

$$
\operatorname{span}\{a',b'\}
=\operatorname{im}L_{\lambda w}
=\operatorname{im}L_w=F.
$$

这里尚未使用整个 $V$ 的有限维性。$\square$

**引理 12.4（没有中心，也没有独立输入的零响应）。** 在定义 12.1 下，

$$
Z:=\{z:D(z,v)=0\ \forall v\in V\}=0,
\qquad
D(a,c)=0\ \Longleftrightarrow\ a,c\text{ 线性相关}.
\tag{12.5}
$$

**证明。** 非零性供应一对实际输入 $a,b$，使 $w=D(a,b)\ne0$。若 $z\in Z$，则 $D(a+z,b)=w$。由引理 12.3，$\operatorname{span}\{a+z,b\}=F$，所以 $z\in F$。交替性又给 $L_wz=0$，而 $L_w|_F$ 单射，故 $z=0$。中心是在原空间中被排除的，没有删去或商掉它。

现在固定任意 $a\ne0$。中心为零使某个 $b$ 满足 $w=D(a,b)\ne0$。若 $D(a,c)=0$，则 $D(a,b+c)=w$。同一输出的平面唯一性给 $c\in\operatorname{span}\{a,b\}$；写 $c=sa+tb$，零响应变成 $tw=0$，所以 $t=0$。这证明 $\ker L_a=\mathbb Ra$。反向由交替双线性成立；$a=0$ 的情形也成立。$\square$

**维数结论的证明。** 再取一个实际非零输出 $w=D(a,b)$ 及其平面 $F$。引理 12.3 给 $L_w(V)=F$ 和 $L_w|_F$ 可逆。对任意原 $v\in V$，在 $F$ 内解唯一的 $L_wp=L_wv$，便有

$$
v-p\in\ker L_w=\mathbb Rw.
$$

又因 $w\notin F$，得到整个原空间的代数直和

$$
V=F\oplus\mathbb Rw.
\tag{12.6}
$$

所以 $\dim V=3$。这个结论覆盖每个原向量；没有先限制到 $a,b$ 的生成子空间，也没有使用无限维上的迹、投影、完备性或指数。$\square$

### 12.3　由系数取得正尺与精确返回

**引理 12.5（实特征线的排除）。** 对每个 $x\in V$，$L_x$ 没有非零实特征值。

**证明。** 若 $L_xy=\lambda y$，$y\ne0$、$\lambda\in\mathbb R\setminus\{0\}$，令 $b=y/\lambda$，则 $D(x,b)=y$ 且 $D(x,y)\in\mathbb Ry$，违反 N。$\square$

此时才使用已经得到的三维性。取上述基 $(a,b,w)$，其中 $w=D(a,b)$。P 给实系数

$$
D(w,a)=pa+qb,\qquad D(w,b)=ra+sb.
\tag{12.7}
$$

$L_w|_F$ 可逆。若 $q=0$，则 $D(w,a)=pa$ 且 $p\ne0$，与引理 12.5 矛盾。因此 $q\ne0$。对输入 $(a,w)$、测试元 $w$ 使用 P，有

$$
D(D(a,w),w)
=(p^2+qr)a+q(p+s)b
\in\operatorname{span}\{a,w\}.
$$

故 $s=-p$。于是 $L_w|_F$ 的矩阵是

$$
\begin{pmatrix}p&r\\q&-p\end{pmatrix}.
$$

若 $p^2+qr>0$，它有非零实特征值；若 $p^2+qr=0$，它不可逆。两种都不可能。因此

$$
\Delta:=-(p^2+qr)>0.
\tag{12.8}
$$

令 $b_0=b+(p/q)a$。直接用双线性得

$$
D(a,b_0)=w,\qquad D(w,a)=qb_0,\qquad
D(b_0,w)=\frac\Delta q a.
\tag{12.9}
$$

还须判定 $q$ 的符号，不能只由非退化性宣称正定。若 $q<0$，令 $\lambda=\sqrt{-q}>0$，则

$$
L_a(\lambda b_0+w)
=\lambda w-qb_0
=\lambda(\lambda b_0+w),
$$

又违反引理 12.5。因此 $q>0$。

**精确比较尺的构造。** 在基 $(e_1,e_2,e_3)=(a,b_0,w)$ 上定义对称双线性形式 $H$，使此基正交且

$$
H(e_1,e_1)=q,\qquad
H(e_2,e_2)=\frac\Delta q,\qquad
H(e_3,e_3)=\Delta.
\tag{12.10}
$$

$q,\Delta$ 都正，所以 $H$ 正定。式 (12.9) 给全部乘法表。为核对精确返回，只需检查第一对输入的三个循环基对与第三槽的三个基向量；两边均三线性，且关于前两槽交替。这九项为

| $(i,j)$ | $D(D(e_i,e_j),e_1)$ | $D(D(e_i,e_j),e_2)$ | $D(D(e_i,e_j),e_3)$ |
|---|---|---|---|
| $(1,2)$ | $qe_2$ | $-(\Delta/q)e_1$ | $0$ |
| $(2,3)$ | $0$ | $(\Delta/q)e_3$ | $-\Delta e_2$ |
| $(3,1)$ | $-qe_3$ | $0$ | $\Delta e_1$ |

它们逐项等于 $H(e_i,e_k)e_j-H(e_j,e_k)e_i$。因此对全部原 $a,b,c$，

$$
D(D(a,b),c)=H(a,c)b-H(b,c)a.
\tag{12.11}
$$

**迹式与唯一性的证明。** 由交替性和 (12.11)，

$$
L_aL_b(c)=H(a,c)b-H(a,b)c,
\qquad L_aL_b=b\otimes H(a,\cdot)-H(a,b)I.
$$

在已经证明的三维空间上，秩一算符 $b\otimes H(a,\cdot)$ 的迹是 $H(a,b)$，而 $\operatorname{Tr}I=3$。故

$$
-\tfrac12\operatorname{Tr}(L_aL_b)=H(a,b).
$$

这就证明 (12.1) 正定、对称、双线性，并证明 (12.2)。基与系数的选择没有留下自由度。事实上，若另一双线性形式 $h$ 也满足同一精确返回式，则对任意 $a\ne0,c$，选与 $a$ 独立的 $b$，有

$$
(h-g_D)(a,c)b-(h-g_D)(b,c)a=0.
$$

独立性给 $(h-g_D)(a,c)=0$；零输入由双线性处理。因此甚至不预设 $h$ 对称或正定，它也只能等于 $g_D$。$\square$

**所有原向量都是实际输出。** 给 $z\ne0$，在已得的三维正定空间中选 $g_D$-单位 $e\perp z$。精确返回给

$$
D(D(e,z),e)=z.
\tag{12.12}
$$

所以 $z$ 本身是实际二元输出，而不只是输出的线性和；零也是输出。若 $z=D(a,b)$，由 (12.2) 立即有

$$
g_D(L_zc,d)
=g_D(a,c)g_D(b,d)-g_D(b,c)g_D(a,d)
=-g_D(c,L_zd).
$$

实际输出覆盖整个 $V$，故每个原 $L_z$ 都斜对称。结合引理 12.4 的核与有限维秩—零度，$L_z$ 在 $z\ne0$ 时秩二，像包含于且等于 $z^\perp$，得到 (12.3)。中心、实际输出、同一输出的不同输入平面、独立零响应及全部核像都已在原 $V,D$ 上确定。

### 12.4　直接复用原分类，处理手性、尺度与群

**原定理 2.2 的适用。** 现在把原来的同一个总映射 $D$、整个原 $V$ 和刚构造的 $g_D$ 代入定义 2.1。非零交替性已使 $V$ 至少含两个独立方向；正定性和完整返回式分别由 (12.10) 与 (12.11) 支付。所以定理 2.2 可直接应用：相对于任一临时正交定向，$D=\pm\times_{g_D}$。这里不再另证或另计叉积分类。

由此三形式

$$
\omega_D(a,b,c)=g_D(D(a,b),c)
$$

是一个单位体积形式；以 $\omega_D$ 为正定向时，原 $D$ 恰为单位叉积。反射将这个定向反转。固定 $g_D$ 的两个手性由 $D$ 与 $-D$ 给出，它们具有相同返回式和迹尺；不要求原 $D$ 对全部反射作为普通向量等变。

**非零尺度。** 若 $\lambda\in\mathbb R\setminus\{0\}$，令 $D^\lambda=\lambda D$。双线性直接给 P、N 保持，且

$$
L_a^\lambda=\lambda L_a,\qquad
g_{D^\lambda}=\lambda^2g_D,\qquad
\omega_{D^\lambda}=\lambda^3\omega_D.
\tag{12.13}
$$

因此负尺度反转手性，绝对尺度改变迹尺。相对于 $D^\lambda$ 自己的尺与定向，它仍是单位叉积。若坚持保留原来的同一把给定尺，返回式容许的共同倍数只有 $\lambda=\pm1$。从同一个 $D$ 读出唯一尺，与从没有标定的关系族得到绝对物理单位，是不同命题。

**Jacobi 与行交换子。** 对 (12.2) 作三个循环相加，六个项因 $g_D$ 对称而两两抵消，故

$$
D(D(a,b),c)+D(D(b,c),a)+D(D(c,a),b)=0.
\tag{12.14}
$$

由 $L_aL_b(c)=g_D(a,c)b-g_D(a,b)c$ 相减又得

$$
[L_a,L_b]=L_{D(a,b)}.
\tag{12.15}
$$

这是已得精确返回及原命题 3.1 的直接应用，不以 Jacobi 为入口。

**精确生成群。** 只在有限维结论之后，定义

$$
\mathcal G_D
=\left\langle\exp(tL_a):a\in V,\ t\in\mathbb R\right\rangle
\subseteq GL(V).
\tag{12.16}
$$

斜对称性给指数保持 $g_D$；行列式沿参数从一连续变化且不为零，故 $\mathcal G_D\subseteq SO(V,g_D)$。若 $a\ne0$，将 $v=v_\parallel+v_\perp$ 按轴 $\mathbb Ra$ 分解，返回式给

$$
\exp(tL_a)v
=v_\parallel+\cos(t\|a\|_D)v_\perp
+\frac{\sin(t\|a\|_D)}{\|a\|_D}D(a,v_\perp),
\qquad \|a\|_D=\sqrt{g_D(a,a)}.
\tag{12.17}
$$

$a=0$ 时指数为恒等。式 (12.17) 来自横面上 $L_a^2=-\|a\|_D^2I$ 的指数级数。

反过来取任意 $Q\in SO(V,g_D)$。在 $g_D$-正交基下，

$$
\det(Q-I)=\det Q\det(I-Q^{-1})
=\det(I-Q^{\mathsf T})=\det(I-Q)=-\det(Q-I).
$$

所以 $Q$ 有单位固定轴 $n$。它在 $n^\perp$ 上的限制是行列式一的二维正交矩阵。选单位 $e\perp n$ 和 $f=D(n,e)$，则 $(e,f)$ 为该平面的正交基，且 $L_ne=f,L_nf=-e$。二维正交矩阵的两列给某个 $\theta\in\mathbb R$，使

$$
Qe=\cos\theta\,e+\sin\theta\,f,\qquad
Qf=-\sin\theta\,e+\cos\theta\,f.
$$

故 $Q=\exp(\theta L_n)$。特别地每个正向等距本身就是一条原行的指数，因而

$$
\mathcal G_D=SO(V,g_D).
\tag{12.18}
$$

这证明的是代数生成子群的精确相等；没有把稠密、闭包或 Lie 代数相等替代群相等。参数 $t$ 此时是导出有限矩阵上的数学参数，不是入口供应的物理时间。

### 12.5　与原有限维逐轴有界入口及全部旧总映射模型等价

**定义 12.6（原逐轴有界条件 B）。** 对有限维实 $V$ 上的非零交替双线性 $D$，任选一把辅助范数 $\|\cdot\|_0$，要求

$$
\forall a\in V\ \exists M_a<\infty\ \forall t\in\mathbb R:
\quad\|\exp(tL_a)\|_{0\to0}\le M_a.
\tag{12.B}
$$

常数允许逐 $a$ 不同，不要求所有轴共有一个界，更不要求任意混合指数词已有共同界。有限维的范数等价使“某把辅助范数”与“每把辅助范数”等价：若 $c\|v\|_0\le\|v\|_1\le C\|v\|_0$，同一个族在新范数下的界至多为 $(C/c)M_a$。逐向量有界也与这里的算符族有界等价，因为可在一组有限基上分别取界再合并。这些都是有限维原入口的量词。

**引理 12.7（逐轴 B 蕴涵 N，不用共同紧性）。** 只要有限维交替双线性模型满足 B，便满足 N。

**证明。** 固定任意原 $a,b$，设 $w=L_ab$ 且 $L_aw=\lambda w$，$\lambda\in\mathbb R$。若 $w\ne0$、$\lambda\ne0$，则

$$
\exp(tL_a)w=e^{\lambda t}w
$$

在全实 $t$ 的一个方向上无界，与这条原轴自己的 $M_a$ 矛盾。若 $w\ne0$、$\lambda=0$，则 $L_a^2b=0$，故

$$
\exp(tL_a)b=b+tw.
$$

由 $\|b+tw\|_0\ge |t|\|w\|_0-\|b\|_0$，仍与同一条轴的 B 矛盾。故只能 $w=0$，正是 N。这个证明既未组合不同轴，也未平均任何群。$\square$

**定理 12.8（同一原 $V,D$ 的三种完整模型类）。** 下列模型在遗忘已给比较尺后，具有完全相同的原有序对 $(V,D)$：

1. 任意实 $V$ 上的非零交替双线性 $D$，满足全域 P 与 N。
2. 有限维实 $V$ 上的非零交替双线性 $D$，满足全域 P 与原逐轴全实参数 B。
3. 原定义 2.1 的全部模型：$V$ 至少有两个独立方向，给正定对称实双线性 $g$，$D:V^2\to V$ 是任意总映射，满足对所有原 $a,b,c$ 的原式 (1)。这里没有预先要求 $D$ 双线性或交替。

每个这样的 $(V,D)$ 向第三类提升的尺恰为 $g_D$，所以尺的遗忘没有丢失选择。

**证明。** 第一类由定理 12.2 得到整个原 $V$ 三维以及 $g_D$ 的精确返回，故属于第三类。各指数在 $g_D$-范数中都是等距，算符范数为一；范数等价随即给原任意辅助范数中的 B，故也属于第二类。此处共同等距性是结论，未被倒用于 B 的逆向。

第二类由引理 12.7 得到 N，P 保持，故属于第一类。

最后从第三类出发，必须先用原定理 2.2 的任意总映射结论：整个原 $V$ 三维，原来的同一个 $D$ 自动成为某一手性的单位叉积，因而自动非零、双线性且交替。原返回式直接给 P。再验证 N：若 $w=D(a,b)\ne0$，则 $a\ne0$、$g(a,w)=0$；叉积的斜性给 $g(D(a,w),w)=0$。若 $D(a,w)=\lambda w$，正定性迫使 $\lambda=0$，但原返回式又给

$$
D(a,w)=g(a,b)a-g(a,a)b.
$$

它为零会使 $b\in\mathbb Ra$，与 $w\ne0$ 矛盾。因此 N 成立，属于第一类。原命题 3.1，或上述秩一迹计算，给原来已给的 $g=-\tfrac12\operatorname{Tr}(L_aL_b)=g_D$。

逆向没有将第三类缩成其预设双线性的子类，也没有换掉原 $D$、原向量、标量或操作域。$\square$

有限维、范数和指数参数因此可以从数学主入口撤去；它们在相应结论之后仍可使用。三个入口定义同一模型类，不等于逻辑总信息严格减少，也不证明全局最少公理或文献优先性。

### 12.6　删除反例与全域量词的边界

**例 12.9（删 P；同时定位仅基三元测试的不足）。** 取

$$
V=\mathbb R^3\oplus\mathbb R^3,\qquad
D((a_1,a_2),(b_1,b_2))=(a_1\times b_1,a_2\times b_2),
$$

两个块使用标准三维叉积。它非零、交替、双线性，总空间六维。以直和 Euclidean 内积计算，所有 $L_a$ 斜对称，且逐块有

$$
\operatorname{im}L_a\perp\ker L_a.
$$

若 $w=L_ab$、$L_aw=\lambda w$，与 $w$ 作内积得 $\lambda\|w\|^2=0$。若 $w\ne0$，则 $L_aw=0$，从而 $w\in\operatorname{im}L_a\cap\ker L_a=0$，矛盾。因此 N 成立；所有指数还是直和等距，B 也成立。

令 $e_1,e_2,e_3$ 是两个块各自的标准基，取

$$
a=(e_1,e_1),\qquad b=c=(e_2,0).
$$

则 $D(a,b)=(e_3,0)$，$D(D(a,b),c)=(-e_1,0)$。若后者等于 $sa+tb$，第二块迫使 $s=0$，第一块就不可能等于 $-e_1$。所以全域 P 失败。

然而对直和的全部六个基向量组成的每个有序三元组，P 都成立：前两输入在不同块时输出为零；在同块时，第三个基向量在另一块给零，在同块则标准叉积返回前两输入平面。这也包括重复指标。因此即使已知双线性、N 和 B，检查所有基三元组仍不能替代 P 对全部线性组合的量词。P 的右侧平面随输入变化，不能把基上的归属关系当作固定目标空间中的三线性恒等式来延拓。

**例 12.10（删 N；保留 P 仍可有中心与额外维数）。** 在 $\mathbb R^4$ 基 $e_1,e_2,e_3,e_4$ 上，规定

$$
D(e_1,e_2)=e_3
$$

及其反向，其他基对均为零。每个输出都是 $e_3$ 的倍数，且 $e_3$ 为中心，故所有 $D(D(a,b),c)=0$，全域 P 成立。但 $D(e_1,D(e_1,e_2))=0$ 而 $D(e_1,e_2)\ne0$，N 失败。维数不是三，$e_4$ 也不是输出。原逐轴 B 在 $a=e_1$ 上失败，因为 $\exp(tL_{e_1})e_2=e_2+te_3$。因此原有限维 P+B 入口中，删掉 B 确实允许这个模型。

**例 12.11（P 与非退化核还不选择正定）。** 在三维基上规定

$$
D(e_1,e_2)=e_3,\qquad
D(e_2,e_3)=-e_1,\qquad
D(e_3,e_1)=e_2,
$$

并交替双线性延拓。令 $h$ 在此基上的矩阵为 $\operatorname{diag}(1,-1,-1)$。对三个循环基对与三个测试基向量代入上述表，得到

$$
D(D(a,b),c)=h(a,c)b-h(b,c)a
\qquad\forall a,b,c.
$$

因此全域 P 成立；同一秩一迹式给 $g_D=h$，它不正定。令 $a=e_3$、$b=e_1+e_2$，则 $D(a,b)=b$，$D(a,D(a,b))=b$，N 失败；$\exp(tL_a)b=e^tb$，B 失败。这是删去 B 后的实指数增长边界，与例 12.10 的零特征值漂移不同。这里甚至每个非零 $a$ 都有 $\ker L_a=\mathbb Ra$：乘法表写成标准叉积后接可逆对角映射 $\operatorname{diag}(-1,1,1)$，零响应仍恰为共线。故仅有零纤维的非退化性不能替代 N 的正定选择。

**例 12.12（删非零性）。** 任意实 $V$ 上的 $D=0$ 满足 P 与 N；有限维时也满足 B，因为每条指数都是恒等。可取四维或无限维，且迹尺在可定义时为零。非零性不能从另外两个条件取得。

**例 12.13（删交替性，即使保留双线性与 B 也失败）。** 令 $W=\mathbb R^2$，$J(x_1,x_2)=(-x_2,x_1)$，$V=\mathbb R\oplus W$，定义

$$
D((s,x),(t,y))=(0,sJy).
\tag{12.19}
$$

它是非零双线性总映射。每个输出第一坐标为零，所以 $D(D(a,b),c)=0$，全域 P 成立。对 $a=(s,x),b=(t,y)$，写 $w=D(a,b)$，则

$$
D(a,w)=(0,-s^2y).
$$

若 $w\ne0$，则 $s\ne0,y\ne0$，而 $y,Jy$ 实线性独立，所以上式不可能在 $\mathbb Rw$ 内。因此 N 成立。每条原行的指数为

$$
\exp(\tau L_{(s,x)})(t,y)=(t,e^{\tau sJ}y),
\qquad \tau\in\mathbb R,
$$

故在标准直和范数中全部等距，B 也成立。但 $D((1,x),(1,x))=(0,Jx)$ 在 $x\ne0$ 时非零，交替性失败。直接取迹得

$$
-\tfrac12\operatorname{Tr}(L_{(s,x)}L_{(t,y)})=st,
$$

只有秩一，不是正定尺。这个模型同时说明不能在引理 12.3 中省去交替性所承担的原输入与输出之间的反向作用。

这些反例保持各自声明的全域量词。原 B 的删除边界包括非零实特征值的两侧指数增长及零特征值的线性漂移；把 B 换成有限参数样本或一段有界参数区间会漏掉这些障碍。全实参数逐轴有界是原逆向使用的条件。

### 12.7　既有结果的前件与参数对应

下列对应区分无尺入口桥与已经具备比较、旋转或量子结构的结论；后者直接消费，不另作新分类。

| 实际正文 | 原前件与已给结果 | 与本节的准确对应 |
|---|---|---|
| 本卷定义 2.1、定理 2.2 | 至少二维实正定空间、任意总 $D$、精确全域返回；自动三维及 $D=\pm\times$ | §12.2–12.3 从 P+N 取得其正定尺与精确返回；随后直接应用原定理。逆向首先用其任意总映射正则性 |
| 本卷命题 3.1 与 §§4、6 | 已得单位叉积和同一正尺；迹、平方锥、正线性读出、Pauli/Born 与切平面正核 | 参数就是本节的原 $D$ 与 $g=g_D$；这些消费者不供应入口所缺的正尺存在性 |
| [OMEGAQ-003](OMEGAQ_003_ORDER_CONTENT_EQUIVALENCE.md) 定义 3.1、引理 3.2、定理 5.2 | 有限全未来预测空间、准确统计逆、概率有界所给的紧忠实群；顺序差商读出同构；矩阵交换子已满足 Jacobi | 它证明原内容空间 $W$ 三维，不能将其有限性、紧性或 Jacobi 倒作本节的前提 |
| OMEGAQ-003 定理 6.1、推论 6.2 | 在已经三维后，由原参照对取得 $\Phi(C_x)=t_0x$，$t_0\ne0$，并定义算符 $D_x=\Phi^{-1}(x)$ | 本节二元关系对应 $D(x,y)=D_xy=t_0^{-1}x\times_{B_0}y$，行算符 $L_x=D_x$，故 $g_D=B_0/t_0^2$。$t_0$ 的符号进入手性，不能漏掉 |
| [OMEGAQ-006](OMEGAQ_006_REGULAR_MUTUAL_ZERO_FIBERS_CONTINUATION.md) 定义 2.1、引理 2.2、定理 4.2 | 有限原预测窗口、紧矩阵作用与其 Lie 代数；一般位置的一对双零纤维；推得 $\mathfrak g=\mathfrak{so}(W)$ | 其二元作用是 $\beta(A,x)=Ax$，两槽类型不同；它不是本节原 $D:V^2\to V$ 的 P 或 N。辛球面步骤使用已经具备的紧性、Jacobi 与正定不变迹配对 |
| OMEGAQ-006 §§7.1–7.3、8、10.1 | 来源轴 $e$ 归一为 $B(e,e)=1$；选择取向构造 $R_xy=x\times_B y$；原概率 Born 表示及原响应身份的条件桥 | 仅有其 Q6 不认定原 $D=R$。若同一原关系另满足 $D=\kappa R$，则 $g_D=\kappa^2B$；同尺使用还须核对 $|\kappa|=1$ 或显式运输尺度 |
| [FIB 稳定关系边界卷](AURIC_FIB_STABLE_RELATION_BOUNDARY_THREE_DIMENSIONAL_CLOSURE.md) 假设 2.3、命题 3.1 | 有限维 $d\ge2$、正定 $g$、非零三线性 $T$、完整三槽 $SO(V,g)$ 不变性；得到 $d=3$ 与 $B=c\times_g$ | 它没有以裸球面传递性推出三维。其非零系数 $c$ 仍须有符号校准，不供应本节的无尺入口 |
| FIB 同卷命题 4.4、5.2–5.3 | 有限维的全部面积和同构要求，及已校准组合的迹回读；固定体积不固定自由度量 | 本节是在整个原 $V$ 推得三维后，才能引用 $\Lambda^2V\simeq V$；对未校准 $B=c\times_g$，其迹尺为 $c^2g$，与 (12.13) 完全一致 |

本节入口证明只用代数直和、二维实矩阵的特征方程和交替双线性展开。秩一迹公式、有限维范数等价、二维正交矩阵的旋转形式及指数级数，都在有限维与所需正定性已经确定后使用。它不借用需要内积相容与范数恒等式的三维／七维向量积分类，不借用需要正定不变配对及 Jacobi 的紧 Lie 代数分类，也没有把三维同型的维数计数用于未知的无限维入口。上述经典事实的前件在相应使用处均已明列。

### 12.8　同一 $g_D$ 的既有消费者与原来源接口

**同尺数学扩张。** 直接在本卷定义 4.1、定理 4.2、4.4 和命题 4.6 中代入 $g=g_D$、$D$ 为原关系，得到

$$
E_D=\mathbb Ru\oplus V,\quad u=(1,0),\qquad
(\alpha,a)\circ(\beta,b)
=(\alpha\beta+g_D(a,b),\alpha b+\beta a),
$$

$$
C_D=\{A\circ A:A\in E_D\}
=\{(t,a):t\ge\|a\|_D\},\qquad
\omega_r(t,a)=t+g_D(r,a),\quad\|r\|_D\le1.
\tag{12.20}
$$

这里 $\omega_r$ 恰为全部正归一实线性读出。采用 $D$ 的自定向正交 Pauli 轴，原有表示就是

$$
\Phi_D(t,a)=tI+a\cdot\sigma_D,\qquad
\rho_r=\tfrac12(I+r\cdot\sigma_D),\qquad
\omega_r(A)=\operatorname{Tr}(\rho_r\Phi_D(A)),
$$

$$
p(m\mid r)=\frac{1+g_D(r,m)}2,\qquad
U_a(t)=\exp(-it(a\cdot\sigma_D)/2).
\tag{12.21}
$$

此处 $\|r\|_D\le1$，$\|m\|_D=1$，二元效果为 $p_m=(u+m)/2$；门公式对所有 $a\in V,t\in\mathbb R$ 成立。更一般的数学效果仍按 $0\le e\le u$ 取值。

因此平方锥、正归一线性读出、单比特 Born 配对及旋转的酉提升用的是同一把 $g_D$，没有另选正尺。证明及适用边界直接由原 §§4、6 提供；这些公式、四元数／Pauli 结构和 Born 事实不构成另一个新增分类。

**原评价的身份。** 若给定实际来源，必须先给保留原单位、原向量与原关系的线性识别，以及原对称比较确实为上述 $\circ$ 的身份。对每个原事件，其评价须仍为同一实线性泛函，原正准备与原效果须在同一正锥及对偶关系内，完整测试须满足原来的总和归一。此时若原事件写作 $e_f=(\alpha,b)$、原准备对应 $r$，就有

$$
p_f=\omega_r(e_f)
=\alpha+g_D(r,b)
=\operatorname{Tr}\bigl(\rho_r(\alpha I+b\cdot\sigma_D)\bigr).
\tag{12.22}
$$

这是原数值的表示，全部原成功、失败、零标签、记录及合法未来均需保留；不能以重新定义一份数学概率替代这些身份条件。只从 P+N 得到 $C_D$ 的数学存在，不自动证明它等于某个已给来源的全部准备或效果。

**来源归一的尺度运输。** OMEGAQ-006 的来源尺 $B$ 与本节迹尺相同，需要原关系的身份和尺度，而不是只凭同一载体名称。若另有同一原群的完整协变，已构造的叉积为 $R=\times_B$，并已确定原 $D=\kappa R$，则置

$$
s=\sqrt{g_D(e,e)}=|\kappa|>0,
\qquad B=g_D/s^2,
\qquad B(e,e)=1.
$$

该来源卷的原评价若为 $f(tc+w)=\alpha t+B(b,w)$，则设 $r=w/s$、$b_D=b/s$，严格有

$$
f(c+w)=\alpha+g_D(b_D,r)
=\operatorname{Tr}\bigl(\rho_r(\alpha I+b_D\cdot\sigma_D)\bigr).
\tag{12.23}
$$

来源轨道与球的归一也同样运输：$B(w,w)\le1$ 当且仅当 $g_D(r,r)\le1$。这只是保留原概率的参数对应，不宣称原对称乘法已等于 $g_D$ 的乘法。若要求原乘法、原响应与此扩张同时具有相同标定，还须原尺度合同给出 $s=1$。没有群协变或原响应身份时，不能仅由两个三维结论推出 $B$ 与 $g_D$ 成比例。

**实际供应仍是条件接口。**

| 要连接的原对象 | 必须给出的同一来源关系 | 可直接使用的既有结论 |
|---|---|---|
| 实际可逆门 | 对指定原 $a,t$，存在原合法调用，其在完整原内容上的作用恰为 $\exp(tL_a)$，并保留原接续、逆及记录；稠密逼近不等于精确调用 | 若全部这些指数实际供应，(12.18) 给其生成作用恰为全部 $SO(V,g_D)$；Pauli 提升由原命题 4.6 给出。它不认定额外原门均属于此菜单 |
| 原有向响应与比较 | 原全对象及实际联合对象上的零接触、全内协变、完整中心与同一指针尺度等合同；不能只查平方或删掉中心输出 | OMEGAQ-006 §10.1–10.3 所复用的 C127 条件桥接回原导子及其标定；本节原 $V$ 的中心为零不替代含单位或多块中心合同 |
| 多系统、参考与全部状态 | 共同复中心的相容识别、指定的联合与完整矩阵正锥、局部与联合原准备／效果的身份；生成型联合才可用相应生成分类 | 本卷 §10 与 OMEGAQ-006 §9.1–9.5；单体球不唯一决定复合锥，两个局部复中心也不自动相同 |
| 同一物理分支与仪器 | 自伴部分实线性及其复线性延拓；同一分支旁接实际完整矩阵参考后在整个联合正锥保正；完整记录的共同迹预算 | OMEGAQ-006 定理 9.9 的 Choi–Kraus 结论；输入维 $d$ 时参考矩阵维数至少 $d$ 足够。仅经典参考或乘积态正性不足，Kraus 指标不自动是原记录 |
| 锐读口、更新与失败 | 实际指针、精确合法门词、全标签、原遗忘与具名支持返回；理想更新另须投影效果及对其支撑内每个态无扰动 | 原命题 4.6、OMEGAQ-006 定理 9.10 与 §10.3；效果概率本身不唯一规定更新，不能通过条件归一抹去原成功质量 |
| 内部记录与钟、作用量 | 记录类型和共同联合、条件化；若用关系钟，另给分解、总约束、钟协变、Hamiltonian 与共同尺度 | 本卷 §§7.1–7.4；同端点或同面积可有不同历史，$H\mapsto\lambda H,T\mapsto T/\lambda$ 保门而改耗时，$\hbar$ 不能由角度读出 |

具体地，原响应身份接口中的零接触仍是对每个原对象及实际联合对象 $A$、每个 $a\in E_A$、每个原正元 $x$ 和每个原实际准备 $\alpha$ 的条件

$$
\alpha(x)=0\ \Longrightarrow\ \alpha(\mathscr D_ax)=0.
$$

这里 $\mathscr D_a$ 表示含单位原对象上已给的响应，须另核对其在 $V$ 上的限制确实为本节 $L_a$。全内协变与同一实际指针 $P$ 的标定仍为

$$
[K,\mathscr D_a]=\mathscr D_{Ka},\qquad
-\operatorname{Tr}_{\mathbb R,E_P}(\mathscr D_{d_0}^{\,2})
=\operatorname{Tr}_{\mathbb R,E_P}((M_{d_0}^{\circ})^2),
\qquad d_0=d-z_P(d),
$$

其中 $K$ 遍历原合同允许的内导子，$M_a^\circ(x)=a\circ x$，$z_P$ 是完整 Jordan 中心投影。还保留该来源合同的实际身份参考和实际准备正锥包覆盖完整正对偶等前件；上述三个式子不能单独替代它们。

同一分支的参考条件量化整个标准联合正锥，而非仅可分态：$\mathcal E\otimes\operatorname{id}_r$ 在全部 $X\ge0$ 上保正，$r\ge d$。所有原记录 $k$ 共用预算

$$
\sum_{k,\mu}K_{k\mu}^*K_{k\mu}=I,
$$

若原仪器不完整则为小于等于 $I$，其余质量须作为原失败部分保留。关系钟的条件则仍是共同 $\mathcal H_C\otimes\mathcal H_S$ 上的

$$
(H_C\otimes I+I\otimes H_S)|\Omega\rangle=0,\qquad
|t\rangle=e^{-iH_Ct/\hbar}|0\rangle,
$$

并仅在这些微分和条件化合法的范围内使用原 §7.2 的 Schrödinger 条件态结论。这些量词均不由局部三维几何替代。

这些条件决定特定物理来源能否采用已有数学表示；不把全部实际供应当作无尺入口定理的前提或额外数学结论。模型定义、条件定理、等价表示与经验主张分别按自己的条件成立。正定几何的证明不要求先无前提推出全部物理；其成立也不推出物理空间、整个 $\Omega$ 或全部历史只有三维。

### 12.9　一段完整白话

先不画球，不放尺，也不假定空间只有几个方向，只给同一个可以相加、缩放的二元关系：两个方向先产生一个响应，这个响应再同任何原方向作用，结果总要回到最初两个方向的平面；而一个非零响应再次同原输入作用时，不能塌回响应自己的同一条线，连塌成零也不允许。第二条先使非零响应离开原平面，并使它对这个平面的作用可逆；第一条于是让同一非零响应只能对应一个原平面。不可见的中心方向和独立却无响应的输入都会制造两个不同平面给出同一输出，所以都被排除。任取一份实际非零响应，它的像就是这个二维平面，核只剩响应自身的一维轴，每个原向量因而都分解成平面部分与轴部分，整个原空间只能是三维。继续核对同一关系的系数，不能落回同线的条件又排除实增长方向，迫使返回系数组成一把正尺；这把尺正是原行算符乘积的负半迹，原关系相对于自己的左右手约定成为单位叉积。此后才有范数、旋转指数和数学参数，原来的正平方锥、正归一线性读出与单比特表示可以原样接上；真实准备、门、复合、记录、钟和作用量仍各须同源接口。这给出一份完整的纯代数几何候选，不宣称宇宙的全部物理已经推出，也不宣称它是全球最小公理。

## 追加锚（本行以下为增补区）

