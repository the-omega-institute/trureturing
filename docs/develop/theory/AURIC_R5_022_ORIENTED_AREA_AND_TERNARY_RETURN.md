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

**命题 12.9（删除 P 的反例；仅基三元测试仍不足）。** 设
$$
V=\mathbb R^3\oplus\mathbb R^3,
\qquad
D((a_1,a_2),(b_1,b_2))=(a_1\times b_1,a_2\times b_2),
$$
其中两个块都使用标准三维叉积，故 $\dim V=6$。这个模型保留“非零、总定义、交替、双线性”、条件 N 以及有限维逐轴全实参数有界条件 B，删除全域条件 P；它满足所有六个块标准基向量组成的有序三元组上的 P，却不满足对全部原向量量化的 P。具体地，取
$$
a=(e_1,e_1),\qquad b=c=(e_2,0),
$$
则
$$
D(D(a,b),c)=(-e_1,0)\notin\operatorname{span}\{a,b\}.
$$

**证明。** 记第一块和第二块的标准基向量为
$u_i=(e_i,0)$ 与 $v_i=(0,e_i)$。非零性由
$D(u_1,u_2)=u_3$ 给出；逐块叉积使 $D$ 为总的交替双线性映射。

先验证 N。给定 $a$ 和 $w=L_ab$，若 $L_aw=\lambda w$ 且 $w\ne0$，则每个块的叉积算子均斜对称，所以
$$
0=\langle L_aw,w\rangle=\lambda\|w\|^2
$$
迫使 $\lambda=0$。此时 $w\in\operatorname{im}L_a\cap\ker L_a$。在每一块中，若 $a_i\ne0$，则 $a_i\times b_i$ 同时垂直于 $a_i$，而落在 $\ker(a_i\times\mathord\cdot)=\mathbb Ra_i$ 时只能为零；若 $a_i=0$，该块输出本来就是零。因此 $w=0$，N 成立。

取直和 Euclidean 范数。每个 $L_a$ 是两个斜对称叉积算子的直和，故
$\exp(tL_a)$ 是两个正交旋转（零块时为恒等），从而
$$
\|\exp(tL_a)\|_{0\to0}=1\qquad(a\in V,\ t\in\mathbb R).
$$
所以 B 也成立。

现在检查基三元组。若前两项分别属于不同块，则 $D$ 输出为零；若同属一块，则输出仍在该块。对同一块的三个标准基向量，叉积再与同块的任一标准基向量作用所得向量落在前两个基向量张成的平面；与另一块的基向量作用则为零；重复的前两项也直接给零。因此对六个基向量的每个有序三元组，均有
$$
D(D(x,y),z)\in\operatorname{span}\{x,y\}.
$$

但对命题中给出的线性组合，$D(a,b)=(e_3,0)$ 且
$D(D(a,b),c)=(-e_1,0)$。若它等于 $sa+tb$，则第二块给出 $se_1=0$，故 $s=0$；第一块随即要求 $-e_1=te_2$，不可能。故全域 P 失败。这个失败说明右侧平面随输入线性组合变化，基三元组上的归属关系不能替代全域三线性恒等式。$\square$

**命题 12.10（删除 N 的中心与额外维数反例）。** 设 $V=\mathbb R^4$，在基
$e_1,e_2,e_3,e_4$ 上定义交替双线性总映射
$$
D(e_1,e_2)=e_3
$$
及其反向，其他基对均为零。这个模型保留非零性、交替性、双线性、总定义和全域 P，删除 N；它不保留逐轴有界条件 B，并且 N、三维性及“每个非零向量都是输出”的结论均失败。

**证明。** 任意 $a,b\in V$ 的输出都是 $e_3$ 的倍数，而 $e_3$ 是中心元，故
$$
D(D(a,b),c)=0\in\operatorname{span}\{a,b\}
\qquad(a,b,c\in V),
$$
全域 P 成立。可是
$$
D(e_1,D(e_1,e_2))=D(e_1,e_3)=0\in\mathbb R D(e_1,e_2),
\qquad D(e_1,e_2)=e_3\ne0,
$$
所以 N 失败。空间维数为 $4$，而像 $D$ 仅为 $\mathbb Re_3$，例如 $e_4$ 不是任何二元输出。

同时 $L_{e_1}e_2=e_3$、$L_{e_1}e_3=0$，因而
$$
\exp(tL_{e_1})e_2=e_2+te_3.
$$
对任意范数，$\|e_2+te_3\|$ 随 $|t|\to\infty$ 无界，故 B 也失败。这正说明在原有限维 P+B 入口中删去 B（从而不再取得 N）允许该中心和额外维数。$\square$

**命题 12.11（删除逐轴有界与正定选择的反例）。** 在 $V=\mathbb R^3$ 的基上定义非零交替双线性总映射
$$
D(e_1,e_2)=e_3,\qquad
D(e_2,e_3)=-e_1,\qquad
D(e_3,e_1)=e_2,
$$
并交替双线性延拓。令 $h$ 的矩阵为
$\operatorname{diag}(1,-1,-1)$。这个模型保留非零性、交替性、双线性、总定义、全域 P 以及
$\ker L_a=\mathbb Ra$（每个 $a\ne0$），删除 N 和 B；N、B 以及正定迹尺的结论均失败。

**证明。** 对三个循环的前两项和三个基向量作计算，左、右两侧的共同值为
$$
\begin{array}{c|ccc}
(a,b)\backslash c & e_1 & e_2 & e_3\\ \hline
(e_1,e_2)&e_2&e_1&0\\
(e_2,e_3)&0&-e_3&e_2\\
(e_3,e_1)&-e_3&0&-e_1
\end{array}
$$
其中右侧是 $h(a,c)b-h(b,c)a$。两侧都对前两项交替、对第三项线性；因此基计算给出全域恒等式
$$
D(D(a,b),c)=h(a,c)b-h(b,c)a
\qquad\forall a,b,c\in V,
$$
即 P 成立。

令 $\times$ 为标准 Euclidean 叉积，令
$S=\operatorname{diag}(-1,1,1)$。上述乘法表正好是
$$
D(a,b)=S(a\times b).
$$
因 $S$ 可逆，标准叉积的核公式给出
$\ker L_a=\mathbb Ra$ 对每个 $a\ne0$ 成立。

由已经写出的返回式，
$$
L_aL_b(c)=h(a,c)b-h(a,b)c.
$$
秩一算子 $b\otimes h(a,\cdot)$ 的迹为 $h(a,b)$，且 $\operatorname{Tr}I=3$，故
$$
-\tfrac12\operatorname{Tr}(L_aL_b)=h(a,b).
$$
这个迹形式的签名是 $(1,2)$，不是正定。取
$a=e_3$、$b=e_1+e_2$，则 $D(a,b)=b\ne0$ 且
$$
D(a,D(a,b))=D(e_3,b)=b\in\mathbb Rb,
$$
所以 N 失败。又 $L_{e_3}b=b$，从而
$\exp(tL_{e_3})b=e^tb$；该族在任意范数中无界，故 B 失败。这是删除 B 后的实指数增长边界，与命题 12.10 的零特征值线性漂移不同；非退化核本身不能替代 N 所承担的正定选择。$\square$

**命题 12.12（删除非零性的反例）。** 对任意实向量空间 $V$，取零映射 $D=0$。该模型保留总定义、双线性、交替性、全域 P 和 N，删除非零性；它不满足三维正定刚性，也不能产生非零输出。若 $V$ 有限维，它还满足 B；$V$ 可取四维或无限维，而在有限维且迹可定义时 $-\tfrac12\operatorname{Tr}(L_aL_b)=0$。

**证明。** 对所有 $a,b,c$，有 $D(D(a,b),c)=0$，故 P 成立；同时 $D(a,D(a,b))=0\in\mathbb R D(a,b)$，而结论 N 的后件 $D(a,b)=0$ 也成立。有限维时每个 $L_a=0$，所以 $\exp(tL_a)=I$，可取 B 中的 $M_a=1$。由于 $D$ 恒为零，像为零，不能得到非零实际输出、三维性或正定迹尺；有限维时迹式确为零。$\square$

**命题 12.13（删除交替性的反例）。** 令 $W=\mathbb R^2$，
$J(x_1,x_2)=(-x_2,x_1)$，$V=\mathbb R\oplus W$，并定义
$$
D((s,x),(t,y))=(0,sJy).
\tag{12.19}
$$
这是一个非零双线性总映射。它保留非零性、双线性、总定义、全域 P、N 以及有限维逐轴全实参数有界条件 B，删除交替性；交替结论和正定迹尺结论均失败。

**证明。** 每个输出的第一坐标为零，而对任意 $z\in W$、$c\in V$ 有
$D((0,z),c)=0$，所以
$$
D(D(a,b),c)=0\in\operatorname{span}\{a,b\}
$$
对所有 $a,b,c$ 成立，P 成立。写 $a=(s,x)$、$b=(t,y)$、$w=D(a,b)=(0,sJy)$。若 $w\ne0$，则 $s\ne0$ 且 $y\ne0$，并且
$$
D(a,w)=(0,sJ(sJy))=(0,-s^2y).
$$
向量 $y$ 与 $Jy$ 在实二维空间中线性独立：若 $Jy=\lambda y$，再作用一次 $J$ 得 $-y=\lambda^2y$，不可能。因此 $D(a,w)\notin\mathbb Rw$；当 $w=0$ 时 N 的结论本身成立，故 N 成立。

对任意 $a=(s,x)$，行算符满足
$L_a(t,y)=(0,sJy)$，且 $J^2=-I$，从而
$$
\exp(\tau L_{(s,x)})(t,y)=(t,e^{\tau sJ}y),
\qquad \tau\in\mathbb R.
$$
$e^{\tau sJ}$ 是平面旋转，所以在标准直和 Euclidean 范数中所有这些指数都是等距的，B 成立。

但若 $x\ne0$，则
$$
D((1,x),(1,x))=(0,Jx)\ne0,
$$
交替性失败。最后对 $a=(s,x)$、$b=(t,y)$ 和任意 $(r,z)$，
$$
L_aL_b(r,z)=(0,-stz).
$$
因此 $\operatorname{Tr}(L_aL_b)=-2st$，从而
$$
-\tfrac12\operatorname{Tr}(L_aL_b)=st.
$$
这个形式的秩为一，且该双线性形式在 $W$ 方向退化，绝非正定。这也说明引理 12.3 中由交替性承担的原输入与输出之间的反向作用不能删去。$\square$

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

## 13　任意域上的全域入口与带标记的四维含单位结构

**定义 13.1（原域、原空间与二次零核条件）。** 设 $F$ 是任意域，$V$ 是任意 $F$-向量空间，$D:V\times V\to V$ 是同一个非零交替 $F$-双线性总映射。交替指 $D(a,a)=0$，在特征 $2$ 中也如此；双线性因而给出 $D(a,b)=-D(b,a)$。记 $L_ab=D(a,b)$。本节的两个入口条件为

$$
\begin{split}
\mathrm P:\quad &D(D(a,b),c)\in\operatorname{span}_F\{a,b\}
&& (a,b,c\in V),\\
\mathrm K:\quad &\ker L_a^2=\ker L_a
&& (a\in V).
\end{split}
\tag{13.1}
$$

这里的量词覆盖整个原 $V$，没有有限维、生成性、商空间、外积同构、比较尺、范数、Jacobi、拓扑或时间的输入。与之比较的条件是

$$
\mathrm N:\quad D(a,D(a,b))\in F D(a,b)
\ \Longrightarrow\ D(a,b)=0\qquad(a,b\in V).
\tag{13.2}
$$

$F0=\{0\}$。本节的同构均固定实际标量域及其结构嵌入：$(V,D)$ 的同构是保持 $D$ 的 $F$-线性双射；带标记含单位代数 $(A,\pi)$ 的同构是固定 $F1$ 且满足 $\pi'\Phi=\pi$ 的含单位 $F$-代数同构。这里 $\pi:A\to F$ 是 $F$-线性映射且 $\pi(1)=1$，所以它限制在 $F1$ 上是恒等，$A=F1\oplus\ker\pi$。不把改变标量域的半线性映射纳入这些同构。

**引理 13.2（K 与 N 等价及非零特征值的排除）。** 对任意域上任意交替双线性 $D$，不要求 P、非零性或有限维，K 与 N 等价。若它们成立，则任何 $L_a$ 都没有属于 $F^\times$ 的特征值。

**证明。** 若 N 成立且 $L_a^2b=0$，则 $L_a^2b\in F L_ab$，故 $L_ab=0$；反向的核包含总成立，得到 K。

若 K 成立，设 $w=L_ab$ 且 $L_aw=\lambda w$。交替性给 $L_wa=-\lambda w$，因此 $L_w^2a=0$。对 $w$ 使用 K，得到 $\lambda w=0$，从而 $L_aw=0$。再对 $a$ 使用 K，得到 $w=0$，即 N。这个论证同时处理 $\lambda=0$ 与特征 $2$。

最后，若 $L_ax=\lambda x$，其中 $x\ne0$、$\lambda\ne0$，则 $L_xa=-\lambda x\ne0$ 而 $L_x^2a=0$，直接违反 K。故所述特征值不存在。K 是 N 的较短表述；即使没有 P，它也不是严格较弱的条件。$\square$

**引理 13.3（非零输出的平面，在任意原维数中）。** 在定义 13.1 的 P、K 下，若 $w=D(a,b)\ne0$，则 $a,b,w$ 线性独立。记 $U=\operatorname{span}_F\{a,b\}$，有

$$
L_w(V)=U,\qquad L_w|_U:U\longrightarrow U\text{ 是同构}.
\tag{13.3}
$$

同一个非零输出及其任一非零标量倍数唯一确定这个原输入平面。

**证明。** 交替双线性使 $a,b$ 独立。假设 $w=ra+sb$，则 $L_wa=-sw$、$L_wb=rw$，两者再受 $L_w$ 作用都为零。K 迫使两者本来就为零，因此 $r=s=0$，与 $w\ne0$ 矛盾。

P 给 $L_w(V)\subseteq U$。对任意 $0\ne x=ra+sb\in U$，选择 $t,u\in F$ 使 $ru-st=1$，令 $y=ta+ub$，便有 $D(x,y)=w$。若 $L_wx=0$，则 $L_x^2y=D(x,w)=0$，K 会迫使 $D(x,y)=0$，矛盾。所以 $L_w|_U$ 单射。二维平面上的单射是满射，于是 (13.3) 成立。若 $D(a',b')=\mu w$、$\mu\in F^\times$，则

$$
\operatorname{span}_F\{a',b'\}
=\operatorname{im}L_{\mu w}=\operatorname{im}L_w=U.
$$

这一步只使用原空间中的二维子空间，没有先假定整个 $V$ 有限维。$\square$

**定理 13.4（中心、独立零响应与整个原空间的三维性）。** 在定义 13.1 的 P、K 下，

$$
Z_D:=\{z:D(z,v)=0\text{ 对所有 }v\in V\}=0,
\qquad \ker L_a=Fa\quad(a\ne0),
\tag{13.4}
$$

并且整个原空间 $V$ 恰为三维。具体地，对任何实际非零输出 $w=D(a,b)$，

$$
V=\operatorname{span}_F\{a,b\}\oplus Fw.
\tag{13.5}
$$

**证明。** 非零性提供 $w=D(a,b)\ne0$。若 $z\in Z_D$，则 $D(a+z,b)=w$。引理 13.3 使 $a+z$ 属于 $U=\operatorname{span}_F\{a,b\}$，故 $z\in U$。又 $L_wz=0$，而 $L_w|_U$ 单射，所以 $z=0$。这里排除了原中心，没有取中心的商。

对任意 $a\ne0$，中心为零保证存在 $b$ 使 $w=D(a,b)\ne0$。若 $D(a,c)=0$，则 $D(a,b+c)=w$。同一输出的平面唯一性使 $c\in\operatorname{span}_F\{a,b\}$。写 $c=ra+sb$，即有 $0=D(a,c)=sw$，所以 $c\in Fa$。反向由交替性成立。这也证明两个独立原输入不可能给零响应。

再固定任意 $w=D(a,b)\ne0$。对每个原 $v\in V$，由引理 13.3 在 $U$ 中解唯一的 $L_wp=L_wv$，便有 $v-p\in\ker L_w=Fw$。同时 $w\notin U$，故得到 (13.5)。该分解适用于每个原向量，因而证明整个 $V$ 三维，而非仅证明一份生成子空间三维。到此为止没有使用迹或任何有限矩阵。$\square$

**引理 13.5（全特征的唯一返回形式与合法回读）。** 在定理 13.4 的结论之后，存在唯一双线性形式 $g$ 使

$$
D(D(a,b),c)=g(a,c)b-g(b,c)a
\qquad(a,b,c\in V).
\tag{13.6}
$$

它对称且非退化。存在基 $(e_1,e_2,e_3)$ 和 $\alpha,\beta\in F^\times$，使

$$
\begin{split}
&D(e_1,e_2)=e_3,\quad D(e_2,e_3)=\beta e_1,
\quad D(e_3,e_1)=\alpha e_2,\\
&[g]_{(e_1,e_2,e_3)}=\operatorname{diag}(\alpha,\beta,\alpha\beta).
\end{split}
\tag{13.7}
$$

诱导映射 $\widetilde D:\Lambda^2V\to V$ 是同构。对所有特征都有

$$
L_aL_b=b\otimes g(a,\cdot)-g(a,b)I,
\qquad \operatorname{Tr}(L_aL_b)=-2g(a,b).
\tag{13.8}
$$

当且仅当 $2\ne0$ 时，可从后一式回读 $g(a,b)=-\tfrac12\operatorname{Tr}(L_aL_b)$；特征 $2$ 中使用 (13.6) 的平面系数或 (13.7)，不使用除以 $2$ 的迹式。

**证明。** 取 $w=D(a,b)\ne0$。现在 $(a,b,w)$ 已是整个 $V$ 的基，且可写

$$
D(w,a)=pa+qb,\qquad D(w,b)=ra+sb.
$$

若 $q=0$，引理 13.3 使 $p\ne0$，于是 $L_wa=pa$ 是引理 13.2 禁止的非零特征值。因此 $q\ne0$。对 $(a,w,w)$ 使用 P，得到

$$
D(D(a,w),w)=(p^2+qr)a+q(p+s)b\in\operatorname{span}_F\{a,w\},
$$

故 $s=-p$。$L_w|_U$ 可逆，其行列式
$\delta=-(p^2+qr)$ 非零。置

$$
e_1=a,\quad e_2=b+(p/q)a,\quad e_3=w,
\qquad \alpha=q,\quad \beta=\delta/q.
$$

双线性给出 (13.7) 的乘法表。定义 $g$ 的矩阵为其中的对角矩阵；其行列式是 $(\alpha\beta)^2\ne0$，所以 $g$ 对称非退化。

以下完整表格验证 (13.6)。每格是 $D(D(e_i,e_j),e_k)$，同时也是 $g(e_i,e_k)e_j-g(e_j,e_k)e_i$：

| $(i,j)\backslash k$ | $1$ | $2$ | $3$ |
|---|---|---|---|
| $(1,2)$ | $\alpha e_2$ | $-\beta e_1$ | $0$ |
| $(2,3)$ | $0$ | $\beta e_3$ | $-\alpha\beta e_2$ |
| $(3,1)$ | $-\alpha e_3$ | $0$ | $\alpha\beta e_1$ |

两侧都三线性且在前两槽交替：两前槽相同时两侧为零，交换前两槽同时变号；因此这九格支付全部基三元组，包括第三槽重复第一槽或第二槽的情况，进而支付全部原向量。在特征 $2$ 中负号等于正号，而交替要求的重复槽仍严格为零；没有借助除以 $2$ 或域中元素数目。

若 $h$ 是另一个满足 (13.6) 的双线性形式，固定 $a\ne0,c$ 并选与 $a$ 独立的 $b$。两返回式相减给

$$
(h-g)(a,c)b-(h-g)(b,c)a=0.
$$

独立性使 $(h-g)(a,c)=0$。$a=0$ 由双线性处理，因此 $h=g$；唯一性甚至不要求先规定 $h$ 对称。

外积基 $(e_1\wedge e_2,e_2\wedge e_3,e_3\wedge e_1)$ 被送到 $(e_3,\beta e_1,\alpha e_2)$，所以 $\widetilde D$ 可逆。由交替性与返回式得到 (13.8) 的算子等式；秩一算子的迹是 $g(a,b)$，而三维恒等的迹是 $3$，故迹为 $-2g(a,b)$。特征 $2$ 中这些乘积的迹全部为零，不能据此恢复 $g$。在任意特征，固定独立 $a,b$ 后，(13.6) 中 $b$ 的系数就是 $g(a,c)$，唯一性保证此读数不依赖辅助 $b$。$\square$

**引理 13.6（核判据、各向异性与实际输出）。** 设三维 $V$ 上的交替双线性 $D$ 满足 (13.6)，其中 $g$ 对称非退化，且 $\widetilde D$ 是同构。令 $q(a)=g(a,a)$。则 K 恰等价于 $q$ 各向异性，即 $q(a)=0\Rightarrow a=0$。在定义 13.1 的 P、K 下，还成立

$$
\operatorname{im}L_a=a^{\perp_g},\qquad
\ker L_a=Fa,\qquad \operatorname{rank}L_a=2\quad(a\ne0),
\tag{13.9}
$$

且每个原向量都是一份实际二元输出。三线性形式
$\omega(a,b,c)=g(D(a,b),c)$ 交替，并满足

$$
g(D(a,b),c)=g(a,D(b,c)).
\tag{13.10}
$$

**证明。** 外积同构使 $D(a,b)=0$ 当且仅当 $a,b$ 线性相关。返回式给

$$
L_a^2b=g(a,b)a-q(a)b.
\tag{13.11}
$$

若 $q$ 各向异性，$a\ne0$ 且 $L_a^2b=0$ 就迫使 $b\in Fa$，因此 $L_ab=0$；$a=0$ 时两个核都是 $V$。所以 K 成立。

反之，若 $a\ne0$ 且 $q(a)=0$，则非退化性使 $a^{\perp_g}$ 是包含 $a$ 的二维平面。取其中与 $a$ 独立的 $b$，(13.11) 给 $L_a^2b=0$，但外积同构给 $L_ab\ne0$，与 K 矛盾。这证明精确等价。

对入口模型，在 (13.7) 的基上，$\omega(e_1,e_2,e_3)$ 及其两个循环值都是 $\alpha\beta$，反向排列取其负值，其余基三元组即所有重复槽都给零。因此 $\omega$ 在全特征中交替，而循环排列保持它，得到 (13.10)。这一步明确检查了重复槽，未把一个未验证的三元缺陷直接命名为交替形式。

于是 $g(D(a,b),a)=0$，所以 $\operatorname{im}L_a\subseteq a^{\perp_g}$。核为 $Fa$，三维秩—零度给像的维数为二，得到 (13.9)。对任意 $z\ne0$，选择 $0\ne a\in z^{\perp_g}$；由各向异性 $q(a)\ne0$，而 (13.11) 给

$$
D\left(a,-q(a)^{-1}D(a,z)\right)=z.
\tag{13.12}
$$

零也显然是输出。这是实际输出满射，不只是像的线性张成。$\square$

**命题 13.7（入口的准确三维参数及反向）。** 对任意域 $F$，取 $\alpha,\beta\in F^\times$，在 $F^3$ 上按 (13.7) 定义交替双线性 $D$ 和对角形式 $g$。这些数据满足全域 P、唯一返回式、非退化性和外积同构；它们满足 K 当且仅当

$$
q(x_1e_1+x_2e_2+x_3e_3)
=\alpha x_1^2+\beta x_2^2+\alpha\beta x_3^2
\tag{13.13}
$$

各向异性。定义 13.1 的每个入口模型均由这种数据得到。在特征 $2$ 中 $q$ 是拟线性二次型，极化式 $q(a+b)-q(a)-q(b)$ 恒为零；这不妨碍对称双线性 $g$ 非退化，但不能用该极化式恢复 $g$。

**证明。** 引理 13.5 的九格验证只使用给定乘法表，所以直接提供全域返回和 P；同一外积基与对角行列式给外积同构和 $g$ 非退化。唯一性的证明也原样适用。引理 13.6 给 K 的充要条件。引理 13.5 则把任意入口模型放入此表。特征 $2$ 的最后结论由 $2g(a,b)=0$ 直接得到。这里把标准乘法表作为入口桥的中间坐标，不将其重新命名为新的四元数或拟线性二次型分类。$\square$

**定理 13.8（同一数据的结合扩张、乘法范数与除法桥）。** 对定义 13.1 的入口模型，以引理 13.5 的同一 $g,D$ 定义

$$
\begin{split}
&A=F\oplus V,\qquad 1=(1,0),\qquad \pi(s,a)=s,\\
&(s,a)(t,b)=(st-g(a,b),\;sb+ta+D(a,b)),\\
&\overline{(s,a)}=(s,-a),\qquad
\operatorname N_A(s,a)=s^2+q(a).
\end{split}
\tag{13.14}
$$

则 $A$ 是四维含单位结合 $F$-代数，共轭是标准反自同构，且

$$
x\bar x=\bar x x=\operatorname N_A(x)1,
\qquad \operatorname N_A(xy)=\operatorname N_A(x)\operatorname N_A(y).
\tag{13.15}
$$

纯部 $q$ 的各向异性蕴涵整个 $\operatorname N_A$ 各向异性，因而 $A$ 是除法代数，非零元素的逆为 $\bar x/\operatorname N_A(x)$。$D$ 自身不是结合乘法。

**证明。** (13.14) 双线性且 $1$ 是两侧单位。结合子三线性，任一槽为标量单位时为零，因此只需对三个纯向量 $a,b,c$ 验证。左、右结合乘积的标量部分分别是

$$
-g(D(a,b),c),\qquad -g(a,D(b,c)),
$$

由 (13.10) 相同。向量部分分别是

$$
-g(a,b)c+D(D(a,b),c),\qquad
-g(b,c)a+D(a,D(b,c)).
$$

(13.6) 与对称性使两者同为
$-g(a,b)c+g(a,c)b-g(b,c)a$。所以结合性在所有重复槽和所有特征中成立。

直接用 $g$ 对称、$D$ 交替验证 $\overline{xy}=\bar y\bar x$、$\bar{\bar x}=x$ 和 $x\bar x=(s^2+q(a))1$。结合性因此给

$$
(xy)\overline{xy}=xy\bar y\bar x
=\operatorname N_A(y)x\bar x
=\operatorname N_A(x)\operatorname N_A(y)1,
$$

证明乘法性。这是标准共轭的经典范数论证；其假设和公式见 [Voight，*Quaternion algebras*，v1.0.5，定义 3.2.1、§3.3，特别是 (3.3.4)](https://jvoight.github.io/quat-book-v1.0.5.pdf)。这里已用原入口数据支付所需结合性和共轭，而没有把经典范数乘法性当作新分类。

还须从纯部到完整四维空间排除零范数。假设 $s^2+q(a)=0$，且 $(s,a)\ne0$。若 $s=0$，纯部各向异性已给矛盾。故 $s\ne0$，$a\ne0$ 且 $q(a)=-s^2\ne0$。取 $0\ne b\in a^{\perp_g}$。此平面在 $L_a$ 下不变，且 (13.11) 给 $L_a^2b=s^2b$。令 $v=(L_a+sI)b$。若 $v\ne0$，则

$$
(L_a-sI)v=(L_a^2-s^2I)b=0,
$$

于是 $v$ 是特征值 $s\ne0$ 的向量；若 $v=0$，则 $b$ 是特征值 $-s\ne0$ 的向量。两者都与引理 13.2 矛盾。在特征 $2$ 中 $s=-s$，同一两分情形仍成立，不要求这两个根不同。故完整范数各向异性，逆元公式由 (13.15) 给出。

最后在 (13.7) 的基上，

$$
D(D(e_1,e_1),e_2)=0,\qquad
D(e_1,D(e_1,e_2))=-\alpha e_2\ne0.
$$

所以结合的是含标量槽的 $A$，不是纯部二元响应 $D$。$\square$

**定理 13.9（入口所导出含单位代数的两种准确类型）。** 定理 13.8 的 $A$ 具有以下分类。

若 $\operatorname{char}F\ne2$，则

$$
A\simeq(-\alpha,-\beta)_F
\tag{13.16}
$$

是四元数除法代数，$V=\ker\operatorname{trd}$，$\pi=\operatorname{trd}/2$，$\operatorname N_A=\operatorname{nrd}$。

若 $\operatorname{char}F=2$，则 $A=L$ 是扩张总次数 $[L:F]=4$、满足 $L^2\subseteq F$ 的纯不可分指数 $1$ 域，连同原指定投影 $\pi:L\to F$。在此情形

$$
\operatorname N_A(x)=x^2,\qquad
V=\ker\pi,\quad g(a,b)=\pi(ab),\quad D(a,b)=ab-\pi(ab)1.
\tag{13.17}
$$

这里不能将 $\pi$ 当作域迹；该纯不可分扩张的通常域迹恒为零。

**证明。** 在 (13.7) 的基上，把纯向量视为 $A$ 中元素，有

$$
e_1^2=-\alpha,\quad e_2^2=-\beta,\quad
 e_1e_2=e_3=-e_2e_1,\quad e_3^2=-\alpha\beta.
\tag{13.18}
$$

$1,e_1,e_2,e_3$ 是基，且结合性、除法性均已证明。当 $2\ne0$ 时，这正是经典四元数的定义和乘法表，直接识别得到 (13.16)，不重新证明四元数分类。[Voight，前引书，定义 2.2.1、引理 2.2.5](https://jvoight.github.io/quat-book-v1.0.5.pdf) 的前件是 $\operatorname{char}F\ne2$ 和两个参数非零；此处参数为 $-\alpha,-\beta\in F^\times$。本节共轭在该基上就是经典标准共轭，故经典约化迹、范数定义给 $\operatorname{trd}(s,a)=2s$ 和 $\operatorname{nrd}(s,a)=s^2+q(a)$；参见同书 §3.3、式 (4.1.1)。

当 $2=0$ 时，交替双线性给 $D(a,b)=D(b,a)$，故整个 $A$ 交换。结合的交换除法代数是域，且 $\bar x=x$，所以 (13.15) 给每个 $x\in A$ 的平方都在实际 $F1$ 内。它是四维非平凡纯不可分指数 $1$ 扩张，且由 (13.18) 可写为

$$
L=F(e_1,e_2)=F(\sqrt\alpha,\sqrt\beta),\qquad [L:F]=4.
$$

这里“总次数四”不意味着存在次数四的单个元素；每个元素的最小多项式次数至多为二。纯不可分术语与逐次添平方根的经典依据见 [Stacks Project，定义 09HE、引理 09HF、09HI](https://stacks.math.columbia.edu/tag/09HD)，此处 $p=2$ 且所有平方已在 $F$，比一般有限纯不可分扩张的条件更具体。式 (13.17) 直接由 (13.14) 的标量和纯部分解给出。

为核对迹的差异，取上述基 $1,e_1,e_2,e_1e_2$。乘以 $1$ 的通常迹为 $4=0$；乘以 $e_1,e_2,e_1e_2$ 的对角系数均为零。因此所有乘法算子的通常迹为零，而 $\pi(1)=1$，两者不可能相同。$\square$

**定理 13.10（每个四元数除法代数的完整反向）。** 固定 $\operatorname{char}F\ne2$。对任意四元数除法 $F$-代数 $Q$，取其标准共轭、约化迹与约化范数，并置

$$
V=Q_0=\ker\operatorname{trd},\qquad
\pi=\operatorname{trd}/2,
$$

$$
g(a,b)=-\tfrac12(ab+ba)=-\pi(ab),\qquad
D(a,b)=\tfrac12(ab-ba)=ab-\pi(ab)1.
\tag{13.19}
$$

标量值 $g(a,b)$ 按 $F1$ 与 $F$ 识别。则这个原 $V,D$ 满足定义 13.1 的全部条件、唯一返回式、非退化性及外积同构；其 $q(a)=\operatorname{nrd}(a)$ 各向异性，定理 13.8 恢复同一个 $Q$ 及其原乘法。

**证明。** 复用经典四元数标准生成元：存在 $i,j$，使 $1,i,j,k=ij$ 是基，$i^2=r$、$j^2=t$、$ji=-ij$，其中 $r,t\in F^\times$。标准共轭在 $i,j,k$ 上取负，故 $V=Fi\oplus Fj\oplus Fk$，且 $Q=F1\oplus V$。这正是 [Voight，前引书，定义 2.2.1、§3.2 的 (3.2.9)、§3.3](https://jvoight.github.io/quat-book-v1.0.5.pdf) 的全部适用条件，未在特征 $2$ 套用此描述。

对纯 $a,b$，$\overline{ab}=ba$，因而 $ab+ba=\operatorname{trd}(ab)1$ 是标量，$ab-ba$ 迹零。这支付了 (13.19) 的类型。它给出对称双线性 $g$ 与交替双线性 $D$；后者的重复输入严格为零。直接用标准乘法表得到

$$
D(i,j)=k,\quad D(j,k)=-t i,\quad D(k,i)=-r j,
\qquad [g]_{(i,j,k)}=\operatorname{diag}(-r,-t,rt).
$$

这就是命题 13.7 中 $\alpha=-r,\beta=-t$ 的数据，所以完整九格验证直接给全域返回、P、非退化性与外积同构。对纯 $a$，有 $q(a)=-a^2=\operatorname{nrd}(a)$。若 $q(a)=0$，则 $a^2=0$，除法性迫使 $a=0$。命题 13.7 因而给 K。最后 $ab=-g(a,b)+D(a,b)$，添标量槽后的 (13.14) 正是 $Q$ 的原乘法，而不是另造一个同维空间上的运算。$\square$

**定理 13.11（特征二中每个指数一四次域及任意投影的完整反向）。** 固定 $\operatorname{char}F=2$。设 $L/F$ 是满足 $[L:F]=4$、$L^2\subseteq F$ 的域扩张，$\pi:L\to F$ 是任意 $F$-线性映射且 $\pi(1)=1$。取 $V=\ker\pi$，并按 (13.17) 定义 $g,D$。则 $V,D$ 满足定义 13.1 的全域 P、K、非零性及交替双线性，$g$ 非退化，$\widetilde D$ 为同构，且唯一返回式为 (13.6)。其 $q(a)=a^2$ 各向异性；(13.14) 恢复同一个带原投影的域 $(L,\pi)$。

**证明。** $\pi|_F=\operatorname{id}$ 使 $L=F1\oplus V$，故 $\dim_FV=3$。对纯 $a,b$，$D(a,b)$ 的投影为零，所以其值确在 $V$。所有公式 $F$-双线性；因 $a^2\in F$，有

$$
D(a,a)=a^2-\pi(a^2)1=0,\qquad g(a,a)=a^2.
$$

域中平方为零只可能 $a=0$，故 $q$ 各向异性。

先独立证明双线性 $g$ 非退化。$B(x,y)=\pi(xy)$ 是 $L$ 上的非退化对称双线性形式：对 $x\ne0$，取 $y=x^{-1}$，就有 $B(x,y)=1$。$B(1,1)=1$，且 $V=1^{\perp_B}$。若 $a\in V$ 与整个 $V$ 正交，它也与 $1$ 正交，因而与整个 $L$ 正交，所以 $a=0$。这证明 $g=B|_V$ 非退化，未调用域迹或二次型极化。

选 $0\ne a\in V$，再在二维平面 $a^{\perp_g}\subset V$ 中选 $0\ne b$。因 $g(a,a)=a^2\ne0$，$b$ 不在 $Fa$。此外 $a\notin F$，$[F(a):F]=2$；若 $b\in F(a)$，则可写 $b=s+ta$，由 $\pi(b)=0$ 得 $s=0$，仍与独立性矛盾。因此 $L=F(a,b)$，且 $1,a,b,ab$ 是 $F$-基。这也可直接应用 [Stacks 引理 09HF 与 09HI](https://stacks.math.columbia.edu/tag/09HD) 的添平方根和次数乘法：两个平方在 $F$ 内，而第二个元素不在第一次二次扩张内。

令 $\alpha=a^2\ne0$、$\beta=b^2\ne0$。因 $g(a,b)=\pi(ab)=0$，$w=ab\in V$，且 $(a,b,w)$ 是 $V$ 的基。域乘法直接给

$$
D(a,b)=w,\quad D(b,w)=\beta a,\quad D(w,a)=\alpha b.
$$

同时 $g(a,w)=\pi(a^2b)=0$、$g(b,w)=\pi(b^2a)=0$，故其矩阵为 $\operatorname{diag}(\alpha,\beta,\alpha\beta)$。这正是命题 13.7 的完整表，直接给非零性、外积同构、全域返回和 P；已证 $q$ 各向异性再给 K。所有重复槽由该表和 $D(x,x)=0$ 支付，不需要假定某个三元缺陷已经交替。最后因特征为二，$ab=g(a,b)+D(a,b)=-g(a,b)+D(a,b)$，所以 (13.14) 经 $(s,a)\mapsto s+a$ 恢复整个原域的乘法及原投影。$\square$

**定理 13.12（固定实际标量嵌入的完整同构分类）。** 对固定域 $F$，入口模型 $(V,D)$ 的同构类恰与以下对象的同构类一一对应：当 $\operatorname{char}F\ne2$ 时，是四元数除法 $F$-代数；当 $\operatorname{char}F=2$ 时，是定理 13.11 的带指定投影 $(L,\pi)$。更准确地，任意两个入口模型之间的 $D$-同构 $T$ 唯一延伸为带标记代数同构

$$
\Phi(s,a)=(s,Ta),
\tag{13.20}
$$

且每个这样的代数同构都如此得到。非二特征中投影是经典约化迹的一半，故无需另加自由标记；特征二中一般必须保留 $\pi$。

**证明。** 若 $T$ 保持 $D$，把目标 $g'$ 经 $T$ 拉回，所得双线性形式满足源的 (13.6)。引理 13.5 的唯一性给
$g'(Ta,Tb)=g(a,b)$。代入 (13.14) 即证明 (13.20) 保乘法、单位和投影。它在 $F1$ 上恒等，而整个空间是 $F1\oplus V$，故延伸唯一。反之，带标记同构把 $\ker\pi$ 送到 $\ker\pi'$，并把乘积的纯部分送到纯部分，所以其限制保持 $D$。

定理 13.9 给正向对象；定理 13.10、13.11 给每个分类对象的完整反向，并恢复其原乘法和标记，因此两构造互逆。非二特征的任意 $F$-代数同构都保持经典标准共轭，因而保持约化迹与 $\pi$；这里直接复用 [Voight，前引书，推论 3.4.4 的标准共轭唯一性](https://jvoight.github.io/quat-book-v1.0.5.pdf)，其前件是已有标准共轭，定理 13.8 和四元数标准结构都已供应。于是非二特征中不必额外要求同构保持投影。二特征的标记不可这样消去，精确关系如下条。$\square$

**定理 13.13（特征二的实际平方子域与 $F^2$ 值标记）。** 固定特征二的实际域 $F$ 及一份代数闭包 $\overline F$。记 $F^2=\{c^2:c\in F\}$。定理 13.12 的特征二对象完全等价于数据

$$
F^2\subseteq M\subseteq F,\qquad [M:F^2]=4,
\qquad \lambda:M\to F^2\text{ 为 }F^2\text{-线性且 }\lambda(1)=1,
\tag{13.21}
$$

其中 $M$ 是实际子域，标记的值域明确是 $F^2$。双向公式为

$$
M=L^2,\qquad
\lambda(m)=\pi(\sqrt m)^2,
\tag{13.22}
$$

$$
L=\{x\in\overline F:x^2\in M\},\qquad
\pi(x)=\sqrt{\lambda(x^2)}\in F.
\tag{13.23}
$$

这里所有平方根在指定代数闭包中唯一，(13.23) 的最后一个平方根由于被开方量属于 $F^2$ 而确实在 $F$ 内。两个对象同构当且仅当它们的实际 $M$ 和实际 $\lambda$ 分别相同。任何 $F^2$-代数同构 $\sigma:M\to M'$ 都必为实际包含下的恒等，故必有 $M=M'$；若它还保持标记，则必有 $\lambda=\lambda'$。

**证明。** 纯不可分扩张到 $\overline F$ 的 $F$-嵌入唯一；这是 [Stacks 引理 09HJ 的纯不可分情形](https://stacks.math.columbia.edu/tag/09HJ)。在此指数一的具体情形也直接由 $x^2\in F$ 和平方根唯一性得到。因而可把每个 $L$ 唯一看作 $\overline F$ 的实际子域。平方映射把 $L$ 同构到子域 $M=L^2\subseteq F$，并把 $F$ 同构到 $F^2$。所以 $F^2\subseteq M$，且 $[M:F^2]=[L:F]=4$。

对 $m,n\in M$，唯一平方根满足 $\sqrt{m+n}=\sqrt m+\sqrt n$。对 $d\in F^2$，写 $d=c^2$、$c\in F$，则 $\sqrt{dm}=c\sqrt m$。$\pi$ 的 $F$-线性于是给

$$
\lambda(m+n)=\lambda(m)+\lambda(n),\quad
\lambda(dm)=d\lambda(m),\quad \lambda(1)=1.
$$

因定义是 $F$ 中元素的平方，其值在 $F^2$，这支付 (13.22) 的值域。

反之，给定 (13.21)，(13.23) 中的集合对加法、乘法和非零取逆封闭，是包含实际 $F$ 的域，且其平方域恰为 $M$。平方映射再次给 $[L:F]=[M:F^2]=4$ 和 $L^2\subseteq F$。定义的 $\pi$ 值在 $F$，并且

$$
\pi(x+y)^2=\lambda(x^2+y^2)=\pi(x)^2+\pi(y)^2,
$$

$$
\pi(cx)^2=\lambda(c^2x^2)=c^2\pi(x)^2
\qquad(c\in F).
$$

域中平方映射单射，故 $\pi$ 可加且 $F$-齐次，$\pi(1)=1$。两套公式互逆，因为相同平方的元素必相等。

若 $\Phi:L\to L'$ 是固定 $F$ 的代数同构，则对 $x\in L$ 有
$\Phi(x)^2=\Phi(x^2)=x^2$，故在 $\overline F$ 内 $\Phi(x)=x$。于是 $L=L'$，并由投影相容得 $\pi=\pi'$，等价于 $M=M'$、$\lambda=\lambda'$。反向的恒等映射显然给同构。

另对任何实际子域间的 $F^2$-代数同构 $\sigma$，因为 $m\in M\subseteq F$ 使 $m^2\in F^2$，有

$$
\sigma(m)^2=\sigma(m^2)=m^2.
$$

仍由平方单射得 $\sigma(m)=m$。故同构像等于 $M$，而满射像又是 $M'$，两子域相同；保持标记的条件 $\lambda'\sigma=\lambda$ 正好化为 $\lambda'=\lambda$。这不是把任意 $F^2$-线性空间同构误当成子域同构。$\square$

**推论 13.14（标记的纯部读数及自同构的精确范围）。** 在定理 13.13 的数据中，

$$
q(V)=\ker\lambda\subset M,\qquad
M=F^2\oplus\ker\lambda,
\tag{13.24}
$$

其中直和按 $F^2$-向量空间理解。固定 $F$ 的原入口模型自同构在特征二中只有恒等。这些结论只分类实际域上的对象和 $F$-有理点自同构，不是群概形的断言。

**证明。** 若 $a\in V$，则 $q(a)=a^2$ 且 $\lambda(a^2)=\pi(a)^2=0$。反之，$m\in\ker\lambda$ 的唯一根 $a\in L$ 满足 $\pi(a)^2=0$，故 $a\in V$、$q(a)=m$，得到第一式。$\lambda(1)=1$ 给第二式。入口自同构依定理 13.12 延伸为固定 $F$ 的域自同构，定理 13.13 已证明该映射逐元素恒等。证明没有对非约化基环或任意基变换上的自同构函子作量化，所以只能得到所述 $F$-点结论。$\square$

**命题 13.15（有限标量域及小特征的边界）。** 若 $F$ 是有限域，则定义 13.1 没有入口模型；上述定理的全特征表述并未排除这些域，而是在它们上给出模型不存在的结论。

**证明。** 若特征为二，有限域的平方映射单射因而满射，所以 $F^2=F$，无法存在 (13.21) 所需的次数四子域。若特征非二，设 $|F|=n$。集合 $S=\{x^2:x\in F\}$ 的大小是 $(n+1)/2$：非零平方恰有两个根，零有一个。对命题 13.7 的 $\alpha,\beta$，两个子集 $\alpha S$ 和 $-\alpha\beta-\beta S$ 的大小之和是 $n+1>n$，必相交。故存在 $x,y\in F$ 使

$$
\alpha x^2+\beta y^2+\alpha\beta=0.
$$

这给 (13.13) 的非零各向同性向量 $(x,y,1)$，与 K 矛盾。证明覆盖最小有限域，不依靠避开少数域元素的选取。$\square$

**推论 13.16（实数特化与既有 P+N 入口的准确接合）。** 当实际标量域另外指定为 $F=\mathbb R$ 时，定义 13.1 的模型恰为本卷定理 12.8 的原有序对 $(V,D)$：整个 $V$ 三维，唯一 $g$ 正定，原 $D$ 为相对于自身定向的单位叉积，含单位结合扩张为 Hamilton 四元数 $\mathbb H$。本卷 §12 的迹、旋转与同尺消费者可直接使用；这一实数特化没有从 P、K 选择出标量域 $\mathbb R$。

**证明。** 引理 13.2 在实域给 P+K 与 P+N 完全相同，而原 $V,D$ 没有改变，所以定理 12.8 及定理 12.2 直接适用。也可从本节坐标核对正定性：实对角三元型各向异性使三个对角系数不能异号，否则两项用实平方根配比即可抵消。$\alpha,\beta,\alpha\beta$ 的乘积为正，三个系数不能全负，故全正。于是 $g$ 正定；以 $e_1/\sqrt\alpha,e_2/\sqrt\beta,e_3/\sqrt{\alpha\beta}$ 为基，D 的循环表均为单位系数，(13.18) 是 $\mathbb H$ 的标准表。这与经典实四元数结构一致，参见 [Voight，前引书，§2.4 与推论 3.5.8](https://jvoight.github.io/quat-book-v1.0.5.pdf)。这里的四维结论由已经证明的入口桥取得，不以 Frobenius 实除法代数分类为三维入口的前提。

原逐轴有界条件 B 的使用仍保留其全部前件：有限维实空间、非零交替双线性 D、同一原行算子的全实参数指数、每条轴自己的有限界。定理 12.8 在这些前件下把 P+B、P+N 及原带正尺返回模型识别为同一类；本节只以引理 13.2 把其中 N 换成等价 K。平方锥、正归一读出、Born 表示及原来源接口则直接消费本卷 §§4、6、12.8 的同一个 $g,D$，不在任意域上追加正性或概率的结论。$\square$

**命题 13.17（标量域未被选定的非实模型）。** 定义 13.1 同时存在以下两个实际非实标量模型。

其一是 $F=\mathbb Q$，在 $\mathbb Q^3$ 上取 (13.7) 的 $\alpha=\beta=1$。其二是

$$
F=\mathbb F_2(u,v),\qquad
L=\mathbb F_2(r,s),\qquad u=r^2,\quad v=s^2,
\tag{13.25}
$$

其中 $r,s$ 代数独立，投影 $\pi$ 取基 $1,r,s,rs$ 的常数系数。第二个模型的 $V=Fr\oplus Fs\oplus Frs$，$q$ 的对角式为 $ux^2+vy^2+uvz^2$。

**证明。** 有理数域的三平方和只有在三个数均为零时才为零，因为它的通常序使非零平方严格为正。故第一模型由命题 13.7 满足 P、K，其扩张是经典 $(-1,-1)_{\mathbb Q}$，而实际标量域仍为 $\mathbb Q$。

对第二个模型，$\mathbb F_2(r,s)$ 在 $\mathbb F_2(r^2,s^2)$ 上的基是 $1,r,s,rs$。确切地，任一有理函数可将分子分母同乘分母，令分母变成平方，再按分子中两个指数的奇偶分组，故四者张成；若有线性关系，清去属于 $\mathbb F_2(r^2,s^2)$ 的分母后，四组多项式单项式的指数奇偶互异，不可能抵消，故线性独立。因此 $[L:F]=4$，且 $L^2=F$。投影 $\pi$ 满足定理 13.11 的全部条件，故给出入口模型与所列 q。亦可按同样奇偶证明 $1,u,v,uv$ 在 $F^2=\mathbb F_2(u^2,v^2)$ 上独立，直接确认该三元 q 各向异性。两例说明从 P、K 得到的是相对于已给标量域的分类；不能据此把标量结构输入消去。$\square$

**定理 13.18（全赋值弱入口的汇总结论与经典重叠边界）。** 对任意实际域 $F$、任意维原 $V$ 和同一非零交替双线性总映射 $D$，全域 P+K 恰好描述定理 13.12 的模型类。它强制整个原 $V$ 三维、$\Lambda^2V\simeq V$、唯一非退化对称返回形式 g、各向异性 q 及同一数据的四维结合除法扩张；特征非二和特征二的扩张分别是四元数除法代数和带指定投影的四次纯不可分指数一域。特征二的完整标记可等价写为 (13.21)，其中 $\lambda$ 的值域是 $F^2$。

**证明。** 引理 13.3 与定理 13.4 支付非零输出平面、原中心、独立零响应及整个原空间分解。引理 13.5、13.6 支付唯一返回、非退化性、外积同构、全特征回读与 K 的精确各向异性含义。定理 13.8 支付结合性、乘法范数以及纯部到完整四维除法性的桥。定理 13.9 给正向类型，定理 13.10、13.11 对每个分类对象给完整反向；定理 13.12、13.13 支付保留实际标量嵌入与投影的同构分类。因此这些结论的假设没有遗漏，正反向构造互逆。

本结论相对于本卷 §12 补足的是任意域、包括特征二的全域入口桥及其到带标记含单位结构的准确接口。实域 P+N 的整个原空间结论已经由 §12 提供；K 与 N 的等价性不形成严格较弱的新模型类。四元数的标准乘法表、共轭、约化迹、乘法范数和实数特化直接复用定理 13.8—13.10、推论 13.16 所引 Voight 条目；纯不可分扩张、添平方根与嵌入唯一性直接复用定理 13.9、13.11、13.13 所引 Stacks 条目。它们都是此推导的经典中间结构，不取得新分类或文献首次性的名义。任意域上的各向异性不称为正定，$F$-点分类不称为群概形分类。这里没有关于某个整个物理 $\Omega$、全部历史、实际控制、复合、记录、时钟或作用量的三维结论；接入这些来源仍使用本卷 §12.8 所列的各自身份与范围条件。这些物理接口也不是本代数定理成立的额外前提。$\square$

**定义 13.19（上述定理的一段完整白话释义）。** 这里的“入口”是先给一份标量规则以及一个允许相加和缩放的原空间，再给同一个二元响应：两个输入先产生响应，这份响应随后同任意原向量作用，总回到最初两个输入的平面；同时，某条原输入若把一个向量作用两次变成零，那么第一次就必须已经为零。第二条虽然比“不许非零响应再次落在自己同一条线上”写得短，但在交替双线性条件下两者等价，不能声称因此减少了逻辑信息。两条合起来先迫使每份非零响应离开原输入平面，并在该平面上作可逆作用；同一响应便不可能对应两个不同的原平面。完全看不见的中心方向、彼此独立却给零响应的方向都会破坏这份唯一性，所以都被排除。取一份非零响应以后，每个原向量都能唯一分成它所确定的二维平面部分和响应轴部分，整个原空间因此只有三维，而不是先挑一个三维片段来研究。随后响应的返回系数给出唯一的对称比较形式；条件要求它没有非零零平方方向，在实数上这成为正尺，在一般域上只叫各向异性。再加入一个标量单位槽，把比较部分和原响应一起保留，得到四维结合除法结构；结合的是这个更大的结构，原三维响应本身仍不结合。标量规则不含特征二时，它就是经典四元数除法代数；特征二时，它是每个元素平方都落回原标量域的四次域，还必须记住哪份线性投影规定了纯部。固定代数闭包后，这个域及其投影也可由实际平方子域和取值于标量平方子域的线性标记完整记录。这个结论统一了二元约束、三维有限提升与四维含单位结构，却没有替输入选择实数，也没有把数学表示的存在替换成 Born 规则、复合方式、实际门、记录或钟的供应。

## 追加锚（本行以下为增补区）

## 14. 同一二元关系的全环自同构与最小标量解锁

**定义 14.1（固定入口的自同构函子与定向）。** 设 $F$ 是任意域，原 $V$ 维数任意，同一非零交替 $F$-双线性映射 $D:V\times V\to V$ 满足定义 13.1 的全域 P、K。以下直接使用引理 13.5—定理 13.12 的结论：整个原 $V$ 三维，$D$ 恢复唯一非退化对称形式 $g$、交替体积形式 $\omega(a,b,c)=g(D(a,b),c)$ 及带投影的四维结合代数 $(A,\pi)$。不另假定一个预给度量，也不重新把入口分类作为结论。

对每个交换含单位 $F$-代数 $R$，包括零环，记 $V_R=R\otimes_F V$，以 $D_R,g_R,\omega_R,\pi_R$ 表示同一数据的标量延拓，并定义

$$
\operatorname{Aut}_D(R)=
\{T\in\operatorname{GL}_R(V_R):
T D_R(x,y)=D_R(Tx,Ty)\text{ 对全部 }x,y\in V_R\}.
\tag{14.1}
$$

群运算为复合。$F$-代数同态 $R\to S$ 使矩阵系数逐项延拓，给出该群值函子的映射。在一份原基上，保持 $D$ 的条件是各对基向量的有限组矩阵多项式等式，因而在 $\operatorname{GL}_3$ 中定义闭子群函子。称 $T$ 保定向，是指对全部 $x,y,z$ 有 $\omega_R(Tx,Ty,Tz)=\omega_R(x,y,z)$。本节的 $\operatorname{SO}(g_R)$ 专指保持双线性 $g_R$ 且行列式为一的群；特征二时不能把这里的条件替换成仅保持 $q_R(x)=g_R(x,x)$。

**定理 14.2（由原关系恢复形式的全环桥）。** 在定义 14.1 的假设下，对每个上述 $R$，有自然等式与自然群同构

$$
\begin{aligned}
\operatorname{Aut}_D(R)
&=\{T:g_R(Tx,Ty)=g_R(x,y),\ \omega_R(Tx,Ty,Tz)=\omega_R(x,y,z)\}\\
&=\operatorname{SO}(g_R),\\
\operatorname{Aut}_D(R)
&\simeq\operatorname{Aut}_{R\text{-alg}}(A_R,\pi_R).
\end{aligned}
\tag{14.2}
$$

第一行的 $T$ 均取自 $\operatorname{GL}_R(V_R)$，其等式量化全部 $x,y,z\in V_R$；最后一群要求保持单位、乘法和指定投影。尤其保持 $D_R$ 本身就强制保持同一个 $g_R$，此断言同时量化非约化环和有零因子的环。

证明。取引理 13.5 的基 $e_1,e_2,e_3$ 及参数 $\alpha,\beta\in F^\times$。其同一乘法表、返回恒等式与形式矩阵延拓到 $R$：

$$
\begin{gathered}
D_R(D_R(x,y),z)=g_R(x,z)y-g_R(y,z)x,\\
G=\operatorname{diag}(\alpha,\beta,\alpha\beta),
\qquad \omega_R(e_1,e_2,e_3)=\alpha\beta.
\end{gathered}
\tag{14.3}
$$

$G$ 可逆，且 $\alpha\beta$ 是 $R$ 中的单位。先证明这里的返回式在 $R$ 上仍唯一决定双线性形式。若 $h$ 也满足它，令 $b=h-g_R$，对任意 $i\ne j$ 和任意 $z$ 有

$$
b(e_i,z)e_j-b(e_j,z)e_i=0.
$$

自由基的坐标比较给 $b(e_i,z)=b(e_j,z)=0$。每个指标都能配上另一个指标，因此 $b=0$。这个论证只比较自由模坐标，不把非零环元素当作可逆元素，也不使用域上的线性独立判据。

若 $T\in\operatorname{Aut}_D(R)$，把 (14.3) 用于 $Tx,Ty,Tz$，再作用 $T^{-1}$，可见 $h(x,z)=g_R(Tx,Tz)$ 满足同一个返回式。上述唯一性给 $h=g_R$。于是

$$
\omega_R(Tx,Ty,Tz)
=g_R(D_R(Tx,Ty),Tz)
=g_R(TD_R(x,y),Tz)=\omega_R(x,y,z).
$$

反过来，若 $T$ 保持 $g_R$ 和 $\omega_R$，则对每个 $z$，

$$
g_R(D_R(Tx,Ty),Tz)
=\omega_R(x,y,z)
=g_R(TD_R(x,y),Tz).
$$

$T$ 可逆且 $g_R$ 非退化，故 $D_R(Tx,Ty)=TD_R(x,y)$。在秩三自由模上，交替三形式在 $T$ 下乘以 $\det T$；将其用于 (14.3) 的单位系数 $\alpha\beta$，保定向恰好是 $\det T=1$。这证明前两个等式，没有从 $\det(T)^2=1$ 擅自推出 $\det T=1$。

最后用 (13.14) 的同一乘法。保持 $D_R,g_R$ 的 $T$ 唯一延伸为
$\Phi(s,a)=(s,Ta)$，此式保持单位、乘法和投影。反向的保投影 $R$-代数自同构保持 $\ker\pi_R=V_R$，在此限制为可逆线性映射，比较乘积的纯部分即得保持 $D_R$。两构造互逆；所有公式均与任意 $R\to S$ 的基变换交换。

非二特征的三维叉积自同构结论是 [Daza-García–Elduque–Tang，arXiv:2006.10324v1，定理 3.3、命题 3.4](https://arxiv.org/pdf/2006.10324v1) 的既有特例，其全局假设是 $\operatorname{char}F\ne2$。这里承重的延伸是同一弱入口所恢复的 $g$ 在任意系数环上的唯一性及特征二接口；不把该文注记 3.5 的光滑性断言外推到特征二。$\square$

**定义 14.3（特征二的实际域、参数源与解锁）。** 以下除特别说明外，假设 $\operatorname{char}F=2$，保留定义 14.1 的原入口。定理 13.9、13.13、推论 13.14 已给出

$$
\begin{gathered}
A=L,\quad [L:F]=4,\quad L^2=M\subset F,\quad [M:F^2]=4,\\
\lambda:M\to F^2,\quad \lambda(1)=1,\quad
q(V)=\ker\lambda,\quad M=F^2\oplus\ker\lambda.
\end{gathered}
\tag{14.4}
$$

在 (14.3) 的基中，$e_1^2=\alpha$、$e_2^2=\beta$、$e_3=e_1e_2$，故
$L=F(e_1,e_2)$、$M=F^2(\alpha,\beta)$。原 K 只量化原 $F$，不把 K 在扩域后继续成立作为假设。

对扩域 $E/F$，把 $L$ 唯一嵌入 $E$ 的一份代数闭包，$LE$ 表示其中的实际合成域；$ME^2$ 则是实际 $E$ 内由 $M$ 与 $E^2$ 生成的子域。称 $E$ 解锁，意为 $\operatorname{Aut}_D(E)\ne\{1\}$。基点为恒等的代数一参数子群指群函子的态射 $\mathbb G_{a,E}\to\operatorname{Aut}_{D_E}$；其底空间是 $\mathbb A^1_E$，零点映到恒等，且群律由加法给出。非恒定指其矩阵在 $E[t]$ 中并非恒等矩阵，而非仅指定一个切向量。

一个 $F$-代数 $R$ 几何约化，是指对每个扩域 $K/F$，$K\otimes_F R$ 都约化；概形的同名条件按基变换及仿射开集理解。这里采用 [Stacks，030V](https://stacks.math.columbia.edu/tag/030V) 的条件，其等价形式允许用有限纯不可分扩张检验。它比仅要求 $R$ 自身约化强。

**定理 14.4（任意交换环上的完整非平凡性判据）。** 对每个交换含单位 $F$-代数 $R$，

$$
\operatorname{Aut}_D(R)\ne\{1\}
\quad\Longleftrightarrow\quad
\exists\,0\ne v\in V_R:\ q_R(v)=0.
\tag{14.5}
$$

右侧不要求 $v$ 是幺模向量，即不要求其坐标生成单位理想。每个非约化 $R$ 均有非恒等自同构；零环的两侧均为假。由某个非零零向量直接写出的秩一式可以恒等，(14.5) 不断言每个这样的向量都给非恒等秩一式。

证明。若 $T\ne1$ 保持 $D_R$，定理 14.2 给它保持 $g_R$。特征二中 $q_R$ 可加，故对基向量有

$$
q_R(Te_i-e_i)=q_R(Te_i)+q_R(e_i)=0.
$$

至少一个 $Te_i-e_i\ne0$，得到必要性。

反向设 $v=\sum_i v_i e_i\ne0$ 且 $q_R(v)=0$，记 $\varphi(x)=g_R(v,x)$、$N(x)=\varphi(x)v$。有

$$
N^2=q_R(v)N=0,
\qquad g_R(Nx,y)=g_R(x,Ny)=\varphi(x)\varphi(y),
\qquad g_R(Nx,Ny)=0.
\tag{14.6}
$$

因此 $I+N$ 的平方为 $I$，并保持 $g_R$。行列式按列多线性展开时，含至少两列 $v$ 的项为零，从而
$\det(I+v\varphi)=1+\varphi(v)=1$。由定理 14.2，$I+N\in\operatorname{Aut}_D(R)$。

若某个 $v_i^2\ne0$，则 $N$ 的第 $i$ 个对角系数为 $G_{ii}v_i^2\ne0$，因为 $G_{ii}$ 是单位；所以此时 $I+N\ne I$。若所有 $v_i^2=0$，取一个非零坐标 $r=v_i$。此时 $r^2=0$，改用

$$
T=\operatorname{diag}(1+r,1+r,1).
\tag{14.7}
$$

$1+r$ 是自己的逆，$T$ 保持对角形式 $G$，$\det T=(1+r)^2=1$，且 $T\ne I$。这给出另一份非恒等自同构，完全不需要坐标可逆。两种情形穷尽全部非零 $v$。

若 $R$ 非约化，取非零幂零元 $a$，设 $n\ge2$ 是 $a^n=0$ 的最小正整数。则 $r=a^{n-1}\ne0$ 且 $r^2=0$，(14.7) 即适用。零环中 $V_R=0$ 且只有一个线性自同构，故单独也满足 (14.5)。$\square$

**定理 14.5（任意扩域的实际平方子域与参数族桥）。** 对任意扩域 $E/F$，以下五个条件等价：

$$
\begin{aligned}
&\operatorname{Aut}_D(E)\ne\{1\};\\
&q_E\text{ 有非零零向量};\\
&[ME^2:E^2]<4;\\
&[LE:E]<4;\\
&\text{存在基点为恒等的非恒定代数一参数子群 }
\mathbb G_{a,E}\longrightarrow\operatorname{Aut}_{D_E}.
\end{aligned}
\tag{14.8}
$$

两项次数实际相等，且只可能为 $1,2,4$。这些条件一旦成立，同一延拓 $D_E$ 就不再满足 K。此处没有把扩域后的入口重新假定为 P+K。

证明。前两项由定理 14.4 等价。为接到实际 $M$，在同一基上写

$$
q_E(X_1e_1+X_2e_2+X_3e_3)
=\alpha X_1^2+\beta X_2^2+\alpha\beta X_3^2.
\tag{14.9}
$$

拟线性形式的零向量由其系数在平方子域上的线性关系判断：$X_i^2$ 属于 $E^2$，反之每个 $E^2$ 中的关系系数在 $E$ 都有平方根。这个经典中间事实是 [Scully，arXiv:1710.09692v1，§2A—B、命题 2.1](https://arxiv.org/pdf/1710.09692v1) 的表示空间描述在此系数表上的应用。令
$C=ME^2=E^2(\alpha,\beta)$。$\alpha^2,\beta^2\in F^2\subset E^2$，所以 $1,\alpha,\beta,\alpha\beta$ 张成 $C$，添入每个参数的次数至多二，$[C:E^2]\in\{1,2,4\}$。当次数为四时它们构成基，(14.9) 各向异性；次数小于四时至多为二，三个系数 $\alpha,\beta,\alpha\beta$ 必线性相关，得到非零零向量。这证明第二、三项等价。

同一经典拟线性理论的范数域公式 [Scully，前引文 §2D](https://arxiv.org/pdf/1710.09692v1) 在原 $q$ 上给

$$
N(q)=F^2(\alpha\beta,\alpha^2\beta)
=F^2(\alpha,\beta)=M.
\tag{14.10}
$$

因此这里用的是原关系恢复的实际子域，不是一个只具有相同抽象次数的代用品。原 $q$ 是三维各向异性形式；按该文引理 2.2，它也是经典的二重拟 Pfister 型邻居。该识别及表示空间事实是本推导的中间输入，不单独承担新的分类结论。

在实际合成域内，平方映射给

$$
(LE)^2=ME^2=C,
\qquad E^2\subset C,
\qquad [LE:E]=[C:E^2].
\tag{14.11}
$$

确切地，平方把 $LE$ 同构到 $C$，把 $E$ 同构到 $E^2$，故把一份域基送到另一份域基。由此第三、四项等价。

若 $0\ne v\in V_E$ 且 $q_E(v)=0$，仍取 $N=v\otimes g_E(v,-)$。域上的非退化性保证 $g_E(v,-)\ne0$，故 $N\ne0$；(14.6) 给 $N^2=0$。对任意交换 $E$-代数 $B$ 和 $t\in B$，定义

$$
U_v(t)x=x+t\,g_B(v,x)v.
\tag{14.12}
$$

相同计算给它保持 $g_B$，行列式为一，逆为 $U_v(t)$，因而保持 $D_B$。又
$U_v(s)U_v(t)=U_v(s+t)$，且 $U_v(0)=I$。矩阵 $I+tN\in\operatorname{Aut}_D(E[t])$ 非恒定，所以第五项成立。任选 $N$ 的一个非零矩阵元，它属于 $E^\times$，因而从 $U_v(t)$ 的该矩阵元能读回 $t$；该群态射在每个 $E$-代数上也单射。这是对实际系数代数的多项式子群，不只是有理点的集合对应。

反之，若 $q_E$ 各向异性，则 $q_{E[t]}$ 没有非零零向量。事实上，将任何多项式向量写成 $w(t)=\sum_j w_jt^j$，拟线性给
$q(w(t))=\sum_j q_E(w_j)t^{2j}$。此多项式为零便逐项给 $q_E(w_j)=0$，继而 $w_j=0$。定理 14.4 因此给 $\operatorname{Aut}_D(E[t])=\{I\}$，排除第五项，甚至排除任意非恒定的 $\mathbb A^1_E$ 保关系族。

最后，返回式、$g_E$ 非退化与 $\widetilde D_E$ 可逆都由原恒等式和原可逆矩阵延拓，未使用 $K_E$。引理 13.6 因而适用于它们，给 $K_E$ 恰等价于 $q_E$ 各向异性；解锁时 $K_E$ 必失败。$\square$

**定理 14.6（几何约化参数源的仿射局部刚性与准确扩域版）。** 对每个几何约化 $F$-代数 $R$，$\operatorname{Aut}_D(R)=\{I\}$。更一般地，几何约化 $F$-概形 $S$ 上，平凡向量丛 $\mathcal O_S\otimes_F V$ 的任何保持同一 $D$ 的可逆 $\mathcal O_S$-线性自同构都在每个仿射开集上恒等，故全局恒等。

对任意扩域 $E/F$，以下两个条件等价：$q_E$ 各向异性；每个几何约化 $E$-参数源上的上述保 $D_E$ 族都恒等。这里第二个条件是对全部这种源的量化，不声称单个源的刚性必以几何约化为必要条件。

证明。设 $R$ 几何约化。按定义及 Stacks 030V，$R\otimes_F L$ 约化。若 $v=\sum_i r_i e_i\in V_R$ 满足 $q_R(v)=0$，考虑此环中的元素

$$
z=\sum_i r_i\otimes e_i,
\qquad z^2=\sum_i r_i^2\otimes e_i^2=q_R(v)\otimes1=0.
\tag{14.13}
$$

约化性给 $z=0$。$1,e_1,e_2,e_3$ 是 $L$ 的 $F$-基，故它们延拓后是 $R\otimes_F L$ 的自由 $R$-基，于是所有 $r_i=0$。定理 14.4 给所需刚性。几何约化性限制到仿射开集仍成立，同一论证逐开集适用；相同的恒等映射在交叠上相容，故得到概形断言。

对 $E$ 版，若 $q_E$ 各向异性，定理 14.5 给 $[LE:E]=4$。乘法映射 $E\otimes_F L\to LE$ 满射，源与目标都为四维 $E$-空间，故它是同构。对几何约化 $E$-代数 $B$，$B\otimes_E LE$ 约化；现在在此环中使用同一 (14.13)，其中 $1,e_1,e_2,e_3$ 是 $LE$ 的 $E$-基，再由定理 14.4 得刚性，概形版也逐仿射开集成立。若 $q_E$ 各向同性，定理 14.5 的 $U_v(t)$ 则在几何约化的 $E$-源 $\mathbb A^1_E$ 上非恒定，推翻普遍刚性条件。这证明精确等价。$\square$

**定理 14.7（最小有限解锁次数及全部二次来源）。** 原入口的最小有限解锁扩张次数恰为二。更精确地，对每个 $c\in F\setminus F^2$，在固定代数闭包内令 $E=F(\sqrt c)$，则

$$
\begin{aligned}
E\text{ 解锁}
&\Longleftrightarrow c\in M\setminus F^2\\
&\Longleftrightarrow F(\sqrt c)\text{ 是实际 }L/F\text{ 的二次中间域}.
\end{aligned}
\tag{14.14}
$$

可分二次扩张不解锁。对固定实际 $L$，这些最小来源、其存在性和最小次数均与 $\pi$ 无关。四次扩张 $E=L$ 足以解锁，但非最小；不同最小来源不必相互包含，不存在本结论所指定的唯一最小包含域。

证明。$E$ 的平方子域恰为 $E^2=F^2(c)$，这是次数二的扩张。若 $c\in M\setminus F^2$，则 $ME^2=M$，域塔给
$[ME^2:E^2]=[M:F^2(c)]=2$，定理 14.5 给解锁。若 $c\notin M$，因 $c^2\in F^2\subset M$，有 $[M(c):M]=2$，从而

$$
[ME^2:E^2]=[M(c):F^2(c)]
=\frac{[M(c):F^2]}{[F^2(c):F^2]}=\frac{8}{2}=4.
\tag{14.15}
$$

故不解锁。这给第一个等价。由于实际代数闭包中的平方根唯一，$\sqrt c\in L$ 恰等价于 $c\in L^2=M$；$c\notin F^2$ 保证对应中间域的次数确为二，得到第二个等价。

任意可分二次 $E/F$ 是可分生成扩域。[Scully，前引文，引理 3.4](https://arxiv.org/pdf/1710.09692v1) 给拟线性形式在可分生成扩域下保持各向异性，故原 $q$ 在 $E$ 上仍各向异性，定理 14.5 排除解锁。此经典输入实际上也排除了全部可分生成扩域，并非只排除二次扩张。

由 $[M:F^2]=4$，可选 $c\in M\setminus F^2$，于是确有二次解锁来源；次数一是原 $F$，其自同构只有恒等。因而最小有限次数为二。特征二的二次域扩张非可分时必为某个 $F(\sqrt c)$，所以 (14.14) 与可分情形穷尽全部最小有限来源。

上述判据只用实际 $M=L^2$，未用 $\lambda$ 或 $\pi$。定理 13.11 允许同一 $L$ 上任意 $F$-线性 $\pi$ 满足 $\pi(1)=1$，且每份投影均给原入口；逐份应用上述证明，判据和最小次数相同。它不把不同投影的完整自同构函子认作相同，也不合并带标记对象。

若 $E=L$，则 $E^2=M$，所以 $[ME^2:E^2]=1$，给四次全开根的充分性。另一方面，$F(e_1)$ 与 $F(e_2)$ 都是二次中间域；若它们相同，则 $L=F(e_1,e_2)$ 的次数至多二，与 $[L:F]=4$ 矛盾。两个不同二次域之间不能有真包含。故最小次数并不挑出一个唯一最小包含域。$\square$

**命题 14.8（平凡交集不能代替实际线性不交）。** 对任意定义 14.3 的原入口，存在扩域 $E/F$，使

$$
E\cap L=F,\qquad E^2\cap M=F^2,
\qquad [LE:E]=[ME^2:E^2]=2,
\tag{14.16}
$$

而同一 $D_E$ 有定理 14.5 的非恒定代数一参数子群。因此即使两个实际交集都最小，仍不能据此判刚性。

证明。在 $L$ 中取 $x=e_1$、$y=e_2$，则 $x^2=\alpha$、$y^2=\beta$，$1,x,y,xy$ 是 $F$-基。在实际有理函数域 $L(t)$ 中，$t$ 对 $L$ 超越，令

$$
z=x+ty,\qquad E=F(t,z),\qquad z^2=\alpha+\beta t^2.
\tag{14.17}
$$

$1,x,y,xy$ 在 $F(t)$ 上仍独立：任何关系清分母后，逐个 $t$ 的幂比较就回到它们在 $F$ 上的独立性。因此 $z\notin F(t)$，而 $z^2\in F(t)$，得 $[E:F(t)]=2$；同时 $LE=L(t)$，由域塔
$[LE:E]=4/2=2$。

若 $\ell\in E\cap L$，可唯一写

$$
\ell=a+bx+cy+dxy
=A(t)+B(t)(x+ty),
\qquad a,b,c,d\in F,\quad A(t),B(t)\in F(t).
$$

比较上述四个 $F(t)$-基系数给 $d=0$、$A(t)=a$、$B(t)=b$ 和 $tB(t)=c$。$t$ 超越而 $b,c\in F$，故 $b=c=0$，$\ell=a\in F$，得到第一个交集。若 $m\in E^2\cap M$，它在 $E$ 中有根，在 $L$ 中也有根；$L(t)$ 中平方单射使这两个根相同，属于 $E\cap L=F$，所以 $m\in F^2$。反向包含显然，得到第二个交集。(14.11) 给余下次数等式。

也可在此实际来源直接看到 (14.9) 的非零零向量：

$$
v=\beta t e_1+\alpha e_2+z e_3,
\qquad q_E(v)=\alpha\beta(\beta t^2+\alpha+z^2)=0.
\tag{14.18}
$$

$\alpha\ne0$ 保证 $v\ne0$，所以定理 14.5 给所述参数子群。

这里的线性不交严格采用 [Stacks，09IC，定义 9.27.2](https://stacks.math.columbia.edu/tag/09IC)：共同环境中的乘法映射 $E\otimes_F L\to EL$ 必须单射。本例此映射的源为四维 $E$-空间、像为二维 $E$-空间，故不单射。平凡交集没有支付这个定义所要求的全部联合线性关系。$\square$

**命题 14.9（双数方向、约化来源与几何约化边界）。** 下列现象均在上述同一入口范围内成立。每份原入口都有非恒等、约化后为恒等的双数自同构，而在原 $F$ 上没有非恒定 $\mathbb A^1_F$ 保关系族；每份二次解锁来源都给约化且光滑于该扩域的参数源，它作为 $F$-源却不几何约化；另有并不几何约化于 $F$、但仍完全刚性的域参数源。因此平方零形式方向、约化来源和几何约化来源具有不同的结论范围。

证明。先令 $R=F[\epsilon]/(\epsilon^2)$，取同一基上的

$$
H=\operatorname{diag}(1,1,0),\qquad
T=I+\epsilon H=\operatorname{diag}(1+\epsilon,1+\epsilon,1).
\tag{14.19}
$$

由 (14.7)，$T\in\operatorname{Aut}_D(R)$，$T\ne I$，但令 $\epsilon=0$ 后变成恒等。对应的 $H$ 是 $D$ 的非零导子：在三对基向量上，$D(e_1,e_2)=e_3$ 的导子式两侧均为零，而 $D(e_2,e_3)=\beta e_1$、$D(e_3,e_1)=\alpha e_2$ 的导子式两侧分别为 $\beta e_1$、$\alpha e_2$；重复槽和交换槽由交替性与双线性给出。一般乘法的自同构、基变换自然性及双数—导子接口直接沿用现有 [EvolutionAutomorphismTangentBridge](../../../D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismTangentBridge.lean) 的 $\mathrm{automorphisms}$、$\mathrm{Realizes}$ 与 $\mathrm{Infinitesimal}$ 中平方零构造及重构，及其 [对应 Blueprint](../../../Blueprint/D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismTangentBridge.md)；这里仅将该接口用于同一 $D$ 和这个 $H$，不另立通用切向分类。

这也展示秩一式的限制：$v=\epsilon e_1$ 是非零零向量，但
$v\otimes g_R(v,-)=0$，所以它的 (14.12) 秩一式恒等。非恒等的 (14.19) 来自定理 14.4 的另一情形。由于原 $q$ 各向异性，定理 14.5 已排除原 $F$ 上任何非恒定 $\mathbb A^1_F$ 族；因此非零双数方向本身不能供应这样的族，也不能把其维数当作几何维数。

再取定理 14.7 的二次解锁 $E=F(s)$、$s^2=c\in M\setminus F^2$。$E[t]$ 是约化环，$\mathbb A^1_E$ 光滑于 $E$，并承载定理 14.5 的非恒定子群。可是

$$
E\otimes_F E\simeq E[\eta]/(\eta^2),
\qquad \eta=1\otimes s-s\otimes1\ne0.
\tag{14.20}
$$

非零性由 $1,s$ 的 $F$-独立性给出；添入 $t$ 后该幂零元仍非零，所以 $E[t]$ 不几何约化于 $F$。因而此例没有违反定理 14.6 的 $F$ 版；它只给出光滑于 $E$ 的来源，不能把基域标签换成 $F$。

最后给出刚性而不几何约化的来源。令

$$
F=\mathbb F_2(u,v,w),\qquad
M=F^2(u,v),\qquad
L=F(\sqrt u,\sqrt v),\qquad E=F(\sqrt w),
\tag{14.21}
$$

其中 $u,v,w$ 代数独立，在 $L$ 上取基 $1,\sqrt u,\sqrt v,\sqrt{uv}$ 的标量坐标投影 $\pi$。有 $F^2=\mathbb F_2(u^2,v^2,w^2)$。按三个变量指数的奇偶分组，八个单项式
$u^iv^jw^k$、$i,j,k\in\{0,1\}$ 是 $F$ 的 $F^2$-基：有理函数分母乘以自身可化成平方分母，故它们张成；关系清去平方域分母后，八组多项式指数奇偶互异，故独立。因此 $[M:F^2]=4$ 且 $w\notin M$；平方映射给 $[L:F]=4$ 和 $L^2=M\subset F$。定理 13.11 保证这些数据确为原 P+K 入口。

定理 14.7 现在给 $\operatorname{Aut}_D(E)=\{I\}$，但把 (14.20) 中的 $c$ 换成 $w$，仍有 $E\otimes_F E$ 含非零平方零元，故域 $E$ 不几何约化于 $F$。这证明几何约化是普遍刚性的充分条件，不是单个来源刚性的必要条件。

特征二双线性等距群的非约化及约化后仍非几何约化的现象已有经典先例，参见 [Milne，*Algebraic Groups: The Theory of Group Schemes of Finite Type over a Field*，iAG2022，练习 24-2](https://www.jmilne.org/math/Books/iAG2022.pdf)。同书练习 24-3 的约化等距群描述以基域完美为前提，此处 $[M:F^2]=4$ 排除了该前提，故不据它推断本入口的光滑性、完整群结构或维数。$\square$

**定义 14.10（关系—来源桥的数学范围与完整白话解释）。** 本节的“关系—来源桥”指由同一全域 P+K 入口恢复的 $D,g,L,M$ 之间的 (14.2)、(14.5)、(14.8)、(14.14)，以及定理 14.6 的来源刚性。它的数学内容是将弱入口的唯一返回形式推广到全环，以此把非约化系数上的存在判据、扩域后的实际平方子域次数和最小二次来源接在同一对象上。叉积等距群、秩一等距变换、拟线性形式的表示空间与范数域、纯不可分域及线性不交都仅作为这些推导中的既有中间事实。所引文献的限定范围不包含从本入口到全部这些来源判据的同一条桥；这里将该桥视为仓内综合推导，不附历史首次性或穷尽文献的断言。C123 的引理 63.2 以实 EJA 及内导子协变为前提，[MatrixUnitGenerator](../../../Blueprint/D5/S3/Quantum/Transport/MatrixUnitGenerator.md) 处理复矩阵单位及实可微路径；两者均不提供这里任意域、特征二和实际 $M$ 的来源判据。

白话中的“原二元关系”就是原空间里两个输入产生一个响应的同一双线性规则；P 要求响应再与任何输入作用时返回最初两输入的平面，K 要求原标量域上作用两次才消失的方向第一次就已消失。§13 已由这两条关系迫使整个原空间只有三维，并恢复唯一的比较形式；把一个标量单位槽同三维纯部合在一起，特征二时得到一个四维域，每个元素的平方都回到原标量域，而投影决定哪三维是纯部。固定这些数据以后，原标量域上没有非恒等保关系变化，但允许平方零量的系数环可以显示只存在于形式层面的微小方向。若要得到一整条真正由多项式参数描述、逐参数保持同一关系的变化，障碍由四维域的实际平方子域决定：把来源域自身的平方同它合在一起后，若仍保留四个独立平方方向，就没有这种变化；若独立数降为二或一，就有非恒定的加法参数子群。最少只需添入原四维域里一个非平凡二次部分，不必把全部平方根都添齐；原标量域内的一个非平方数能否这样开根，恰由它是否属于实际平方子域判断。不同二次部分都可达到这个最小次数，投影的选择不改变此存在性判据。代价是原 K 在解锁后的域上失效，而新参数源的光滑性属于新域；这没有把形式方向变成原域上的变化，也没有提供物理控制、时间演化、Born 规则、复合或钟的实现。这里的三维始终指原 $V$，不指一个额外的整个物理状态空间。

## 追加锚（本行以下为增补区）

## 15. 同一实际域的相对约化检测与纯部次数边界

**定义 15.1（固定域的相对约化与归一化纯部）。** 设 $F$ 是特征二的域，$L/F$ 是有限域扩张，满足 $L^2\subseteq F$，记 $n=[L:F]=2^r$。允许 $r=0$，此时 $L=F$；$r\ge1$ 时扩张为纯不可分指数一。归一化投影指 $F$-线性映射 $\pi:L\to F$ 满足 $\pi(1)=1$。置

$$
V_\pi=\ker\pi,\qquad L=F1\oplus V_\pi,\qquad
q_\pi(v)=v^2\in F.
\tag{15.1}
$$

对每个交换含单位 $F$-代数 $R$，包括零环，置

$$
A_R=L\otimes_F R=R1\oplus V_{\pi,R},\qquad
V_{\pi,R}=V_\pi\otimes_F R,\qquad
\pi_R=\pi\otimes_F\operatorname{id}_R.
\tag{15.2}
$$

按 $L$ 中原乘法定义 $A_R$ 的乘法。选择任意 $F$-基 $1,b_1,\ldots,b_{n-1}$，其中 $b_i\in V_\pi$，则

$$
\begin{aligned}
q_{\pi,R}\Bigl(\sum_i t_i b_i\Bigr)&=\sum_i b_i^2t_i^2,\\
Q_R\Bigl(s1+\sum_i t_i b_i\Bigr)&=s^2+\sum_i b_i^2t_i^2,\\
x^2&=Q_R(x)1\qquad(x\in A_R).
\end{aligned}
\tag{15.3}
$$

这些式子由特征二和 $L^2\subseteq F$ 给出，与所选基无关。$R\to A_R$ 是直和分解中的单射，包括零环情形；因此 $Q_R$ 的标量值唯一。这里称 $q_{\pi,R}$ 各向异性，严格指全部向量上的条件

$$
\forall v\in V_{\pi,R},\quad q_{\pi,R}(v)=0\Longrightarrow v=0.
\tag{15.4}
$$

不要求向量幺模。称 $R$ 对固定实际 $L/F$ 相对约化，是指 $A_R$ 没有非零幂零元。它只涉及这一个 $L$。与之分别，$R$ 自身约化只检验 $R$ 中的幂零元；$R$ 几何约化于 $F$ 则要求对每个扩域 $K/F$，$K\otimes_F R$ 都约化，沿用定义 14.3 及 [Stacks，030V](https://stacks.math.columbia.edu/tag/030V)。

当 $n=4$ 且 $L$ 来自定义 14.3 的同一原入口 $D$ 时，其原投影为 §13 恢复的指定 $\pi$，$V_\pi$ 和 $q_\pi$ 就是原 $V$ 和 $q$。在同一实际 $L$ 上另选归一化投影时，定理 13.11 给相应的原模型 $(V_\pi,D_\pi)$，其中 $D_\pi(a,b)=ab-\pi(ab)1$。比较不同投影不表示同一 $D$ 可以任意改动其已恢复投影。对一般 $n$，本定义只取域乘法、投影与平方，不附加一个满足 P+K 的二元关系，也不假设扩底后的 K。

**定理 15.2（纯部到全部扩底代数的全环桥）。** 在定义 15.1 中，若 $r\ge2$，则对每份归一化 $\pi$ 及每个交换含单位 $F$-代数 $R$，

$$
q_{\pi,R}\text{ 各向异性}
\quad\Longleftrightarrow\quad
L\otimes_F R\text{ 约化}.
\tag{15.5}
$$

特别地，对定义 14.3 的同一四次原入口，准确的来源判据是

$$
\operatorname{Aut}_D(R)=\{I\}
\quad\Longleftrightarrow\quad
q_R\text{ 各向异性}
\quad\Longleftrightarrow\quad
L\otimes_F R\text{ 约化}.
\tag{15.6}
$$

第一等价直接使用定理 14.4；最后一项推出中间项的四次情形直接使用定理 14.6 证明中的 (14.13)，其中只需所述扩底环约化。反向蕴涵不要求 $R$ 是整环、Noether 环或有限生成 $F$-代数。

证明。先在本证明内给出所需域计算。对任意扩域 $E/F$，在 $E$ 的一份代数闭包中取 $L$ 的唯一 $F$-嵌入，记实际合成域为 $LE$。经典纯不可分逐次添根事实 [Stacks，09HF、09HI](https://stacks.math.columbia.edu/tag/09HI) 在此给出 $L=F(a_1,\ldots,a_r)$，其中 $a_i^2\in F$，逐次添入的次数均为二；故

$$
d=[LE:E]\in\{2^s:0\le s\le r\}.
\tag{15.7}
$$

乘法映射

$$
\mu_E:A_E\longrightarrow LE,\qquad \ell\otimes e\longmapsto \ell e
\tag{15.8}
$$

满射：其像是包含 $E,L$ 的有限维 $E$-子代数，且位于域中；非零元素的乘法在该有限维空间上单射，因而满射，故像本身是域，必等于 $LE$。对每个 $x\in A_E$，(15.3) 使

$$
\mu_E(x)=0\quad\Longleftrightarrow\quad x^2=0.
\tag{15.9}
$$

正向用 $0=\mu_E(x)^2=Q_E(x)$，以及 $x^2=Q_E(x)1$；反向用域 $LE$ 中平方单射。任何幂零元的像在域中为零，而 (15.9) 的元素都是幂零元。因此

$$
N_E:=\ker\mu_E=\sqrt{(0)}_{A_E}
=\{x\in A_E:x^2=0\},\qquad
\dim_E N_E=n-d.
\tag{15.10}
$$

等式不声称理想 $N_E$ 的乘积 $N_E^2$ 必为零，只说其中每个元素的平方为零。域上拟线性形式的零向量构成线性子空间是 [Scully，*Quasilinear quadratic forms and function fields of quadrics*，arXiv:1710.09692v1，§2A](https://arxiv.org/pdf/1710.09692v1) 的经典事实；此处 (15.8)—(15.10) 还明确识别了同一实际扩底代数中的该子空间。

若 $d<n$，二的幂条件给 $d\le n/2$。$V_{\pi,E}$ 是 $A_E$ 的余维一子空间，故

$$
\dim_E(N_E\cap V_{\pi,E})\ge n-d-1\ge n/2-1>0
\qquad(n\ge4).
\tag{15.11}
$$

其非零元素由 (15.9) 给纯部非零零向量。若 $d=n$，$N_E=0$，纯部便没有非零零向量。因此在域 $E$ 上，纯部各向异性当且仅当 $d=n$，也当且仅当 $A_E$ 约化。没有要求 $\pi$ 对某个添根基是坐标投影。

现在设 $q_{\pi,R}$ 各向异性。若 $R$ 非约化，从非零幂零元的最小消失幂可取 $0\ne t\in R$ 满足 $t^2=0$。取任意非零 $b\in V_\pi$ 并将它补成 $F$-基，则 $tb\ne0$，而 $q_{\pi,R}(tb)=b^2t^2=0$，矛盾。故 $R$ 约化。

还须把纯部条件传到局部环，不能把它直接传到剩余域。设 $S\subset R$ 为乘法闭集，$w=v/s\in S^{-1}V_{\pi,R}$ 且 $q(w)=0$。自由模的有限个坐标允许取共同分母 $s\in S$。存在 $t\in S$ 使 $tq(v)=0$，于是 $q(tv)=t^2q(v)=0$，由假设 $tv=0$，故 $w=(tv)/(ts)=0$。所以纯部各向异性保持于任意局部化；该清分母论证没有使用 $R$ 约化或 $s,t$ 非零因子。

对每个极小素理想 $\mathfrak p$，约化环 $R$ 的 $R_{\mathfrak p}$ 是域，且

$$
R\hookrightarrow
\prod_{\mathfrak p\in\operatorname{Min}R}R_{\mathfrak p}.
\tag{15.12}
$$

这是 [Stacks，00EU、00EW](https://stacks.math.columbia.edu/tag/00EW) 对任意约化环的结论，没有有限极小素或 Noether 假设。纯部条件经上述局部化成立于每个 $R_{\mathfrak p}$，域计算遂使每个 $A_R\otimes_R R_{\mathfrak p}$ 约化。取 $L$ 的有限 $F$-基，(15.12) 逐坐标给单射

$$
A_R\hookrightarrow
\prod_{\mathfrak p\in\operatorname{Min}R}
\bigl(L\otimes_F R_{\mathfrak p}\bigr).
\tag{15.13}
$$

左侧幂零元在右侧每个因子中均为零，故本来就是零。这支付了任意 $R$ 上从纯部到整体的方向。

反向对所有 $n$ 都成立：若 $A_R$ 约化，$v\in V_{\pi,R}$ 且 $q(v)=0$，则 (15.3) 给 $v^2=0$，因而 $v=0$。在四次情形这正是已引的 (14.13)。最后把定理 14.4 的原全环等价接上，得到 (15.6)，没有重新证明其自同构构造。零环中 $A_R=V_{\pi,R}=0$，约化与各向异性均成立，$\operatorname{Aut}_D(R)$ 只有恒等；因此它也满足全部等价。$\square$

**定理 15.3（准确次数阈值与两个低次替代）。** 称一对 $(L,\pi)$ 具有普遍纯部检测性质，是指 (15.5) 对所有交换含单位 $F$-代数 $R$ 成立。在定义 15.1 的全部次数中，该性质当且仅当 $r\ge2$，且其真假与归一化投影的选择无关。低次的准确替代如下。

若 $r=1$，对每份归一化投影可取 $0\ne\theta\in\ker\pi$，置 $a=\theta^2$，则 $a\in F^\times\setminus F^2$，$L=F(\theta)$，并且对所有 $R$，

$$
\begin{aligned}
q_{\pi,R}(t\theta)&=a t^2,\\
q_{\pi,R}\text{ 各向异性}&\quad\Longleftrightarrow\quad R\text{ 约化},\\
L\otimes_F R\text{ 约化}
&\quad\Longleftrightarrow\quad
\bigl[s^2+a t^2=0\Longrightarrow s=t=0
\text{ 对所有 }s,t\in R\bigr].
\end{aligned}
\tag{15.14}
$$

若 $r=0$，唯一投影是恒等，纯部为零，$q_{\pi,R}$ 对每个 $R$ 均各向异性，而 $L\otimes_F R$ 约化恰当且仅当 $R$ 约化。因而在所有次数中，固定 $L$ 后纯部各向异性的真假谓词都与 $\pi$ 无关；只有 $r\ge2$ 时，它才普遍检测整个扩底代数。

证明。$r\ge2$ 的结论直接使用定理 15.2。设 $r=1$。$\ker\pi$ 一维且与 $F1$ 的交为零，故 $\theta\notin F$，且 $1,\theta$ 是基。若 $a=c^2$、$c\in F$，域中平方单射给 $\theta=c$，矛盾；$a=0$ 同样不可能。因此 $a$ 是所述非零非平方数。因为 $a$ 在每个非零 $F$-代数中为单位，$q$ 各向异性恰指 $R$ 中没有非零平方零元；这与约化等价：任何非零幂零元 $u$ 以其最小消失幂 $m\ge2$ 给非零平方零元 $u^{m-1}$。零环也满足这两个条件。

对 (15.14) 的最后一项，$s+t\theta$ 的平方正是 $s^2+a t^2$。任意交换环约化当且仅当其平方零元只有零，故该二元条件正好检验整个 $A_R$。更一般地，定义 15.1 的每个次数都有

$$
A_R\text{ 约化}\quad\Longleftrightarrow\quad
\bigl[Q_R(x)=0\Longrightarrow x=0\quad(x\in A_R)\bigr],
\tag{15.15}
$$

因为 $Q_R(x)=0$ 与 $x^2=0$ 等价。纯部是这个完整条件的限制，二次时该限制仅保留原 $R$ 的约化信息。

严格的二次反例取 $R=L$。环 $R$ 是域，故对任意归一化 $\pi$，纯部形式各向异性。然而

$$
0\ne z=\theta\otimes1+1\otimes\theta\in L\otimes_F L,
\qquad z^2=a\otimes1+1\otimes a=0.
\tag{15.16}
$$

非零性由 $1\otimes1,\theta\otimes1$ 是右侧自由 $L$-模的基给出：$z$ 在第二个基元上的系数为一。这也在二元条件中给出 $(s,t)=(\theta,1)$ 的非零零向量。故每一份二次 $(L,\pi)$ 都不具有普遍检测性质。

若 $r=0$，$A_R=R$ 且纯部为零，取 $R=F[\epsilon]/(\epsilon^2)$，则纯部条件真而 $A_R$ 非约化，给一次情形的严格反例。所有次数已经穷尽。

在 $r\ge2$ 时纯部维数是 $2^r-1$，故三维、七维、十五维及更高这些维数均具有所述检测性质。定理没有把 $r\ge3$ 的纯部赋予一个新的 P+K 入口；原三维性仍直接来自定理 13.4。普遍纯部检测性质本身不能在这些维数之间唯一选出三维。$\square$

## 追加锚（本行以下为增补区）

## 16. 相对约化的局部判据与标记信息

**定义 16.1（局部环、剩余域与真假谓词）。** 保留定义 15.1。记 $\operatorname{Spec}R$、$\operatorname{Max}R$、$\operatorname{Min}R$ 分别为素理想、极大理想、极小素理想的集合。对素理想 $\mathfrak p$，$R_{\mathfrak p}$ 是局部环，$\kappa(\mathfrak p)=R_{\mathfrak p}/\mathfrak pR_{\mathfrak p}$ 是其剩余域。在 $\kappa(\mathfrak p)$ 的代数闭包中取唯一的 $L$ 嵌入以形成实际合成域 $L\kappa(\mathfrak p)$。定义下列真假谓词：

$$
\begin{aligned}
\mathcal P_{L,\pi}(R)&: q_{\pi,R}\text{ 各向异性},\\
\mathcal B_L(R)&:\ L\otimes_F R\text{ 约化},\\
\mathcal C_{L,\pi}(R)&:\quad
q_{\pi,\kappa(\mathfrak p)}\text{ 对每个 }
\mathfrak p\in\operatorname{Spec}R\text{ 各向异性}.
\end{aligned}
\tag{16.1}
$$

$\mathcal P$ 检验原环中的全部纯向量，$\mathcal C$ 检验全部剩余域中的向量；后者先商去素理想再取分式，前者的局部化只容许清分母。这是不同的操作。零环的上述素理想集合均为空，涉及这些集合的全称条件按空真理解。

**定理 16.2（准确的局部与整体条件）。** 对定义 15.1 的任意次数 $n$ 和任意 $R$，有

$$
\begin{aligned}
\mathcal P_{L,\pi}(R)
&\Longleftrightarrow
\forall\mathfrak m\in\operatorname{Max}R,\quad
\mathcal P_{L,\pi}(R_{\mathfrak m})\\
&\Longleftrightarrow
\forall\mathfrak p\in\operatorname{Spec}R,\quad
\mathcal P_{L,\pi}(R_{\mathfrak p}),\\[2pt]
\mathcal B_L(R)
&\Longleftrightarrow
\forall\mathfrak m\in\operatorname{Max}R,\quad
\mathcal B_L(R_{\mathfrak m})\\
&\Longleftrightarrow
\forall\mathfrak p\in\operatorname{Spec}R,\quad
\mathcal B_L(R_{\mathfrak p}).
\end{aligned}
\tag{16.2}
$$

其准确极小素判据为

$$
\mathcal B_L(R)
\quad\Longleftrightarrow\quad
\left[
R\text{ 约化，且 }
[L\kappa(\mathfrak p):\kappa(\mathfrak p)]=n
\text{ 对每个 }\mathfrak p\in\operatorname{Min}R
\right].
\tag{16.3}
$$

若 $n\ge2$，另有

$$
\mathcal P_{L,\pi}(R)
\quad\Longleftrightarrow\quad
\left[
R\text{ 约化，且 }
q_{\pi,\kappa(\mathfrak p)}\text{ 各向异性}
\text{ 对每个 }\mathfrak p\in\operatorname{Min}R
\right].
\tag{16.4}
$$

在 $n\ge4$ 时，(16.3)、(16.4) 的右侧等价；二次时 (16.4) 的剩余域条件自动成立，而 (16.3) 的次数条件仍不能省略。$n=1$ 时应使用定理 15.3 的零纯部结论，不能从纯部各向异性推出 $R$ 约化。

证明。定理 15.2 证明中的清分母论证只使用 (15.3)，故适用于所有次数的 $\mathcal P$，给它保持于任意局部化。反向设 $0\ne v\in V_{\pi,R}$ 且 $q(v)=0$。其 $R$-模湮灭理想

$$
\operatorname{Ann}_R(v)=\{a\in R:av=0\}
\tag{16.5}
$$

是一个真理想，取包含它的极大理想 $\mathfrak m$。若 $v/1=0$，便有 $s\notin\mathfrak m$ 使 $sv=0$，与 $s\in\operatorname{Ann}_R(v)\subseteq\mathfrak m$ 矛盾。故 $v/1$ 在该局部环中仍是非零零向量。这证明 $\mathcal P$ 的两项局部等价，且不要求向量幺模。

对 $\mathcal B$，扩底与局部化交换。若 $A_R$ 约化，而 $x/s$ 是其局部化中的幂零元，则存在正整数 $k$ 及被倒置的 $t$，使 $tx^k=0$。于是 $(tx)^k=t^{k-1}(tx^k)=0$，约化性给 $tx=0$，故 $x/s=0$。反向若 $0\ne x\in A_R$ 幂零，取包含真理想 $\operatorname{Ann}_R(x)$ 的极大理想；与上一段相同的论证使 $x/1$ 仍非零且幂零。因此得到 $\mathcal B$ 的两项局部等价。

若 $A_R$ 约化，单射 $R\to A_R$ 使 $R$ 约化。对极小素 $\mathfrak p$，经典事实 [Stacks，00EU](https://stacks.math.columbia.edu/tag/00EU) 给 $R_{\mathfrak p}$ 是域，故 $\mathfrak pR_{\mathfrak p}=0$ 且 $R_{\mathfrak p}=\kappa(\mathfrak p)$。$A_R$ 的局部化约化，由 (15.8)—(15.10) 得 $[L\kappa(\mathfrak p):\kappa(\mathfrak p)]=n$。反之，若 (16.3) 右侧成立，(15.10) 使所有这些域上的扩底环约化，而 [Stacks，00EW](https://stacks.math.columbia.edu/tag/00EW) 的约化环嵌入逐个有限自由坐标给出 (15.13)。故 $A_R$ 是约化环的积的子环，也约化。这证明 (16.3)。

对 (16.4)，当 $n\ge2$ 时，定理 15.2 证明中用平方零标量乘非零纯基元的论证仍适用，故 $\mathcal P$ 强制 $R$ 约化。再局部化到极小素，得到所述剩余域条件。反之，若右侧成立，一个 $q(v)=0$ 的纯向量在每个 $R_{\mathfrak p}=\kappa(\mathfrak p)$ 中都为零，(15.12) 逐坐标使 $v=0$。$n\ge4$ 时的比较由 (15.10)—(15.11) 给出；二次的纯形式在任何域上都是系数非零的一元平方形式，故其剩余域条件自动成立。

在 (16.3) 中，次数条件也恰好说 $L$ 与这些 $\kappa(\mathfrak p)$ 对实际嵌入线性不交：按 [Stacks，09IC，定义 9.27.2](https://stacks.math.columbia.edu/tag/09IC)，要求的正是 (15.8) 的乘法映射单射；其源维数为 $n$，像维数为所列次数。不能以实际交集最小代替此条件，反例已由命题 14.8 给出。

几何约化的全部扩张量词蕴涵 $\mathcal B_L(R)$，但固定 $L$ 的检验一般不蕴涵几何约化。在命题 14.9 的同一 (14.21) 中，$E=F(\sqrt w)$ 不几何约化于 $F$，且原 $\operatorname{Aut}_D(E)=\{I\}$；(15.6) 因而给 $L\otimes_F E$ 约化。这直接复用该例，不另作来源构造。另一方面，若固定的有限 $L$ 恰好是 $F^{1/2}$，[Stacks，030V](https://stacks.math.columbia.edu/tag/030V) 使这一次检验确与几何约化等价。因此边界是一般不能以一个选定 $L$ 代表全部扩张；不是断言每一个有限 $L$ 的检验都严格较弱。(15.5) 对所有 $R$ 成立的量词也只给每个 $R$ 上两个条件的等价，不把 $\mathcal B_L(R)$ 改成对所有扩域的条件。$\square$

**定理 16.3（全部剩余域判据的两个失败方向）。** 固定定义 14.3 的同一实际四次 $L/F$，对其每份归一化投影，下列两个蕴涵都不成立：

$$
\mathcal C_{L,\pi}(R)\Longrightarrow\mathcal P_{L,\pi}(R),
\qquad
\mathcal P_{L,\pi}(R)\Longrightarrow\mathcal C_{L,\pi}(R).
\tag{16.6}
$$

第一项的反例可取所有剩余域都等于原 $F$ 的非约化局部环；第二项的反例可取扩底代数本身为整环的几何约化 $F$-代数。对原 $D$，按 (15.6)，两项同样是以全部剩余域上的刚性替代原环刚性的失败方向。

证明。第一项取命题 14.9 已用的 $R_+=F[\epsilon]/(\epsilon^2)$。每个素理想包含幂零元 $\epsilon$，且商环 $F$ 是域，所以其唯一素理想是 $(\epsilon)$，剩余域为 $F$。原 $q_\pi$ 按定理 13.11 各向异性，故 $\mathcal C_{L,\pi}(R_+)$ 成立。然而对任何非零 $b\in V_\pi$，$\epsilon b$ 是非零平方零纯向量，故 $\mathcal P_{L,\pi}(R_+)$ 不成立。定理 14.4 给非恒等自同构，命题 14.9 的双数式已给具体实例。原环信息在取剩余域时被丢去。

第二项令 $R_-=F[t]$。有 $L\otimes_F R_-=L[t]$，这是整环，故 (15.5) 给 $\mathcal P_{L,\pi}(R_-)$。任意扩域 $K/F$ 上 $K[t]$ 都是整环，也直接说明 $R_-$ 几何约化于 $F$。

由原实际平方子域 $M=L^2$ 的 $[M:F^2]=4$，取 $c\in M\setminus F^2$。多项式 $t^2+c$ 按 [Stacks，09HF](https://stacks.math.columbia.edu/tag/09HF) 不可约，所以

$$
\mathfrak p=(t^2+c)\in\operatorname{Max}F[t],\qquad
\kappa(\mathfrak p)\simeq E:=F(\sqrt c).
\tag{16.7}
$$

这是定理 14.7 的原二次解锁域，故定理 14.4、14.7 给 $q_{\pi,E}$ 的非零零向量；因此 $\mathcal C_{L,\pi}(R_-)$ 不成立。这里的 $\mathfrak p$ 不是极小素，$F[t]$ 的唯一极小素是 $(0)$。其特殊纤维 $L\otimes_F E$ 的非约化性还能直接写出：在 $L$ 中令 $h=\sqrt c\notin F$，在 $E$ 中令 $s=\sqrt c$，则

$$
0\ne h\otimes1+1\otimes s\in L\otimes_F E,
\qquad (h\otimes1+1\otimes s)^2=0.
\tag{16.8}
$$

非零性由把 $1,h$ 补成 $L$ 的 $F$-基、再比较扩底后的 $E$-坐标给出。原环上的 $L[t]$ 没有幂零元，商出这个特殊纤维后却产生幂零元；(16.2) 中的实际局部环仍满足纯部各向异性，其剩余域则不满足。故两个方向的失败分别来自被抹去的原环幂零信息，以及取商后新出现的纤维退化。加上 $R$ 约化时，$\mathcal C$ 由 (16.4) 足以推出 $\mathcal P$，但第二个反例说明仍非必要。$\square$

**定理 16.4（共同真假谓词不能恢复纯部标记）。** 固定同一实际四次 $L/F$。对任意两份归一化投影 $\pi,\pi'$，以及每个交换含单位 $F$-代数 $R$，

$$
\begin{aligned}
\mathcal P_{L,\pi}(R)&=\mathcal P_{L,\pi'}(R)=\mathcal B_L(R),\\
\bigl[\operatorname{Aut}_{D_\pi}(R)=\{I\}\bigr]
&=\bigl[\operatorname{Aut}_{D_{\pi'}}(R)=\{I\}\bigr].
\end{aligned}
\tag{16.9}
$$

等号表示真假相同。若 $\pi\ne\pi'$，则其带标记代数不同构，原 $D_\pi,D_{\pi'}$ 模型不同构，而且纯二次形式 $q_\pi,q_{\pi'}$ 不 $F$-等距。因此即使知道对所有 $R$ 的共同真假谓词，仍不能恢复原投影、原纯部形式或原带标记对象。

证明。(16.9) 逐份由 (15.6) 给出；右端只用同一实际 $L$。带标记代数不同构直接使用定理 13.13：固定 $F$ 的纯不可分实际域没有非恒等 $F$-自同构，因此不同投影不能通过这样的同构等同。原 $D$ 模型的结论直接使用定理 13.12，而不重作入口分类。

还须核对纯形式本身。使用定理 13.13、推论 13.14 的同一实际 $M=L^2$ 及标记

$$
\lambda_\pi(m)=\pi(\sqrt m)^2\in F^2,\qquad
q_\pi(V_\pi)=\ker\lambda_\pi\subset M,
\tag{16.10}
$$

以及 $\pi'$ 的对应式。若 $\lambda_\pi=\lambda_{\pi'}$，对每个 $x\in L$ 取 $m=x^2$，平方单射便给 $\pi(x)=\pi'(x)$。因此不同投影有不同的归一化 $F^2$-线性标记。这些标记若有相同核 $H$，任意 $m\in M$ 可写成 $m=\lambda_\pi(m)1+h$、$h\in H$，而 $\lambda_{\pi'}(1)=1$ 会给 $\lambda_{\pi'}(m)=\lambda_\pi(m)$，矛盾。故不同投影的 (16.10) 表示集合不同。形式的 $F$-等距必保持全部表示值，因而不存在这样的等距；这也符合 [Scully，前引文，命题 2.1](https://arxiv.org/pdf/1710.09692v1) 的各向异性拟线性形式表示空间判据。

不同投影确实存在：取原 $L$ 上非零 $F$-线性泛函 $\ell$ 满足 $\ell(1)=0$，则 $\pi'=\pi+\ell$ 仍归一化而不同于 $\pi$。所以该信息丢失有实际实例。式 (16.9) 只比较每个参数环上“是否只有恒等”的真值，既没有给出不同 $V_{\pi,R}$ 的指定等距，也没有给出完整自同构群函子之间的识别。原标记仍由 (16.10) 的实际 $F^2$ 值泛函及其核保留。$\square$

**定义 16.5（同一关系、三维纯部与四维检验的完整白话释义）。** 这里把“同一实际域的有限检验”理解为：先保留原标量域和同一个二元响应，原关系要求响应再次作用时回到原输入平面，并排除原域上作用两次才消失的方向。§13 已证明这迫使整个原空间只有三维，并恢复比较形式；在特征二时，添上一个标量单位槽便得到四维实际域，原投影决定哪三维是纯部。现在给定任何系数环，检验的不是重新假设原核条件，而是问原三维纯部中是否出现非零却平方为零的向量。定理 14.4 已把这个问题同保关系自同构是否仍只有恒等精确连接；(15.5) 则说，仅检验由同一个四维域扩底得到的整个代数有没有非零幂零元，恰好就够了。这个环可以有零因子、幂零元或无限多极小素，零环也包含在内；证明在原环已有幂零元时由纯方向检出它，在原环约化时转到各极小素的域，再把各处结论接回原环。它不是把全部剩余域当作原环：剩余域能抹去双数方向，也能在一个原本约化的多项式来源的特殊纤维中新增退化。几何约化原先保证每一种扩域都不产生幂零元；这里对一个给定参数环只需同一实际四维域的这一次扩底，通常不必要求所有扩域。纯部检测整体也不是三维的唯一选择原则：次数为四、八、十六及更高二幂时，余下一维标量槽后的纯部都能这样检测；二次时纯部只有一维，只能看见原系数环是否约化，不能看见两槽之间的平方抵消。固定实际四维域以后，改变归一化投影不会改变每个参数环上的这些真假答案，却会改变原纯部的实际表示值、形式和带标记对象；共同真假答案也没有把完整群函子合并。这些结论只连接原代数关系、三维纯部、四维整体和固定域的约化检验，不增加物理控制、Born 规则、复合或时钟的含义。

## 追加锚（本行以下为增补区）


## 17. 任意观察子空间的最小检测

**定义 17.1（观察形式与检测性质）。** 设 $F$ 是特征二的域，$L/F$ 是有限扩张，满足
$L^2\subseteq F$，并记
$$
n=[L:F]=2^r\ge2,\qquad M=L^2,\qquad [M:F^2]=n.
$$
不再选取投影或坐标。对任意 $F$-线性子空间 $W\le L$，由于平方映射在特征二下可加且 $L^2\subseteq F$，定义
$$
q_W(w)=w^2\in F\qquad(w\in W).
$$
对交换含单位 $F$-代数 $R$，记 $W_R=W\otimes_F R$，并定义
$$
q_{W,R}\left(\sum_i w_i\otimes t_i\right)
=\sum_i w_i^2t_i^2\in R.
\tag{17.1}
$$
称 $q_{W,R}$ 各向异性，是指对全部向量
$$
q_{W,R}(v)=0\Longrightarrow v=0\qquad(v\in W_R);
\tag{17.2}
$$
这里不要求向量的坐标生成单位理想。置
$$
A_R=L\otimes_F R.
$$
称 $W$ 具有全环检测性质，是指
$$
\mathsf U(W):\qquad
\forall R,\quad
q_{W,R}\text{ 各向异性}
\Longleftrightarrow
A_R\text{ 约化},
\tag{17.3}
$$
其中 $R$ 遍历全部交换含单位 $F$-代数，包括零环、带零因子环、非约化环和非 Noether 环。相应地，称 $W$ 具有全域检测性质，是指 (17.3) 只对所有域扩张 $E/F$ 成立。

**引理 17.2（域上的核与观察交）。** 对任意域扩张 $E/F$，在代数闭包中取 $L$ 与 $E$ 的实际合成域 $LE$，令
$$
\mu_E:L\otimes_F E\longrightarrow LE,\qquad
\ell\otimes e\longmapsto \ell e,
$$
并置 $d_E=[LE:E]$。则
$$
\dim_E\ker\mu_E=n-d_E,
\tag{17.4}
$$
且
$$
\begin{aligned}
L\otimes_F E\text{ 约化}
&\Longleftrightarrow d_E=n,\\
q_{W,E}\text{ 各向异性}
&\Longleftrightarrow
\ker\mu_E\cap W_E=0.
\end{aligned}
\tag{17.5}
$$
若 $d_E<n$，则 $d_E\le n/2$。

证明。扩底后的平方恒等式与 (15.3) 相同：对 $x\in L\otimes_F E$，
$$
x^2=Q_E(x)1.
$$
于是 $\mu_E(x)=0$ 当且仅当 $x^2=0$：一方面零像的平方为零，另一方面 $x^2=0$ 时 $\mu_E(x)^2=0$，而 $LE$ 是域，故 $\mu_E(x)=0$。同一论证说明 $\ker\mu_E$ 正是 $L\otimes_F E$ 的幂零根，维数由满射 $\mu_E$ 的像维数 $d_E$ 给出。限制到 $W_E$ 即得第二个等价。

$L/F$ 是有限指数一纯不可分扩张，逐次添入平方根的次数均为二；因此 $d_E$ 是 $n$ 的二幂。若它严格小于 $n$，便至多为 $n/2$。这正是旧§15 中 (15.7)--(15.10) 的域计算，所用条件恰为本引理的 $\operatorname{char}F=2$、$L^2\subseteq F$ 和有限性；没有加入投影、P+K 或扩域后的额外关系。$\square$

**引理 17.3（半维以下的避交元）。** 若 $W\le L$ 的维数 $m$ 满足 $m\le n/2$，则存在 $h\in L\setminus F$ 使
$$
W\cap hW=0.
\tag{17.6}
$$
对任意 $h\in L\setminus F$，(17.6) 等价于由乘法给出的 $E_h$-线性映射
$$
W\otimes_F E_h\longrightarrow L,\qquad
x\otimes1+y\otimes h\longmapsto x+hy,
\quad E_h=F(h),
\tag{17.7}
$$
单射。

证明。若 $W=0$，任选 $h\in L\setminus F$ 即可。以下设 $m\ge1$。本假设下 $F$ 必为无限域：若 $F$ 有限，则 $L$ 亦有限，单射的平方映射在 $L$ 上满射，故 $L=L^2\subseteq F$，与 $n\ge2$ 矛盾。

令
$$
\mathcal S(W)=\{xy^{-1}:x,y\in W,\ y\ne0\}\subseteq L.
$$
对 $h\in L\setminus F$，存在非零向量同时属于 $W$ 和 $hW$，当且仅当 $h\in\mathcal S(W)$。又因 $W\ne0$，有 $F\subseteq\mathcal S(W)$。所以只须在 $L$ 中找一个不属于 $\mathcal S(W)$ 的实际元素。

任选 $W$ 的 $F$-基 $w_1,\ldots,w_m$，并用 $L$ 的一组 $F$-基将其识别为 $\mathbf A_F^n$。对每个 $1\le j\le m$，取 $d=2m-1$ 个独立变元 $s_1,\ldots,s_m$ 及 $t_i\ (i\ne j)$，置
$$
X=\sum_{i=1}^m s_iw_i,\qquad
Y_j=w_j+\sum_{i\ne j}t_iw_i,\qquad
Q_j=Y_j^2=w_j^2+\sum_{i\ne j}t_i^2w_i^2\in F[t_i:i\ne j].
$$
$Q_j$ 的常数项为 $w_j^2\ne0$。在主开集 $U_j=\{Q_j\ne0\}\subseteq\mathbf A_F^d$ 上定义正则映射
$$
f_j:U_j\longrightarrow\mathbf A_F^n,\qquad
f_j(s,t)=\frac{XY_j}{Q_j}.
$$
这里乘法取自 $L$ 的 $F$-代数结构，分母是 $F$ 上的标量多项式；每个坐标的分子和共同分母 $Q_j$ 的总次数均至多为二。在每个 $F$-点上，$Y_j\ne0$ 且 $Y_j^{-1}=Y_j/Q_j$，故 $f_j(s,t)=XY_j^{-1}\in\mathcal S(W)$。

反过来，任取 $xy^{-1}\in\mathcal S(W)$，写 $y=\sum_i a_iw_i$，选取 $a_j\ne0$。同时把 $x,y$ 乘以 $a_j^{-1}$，比值不变，而新分母的第 $j$ 个坐标为一。因此它们给出 $U_j(F)$ 的一个点，像恰为 $xy^{-1}$。于是实际点的像满足
$$
\mathcal S(W)=\bigcup_{j=1}^m f_j\bigl(U_j(F)\bigr).
$$

因为 $d=2m-1<n$，每个 $f_j$ 的 $n$ 个坐标有理函数代数相关。所需的维数比较可直接验证：把这些坐标的全部总次数至多 $D$ 的单项式乘以 $Q_j^D$，便得到 $d$ 个变元中总次数至多 $2D$ 的多项式。这样的单项式有 $\binom{D+n}{n}$ 个，所在多项式空间的维数为 $\binom{2D+d}{d}$。由 $n>d$，当 $D$ 充分大时前者严格大于后者，故存在非平凡的 $F$-线性关系。这给出非零多项式
$$
P_j\in F[Z_1,\ldots,Z_n],\qquad P_j\circ f_j=0.
$$
关系是有理函数恒等式，故在 $U_j$ 的每个 $F$-点上成立；特别地，像的闭包包含于真闭集 $V(P_j)$。多项式 $P=\prod_{j=1}^m P_j$ 非零，并在整个 $\mathcal S(W)$ 上消失。无限域上的非零多项式不能在全部 $F^n$ 上消失，所以存在实际 $h\in L$ 满足 $P(h)\ne0$。这使 $h\notin\mathcal S(W)$，又由 $F\subseteq\mathcal S(W)$ 得 $h\notin F$，从而得到 (17.6)。特别在 $m=n/2$ 时仍有 $d=n-1<n$，因此同一证明覆盖等号边界。

对 $h\in L\setminus F$，由 $h^2\in F$ 知 $1,h$ 是 $E_h$ 的 $F$-基，故 (17.7) 的源向量唯一写为 $x\otimes1+y\otimes h$。若其像为零，则 $x=hy\in W\cap hW$；交为零时 $x=0$，并由 $h\ne0$ 得 $y=0$。反过来，若 $0\ne x=hy\in W\cap hW$，则 $x\otimes1+y\otimes h$ 是非零核向量。因此 (17.6) 正好等价于 (17.7) 的单射性。$\square$

**定理 17.4（任意观察子空间的精确全环判据）。** 在定义 17.1 的条件下，对任意 $W\le L$，令 $m=\dim_F W$。以下三项等价：
$$
\begin{aligned}
&\text{$W$ 具有全环检测性质；}\\
&\text{$W$ 具有全域检测性质；}\\
&m>n/2.
\end{aligned}
\tag{17.8}
$$
因此最小检测维数为
$$
m_{\min}=n/2+1.
\tag{17.9}
$$
这同时是给定 $W$、某个 $m$ 维 $W$ 和全部 $m$ 维 $W$ 三种量词的准确结论：
$$
\begin{array}{c|c}
m>n/2&m\le n/2\\ \hline
\text{每个 $m$ 维 $W$ 都检测}&
\text{没有一个 $m$ 维 $W$ 检测}\\
\text{存在一个 $m$ 维 $W$ 检测}&
\text{不存在 $m$ 维 $W$ 检测}.
\end{array}
\tag{17.10}
$$
等号 $m=n/2$ 属于失败侧，不能并入成功侧。

特别地，$W=0$ 总是失败，因为它的各向异性对所有 $R$ 都为真；$W=L$ 总是成功，因为它检验整个 $A_R$ 的平方零元。

证明。先设 $m>n/2$。对任意域 $E/F$，若 $A_E$ 约化，则引理 17.2 给 $\ker\mu_E=0$，所以 $q_{W,E}$ 各向异性。若 $A_E$ 不约化，则 $d_E<n$，从而 $d_E\le n/2<m$。由维数公式
$$
\dim_E(W_E\cap\ker\mu_E)
\ge m+(n-d_E)-n
=m-d_E>0,
\tag{17.11}
$$
引理 17.2 给 $q_{W,E}$ 的非零零向量。故全域检测成立。

还须把这件事延伸到任意环。对非零 $W$，若 $R$ 非约化，取非零平方零元 $t\in R$ 和非零 $w\in W$；把 $w$ 补成 $W$ 的 $F$-基可见 $tw\ne0$，而
$$
q_{W,R}(tw)=t^2w^2=0.
$$
所以两边都为假。若 $R$ 约化，旧§16 的极小素桥对任意有限自由子模逐坐标适用：由 [Stacks，00EU](https://stacks.math.columbia.edu/tag/00EU) 和 [Stacks，00EW](https://stacks.math.columbia.edu/tag/00EW)，
$$
q_{W,R}\text{ 各向异性}
\Longleftrightarrow
q_{W,\kappa(\mathfrak p)}\text{ 各向异性对每个 }
\mathfrak p\in\operatorname{Min}R.
\tag{17.12}
$$
这一步只用局部化清分母和约化环嵌入极小素局部域的结论，不要求 $R$ 是整环、Noether 或有限生成。对同一批极小素，旧§16 的全环桥给
$$
A_R\text{ 约化}
\Longleftrightarrow
[L\kappa(\mathfrak p):\kappa(\mathfrak p)]=n
\quad\text{对每个 }\mathfrak p\in\operatorname{Min}R.
\tag{17.13}
$$
若右侧在某个 $\mathfrak p$ 失败，(17.11) 在剩余域上给非零核交；(17.12) 使 $q_{W,R}$ 失败。若右侧处处成立，$A_R$ 约化而 $q_{W,R}$ 自动各向异性。零环的极小素集合为空，两个全称条件都按空真处理，结论仍成立。

反过来设 $m\le n/2$。由引理 17.3 取 $h\in L\setminus F$ 满足 $W\cap hW=0$，令
$$
c=h^2\in M\setminus F^2,\qquad E_h=F(h).
\tag{17.14}
$$
$h\notin F$ 且平方映射在域上单射，所以 $c\notin F^2$，从而 $[E_h:F]=2$；这是同一实际 $L$ 内的二次子域。由于 $E_h\subset L$，
$$
[LE_h:E_h]=[L:E_h]=n/2<n,
$$
故 $A_{E_h}$ 非约化。另一方面，(17.7) 的单射性与引理 17.2 给
$$
q_{W,E_h}\text{ 各向异性}.
$$
这里使整体不约化与使观察形式各向异性的正是同一个 $h$ 和同一个实际子域 $E_h\subset L$。特别在 $m=n/2$ 时，(17.7) 是两个 $m$ 维 $E_h$-空间间的单射，故为同构；等号并不迫使出现观察零向量。所以全域检测失败，也因而全环检测失败。

最小有限扩域次数不能为一：唯一的一次扩域是 $F$，而 $L\otimes_FF=L$ 是域。上面构造的 $E_h$ 次数为二，故每个 $m\le n/2$ 的失败 $W$ 的最小有限失败见证次数恰为二。$\square$

**定理 17.5（二次失败来源的实际刻画）。** 设 $m\le n/2$。对 $h\in L\setminus F$，令 $E_h=F(h)$。则下列条件等价：
$$
\begin{aligned}
&[E_h:F]=2,\quad L\otimes_FE_h\text{ 不约化，且 }q_{W,E_h}\text{ 各向异性};\\
&h^2\in M\setminus F^2\quad\text{且}\quad W\cap hW=0;\\
&\text{(17.7) 是单射。}
\end{aligned}
\tag{17.15}
$$
所有使整体退化而保留给定 $W$ 各向异性的二次来源，恰由这些条件给出。反之，若 $E/F$ 是任意二次扩域且 $L\otimes_FE$ 不约化，则 $E$ 必为某个 $E_h$，其中 $h\in L\setminus F$；它是否保留 $W$，仍须另外检查 $W\cap hW=0$。

证明。第一行到第二行的平方根条件已在 (17.14) 中说明；(17.7) 的核由 $x+hy=0$ 描述，故其单射性正好是 $W\cap hW=0$。这也证明第二行与第三行等价。

再设 $E/F$ 为二次且 $L\otimes_FE$ 不约化。若 $E/F$ 可分，则它与纯不可分扩张 $L/F$ 线性不交，故扩底仍为域。于是 $E/F$ 不可分，可写为 $E=F(\sqrt c)$，其中 $c\in F\setminus F^2$。令 $E^2=F^2(c)$。同一实际平方子域计算给
$$
[LE:E]=[ME^2:E^2]
=\begin{cases}
n/2,&c\in M\setminus F^2,\\
n,&c\notin M.
\end{cases}
\tag{17.16}
$$
非约化性迫使第一种情形。唯一平方根 $h=\sqrt c$ 属于 $L$，于是 $E=F(h)$，且 $h^2=c\in M\setminus F^2$。这正是旧§14.7 的二次解锁计算在任意 $n=2^r$ 上的同一参数对应；它没有把破坏 $A_E$ 误当成保留给定 $W$，后者仍由交为零这一独立条件决定。$\square$

**命题 17.6（固定参数环的准确等价条件）。** 对固定交换含单位 $F$-代数 $R$，令
$$
d_{\mathfrak p}=[L\kappa(\mathfrak p):\kappa(\mathfrak p)]
$$
并令
$$
\rho_{\mathfrak p}:W\otimes_F\kappa(\mathfrak p)
\longrightarrow L\kappa(\mathfrak p)
$$
为乘法映射的限制。若 $W\ne0$，则
$$
q_{W,R}\text{ 各向异性}
\Longleftrightarrow
\left[
R\text{ 约化，且 }\rho_{\mathfrak p}\text{ 对每个 }
\mathfrak p\in\operatorname{Min}R\text{ 单射}
\right].
\tag{17.17}
$$
同时
$$
A_R\text{ 约化}
\Longleftrightarrow
\left[
R\text{ 约化，且 }d_{\mathfrak p}=n
\text{ 对每个 }\mathfrak p\in\operatorname{Min}R
\right].
\tag{17.18}
$$
因此，对 $W\ne0$，固定 $R$ 时
$$
q_{W,R}\text{ 各向异性}
\Longleftrightarrow A_R\text{ 约化}
\tag{17.19}
$$
当且仅当
$$
\begin{cases}
R\text{ 非约化},\quad\text{或}\\
R\text{ 约化且 }\bigl[
d_{\mathfrak p}=n\ \text{对所有 }\mathfrak p,
\ \text{或存在 }\mathfrak p\text{ 使 }\ker\rho_{\mathfrak p}\ne0
\bigr].
\end{cases}
\tag{17.20}
$$
若 $W=0$，左侧在每个 $R$ 上恒真，故固定 $R$ 的等价条件恰为 $A_R$ 约化，即恰为 (17.18)。

证明。$R$ 非约化时，非零平方零标量乘以 $W$ 中的非零向量，直接给出 (17.17) 的反向失败；这一步覆盖所有零因子和幂零情形。$R$ 约化时，若观察条件在 $R$ 中成立，局部化清分母给每个 $R_{\mathfrak p}$ 中的条件；反之若每个极小素局部域中成立，(17.12) 的逐坐标嵌入把任意零向量送成零，遂使它本身为零。极小素局部环是域，故得到 (17.17)。式 (17.18) 正是旧§16 的 (16.3)，其证明使用同一 [Stacks，00EU、00EW] 桥。将两式逐项比较即得 (17.20)。零环的极小素集合为空，且零模块上的各向异性按定义成立，所以所有边界仍相容。$\square$

这里出现的始终是极小素理想；把 (17.17) 改成所有素理想的剩余域条件会落入§16.3所示的两个失败方向。式 (17.9) 是对所有参数环的普遍结论，不能替代 (17.20) 对一个固定 $R$ 的准确必要条件。

**定义 17.7（维数边界与四次整体的白话释义）。** “观察 $W$ 能检测整体”不是说 $W$ 已经包含某个投影核，也不是说它闭合于乘法；它只说在每一个参数环上，$W$ 中的平方零向量与整个 $L\otimes_F R$ 的幂零退化同时出现或同时不出现。域上，整体退化的核至少有半个 $L$ 的维数；留下多于半维的观察部分，必与它相交。留下恰好半维时，交可以被避开，而且每个这样的 $W$ 都能在同一个实际 $L$ 内找到一个二次子域作为失败来源。这个二次来源必须同时满足 $h^2\in L^2\setminus F^2$ 与 $W\cap hW=0$；仅仅知道 $L\otimes_FE_h$ 退化，并不能说明给定 $W$ 看见了零向量。

当原整体是四维时，$n=4$，最小检测维数为 $3$。因此“四次整体中的最小三维观察”是本定理的半维加一边界：任意三维 $F$-子空间都能检测全部交换含单位 $F$-代数，而任意二维子空间都在某个同一实际四次域的二次子域上失效。这里的三维最小性只描述检测任务；§13 由原 P+K 关系选出的三维纯部是另一条结论，不能由本检测定理单独推出。

当 $n=8,16,\ldots$ 时，最小维数分别为 $5,9,\ldots$；旧纯部的维数 $n-1$ 当然仍能检测，却不再是最小观察。二次整体 $n=2$ 是极端边界，只有 $W=L$ 能作普遍检测。结论不选择实复数、复合、物理时间、完整 $\Omega$ 维数或任何新的高维 $D$、群和导子分类；它只刻画固定实际域的线性观察部分与扩底约化之间的关系。

本单元的外部条件与旧桥逐一对应：有限指数一域的逐次二次塔和二次来源使用 [Stacks，09HF](https://stacks.math.columbia.edu/tag/09HF) 及 [Stacks，09HI](https://stacks.math.columbia.edu/tag/09HI) 所适用的纯不可分条件；任意环的极小素局部化与约化嵌入使用 [Stacks，00EU](https://stacks.math.columbia.edu/tag/00EU) 及 [Stacks，00EW](https://stacks.math.columbia.edu/tag/00EW)。域上平方形式核的识别沿用旧§15 已注明的 Scully，*Quasilinear quadratic forms and function fields of quadrics*，arXiv:1710.09692v1，§2A；这里新增的承重连接仅是把该核与任意 $W_E$ 的交作精确比较。$\square$

## 追加锚（本行以下为增补区）

## 18　实际交替乘法的线性记录与来源恢复

**定义 18.1（固定实际乘法、窗口与来源）。** 设 $F$ 是特征二的域，$L/F$ 是有限域扩张，满足 $L^2\subseteq F$，记 $n=[L:F]$，允许 $n=1$。以下始终使用同一个实际 $L$ 的乘法及其诱导的 $F$-线性映射
$$
\kappa:\Lambda_F^2L\longrightarrow L/F,
\qquad \kappa(u\wedge v)=uv+F.
\tag{18.1}
$$
这里 $L/F$ 表示商向量空间。乘法模 $F$ 是交替双线性的，因为 $u^2\in F$；故 (18.1) 确定唯一的线性映射。它在整个 $L$ 上满射，因为 $\kappa(1\wedge h)=h+F$。不另选线性记录器。

预先固定任意 $F$-子空间 $W\le L$，记 $m=\dim_FW$。对 $h\in L\setminus F$，置 $K_h=F(h)$。称实际二次中间域 $K_h$ 在 $W$ 中可见，当且仅当存在 $v\in L^\times$ 使 $vK_h\subseteq W$，并记
$$
\operatorname{Src}(W)=\{K_h:\exists v\in L^\times,
\ vK_h\subseteq W\}.
\tag{18.2}
$$
对一个指定记录 $r\in L/F$，其来源使用同一输入对定义为
$$
\operatorname{Src}_W(r)=
\{F(u/v):u,v\in W\text{ 在 }F\text{ 上独立，且 }uv+F=r\}.
\tag{18.3}
$$
所有向量、子域和存在量词均在原 $L/F$ 内。

式 (18.1) 在完整四次域上直接沿用 Havlicek，[*Clifford Parallelisms and External Planes to the Klein quadric*，arXiv:1511.06308v1](https://arxiv.org/abs/1511.06308v1)，§3 case (B)、§5 式 (5.1)–(5.3) 的 $H/F$ 与 $\kappa$：case (B) 中共轭为恒等，因而 $\overline u v+F=uv+F$。该文的 case (B) 明确要求 $[H:F]=4$；这里只把同一公式用于已给定的任意有限指数一域，不借用其四维平行类分类处理高次域。

**定理 18.2（实际乘积唯一绑定二次来源）。** 对任意独立的 $u,v\in L$，有
$$
uv\notin F,\qquad F(u/v)=F(uv),\qquad
Fu+Fv=vF(u/v).
\tag{18.4}
$$
每个非零 $r=h+F\in L/F$ 唯一确定一个实际二次域 $K_h$，且
$$
\operatorname{Src}_W(r)=
\begin{cases}
\{K_h\},&r\text{ 有 }W\text{ 内的实际独立输入对},\\
\varnothing,&r\text{ 没有这样的输入对}.
\end{cases}
\qquad \operatorname{Src}_W(0)=\varnothing.
\tag{18.5}
$$
改变 $r$ 的非零 $F$-倍数不改变其候选来源域。于是实际二次中间域与 $\mathbf P_F(L/F)$ 的 $F$-点一一对应，但一个候选域是否在 $W$ 可见仍是另一条件。

证明。独立性给 $v\ne0$、$u/v\notin F$。因 $v^2\in F^\times$，
$$
uv=v^2(u/v),\qquad u/v=(v^2)^{-1}uv.
$$
这证明前两式，第三式由 $u=v(u/v)$ 得到。每个 $h\notin F$ 的平方在 $F$，所以 $K_h=F+Fh$ 是二次域；这里复用 [Stacks，09HF，Lemma 9.14.2](https://stacks.math.columbia.edu/tag/09HF) 在 $p=2$ 的不可约性结论。若 $h$ 加上标量，或乘以非零标量，$F(h)$ 都不变。反过来，$F(h)=F(h')$ 恰好意味着 $h'=\alpha+\beta h$，其中 $\alpha\in F$、$\beta\in F^\times$。这给所述射影点对应。若 $uv+F=h+F\ne0$，则 $F(u/v)=F(uv)=F(h)$，标签确实来自这同一对输入；零记录由 $uv\notin F$ 排除。最后，任一平面 $vK_h\subseteq W$ 可取一组独立基，其比值生成 $K_h$；故 (18.2) 与全部实际记录的来源并集相同。这一比值桥复用 §17 引理 17.3、定理 17.5 中同一实际 $h$ 的关系。$\square$

**定义 18.3（实际集、线性像与射影中心）。** 置
$$
\begin{aligned}
\mathcal A(W)&=\{u\wedge v:u,v\in W\text{ 在 }F\text{ 上独立}\},\\
\mathcal T_\kappa(W)&=\kappa(\mathcal A(W)),\\
I_\kappa(W)&=\kappa(\Lambda_F^2W).
\end{aligned}
\tag{18.6}
$$
非零虚假记录指 $I_\kappa(W)\setminus(\mathcal T_\kappa(W)\cup\{0\})$ 中的元素。$\mathcal A(W)$ 是去掉原点的实际分解锥；当 $m\le1$ 时它为空，$\mathcal T_\kappa(W)=\varnothing$，而 $\Lambda^2W=I_\kappa(W)=\{0\}$。对所有 $m$，均有
$$
I_\kappa(W)=\operatorname{span}_F\mathcal T_\kappa(W),
\qquad 0\notin\mathcal T_\kappa(W).
\tag{18.7}
$$
第一式由基外积张成性得到，第二式由 (18.4) 得到。

Grassmann 点是 $\mathcal A(W)$ 的射影化：$\operatorname{Gr}_F(2,W)(F)=\mathcal A(W)/F^\times$，而不是 $\mathcal A(W)$ 本身。$\kappa_W=\kappa|_{\Lambda^2W}$ 的射影中心是 $\mathbf P_F(\ker\kappa_W)$；定理 18.2 保证它不含实际 Grassmann $F$-点。因此 $\mathbf P(\kappa_W)$ 在全部实际 Grassmann 点上有定义，其像经 $[h+F]\mapsto K_h$ 正是 $\operatorname{Src}(W)$。$\mathbf P_F(I_\kappa(W))(F)$ 则只给线性张成中的候选来源。扩到代数闭包后的 Grassmann 点、中心和投影须另取基变换；几何像或其闭包不能替代这里的实际 $F$-点像。

这些外积与射影术语直接使用 Ghorpade–Patil–Pillai，[*Decomposable Subspaces, Linear Sections of Grassmann Varieties, and Higher Weights of Grassmann Codes*，arXiv:0710.5161v1](https://arxiv.org/abs/0710.5161v1)，§§1–2 的定义，以及 Havlicek 前引文 §2 的 Plücker 嵌入。它们是以下乘法恢复判据的经典输入。

**定理 18.4（任意固定窗口的交叠、秩与完整实际纤维）。** 对任意 $W\le L$ 及 $h\in L\setminus F$，记 $r=h+F$、$K=K_h$，并置
$$
C_h(W)=W\cap hW.
$$
则 $C_h(W)$ 是 $K$-向量空间，而且下列条件等价：
$$
\begin{aligned}
&K\in\operatorname{Src}(W);\\
&r\in\mathcal T_\kappa(W);\\
&C_h(W)\ne0;\\
&\dim_K C_h(W)\ge1;\\
&\operatorname{rank}_F\Phi_h<2m,
\quad\Phi_h:W\oplus W\to L,\quad(x,y)\mapsto x+hy.
\end{aligned}
\tag{18.8}
$$
更准确地，置 $\rho_h=\operatorname{rank}_F\Phi_h$，有
$$
\dim_F C_h(W)=2m-\rho_h,
\qquad
\dim_K C_h(W)=m-\rho_h/2.
\tag{18.9}
$$
取 $L$ 的任意 $F$-基，以列满秩矩阵 $B\in F^{n\times m}$ 表示 $W$ 的包含映射，以 $M_h\in F^{n\times n}$ 表示原域中乘以 $h$，则
$$
\rho_h=\operatorname{rank}_F[B\ \ M_hB].
\tag{18.10}
$$
特别地，$m>n/2$ 时所有实际二次来源均可见，且 $I_\kappa(W)=L/F$、$\mathcal T_\kappa(W)=(L/F)\setminus\{0\}$。一般情况下，非零虚假记录恰为
$$
\{h+F\in I_\kappa(W)\setminus\{0\}:
\operatorname{rank}_F[B\ \ M_hB]=2m\}.
\tag{18.11}
$$

完整实际提升纤维还有如下参数化：$C=C_h(W)$ 时，存在自然双射
$$
\mathbf P_K(C)\ \longrightarrow
\{\xi\in\mathcal A(W):\kappa(\xi)=r\},
\qquad
Kv\longmapsto \xi_v:=v\wedge\frac{hv}{v^2}.
\tag{18.12}
$$
这里 $\mathbf P_K(0)=\varnothing$；右侧保留实际外积向量而非只保留射影类。每个 $Kv$ 同时给出窗口内同一来源的实际支撑平面。

证明。因为 $h^2\in F^\times$，有
$$
C_h(W)=\{v\in W:hv\in W\}.
\tag{18.13}
$$
若 $v\in W\cap hW$，写 $v=hy$、$y\in W$，则 $hv=h^2y\in W$；反向由 $v=h((h^2)^{-1}hv)$ 得到。式 (18.13) 也说明 $hC_h(W)\subseteq C_h(W)$，故 $C_h(W)$ 对 $F+Fh=K$ 稳定。这正是 §17 的固定 $h$ 交叠条件，其 $K$-线性结构无需另加假设。

若 $C_h(W)$ 含非零 $v$，则 $vK\subseteq W$，且 $v,hv/v^2$ 独立，乘积恰为 $h$。所以同一输入对同时见证来源 $K$ 和指定记录 $r$。反过来，若 $u,v\in W$ 独立且 $uv+F=h+F$，写 $uv=h+\alpha$，$\alpha\in F$，便有
$$
hv=(uv+\alpha)v=v^2u+\alpha v\in W.
$$
因此 $0\ne v\in C_h(W)$。若从 $vK\subseteq W$ 出发，则也直接得到 $v\in C_h(W)$，支付前三项等价与来源标签的绑定。

$\Phi_h$ 的像为 $W+hW$。其核由 $x=hy$ 描述，映射 $(hy,y)\mapsto y$ 将该核与 $C_h(W)$ 作 $F$-线性同构。秩—零度给 (18.9) 的第一式；$[K:F]=2$ 给第二式。矩阵表示就是 (18.10)。于是 (18.8)、(18.11) 均得证。若 $2m>n$，秩至多为 $n<2m$，每个非零 $r$ 都实际可得；这也与 §17 的半维交叠边界相接。这里给出的是固定来源的一次线性秩判据，不需要枚举输入对或先解分解存在性的定义。

对 (18.12)，若 $v'=kv$、$k=\alpha+\beta h\in K^\times$，则双线性及 $h^2\in F$ 给
$$
v'\wedge hv'=k^2(v\wedge hv),\qquad (v')^2=k^2v^2,
$$
故 $\xi_{v'}=\xi_v$；其支撑平面恰为 $Kv$，所以不同 $K$-线给不同外积。反之，任一实际提升写成 $\xi=u\wedge v$。上面的计算说明 $v\in C_h(W)$，而 $uv=h+\alpha$ 给
$$
u=\frac{hv+\alpha v}{v^2},\qquad
u\wedge v=\frac{hv}{v^2}\wedge v
=v\wedge\frac{hv}{v^2}.
$$
最后一个等号使用特征二。因而该提升等于 $\xi_v$，双射成立。若换代表 $h'=\alpha+\beta h$、$\beta\ne0$，(18.13) 给 $C_{h'}(W)=C_h(W)$；所以判据也不依赖同一候选来源的代表。$\square$

**定理 18.5（完整 Plücker 条件与整条乘法纤维的等价）。** 固定任意 $m$ 维窗口 $W$、一组 $F$-基 $w_1,\ldots,w_m$，并以 $L/F$ 的一组基表示记录。令 $T_W$ 的列为 $w_iw_j+F$（$i<j$）的坐标。对非零实际 $r=h+F$，下列条件均与 (18.8) 等价：
$$
\begin{gathered}
\exists (p_{ij})\in F^{\binom m2},\quad T_Wp=r,\\
p_{ij}p_{kl}+p_{ik}p_{jl}+p_{il}p_{jk}=0
\quad\text{对全部 }1\le i<j<k<l\le m.
\end{gathered}
\tag{18.14}
$$
这里 $r$ 在矩阵等式中表示其坐标列，所有未知量必须属于 $F$。若 $r\in I_\kappa(W)$，任选一个解 $p_0$，则 (18.14) 恰等价于
$$
\exists k\in\ker T_W,\quad
p_0+k\text{ 满足全部 Plücker 关系}.
\tag{18.15}
$$
一个满足关系的非零实际提升足以证明存在；一个不满足关系的任意提升不能否定存在。$r=0$ 的纤维没有非零实际分解点，其来源为空。

证明。这里使用经典二维 Plücker 判据作为中间步骤：非零 $p$ 是某个 $u\wedge v$ 的坐标，当且仅当它满足 (18.14) 的所有二次关系。为明确其任意域实际点含义，将 $p_{ji}=p_{ij}$、$p_{ii}=0$；取 $p_{ij}\ne0$，在该坐标片上可直接取
$$
x_k=p_{ik},\qquad y_k=p_{jk}/p_{ij}.
$$
Plücker 关系给 $x_ky_l+x_ly_k=p_{kl}$，包括指标重复的情形。因此 $x,y\in F^m$ 独立，$p=x\wedge y$；没有从代数闭包取解。反向将 $p_{ij}=x_iy_j+x_jy_i$ 代入即得这些关系。这是标准 Plücker 坐标计算；四维形式正是 Havlicek 前引文 §2 的 Klein 方程，分解与支撑平面的经典关系见 Ghorpade–Patil–Pillai 前引文 §2，Lemma 1、Corollary 2。

由于 $T_W$ 正是原 $\kappa_W$ 的矩阵，$T_Wp=r\ne0$ 已强制 $p\ne0$。故上述中间判据把 (18.14) 与实际乘法纤维中的分解点等同，再由定理 18.4 与固定 $h$ 的秩条件等同。所有线性解恰为 $p_0+\ker T_W$，得到 (18.15)。对于 $r=0$，若有非零实际分解点，就会违反独立输入的 $uv\notin F$。

一个确有核的边界说明为何必须保留整条纤维。取完整四次域 $L_0/F$，基为 $1,a,b,ab$，$a^2=s$、$b^2=t$，并取 $W=L_0$。同一记录 $a+F$ 有分解提升 $1\wedge a$，也有提升
$$
1\wedge a+1\wedge ab+a\wedge b.
\tag{18.16}
$$
后者的像仍为 $a+F$，因为两个 $ab$ 相消；其 Klein Pfaffian 为 $1$，故不可分解。因而只检查这一坏提升会否定一个已由前一实际输入对见证的来源。此处仅将经典四维 Klein 方程用于原乘法纤维，不把不可分解提升本身叫作虚假输出。$\square$

**定理 18.6（原乘法记录首次失真的两个最小量）。** 对同一实际交替乘法 (18.1)，以下边界成立：任意 $n$ 下，$m\le3$ 的所有窗口均无非零虚假记录；$n\le4$ 时，所有窗口均无非零虚假记录。存在 $m=4$、$n=8$ 的窗口有非零虚假记录。因此首次可能失真的最小窗口维数与最小整体次数分别为
$$
m_{\min}=4,\qquad n_{\min}=8.
\tag{18.17}
$$
在上述无失真范围内，线性像足以恢复来源：$\operatorname{Src}(W)=\{F(h):0\ne h+F\in I_\kappa(W)\}$。两下界由同一个实例同时达到。具体地，取代数独立的 $s,t,z$，令
$$
F=\mathbf F_2(s,t,z),\quad
L=F(a,b,c),\quad a^2=s,\quad b^2=t,\quad c^2=z,
\qquad W=F1+Fa+Fb+Fc.
\tag{18.18}
$$
则 $[L:F]=8$，$\kappa_W$ 单射，而
$$
r=a+bc+F
=\kappa(1\wedge a+b\wedge c)
\in I_\kappa(W)\setminus\mathcal T_\kappa(W).
\tag{18.19}
$$
两项分别来自窗口内的实际输入对 $(1,a)$ 与 $(b,c)$，其来源分别为 $F(a)$ 与 $F(b/c)=F(bc)$。

证明。经典低维外积事实给 $m\le3$ 时每个非零二外积均可分解；三维情形是 Ghorpade–Patil–Pillai 前引文 §2 Corollary 2 的 $\ell=m-1$ 情形，二维情形直接由基外积得到。任一非零 $r\in I_\kappa(W)$ 有非零提升，因而有实际独立输入对。事实上，此时 $\kappa_W$ 还必单射，否则非零核元的分解会违反 (18.4)。$m\le1$ 按定义为空集边界。

若 $n\le4$，除上述 $m\le3$ 情形，只须考虑 $n=m=4$，这时 $W=L$，每个非零 $h+F$ 都由 $(1,h)$ 产生。特别是完整四次域中的非分解外积，在经过原 $\kappa$ 后不能据此称为虚假记录。有限指数一扩张的次数为二幂，这里直接复用 [Stacks，09HI，Lemma 9.14.5](https://stacks.math.columbia.edu/tag/09HI) 的逐次二次塔；所以排除 $n\le4$ 就排除了全部 $n<8$。

对 (18.18)，可取代数独立的 $a,b,c$，令 $s=a^2,t=b^2,z=c^2$。按三个指数的奇偶分组，
$$
1,a,b,c,ab,ac,bc,abc
\tag{18.20}
$$
是 $L/F$ 的基：对有理函数先同乘分母使分母成为平方，再按奇偶分组给出张成；任何线性关系清去 $F$ 中的分母后，不同奇偶类的多项式项不能相消，给出独立性。这与 §13 命题 13.17 的双变量实例使用同一基论证。

在 $W$ 的有序基 $(1,a,b,c)$ 下，六个基外积的像依次为
$$
a+F,\ b+F,\ c+F,\ ab+F,\ ac+F,\ bc+F,
$$
由 (18.20) 独立。因此 $r$ 的提升唯一，正是 $1\wedge a+b\wedge c$。该提升在坐标 $p_{01}=p_{23}=1$、其余为零处的 Klein Pfaffian
$$
\operatorname{Pf}(p)=p_{01}p_{23}+p_{02}p_{13}+p_{03}p_{12}
\tag{18.21}
$$
为 $1$。由定理 18.5 的经典分解条件，它不是实际分解点，且不存在另一提升可以补救。特征二中 $\xi\wedge\xi=0$ 恒成立，不能替代 (18.21)。这支付的是原乘法商输出的失真，而非忠实外积记录器的另一问题。$\square$

**定理 18.7（同一 $L$、同一 $\kappa$、同像而不同的完整来源集）。** 在 (18.18) 的同一实际 $L/F$ 内，另取
$$
W'=F1+F(a+bc)+Fb+Fc.
$$
则
$$
I_\kappa(W)=I_\kappa(W')
=F(a+F)+F(b+F)+F(c+F)+F(ab+F)+F(ac+F)+F(bc+F),
\tag{18.22}
$$
但 $\operatorname{Src}(W)\ne\operatorname{Src}(W')$，而且两来源集互不包含。更准确地，对 $x=(A,B,C,D,E,G)\in F^6$，置
$$
H(x)=Aa+Bb+Cc+Dab+Eac+Gbc,
\qquad Q(x)=AG+BE+CD.
$$
两个完整来源集分别为
$$
\begin{aligned}
\operatorname{Src}(W)
&=\{F(H(x)):0\ne x\in F^6,\ Q(x)=0\},\\
\operatorname{Src}(W')
&=\{F(H(x)):0\ne x\in F^6,
\ Q(x)+A^2+tD^2+zE^2=0\}.
\end{aligned}
\tag{18.23}
$$
特别地，
$$
\begin{aligned}
&F(a+bc)\in\operatorname{Src}(W')\setminus\operatorname{Src}(W),\\
&F(a)\in\operatorname{Src}(W)\setminus\operatorname{Src}(W').
\end{aligned}
\tag{18.24}
$$
所以线性像本身不能恢复完整可见来源，即使这两个四维窗口上的 $\kappa$ 都单射。

证明。$1,a+bc,b,c$ 由 (18.20) 独立。在此有序基下，$\kappa_{W'}$ 的六个基像为
$$
a+bc+F,\ b+F,\ c+F,\ ab+tc+F,\ ac+zb+F,\ bc+F.
\tag{18.25}
$$
它们张成 (18.22)：用最后一项从第一项取回 $a+F$，用 $c+F,b+F$ 分别从第四、第五项取回 $ab+F,ac+F$。这六个向量独立，故 $\kappa_{W'}$ 也单射。

在 $W$ 中，$H(x)+F$ 的唯一提升坐标就是 $(A,B,C,D,E,G)$，其 Pfaffian 为 $Q(x)$。在 $W'$ 中，同一输出的唯一提升坐标是
$$
(p'_{01},p'_{02},p'_{03},p'_{12},p'_{13},p'_{23})
=(A,B+zE,C+tD,D,E,G+A).
$$
其 Pfaffian 为
$$
A(G+A)+(B+zE)E+(C+tD)D
=Q(x)+A^2+tD^2+zE^2.
$$
因此 (18.23) 由同一乘法纤维的分解条件与定理 18.2 的唯一来源标签得到；它描述全部实际 $F$-点，而非只展示两个选定来源。候选来源在共同像中的参数正是 $F^6\setminus\{0\}$ 模非零标量，不存在另外的标签歧义。

取 $x=(1,0,0,0,0,1)$，两方程的值分别为 $1$ 与 $0$，得到第一项；在 $W'$ 中，实际输入对就是 $(1,a+bc)$。取 $x=(1,0,0,0,0,0)$，两方程的值分别为 $0$ 与 $1$，得到第二项；在 $W$ 中输入对为 $(1,a)$。

第一项还可直接用线性交叠核对。令 $h=a+bc$，对任意 $x_0+x_1a+x_2b+x_3c\in W$，乘以 $h$ 后在 $bc,abc,ab,ac$ 四个窗外基方向的系数依次是 $x_0,x_1,x_2,x_3$。故 $C_h(W)=0$。在 $W'$ 中，用基 $1,h,b,c$ 写向量，乘以 $h$ 后，$ab,ac$ 两个窗外方向的系数分别是 $b,c$ 的原系数；故
$$
C_h(W')=F1+Fh=K_h,
\qquad \rho_h(W)=8,\quad \rho_h(W')=6.
$$
这使同源性、实际输入对和秩判据在同一 $h$ 上一致。$\square$

**定理 18.8（四维的一个关系与原三维入口）。** 对任意四维窗口，实际来源的充分且必要恢复可由整条 $\kappa_W$ 仿射核纤维上的一个 Pfaffian 方程 (18.21) 完成，或等价地由每个候选 $h$ 的单个秩判定 (18.10) 完成。在 (18.18) 的单射窗口中，省去该 Pfaffian 条件就会纳入 (18.19) 的虚假记录。这里“一个关系”只表示四维 Plücker 判据有一个二次方程；不声称它是所有编码中的唯一最小信息，也不把高维的全部 Plücker 关系缩成一个方程。

若另有 §13 定义 13.1 的全部 P+K 前件，且 $\operatorname{char}F=2$，则定理 13.9、13.11 给出同一个完整四次域 $(L,\pi)$、$V=\ker\pi$、$\dim_FV=3$。在这一原纯部窗口上，
$$
I_\kappa(V)=L/F,\qquad
\mathcal T_\kappa(V)=(L/F)\setminus\{0\},\qquad
\operatorname{Src}(V)=\{K_h:h\in L\setminus F\}.
\tag{18.26}
$$
并且原响应 $D(u,v)=uv-\pi(uv)$ 满足 $\kappa(u\wedge v)=D(u,v)+F$。八次反例不满足该入口所强制的整体次数，不能据此改变其三维结论。

证明。四维只有一个四指标组，定理 18.5 因而恰给 (18.21)；核存在时仍须使用 (18.15) 的存在量词。必要性的具体见证已由定理 18.6 给出；任意窗口的等价秩判定已由定理 18.4 给出。对于原纯部，$m=3>4/2$，故同一定理直接给 (18.26)，也可用定理 18.6 中三维 $\kappa_V$ 的单射性及两边维数同为三得到。$D$ 与 $\kappa$ 的关系则直接来自原公式。这里保留 P+K、实际四次域和指定投影；未从高次域的窗口记录推出新的 P+K、Born 规则或物理维数。$\square$

**定义 18.9（真实面积相加的数学释义）。** 一对窗口内的独立方向给一块可分解面积 $u\wedge v$，实际记录是同一域乘法给出的 $uv+F$。这个非零输出已经唯一指定候选二次域 $F(uv)=F(u/v)$。将许多实际记录相加只保留线性张成；相加后的候选域能否仍由窗口中的一对方向产生，须有该记录纤维中的实际分解点。一个这样的点就足够；一个坏提升不够否定。四维时，保留 Pfaffian 与整条纤维恰好保留这一要求；任意维时，可用固定 $h$ 的交叠乘法秩判据直接恢复。八次实例中，两块真实面积的和具有唯一的不可分解提升，因此输出不再有单对实际方向；另一个窗口虽保留完全相同的线性像，却有不同的真实面积集合和实际来源。

本节使用的经典输入是前引 Havlicek v1 的完整四次域 case (B)、$\kappa$ 与 Klein 方程，Ghorpade–Patil–Pillai v1 的外积及分解事实，和 Stacks 09HF、09HI 的纯不可分二次塔；比值与交叠复用本卷 §17。相对于这些输入，本节推导的是原乘法输出的来源绑定、任意固定窗口的秩与实际纤维连接、最小 $(m,n)=(4,8)$，以及 (18.22)–(18.24) 在同一实际域和同一乘法下的两个完整来源集。经典几何本身不在此取得新的名称或首次性主张。

## 追加锚（本行以下为增补区）

## 19　完整实际来源与窗口的标量恢复

**定义 19.1（带标签来源所要恢复的对象）。** 固定定义 18.1 的同一个实际域扩张 $L/F$：$\operatorname{char}F=2$、$n=[L:F]<\infty$、$L^2\subseteq F$，仍用原映射 $\kappa(u\wedge v)=uv+F$。对 $W\le L$，记
$$
[W]_{L^\times}=\{xW:x\in L^\times\}.
\tag{19.1}
$$
这里的恢复问题是：在 $m=\dim_FW$ 已知时，实际子域的集合 $\operatorname{Src}(W)$ 是否唯一决定 (19.1)。来源标签是原 $L$ 内的二次子域本身；观察不包含支撑平面、来源的重数或交空间的维数。

令 $q:L\to L/F$ 为原商映射。对任意实际二次子域集合 $\mathcal S$，置
$$
\begin{aligned}
\Sigma(\mathcal S)
 &=\{h+F:h\in L\setminus F,\ F(h)\in\mathcal S\},\\
E(\mathcal S)&=F\bigl(\bigcup_{K\in\mathcal S}K\bigr)\subseteq L,
\qquad E(\varnothing)=F.
\end{aligned}
\tag{19.2}
$$
第一项是实际商向量的集合，第二项是由这些实际子域生成的子域。对非零窗口另记实际比值集
$$
R(W)=\{u/v:u\in W,\ 0\ne v\in W\}\subseteq L.
\tag{19.3}
$$

**定理 19.2（标量不变性与来源所确定的生成域）。** 对任意 $W\le L$ 和 $x\in L^\times$，有
$$
\operatorname{Src}(xW)=\operatorname{Src}(W),\qquad
\Sigma(\operatorname{Src}(W))=\mathcal T_\kappa(W),\qquad
I_\kappa(W)=\operatorname{span}_F\Sigma(\operatorname{Src}(W)).
\tag{19.4}
$$
若 $W\ne0$，则对每个 $w\in W\setminus\{0\}$，
$$
R(W)=F\ \cup\!\bigcup_{K\in\operatorname{Src}(W)}K,
\qquad
E(\operatorname{Src}(W))=F(w^{-1}W).
\tag{19.5}
$$
因此右侧的实际生成域与归一化所选的 $w$ 无关。$\operatorname{Src}(W)=\varnothing$ 当且仅当 $\dim_FW\le1$；在这个空集情形仍须保留已知的维数。

证明。对每个实际 $K$，乘以 $x$ 将 $vK\subseteq W$ 与 $(xv)K\subseteq xW$ 双向对应，故保留同一个标签 $K$。定理 18.2、18.4 说明：标签 $F(h)$ 可见，当且仅当指定记录 $h+F$ 由 $W$ 内的一对独立输入实际取得。这给 (19.4) 的第二式；第三式是 (18.7)，没有把线性张成当作完整来源。

若 $h=u/v\notin F$，则 $u,v$ 独立，且 $vF(h)=Fv+Fu\subseteq W$，所以 $h$ 属于 (19.5) 第一式的右侧。若 $h\in K\in\operatorname{Src}(W)$，取 $vK\subseteq W$，便有 $h=(vh)/v\in R(W)$。任一非零 $w\in W$ 又给出 $\alpha=(\alpha w)/w\in R(W)$，其中 $\alpha\in F$。于是第一式成立，包括来源为空的非零窗口。

令 $U=w^{-1}W$，则 $1\in U$。任一 $K\in\operatorname{Src}(U)$ 有 $0\ne v\in U$ 且 $vK\subseteq U$，故 $K\subseteq F(U)$。反过来，对每个 $u\in U\setminus F$，平面 $F+Fu$ 已在 $U$ 内，因而 $F(u)\in\operatorname{Src}(U)$。所以 $E(\operatorname{Src}(U))=F(U)$；再用标量不变性即得第二式。最后，维数至少二时任选两个独立向量就有来源；维数至多一时不能容纳一个二次域的标量副本。$\square$

**定理 19.3（八次生成情形中的四维窗口重建）。** 设 $\dim_FW=4$，且 $E=E(\operatorname{Src}(W))$ 满足 $[E:F]=8$。完全从带标签来源定义
$$
\mathfrak B(\mathcal S)=
\left\{q^{-1}(D):
\begin{array}{l}
D\le L/F,\quad\dim_FD=3,\\
D\setminus\{0\}\subseteq\Sigma(\mathcal S),\\
q^{-1}(D)\text{ 不是 }L\text{ 的子域}
\end{array}\right\}.
\tag{19.6}
$$
其中“子域”使用已固定的实际 $L$ 的乘法。则
$$
\mathfrak B(\operatorname{Src}(W))
=\{uW:0\ne u\in W\}
=\{X\in[W]_{L^\times}:1\in X\}.
\tag{19.7}
$$
这给出整个标量轨道中所有含 $1$ 的代表；(19.6) 没有增加关于 $W$ 的交维数或支撑信息。

证明。先支付 $\kappa_W$ 在这个范围内的单射性。选 $0\ne w\in W$，写
$$
U=w^{-1}W=F1+Fa+Fb+Fc.
$$
由定理 19.2，$E=F(a,b,c)$。$1,a,b$ 独立，所以 $[F(a,b):F]=4$：先有 $[F(a):F]=2$，再由 $b\notin F(a)$、$b^2\in F$ 得第二个二次扩张。$[E:F]=8$ 则迫使 $c\notin F(a,b)$。逐次二次塔给出 $E$ 的基
$$
1,a,b,ab,c,ac,bc,abc.
\tag{19.8}
$$
因此 $\kappa_U$ 的六个基像 $a+F,b+F,c+F,ab+F,ac+F,bc+F$ 独立。乘以 $w$ 对外平方诱导的同构满足
$$
\kappa_W(wu\wedge wv)=w^2\kappa_U(u\wedge v),
\qquad w^2\in F^\times,
$$
故 $\kappa_W:\Lambda_F^2W\to I_\kappa(W)$ 也是同构。

现在取 (19.6) 中的 $D$。由 (19.4)，$D\subseteq I_\kappa(W)$。令 $A=\kappa_W^{-1}(D)$，则 $\dim_FA=3$。对每个 $0\ne\xi\in A$，其像属于 $\Sigma(\operatorname{Src}(W))=\mathcal T_\kappa(W)$，故有实际分解向量 $\eta\in\Lambda_F^2W$ 满足 $\kappa_W(\eta)=\kappa_W(\xi)$。单射性给 $\xi=\eta$。于是 $A$ 的每个非零实际 $F$ 向量都可分解。

在这一步直接使用 Ghorpade–Patil–Pillai，[*Decomposable Subspaces, Linear Sections of Grassmann Varieties, and Higher Weights of Grassmann Codes*，arXiv:0710.5161v1](https://arxiv.org/abs/0710.5161v1)，§2 Theorem 6 及其前面的两类 close subspace 定义。该节的底域是任意域；代入其参数 $\ell=2$、$\dim_FV=4$、$r=3$、$V=W$，精确给出且只给出
$$
A=u\wedge W\quad(0\ne u\in W),
\qquad\text{或}\qquad
A=\Lambda_F^2V\quad(V\le W,\ \dim_FV=3).
\tag{19.9}
$$
这是对原 $F$ 上全分解线性子空间的经典分类，不要求有限域，也不以代数闭包上的几何点替代实际点。

第一种情形有 $q(uW)=D$，且 $u^2\in F^\times$ 使 $F\subseteq uW$。由于 $\dim_FuW=4$，遂有 $q^{-1}(D)=uW$。这个四维空间不能是子域 $H$：若是，则 $W=u^{-1}H$，由 (19.5) 得 $E(\operatorname{Src}(W))=H$，与 $[E:F]=8$ 矛盾。

第二种情形选 $0\ne z\in V$，写 $z^{-1}V=F1+Fp+Ft$。其三个基向量独立，故与前面的二次塔论证相同，$H=F(p,t)$ 是实际四次子域，基为 $1,p,t,pt$。又因 $z^2\in F^\times$，
$$
\kappa(\Lambda_F^2V)
=\operatorname{span}_F\{p+F,t+F,pt+F\}=H/F.
\tag{19.10}
$$
故 $q^{-1}(D)=H$ 是子域。这一类恰被 (19.6) 的最后条件排除。

反过来，每个 $u\wedge W$ 都是三维全分解子空间；其非零向量经 $\kappa_W$ 给出实际来源，故它的像满足 (19.6) 的前两项，而上面的八次生成条件保证其提升不是子域。因此所有 $uW$ 都在左侧，第一处集合等号成立。最后 $1\in uW$，因为 $u^{-1}=u/u^2\in W$。若 $X=xW$ 且 $1\in X$，则 $v=x^{-1}\in W\setminus\{0\}$，从而
$$
xW=v^{-1}W=(v^2)^{-1}vW=vW.
$$
非零 $F$ 标量不改变 $F$ 子空间，故第二处集合等号也成立。$\square$

**文献应用 19.4（全部四维及以下窗口的准确恢复）。** 对固定的任意有限指数一实际扩张 $L/F$，若 $W,W'\le L$ 且
$$
\dim_FW=\dim_FW'=m\le4,
$$
则
$$
\operatorname{Src}(W)=\operatorname{Src}(W')
\quad\Longleftrightarrow\quad
\exists x\in L^\times\;W'=xW.
\tag{19.11}
$$
这包括 $m=0,1$、$n=1$ 及所有允许的低次退化。维数超过 $n$ 的窗口不存在。此处相似结论归于 Zemková，[*Vishik equivalence and similarity of quasilinear p-forms and totally singular quadratic forms*，arXiv:2309.13346v2](https://arxiv.org/html/2309.13346v2)，Definition 3.2、Theorem 4.6 与 Corollary 3.5(ii)，经下面的窗口对应使用；它是定理 19.5 最小性所需的文献应用，不作为新的相似定理。

证明与对象对应。反向已由定理 19.2 给出。$m=0$ 时两个窗口都是 $0$；$m=1$ 时写 $W=Fw$、$W'=Fw'$，便有 $W'=(w'/w)W$。这两类来源都为空，但各自的标量轨道唯一。以下设 $m\ge2$。

在包含原 $L$ 的代数闭包内取 $\Omega=F^{1/2}$，则 $L\subseteq\Omega$ 且 $\Omega^2=F$。若 $w_1,\ldots,w_m$ 是 $W$ 的 $F$-基，在 $\Omega$ 上定义全奇异二次型
$$
\varphi_W=\langle w_1,\ldots,w_m\rangle,
\qquad D_\Omega(\varphi_W)=W.
\tag{19.12}
$$
这里 $D_\Omega$ 是该文的值集。$F$-线性独立性保证 $\varphi_W$ 各向异性；该文 Lemma 2.2 保证其等距类只取决于 $W$，并给出
$$
\varphi_{W'}\simeq c\varphi_W
\quad\Longleftrightarrow\quad W'=cW
\qquad(c\in\Omega^\times).
\tag{19.12a}
$$
若右侧成立，任取 $0\ne w\in W$ 就有 $c=(cw)/w\in L^\times$。所以形式在 $\Omega$ 上的相似，双向恰对应原 $L^\times$ 标量轨道；没有把目标改成较大域中的轨道或抽象同构。按该文 §2.3 的范数域定义与 (19.5)，还得到
$$
N_\Omega(\varphi_W)=F(R(W))
=E(\operatorname{Src}(W)).
\tag{19.12b}
$$

对每个 $h\in\Omega\setminus F$，令 $d_h(W)=\dim_F(W\cap hW)$。因 $h^2\in F$，交空间在 $F(h)$ 下封闭，故 $d_h(W)$ 为偶数。又有 $\Omega(\sqrt h)^2=F(h)$ 及 $F(h)W=W+hW$，因此该文所用缺陷满足
$$
\begin{aligned}
\mathfrak i_{\mathrm d}\bigl((\varphi_W)_{\Omega(\sqrt h)}\bigr)
&=m-\dim_{F(h)}(W+hW)\\
&=\tfrac12 d_h(W).
\end{aligned}
\tag{19.12c}
$$
这里用的是全奇异型的各向异性部分维数等于值集在平方子域上的维数，即该文 Lemma 2.2。若 $h\in\Omega\setminus L$，非零交点会给 $h=u/v\in L$，故此时缺陷为零。若 $h\in F$，则 $\sqrt h\in\Omega$，扩张平凡，缺陷也为零。对 $h\in L\setminus F$，定理 18.4 给出准确的标签对应
$$
F(h)\in\operatorname{Src}(W)
\quad\Longleftrightarrow\quad
\mathfrak i_{\mathrm d}\bigl((\varphi_W)_{\Omega(\sqrt h)}\bigr)>0.
\tag{19.12d}
$$
来源只给出缺陷是否为正；Zemková 的 Definition 3.2 要求同维数并且对每个 $h\in\Omega$ 缺陷数本身相同，称为弱 Vishik 等价。两者在任意维数下不能直接等同。

现在设两窗口的来源相同，记共同的实际生成域为 $E$。当 $m=2,3$ 时，非零的偶数 $d_h(W)\le m$ 只能为二。因此 (19.12c)–(19.12d) 已给两个形式在每个 $\Omega(\sqrt h)$ 上相同的缺陷。

当 $m=4$ 时，归一化为 $U=w^{-1}W=F1+Fa+Fb+Fc$。由 $1,a,b$ 独立，$F(a,b)$ 是四次域；添入平方在 $F$ 内的 $c$ 后，$E=F(U)$ 的次数只能为四或八。若 $[E:F]=4$，则 $U=E$，故 $W=wE$；于是 $d_h(W)=4$ 恰在 $h\in E\setminus F$ 时成立，其余 $h\notin F$ 的交维数为零。两窗口因而仍有相同的缺陷。若 $[E:F]=8$，则 $d_h(W)=4$ 不可能：它会使 $hW=W$，归一化后的 $U$ 便是含 $1$ 的二维 $F(h)$-空间，写成 $F(h)+F(h)t$；由于 $t^2\in F$，这个空间就是四次域 $F(h,t)$，与 $F(U)=E$ 八次矛盾。因此八次生成时非零的 $d_h$ 仍只能为二。相同来源再次给出全部相同缺陷。这同时检查了 $h$ 在原 $L$ 之外的所有二次测试，故两形式确实满足 Definition 3.2 的全部量词。

最后逐项核对相似定理的前件。$m=2,3$ 的归一化窗口分别生成二次、四次域：后者由 $U=F1+Fa+Fb$ 及 $b\notin F(a)$ 得到。结合 (19.12b)，这些形式的范数次数分别是 $2^{m-1}$；$m=4$、$[E:F]=8$ 时也如此。它们因此满足该文 Definition 2.11 的 minimal 条件，直接由 Theorem 4.6 得到相似。余下 $m=4$、$[E:F]=4$ 时，归一化的值空间是 $E=F(a,b)$，对应形式正是二重 quasi-Pfister 型 $\langle1,a,b,ab\rangle$，由 Corollary 3.5(ii) 得到相似，再撤销归一化。用 (19.12a) 回到原 $L$ 即得 (19.11)。定理 19.3 另给出了由实际标签直接构造所有含 $1$ 的代表的公式 (19.6)–(19.7)；该更具体的重建输出与已有相似结论相容，不使相似结论成为新数学。$\square$

**定理 19.5（完整来源丢窗口的首次失效）。** 在 (18.18) 的同一个实际扩张
$$
F=\mathbf F_2(s,t,z),\qquad
L=F(a,b,c),\qquad a^2=s,\ b^2=t,\ c^2=z,
$$
其中 $s,t,z$ 代数独立，取两个实际窗口
$$
W_5=\operatorname{span}_F\{1,a,b,c,ab\},\qquad
W'_5=\operatorname{span}_F\{1,a,b,c,ac\}.
\tag{19.13}
$$
它们满足 $\dim_FW_5=\dim_FW'_5=5$、$[L:F]=8$，并且
$$
\operatorname{Src}(W_5)=\operatorname{Src}(W'_5)
=\{K\subseteq L:[K:F]=2\},
\qquad W'_5\ne xW_5\quad\text{对所有 }x\in L^\times.
\tag{19.14}
$$
因此，在维数已知的原恢复问题中，首次可能失效的最小窗口维数和最小整体次数分别是
$$
m_{\min}=5,\qquad n_{\min}=8,
\tag{19.15}
$$
并由同一对窗口同时达到。

证明。(18.20) 已给出这个实际 $L/F$ 的八个基单项式，故 (19.13) 中各五个向量确实独立。对每个实际 $h\in L\setminus F$，$5+5>8$ 保证 $W_5\cap hW_5\ne0$，对 $W'_5$ 亦然。由定理 18.4，二者都看见该同一个实际标签 $F(h)$。这支付全部二次子域的量词，而非仅比较两个来源子集或线性像。

还须排除所有实际标量。令 $A=F(a,b)=\operatorname{span}_F\{1,a,b,ab\}$，则 $A\subseteq W_5$。假设 $xW_5=W'_5$，其中 $x\ne0$。必有 $xA\subseteq W'_5$，所以 $x,ax,bx,abx$ 都在 $W'_5$ 内。先写
$$
x=\alpha+\beta a+\gamma b+\delta c+\varepsilon ac,
\qquad\alpha,\beta,\gamma,\delta,\varepsilon\in F.
$$
由
$$
ax=\beta s+\alpha a+\gamma ab+\delta ac+\varepsilon s c
$$
及八个基单项式的独立性，$ax\in W'_5$ 迫使 $\gamma=0$。再由
$$
bx=\alpha b+\beta ab+\delta bc+\varepsilon abc
$$
与 $bx\in W'_5$ 得 $\beta=\delta=\varepsilon=0$。于是 $x=\alpha$，而 $abx=\alpha ab\in W'_5$ 又迫使 $\alpha=0$，与 $x\ne0$ 矛盾。这一障碍是在同一个实际四次子域 $A$ 上得到的；没有改用抽象同构或半线性变换。

这两个窗口的同来源也不等于弱 Vishik 等价。例如同一个实际 $b$ 给出
$$
W_5\cap bW_5=A,\qquad
W'_5\cap bW'_5=F1+Fb.
\tag{19.14a}
$$
第一式由 $W_5=A+Fc$、$bA=A$ 及 $c,bc$ 模去 $A$ 后独立得到；第二式由 $W'_5$ 的基与 $bW'_5=\operatorname{span}_F\{b,ab,t,bc,abc\}$ 逐项比较得到。因此 (19.12c) 在 $\Omega(\sqrt b)$ 上给出的缺陷分别为二与一。Zemková 前引文 Corollary 4.21 回答的 Question Q 采用 Definition 2.14，要求在所有域扩张上缺陷相同，即 full Vishik 等价；该文 Remark 4.19 也明确区分这一条件与弱等价。本例连弱等价都不满足，所以不受 Corollary 4.21 的五维相似结论覆盖。

文献应用 19.4 排除了任意整体次数下全部 $m\le4$ 的反例。另一方面，有限指数一扩张可逐次添入平方在 $F$ 内的元素；每个非平凡步骤的次数都是二，故 $n$ 是二的幂。若 $n<8$，只有 $n=1,2,4$，所有可有的窗口维数都至多四，因而也被文献应用 19.4 排除。这给 (19.15) 的两个独立下界，(19.13) 同时达到它们。$\square$

**定理 19.6（已知维数的必要性及两层信息损失）。** 即使保留实际标签，单独的 $\operatorname{Src}(W)$ 也不决定窗口维数。除 $0$ 与任一一维窗口的共同空来源外，在 (18.18) 的实际四次子域 $A=F(a,b)\subset L$ 内，
$$
U_3=F1+Fa+Fb,\qquad U_4=A
$$
也有
$$
\operatorname{Src}(U_3)=\operatorname{Src}(U_4)
=\{K\subseteq A:[K:F]=2\},
\qquad\dim_FU_3=3\ne4=\dim_FU_4.
\tag{19.16}
$$
故 (19.11) 的同维数前件不可省。保留该前件时，线性记录丢来源的最小窗口维数是定理 18.6 的四，而完整来源丢标量窗口的最小窗口维数是定理 19.5 的五；两者的最小整体次数均为八。

证明。若二次标签在 $U_i\subseteq A$ 中可见，取 $vK\subseteq U_i$，则 $v\in A^\times$，故 $K\subseteq A$。反过来，在整个实际扩张 $A/F$ 内，$\dim_FU_3=3>4/2$，所以定理 18.4 给每个二次 $K\subseteq A$ 的可见性；$U_4=A$ 当然也包含它们。于是 (19.16) 成立，异维数排除标量相似。关于两层最小量的结论分别直接引用定理 18.6、18.7 和文献应用 19.4、定理 19.5；它们分别涉及从线性张成恢复来源和从完整来源恢复标量轨道，后者的观察仍不包含交空间维数。$\square$

**定义 19.7（完整来源恢复的数学白话与适用边界）。** 把窗口内任意两个独立方向作实际乘法，每个非零商输出都标出同一个 $L$ 内的一个二次子域。只保留这些输出的线性张成，会把本来没有实际输入对的标签也混进来；这是四维、八次时已经出现的第一层损失。现在保留全部真实标签，并事先知道窗口维数，四维及以下还能找回窗口的标量轨道。四维中最有区别的情形生成八次域：真实标签里所有三维线性片，提升回原 $L$ 后分成两种，一种本身是四次子域，另一种就是原窗口乘以其中的一个非零元素。实际乘法让这两类可以分开，因此不必再知道某个来源出现几次或支撑在哪里。到八次域的五维窗口，任何二次标签都已可见，来源集饱和；(19.13) 的两个窗口却不能由任何非零标量互相移到。全部来源相同由此仍可丢失窗口，这是与线性张成丢来源不同的第二层损失。

本节的低维相似结论 (19.11) 是 Zemková v2 的 Theorem 4.6 与 Corollary 3.5(ii) 的应用；(19.12)–(19.12d) 明确了原窗口、实际来源、缺陷与相似标量的往返。Ghorpade–Patil–Pillai v1 的 Theorem 6 提供 (19.9) 的经典全分解子空间分类，本身也不作为新增结果。相对于这些输入，本节的具体综合内容是：利用同一个实际乘法，将两类全分解子空间的提升分别识别为标量窗口与实际四次子域，得到从标签直接定义的完整代表族 (19.6)–(19.7)；并在同一个实际八次域内给出 (19.13)–(19.14) 的同来源而非相似窗口，以已有低维相似结论和次数二幂性确定 (19.15) 的最小性。这些实际重建和反例结论不由上述相似定理直接给出；这里不主张它们的历史首次性。Havlicek v1 的 case (B) 仍只用于完整四次域的原 $\kappa$ 背景。

若接回原三维入口，仍须具有定义 13.1 的全部 P+K 前件；定理 13.9、13.11 给出的是同一个完整四次域、原指定投影 $\pi$ 和 $V=\ker\pi$。此时 (18.26) 与 $m=3$ 相接，(19.11) 只恢复 $V$ 的标量轨道，不恢复指定投影本身，也不从高次窗口推出新的 P+K。这里的维数、域与记录均为上述代数对象，不给出 Born 规则、物理维数、复数域或全部量子起源的推导。

## 追加锚（本行以下为增补区）

## 20　三方向共同见证的四次稳定部分与首次维数碰撞

**定义 20.1（同一实际来源中的三个维数）。** 固定特征二的域 $F$、有限实际域扩张 $L/F$ 和实际中间域 $K$，满足

$$
L^2\subseteq F,\qquad [K:F]=4,\qquad n=[L:F].
$$

固定任意三维 $F$-子空间 $H\le K$，不要求 $1\in H$。对原 $L$ 内任意 $F$-子空间 $W$，定义

$$
\begin{aligned}
T=C_H(W)&=\{x\in L:xH\subseteq W\},\\
C=\operatorname{core}_K(W)&=\{x\in L:xK\subseteq W\},\\
m&=\dim_F W,\qquad j=\dim_F T,\qquad c=\dim_F C.
\end{aligned}
\tag{20.1}
$$

$C$ 是 $W$ 所含的最大 $K$-线性子空间。这里 $j$ 只是在这一个固定实际 $H$ 上的共同见证空间维数；不包含改变 $H$ 后的全部读数。对 $F$-子空间 $A,B\le L$，$AB$ 表示原乘积 $ab$ 的 $F$-线性张成。因此 $HT$、$KT$ 是实际子空间，不能与两个维数 $j,c$ 混同。

全部量词取原 $L$ 中的实际 $F$-点，乘法始终是原域乘法。窗口的整体标量变化只指 $W\mapsto xW$、$x\in L^\times$，不引入抽象域同构、半线性变化或另一份记录映射。

**定理 20.2（结构桥及十一维以内的恢复）。** 对定义 20.1 的每份 $L,K,H,W$，自然乘法给出 $K$-线性同构

$$
\begin{aligned}
\mu:K\otimes_F(T/C)&\longrightarrow KT/C,\\
k\otimes(t+C)&\longmapsto kt+C.
\end{aligned}
\tag{20.2}
$$

并有实际子空间等式及维数公式

$$
\begin{aligned}
W\cap KT&=HT,\\
\dim_F KT&=4j-3c,\\
\dim_F HT&=3j-2c.
\end{aligned}
\tag{20.3}
$$

特别地，存在非负整数 $q,t$，满足

$$
\begin{gathered}
c=4q,\qquad t=j-c,\qquad j=4q+t,\\
4q+3t\le m,\qquad 4q+4t\le n,\qquad m+t\le n.
\end{gathered}
\tag{20.4}
$$

于是对全部 $0\le m\le\min\{11,n\}$ 的实际窗口，

$$
\boxed{\ c=4\left\lfloor\frac j4\right\rfloor\ }.
\tag{20.5}
$$

式 (20.4) 是必要界，不将满足这些整数不等式的每个元组都宣告为可达。

证明。先说明包含关系及缩放。由 $1\in K$ 得 $C\subseteq W$；对 $k\in K$，$xK\subseteq W$ 蕴涵 $(kx)K\subseteq W$，所以 $C$ 是 $K$-空间，且 $C\subseteq T$。反之，任何 $K$-子空间 $U\subseteq W$ 均满足 $U\subseteq C$。这证明最大性及 $c\in4\mathbb Z_{\ge0}$。由于 $H$ 含非零元素，还成立 $HC=C$，从而

$$
C\subseteq HT\subseteq W,\qquad C\subseteq KT.
\tag{20.6}
$$

对任意 $h_0\in H\setminus\{0\}$，在同一个实际 $K$ 内置

$$
H_0=h_0^{-1}H,\qquad W_0=h_0^{-1}W.
$$

此时 $1\in H_0$，并且逐元素有

$$
C_{H_0}(W_0)=T,\qquad
\operatorname{core}_K(W_0)=h_0^{-1}C=C.
\tag{20.7}
$$

第一式因为 $xH_0\subseteq W_0$ 恰等价于 $xH\subseteq W$；第二式使用 $h_0\in K^\times$ 和 $C$ 的 $K$-稳定性。因此 $m,j,c$ 均不改变，$K$ 仍是原来的实际子域。更一般地，对 $x\in L^\times$，

$$
C_H(xW)=xC_H(W),\qquad
\operatorname{core}_K(xW)=x\operatorname{core}_K(W).
$$

这些只是原乘法下的整体标量变化。

所需的普通残余复合在这里有直接的来源对应。Eliahou–Lecouvey，[*On linear versions of some addition theorems*，arXiv:0802.3523v1，Proposition 6.5](https://arxiv.org/pdf/0802.3523v1)，对任意有限交换域扩张及维数之和超过总次数的两个非零子空间，给出乘积张成整个域；该命题没有可分性前件。代入其底域 $F$、扩张域 $K$ 及两个子空间 $H,H$，因 $3+3>4$ 得 $HH=K$。结合原乘法的结合律，

$$
C_H(T)=C_H(C_H(W))=C_{HH}(W)=C.
\tag{20.8}
$$

其中中间等号只说 $x h_1h_2\in W$ 对全部 $h_1,h_2\in H$，等价于 $x(HH)\subseteq W$。乘积张成与这条普通复合恒等式仅是中间步骤；它们将 $C$ 解释为共同见证中还能继续满足同一要求的部分。

下面直接对任意原 $H$ 证明结构式，因而不依赖它是否含 $1$。令 $Q=L/W$，$p:L\to Q$ 为商映射。取非零 $F$-线性泛函 $\rho:K\to F$，使 $\ker\rho=H$，再取 $z\in K$ 满足 $\rho(z)=1$。对 $x\in T$ 和 $k\in K$，因 $k-\rho(k)z\in H$，有

$$
p(kx)=\rho(k)p(zx).
\tag{20.9}
$$

由 $zC\subseteq C\subseteq W$，得到定义良好的 $F$-线性映射

$$
\theta:T/C\longrightarrow Q,\qquad x+C\longmapsto p(zx)
$$

是单射：若 $p(zx)=0$，(20.9) 给 $p(kx)=0$ 对全部 $k\in K$，即 $x\in C$。

这里使用的配对 $\rho(sk)$ 是经典 Frobenius 乘法配对；其非退化性及乘法自伴随性见 Bachoc–Serra–Zémor，[*Revisiting Kneser's theorem for field extensions*，arXiv:1510.01354v2，§2.2](https://arxiv.org/pdf/1510.01354v2)。该文 §2.3 的饱和空间定义也使用条件 $xS\subseteq XS$。在当前有限扩张 $K/F$ 上，所需非退化性可直接写成：若 $k\ne0$，取 $s=z/k$，就有 $\rho(sk)=1$。这里无需域迹，也无需可分性。

取 $T/C$ 的任意 $F$-基 $t_1+C,\ldots,t_t+C$，其中 $t=j-c$，记 $v_i=p(zt_i)$。由 $\theta$ 单射，$v_1,\ldots,v_t$ 在 $F$ 上独立。若 $k_i\in K$ 且

$$
\sum_{i=1}^t k_it_i\in C,
$$

则对每个 $s\in K$，由 $sC\subseteq C\subseteq W$ 及 (20.9)，

$$
0=p\left(s\sum_i k_it_i\right)
=\sum_i\rho(sk_i)v_i.
$$

独立性给 $\rho(sk_i)=0$ 对每个 $s$ 及每个 $i$。上述非退化性迫使所有 $k_i=0$。因此这些原向量的 $K$-张成模去 $C$ 后仍独立，得到实际直和

$$
KT=C\oplus\bigoplus_{i=1}^t Kt_i.
\tag{20.10}
$$

它同时证明 (20.2) 的单射性；满射性则来自 $KT$ 的定义。张量积中的 $T/C$ 只按 $F$-空间使用，不假定它原先已经对 $K$ 稳定。

对 (20.10) 中的向量 $u=c_0+\sum_i k_it_i$，其中 $c_0\in C$，再次使用 (20.9) 得

$$
u\in W
\ \Longleftrightarrow\quad
\sum_i\rho(k_i)v_i=0
\ \Longleftrightarrow\quad
k_i\in H\quad\text{对每个 }i.
$$

又因 $T=C\oplus\operatorname{span}_F\{t_1,\ldots,t_t\}$ 及 $HC=C$，所以

$$
W\cap KT=C\oplus\bigoplus_{i=1}^t Ht_i=HT.
\tag{20.11}
$$

由 $\dim_F K=4$、$\dim_F H=3$，两份直和给出

$$
\dim_F KT=c+4t=4j-3c,\qquad
\dim_F HT=c+3t=3j-2c.
$$

前者至多为 $n$，后者至多为 $m$。此外

$$
\dim_F(W+KT)=m+\dim_F KT-\dim_F HT=m+t\le n.
$$

这证明 (20.3)–(20.4)。当 $m\le11$，$c+3t\le m$ 迫使 $0\le t\le3$；将 $j=4q+t$ 除以四，恰有 $q=\lfloor j/4\rfloor$，即 (20.5)。在这个范围，$c$ 只能为 $0,4,8$，而其余必要限制仍由 (20.4) 给出；这里没有添加充分可达性的断言。

所有边界使用同一公式。$W=0$ 时，任取 $0\ne h\in H$，$xh=0$ 迫使 $x=0$，所以 $T=C=0$。$W=L$ 时，$T=C=L$，故 $m=j=c=n$、$t=0$。若 $L=K$，则 $m\le2$ 时没有非零 $x$ 能将三维 $H$ 送入 $W$，所以 $j=c=0$；$m=4$ 时是刚述的全窗口。余下 $m=3$ 时 $C=0$，而 $j=1$：写 $W=\ker\sigma$，$\sigma:K\to F$ 非零，非退化乘法配对将 $K$ 同构到 $K$ 的 $F$-线性对偶；满足 $\sigma(xH)=0$ 的 $x$ 对应于消去 $H$ 的一维泛函空间。因此 $(m,j,c)=(3,1,0)$。这些结论也覆盖任意不含 $1$ 的原 $H$。$\square$

**命题 20.3（同一十六次来源内的两个十二维窗口）。** 取在 $\mathbb F_2$ 上代数独立的 $a,b,u,v$，并固定实际域

$$
\begin{gathered}
L=\mathbb F_2(a,b,u,v),\qquad
F=\mathbb F_2(a^2,b^2,u^2,v^2),\\
K=F(a,b),\qquad H=\operatorname{span}_F\{1,a,b\},\\
e_1=1,\qquad e_2=u,\qquad e_3=v,\qquad e_4=uv.
\end{gathered}
\tag{20.12}
$$

则 $L^2=F$、$[L:F]=16$、$[K:F]=4$，且 $e_1,\ldots,e_4$ 是同一 $L$ 的 $K$-基。令 $\lambda:K\to F$ 取基 $1,a,b,ab$ 的 $ab$ 系数。在实际 $K$-子空间

$$
M=Ke_2\oplus Ke_3\oplus Ke_4
$$

上定义

$$
B\left(\sum_{i=2}^4 x_ie_i,\sum_{i=2}^4 y_ie_i\right)
=\lambda\left(\sum_{i=2}^4 x_iy_i\right).
$$

取原空间中的子空间

$$
\begin{aligned}
r&=ae_2+be_3+ab e_4,\\
R&=\operatorname{span}_F\{e_2,e_3,e_4,r\}\le M,\\
Y&=R^{\perp_B}\le M,\\
W_0&=\bigoplus_{i=1}^4 He_i,\qquad
W_1=Ke_1\oplus Y.
\end{aligned}
\tag{20.13}
$$

它们在这同一实际 $L,K,H$ 中满足

$$
\begin{array}{c|ccc|cc}
 &m&j&c&C_H(W)&\operatorname{core}_K(W)\\ \hline
W_0&12&4&0&\displaystyle\bigoplus_{i=1}^4 Fe_i&0\\
W_1&12&4&4&Ke_1&Ke_1.
\end{array}
\tag{20.14}
$$

所以相同的 $m,j$ 在十二维时不能决定 $c$；比较的是这一个固定三维 $H$ 的局部共同见证数。

证明。四个变量指数的奇偶类给出 $L/F$ 的十六个基单项式

$$
a^{\epsilon_1}b^{\epsilon_2}u^{\epsilon_3}v^{\epsilon_4},
\qquad \epsilon_i\in\{0,1\}.
$$

具体地，将任一有理函数的分子分母同乘分母，可使分母成为平方，随后分子按四个指数的奇偶分组，证明张成。若有 $F$-线性关系，清去平方有理函数分母后，不同奇偶类的多项式单项式不能抵消，证明独立。这是本卷命题 13.17、定理 18.6 所用基论证在四个变量上的应用。因此 (20.12) 的域次数、平方域及 $K$-基均确实成立。

对 $W_0$，四个三维分量在原 $K$-基上直和，所以 $m=12$。若 $x\in K$ 且 $xH\subseteq H$，则 $x\in F$：否则 $x^2\in F$ 且 $x\notin F$ 使 $F(x)/F$ 二次，而 $H$ 对 $x$ 稳定就使 $H$ 成为 $F(x)$-向量空间，与 $\dim_FH=3$ 矛盾。这里对 $F(x)$ 的稳定性可直接由 $F(x)=F+Fx$ 得到。反之，$F$ 中每个元素都稳定 $H$。按 $K$-基逐坐标应用，便有

$$
C_H(W_0)=\bigoplus_{i=1}^4 Fe_i.
$$

若 $\sum_i x_ie_i\in\operatorname{core}_K(W_0)$，每个非零 $x_i$ 都会给出 $x_iK=K\subseteq H$，不可能。因此 $C=0$，得到表中第一行。

对 $W_1$，配对 $B$ 是非退化、对称、且使全部 $K$-乘法自伴随的 $F$-双线性形式。它逐坐标复用前引 Bachoc–Serra–Zémor §2.2 的 Frobenius 配对；同一一般事实也见 Ueoka–Nagi–Akari–Sui，[*Weak Vishik Equivalence and Linear 2-Basis Blindness for Totally Singular Quadratic Forms*，Zenodo 21758447，Lemma 4.1](https://zenodo.org/records/21758447)。在这里，若某个 $x_i\ne0$，可令 $y_i=x_i^{-1}ab$、其余 $y$ 坐标为零，便得 $B(x,y)=\lambda(ab)=1$，直接核实非退化。自伴随性就是 $B(kx,y)=B(x,ky)$，来自原 $K$ 的交换结合乘法。

$R$ 的四个指定向量独立：前三个分别占三个 $K$-坐标，而 $r$ 的系数 $a,b,ab$ 不能同时是 $F$ 标量。因此 $\dim_FR=4$，非退化性给 $\dim_FY=12-4=8$。本例还可完全写成实际向量的张成：

$$
Y=\operatorname{span}_F\{
 e_2,ae_2,e_3,be_3,ae_4,be_4,
 be_2+e_4,ae_3+e_4\}.
\tag{20.15}
$$

确切地，写 $y=x_2e_2+x_3e_3+x_4e_4$，与前三个 $R$ 基向量正交恰要求 $x_i\in H$。若 $x_i=s_i+t_i a+z_i b$，与 $r$ 正交又恰要求 $z_2+t_3+s_4=0$，这就给出 (20.15)。所有系数均在原 $F$ 内。

关键的联合乘积在同一个 $M$ 中计算。记

$$
A=He_2\oplus He_3\oplus He_4\subseteq HR.
$$

$\dim_FA=9$，$M/A$ 由三个坐标的 $ab+H$ 张成。对 $h=s+ta+zb\in H$，原乘法及 $a^2,b^2\in F$ 给出

$$
(ah+H,\ bh+H,\ ab h+H)
=(z(ab+H),\ t(ab+H),\ s(ab+H)).
\tag{20.16}
$$

因此 $h\mapsto hr+A$ 从 $H$ 到 $M/A$ 为同构。由 $HR=A+Hr$ 得

$$
HR=M.
\tag{20.17}
$$

这里的三个坐标使用同一个 $h$；(20.16) 支付的是这份联合映射的满射性。

由于 $1\in H$，$xH\subseteq Y$ 蕴涵 $x\in Y\subseteq M$。所以全部共同见证都在 $M$ 内；由 $K$-乘法自伴随性，逐元素有

$$
\begin{aligned}
x\in C_H(Y)
&\Longleftrightarrow B(hx,r')=0
 \quad(h\in H,\ r'\in R)\\
&\Longleftrightarrow x\in(HR)^{\perp_B}.
\end{aligned}
$$

结合 (20.17) 及非退化性，得到 $C_H(Y)=0$。于是按 $L=Ke_1\oplus M$ 的原直和，

$$
C_H(W_1)=Ke_1\oplus C_H(Y)=Ke_1.
$$

又因 $Ke_1\subseteq\operatorname{core}_K(W_1)\subseteq C_H(W_1)$，其稳定部分恰为 $Ke_1$。最后 $\dim_FW_1=4+8=12$，得到表中第二行。配对 $B$ 只用于指定实际子空间 $Y$，共同见证与稳定部分的条件始终使用原 $L$ 中的 $xH$ 与 $xK$。整个构造均在 (20.12) 的原域内完成。$\square$

**定理 20.4（两个首次失效量）。** 在定义 20.1 的全部实际域及窗口中，若同一 $L,K,H$ 内的两个窗口满足

$$
m(W)=m(W'),\qquad j(W)=j(W'),\qquad c(W)\ne c(W'),
$$

则必有

$$
m(W)\ge12,\qquad [L:F]\ge16.
\tag{20.18}
$$

两个下界由命题 20.3 的同一对窗口同时达到。因此最小窗口维数为十二，最小整体次数为十六；这两个最小性均只针对固定 $K,H$ 的读数 $(m,j)$ 对维数 $c$ 的恢复。

证明。设共同见证维数为 $j$，交换窗口名称后令 $c<c'$。两稳定部分的维数均为四的倍数，所以 $c'-c\ge4$。又因 $C'\subseteq T'$，有 $j\ge c'$，因此对稳定部分较小的那个窗口，

$$
t=j-c\ge c'-c\ge4.
$$

将它代入定理 20.2 的两个维数公式，得到

$$
m\ge c+3t\ge12,\qquad
n\ge c+4t\ge16.
$$

这是对任意维数窗口的两个独立必要下界。命题 20.3 已在实际指数一域内同时实现 $m=12,n=16$，故二者均为最小值。特别地，当 $n<16$ 时，不论窗口大小如何，都有 $t\le3$，所以 (20.5) 仍成立；本设定下低于十六的允许整体次数只有四与八。$\square$

**定义 20.5（维数读数的数学释义与结论范围）。** 定理 20.2 的含义可由原空间中的分解 (20.10)–(20.11) 直接说明。$C$ 是窗口已完整保留的 $K$-线性部分，每个 $K$ 维度占四个 $F$ 维度；模去它以后，共同见证的每个独立方向 $t_i$ 又占据一个独立的 $K t_i$，而窗口在这份四维空间里恰留下三维 $H t_i$。所以共同见证数由完整部分贡献的 $c$ 与这些剩余方向的个数 $t$ 相加得到，窗口至少要支付 $c+3t$ 个维度。十一维以内的窗口容不下四份这样的三维部分，故 $t$ 只能是除以四的余数，$j$ 中每满四个便恰对应稳定部分的四个维度。

十二维时，$W_0$ 把空间用于四份独立三维部分，给四个共同见证维度，却没有完整的 $K$-稳定部分；$W_1$ 则保留一份完整四维 $K e_1$，余下八维 $Y$ 不容纳任何非零 $xH$，同样给四个共同见证维度。两个窗口大小相同，同一三方向的共同见证数也相同，能继续保留的最大 $K$-稳定部分却不同。这里证明的是两个整数读数不足以决定另一个整数；(20.2) 也没有从维数恢复实际的 $T,C$ 子空间。

所用普通乘积张成来自 Eliahou–Lecouvey Proposition 6.5，乘法配对来自 Bachoc–Serra–Zémor §2.2，饱和的既有定义见同文 §2.3；普通复合与配对只作上述推导的中间步骤，不另作分类结论。Ueoka 等前引文的 Theorem 4.2 是半维子空间及其正交补具有相同全部一次交叠维数的结论，Lemma 6.1 给出其具体八维非相似对，Proposition 6.5 再用一个实际四次子域分离相应乘积张成。命题 20.3 的窗口在十六维中为十二维，$Y$ 在十二维 $M$ 中为八维；它用的是 (20.16) 的联合三坐标计算，不是那份半维对偶对，也没有断言全部一次交叠谱相同。

同样，Zemková，[*Vishik equivalence and similarity of quasilinear p-forms and totally singular quadratic forms*，arXiv:2309.13346v2](https://arxiv.org/pdf/2309.13346v2)，Definition 3.2 的弱等价比较所有单次添根后的缺陷；Corollary 4.21 使用 Definition 2.14 的全等价，比较所有扩域上的缺陷。这里仅比较固定实际 $K,H$ 的一个 $j$，未将它与上述任何一种完整等价条件等同。本节也不求全部 $(m,j,c)$ 的可达性、完整来源谱、完整交叠谱或窗口的标量轨道恢复。

若接回本卷 §13 的三维入口，仍须满足原 P+K 的全部假设，并由该节得到同一完整四次域及指定投影；在 $L=K$、$\dim_FW=3$ 时，这里的维数只是 $(m,j,c)=(3,1,0)$。高次域中的十二维碰撞不改变该入口的三维结论，也不给出 Born 规则、复数域、物理三维或全部量子起源的推导。

## 追加锚（本行以下为增补区）

## 21　固定实际见证与规范余项的全部提升及标量恢复

**定义 21.1（保留实际位置的商读数）。** 仍固定定义 20.1 的同一个实际 $L,K,H$，即 $\operatorname{char}F=2$、$L^2\subseteq F$、$[L:F]<\infty$、$[K:F]=4$、$\dim_FH=3$，不要求 $1\in H$。给定待实现的实际 $F$-子空间 $C\subseteq T\le L$，置

$$
\begin{gathered}
D=KT,\qquad A=HT,\qquad V=L/D,\qquad
\pi:L\longrightarrow V,\qquad Q\le_F V,\\
B=\pi^{-1}(Q),\qquad R=D/A,\qquad
c=\dim_F C,\quad t=\dim_F(T/C),\quad q=\dim_F Q.
\end{gathered}
\tag{21.1}
$$

$V$ 是规范的 $K$-向量空间；这里只使用 $h(y+D)=hy+D$ 的 $K$-作用，不赋予 $V$ 完整的 $L$-乘法。对它的实际 $F$-子空间 $Q$，定义商共同见证

$$
(Q:_V H)=\{v\in V:hv\in Q\text{ 对每个 }h\in H\}.
\tag{21.2}
$$

所要分类的实际提升纤维为

$$
\mathscr F(T,C,Q)=
\{W\le_F L:(W:H)=T,\ (W:K)=C,\ \pi(W)=Q\}.
\tag{21.3}
$$

若给定 $C\not\subseteq T$，相应纤维为空。对实际窗口，定理 20.2 已给出 $W\cap D=A$；所以限制映射 $W/A\to V$ 单射，$Q=\pi(W)$ 正是 $W/HT$ 在 $L/KT$ 中的规范像。观察保留的是这些实际子空间，而非它们的抽象同构类或维数。$\dim_FW$ 将由读数决定，不必另外指定。

**定理 21.2（实际可实现条件及无遗漏的提升纤维）。** 定义 21.1 的数据可由实际窗口实现，当且仅当以下三项同时成立：$C$ 是 $K$-子空间；自然乘法映射

$$
\mu:K\otimes_F(T/C)\longrightarrow D/C,
\qquad k\otimes(x+C)\longmapsto kx+C
$$

是同构；商中没有非零共同见证，即 $(Q:_V H)=0$。这里第二项只在第一项成立时使用，张量积中的 $T/C$ 按 $F$-空间理解。

满足这些条件时，所有满足 $W\cap D=A$ 及 $\pi(W)=Q$ 的普通线性提升都属于 $\mathscr F(T,C,Q)$，没有需要另行剔除的提升。这个纤维规范地对应于下列短正合列的全部 $F$-线性截面：

$$
0\longrightarrow R\longrightarrow B/A
 \xrightarrow{\bar\pi}Q\longrightarrow0.
\tag{21.4}
$$

因而它是 $\operatorname{Hom}_F(Q,R)$ 的仿射挠子，仿射维数为 $tq$，且每个窗口满足

$$
\begin{aligned}
\dim_F R&=t,\\
\dim_F W&=c+3t+q,\\
\dim_F B&=c+4t+q\le [L:F].
\end{aligned}
\tag{21.5}
$$

全部陈述包括 $T=C$、$Q=0$、$C=0$ 及零空间的情形，参数只取实际 $F$-点。

证明。实际窗口的 $C$ 为 $K$-空间、$\mu$ 为同构及 $W\cap D=A$，均直接复用定理 20.2，不重新证明其结构桥。先仅假定待实现的数据满足前两项，分析它们的全部普通线性提升。

取 $T/C$ 的 $F$-基 $t_1+C,\ldots,t_t+C$。乘法同构给出实际直和

$$
\begin{aligned}
T&=C\oplus\bigoplus_{i=1}^t Ft_i,\\
D&=C\oplus\bigoplus_{i=1}^t Kt_i,\\
A&=C\oplus\bigoplus_{i=1}^t Ht_i.
\end{aligned}
\tag{21.6}
$$

最后一式使用 $HC=C$：$H$ 含非零元素，而 $C$ 对 $K$ 稳定。$C=0$ 或 $t=0$ 时，空直和按通常约定处理。

这里 $\{k\in K:kH\subseteq H\}=F$。确实，若 $k\notin F$ 稳定 $H$，则 $k^2\in F$ 使 $F(k)/F$ 为二次扩张，而 $H$ 是 $F(k)$-向量空间，与 $\dim_FH=3$ 矛盾；反向包含显然。这个奇维稳定子事实是成熟输入，亦与 Gulde–Stroppel，[*Stabilizers of Subspaces under Similitudes of the Klein Quadric, and Automorphisms of Heisenberg Algebras*，arXiv:1012.0502v1，Theorem 2.10(b)–(e)](https://arxiv.org/pdf/1012.0502v1) 的特征二相似稳定子域结论一致。

在 (21.6) 中逐坐标应用上述事实，得到原 $L$ 中的等式

$$
(A:H)=T,\qquad (A:K)=C,\qquad (T:H)=C.
\tag{21.7}
$$

为说明这些等式也排除了窗外向量，若 $xH\subseteq D$，任取 $0\ne h_0\in H$，即有 $x=h_0^{-1}(h_0x)\in D$。于是在第一式中，各坐标条件为 $k_iH\subseteq H$，故 $k_i\in F$；第二式要求 $k_iK\subseteq H$，迫使 $k_i=0$；第三式要求 $k_iH\subseteq F$，同样迫使 $k_i=0$，因为非零 $k_i$ 的乘法不能把三维 $H$ 放进一维 $F$。$C$ 中的坐标均满足相应条件。此论证没有使用 $1\in H$。

把原乘法限制到这些实际子空间，得到 $F$-线性映射

$$
\beta:D/T\longrightarrow\operatorname{Hom}_F(H,R),
\qquad
\beta(d+T)(h)=hd+A.
\tag{21.8}
$$

由 $(A:H)=T$，它定义良好且单射；由 (21.6)，两边维数同为 $3t$，所以它是同构。这一步把普通截面的自由度接回实际 $H$-见证：每一份从 $H$ 到缺失方向 $D/A$ 的线性误差，恰能由原 $D$ 中的乘法修正。

普通短正合列 (21.4) 总有 $F$-线性截面。对其中任意截面 $\sigma:Q\to B/A$，取 $W/A=\sigma(Q)$ 的原像，就得到 $W\cap D=A$、$\pi(W)=Q$；反之，每个这样的 $W$ 唯一给出这个截面。这只是标准 Grassmann 图坐标的线性代数，参见 [Stacks，§27.22，Tag 089R，Lemma 27.22.1 的仿射开图](https://stacks.math.columbia.edu/tag/089R)，不将截面参数化本身作为新的分类。

对每个这样的普通提升，原共同见证实际上满足短正合列

$$
0\longrightarrow T\longrightarrow(W:H)
 \xrightarrow{\pi}(Q:_V H)\longrightarrow0.
\tag{21.9}
$$

中间映射的像包含于右侧，核由 $W\cap D=A$ 及 (21.7) 恰为 $T$。满射性需要使用 (21.8)，不能单凭商中的包含关系断言。具体地，取 $v\in(Q:_V H)$，任取原提升 $y\in L$、$\pi(y)=v$。对每个 $h\in H$，$hy\in B$，且

$$
e(h)=\sigma(hv)-(hy+A)\in R
$$

给出 $F$-线性映射 $e:H\to R$。由 $\beta$ 满射，可取 $d\in D$ 使 $hd+A=e(h)$ 对全部 $h\in H$ 成立。因此

$$
h(y+d)+A=\sigma(hv)\in W/A,
$$

从而 $y+d\in(W:H)$，且 $\pi(y+d)=v$。这证明 (21.9)，也证明商见证的提升使用同一个原向量 $d$ 同时修正全部 $h$，而非分别为每个方向选取不相容的提升。

若 $(Q:_V H)\ne0$，(21.9) 使每个普通提升都产生位于 $D$ 外的额外共同见证，故没有一个能满足 $(W:H)=T$。这证明第三项的必要性。若 $(Q:_V H)=0$，同一正合列给出全部提升的 $(W:H)=T$。对其稳定部分，$C\subseteq W$ 且 $C$ 为 $K$-空间，故 $C\subseteq(W:K)$；反过来，$H\subseteq K$ 使 $(W:K)\subseteq T\subseteq D$，于是 $xK\subseteq W\cap D=A$，由 (21.7) 得 $x\in C$。因此全部提升的 core 都恰为 $C$，充分性与无遗漏性得证。

任意两个截面的差唯一落在 $R$ 中，给出 $\operatorname{Hom}_F(Q,R)$ 对截面的自由且传递的加法作用。指定一个截面才会选出仿射坐标的零点；未指定时只有挠子。由 (21.6) 及 (21.4) 立即得到 (21.5)，也证明 $m=\dim_FW$ 已由读数确定。$\square$

**定理 21.3（全部实际标量的纤维作用与恢复充要判据）。** 假定定理 21.2 的可实现条件成立，定义实际子域

$$
E=\{x\in L:xT\subseteq T,\ xB\subseteq B\}.
\tag{21.10}
$$

恰好 $E^\times$ 是能够把纤维中某个窗口送到该纤维中窗口的实际 $L^\times$ 标量的集合；它作用于整个纤维。选择任意 $F$-线性截面 $\sigma$，将窗口记为

$$
W_\phi/A=(\sigma+\phi)(Q),
\qquad \phi\in\operatorname{Hom}_F(Q,R).
\tag{21.11}
$$

对 $x\in E^\times$，令 $a_x$、$b_x$ 分别是原乘法在 $R$、$Q$ 上诱导的作用，并置

$$
c_x=m_x\sigma-\sigma b_x:Q\longrightarrow R,
$$

其中 $m_x$ 是乘法在 $B/A$ 上诱导的作用。完整实际轨道作用为

$$
x\cdot\phi=(a_x\phi+c_x)b_x^{-1}.
\tag{21.12}
$$

因此，对任意两份实际 $F$-坐标，准确的两点判据为

$$
W_\phi\sim_{L^\times}W_\psi
\quad\Longleftrightarrow\quad
\exists x\in E^\times:\ \psi b_x=a_x\phi+c_x.
\tag{21.13}
$$

可选择 $E$-线性截面，使所有 $c_x=0$。在这种坐标中，整个纤维决定唯一 $L^\times$ 标量轨道，当且仅当

$$
\boxed{\ t\,\dim_FQ=tq=0.\ }
\tag{21.14}
$$

此时纤维还只含一个实际窗口。$tq>0$ 时必有不相似的提升，但不由此宣称一般纤维的全部不同坐标两两不相似；其完整判据仍为 (21.13)。

证明。稳定子成域是标准事实，在这里可直接应用于 (21.10)：它包含 $F$，对加法、乘法封闭；若 $0\ne x\in E$，则 $x^{-1}=x/x^2$，且 $x^2\in F^\times$，故 $x^{-1}$ 也保持 $T,B$。因此 $E$ 是原 $L$ 内的实际中间域，非零元素对这两个空间的包含均为等号。即使 $T=0$ 或 $B=0$，此论证仍成立。

原乘法可交换，故 $xT=T$ 还给出 $xD=D$、$xA=A$；由 $(T:H)=C$，同时有 $xC=C$。于是 $xB=B$ 诱导的商作用恰保持 $Q$。这些作用只来自已经保持相应子空间的 $x$，没有把任意 $L$ 标量强行作用到 $L/D$ 上。

若 $xW=W'$ 且二者在同一纤维，实际见证的标量协变性给出 $xT=T$。又有 $B=W+D=W'+D$，所以 $xB=B$，即 $x\in E^\times$。反之，$x\in E^\times$ 保持 $T,C$ 及 $Q$，故把任意一份纤维中的窗口送到同一纤维。这证明可用标量群的准确性，未扩大为一般 $K$-线性变换群。

在坐标 (21.11) 中，逐元素计算

$$
m_x\bigl(\sigma(v)+\phi(v)\bigr)
=\sigma(b_xv)+c_x(v)+a_x\phi(v).
$$

令新的商坐标为 $b_xv$，即得 (21.12)，故 (21.13) 同时必要且充分。换截面只会作仿射换坐标，并不改变原窗口或此轨道关系。

$A,D,B$ 均是 $E$-子空间，所以 (21.4) 是有限维 $E$-空间的短正合列。应用普通向量空间分裂，取一个 $E$-线性截面 $\sigma$，便有 $m_x\sigma=\sigma b_x$，故 $c_x=0$ 对每个 $x\in E^\times$ 成立。这里的分裂只是选坐标，不是原读数附带的一份规范补空间；它使用 $E$-作用。$A$ 一般不是 $K$-子空间，不能因为 $D$ 对 $K$ 稳定就把 $D/A$ 当作 $K$-向量空间。

关键是由这份分裂得到的实际 $W_0$ 被全部 $E^\times$ 固定。如果 $tq>0$，则 $\operatorname{Hom}_F(Q,R)$ 中存在非零 $\phi$，而 $W_\phi\ne W_0$。若存在任何原 $L^\times$ 标量把二者相连，刚证明的标量必要性迫使它在 $E^\times$ 内；但这个群的每个元素都固定 $W_0$，矛盾。因此同一读数至少有两个实际标量轨道。

若 $tq=0$，则 $R=0$ 或 $Q=0$，截面集合只有一个元素，所以连实际窗口也唯一。更具体地，$t=0$ 时 $T=C$、$D=A=C$，唯一窗口为 $B=\pi^{-1}(Q)$；$Q=0$ 时唯一窗口为 $A=HT$。这也包括两者同时成立的情形。证明没有借助有限域计数、代数闭包中的点或一般轨道正规形。$\square$

**定理 21.4（全部最小窗口纤维与其实际标量分离）。** 固定任意上述实际 $L,K,H$，取

$$
0\ne\tau\in L,\qquad v\in L\setminus K\tau,
\qquad z\in K\setminus H.
$$

则全部参数 $s\in F$ 给出的窗口

$$
W_s=H\tau\oplus F(v+s z\tau)
\tag{21.15}
$$

维数均为四，并且它们恰好组成同一实际读数的完整纤维：

$$
\begin{gathered}
T=F\tau,\qquad C=0,\qquad D=K\tau,\qquad
Q=F(v+K\tau)\le L/K\tau,\\
\mathscr F(F\tau,0,F(v+K\tau))=\{W_s:s\in F\}.
\end{gathered}
\tag{21.16}
$$

参数 $s$ 无重复，且

$$
W_s\sim_{L^\times}W_{s'}\quad\Longleftrightarrow\quad s=s'.
\tag{21.17}
$$

反过来，任何非空、不能由读数恢复标量轨道的四维窗口纤维，都有 (21.16) 的形式，因而在选择 $v,z$ 后由 (21.15) 完整列出。该结论保留任意原 $H$，包括不含 $1$ 的情形。

证明。取 $T=F\tau$、$C=0$，自然乘法 $K\otimes_FF\tau\to K\tau$ 是同构。对 $V=L/K\tau$ 中任意非零 $y$，$h\mapsto hy$ 在 $H$ 上单射，因为 $V$ 是 $K$-空间，每个非零 $h\in K$ 的作用可逆；故 $Hy$ 为三维，不可能包含于一维 $Q$。这证明 $(Q:_V H)=0$。由定理 21.2，全部普通提升都确实保持 (21.16) 中的见证及 core。

$K/H$ 由 $z+H$ 张成。选择 $Q$ 的生成元 $v+K\tau$ 后，它的一切提升模去 $H\tau$ 唯一为 $v+s z\tau+H\tau$，所以 (21.15) 给出整个纤维。若两份窗口相同，它们在 $Q$ 的这一个指定生成元上有相同提升模 $H\tau$，于是 $(s-s')z\in H$，即 $s=s'$。

若 $xW_s=W_{s'}$，实际共同见证给出 $xF\tau=F\tau$，所以 $x\in F^\times$。但 $F^\times$ 固定每个 $F$-子空间 $W_s$，故两窗口必须相同，得到 (21.17)。这里两两分离由实际见证直线支付，不由仿射坐标不同直接推出。

对于反向完整性，四维窗口的非恢复纤维由定理 21.3 满足 $t,q\ge1$。式 (21.5) 给 $4=c+3t+q$，所以只能是 $c=0$、$t=q=1$。于是 $T=F\tau$、$Q=F(v+K\tau)$，其中 $\tau\ne0$、$v\notin K\tau$；取任意 $z\notin H$，已证明的完整参数化即适用。$\square$

**定理 21.5（本观察的准确首界与低范围恢复）。** 对实际读数 $(T,C,Q)$ 的标量恢复失败，窗口维数和环境次数的准确最小值分别为

$$
m_{\min}=4,\qquad n_{\min}=8.
\tag{21.18}
$$

两界可在同一实际扩张内同时达到。若 $\dim_FW\le3$，或 $[L:F]\le4$，则这个观察甚至唯一决定实际窗口；恢复公式是定理 21.3 的 $W=\pi^{-1}(Q)$ 或 $W=HT$。

证明。这里的下界须由本观察自身给出。若某个实际读数不能恢复标量轨道，由 (21.14) 有 $t,q\ge1$。因此 (21.5) 给出

$$
m=c+3t+q\ge4,\qquad
n\ge c+4t+q\ge5.
\tag{21.19}
$$

又因实际 $K\subseteq L$ 且 $[K:F]=4$，$n$ 是四的倍数，所以 $n\ge8$。这两个必要下界没有使用 §18 的线性像失真界，也没有把 §19 的完整来源观察换成本观察。

为同时达到两界，直接复用 (18.18)–(18.20) 的八次域及其基，仅将旧变量 $(a,b,c)$ 换成 $(u,a,b)$。等价地，可将 $a,b,u$ 取为在 $\mathbb F_2$ 上代数独立的变量，写为

$$
\begin{gathered}
L=\mathbb F_2(a,b,u),\qquad
F=\mathbb F_2(a^2,b^2,u^2),\qquad K=F(a,b),\\
H=F1+Fa+Fb,\qquad \tau=1,\qquad v=u,\qquad z=ab.
\end{gathered}
\tag{21.20}
$$

原八维基保证 $[L:F]=8$、$[K:F]=4$、$u\notin K$、$ab\notin H$。由定理 21.4，整个实际族

$$
W_s=F1+Fa+Fb+F(u+sab),\qquad s\in F,
\tag{21.21}
$$

具有同一 $T=F$、$C=0$ 及同一实际 $Q=F(u+K)\le L/K$，且不同参数两两不相似。取 $s=0,1$ 即同时达到 (21.18)；这两个端点正是定理 18.7 经上述合法变量对应后的旧窗口，不作为新的端点反例或新的八次域构造。

低范围结论由 (21.19) 的逆否命题及 (21.14) 得到：其中必有 $t=0$ 或 $q=0$，故实际窗口唯一。特别地，$L=K$ 时全部窗口都在此恢复范围内；$W=0$ 给出 $T=C=0,Q=0$，$W=L$ 给出 $T=C=L,Q=0$，也均符合公式。对于任意给定的八次实际扩张和四次子域，只需任选 $v\notin K\tau$，定理 21.4 就给出完整的最小纤维，不限于有理函数表示 (21.20)。$\square$

**定义 21.6（实际观察、等价关系与数学白话）。** 这份观察先记住全部“能把三个指定方向同时送入窗口”的原向量，它们组成实际的 $T$；再记住窗口已完整保留的最大 $K$-空间 $C$。在 $KT$ 中，窗口已被这些读数强制为 $HT$，不是任意选取的三维片段。随后观察还保留窗口离开 $KT$ 后在原商空间中占据的实际位置 $Q$。它忘掉的是：每个商方向回到原空间时，沿 $KT/HT$ 偏移了多少。这个偏移必须同时线性地处理整个 $Q$，所以丢失的自由度是从 $Q$ 到 $KT/HT$ 的一整份线性映射。

商中没有共同见证时，原空间中每个共同见证的投影都只能是零；再由 (21.7)，它恰落在原 $T$ 中。反过来，(21.8)–(21.9) 证明：如果商中存在非零共同见证，它在全部 $H$ 方向上的误差总能由同一个原向量修正，所以任何普通提升都会长出额外见证。因此“商中无见证”同时必要且充分，全部合格提升还自动保留原 core。这正是普通 Grassmann 图坐标之外所需的实际实现桥。

窗口是否相同、是否能由原域中的一个非零数整体相乘得到，以及是否能由一般线性变换得到，是三个不同的判断。最小纤维把这一区别写得完全具体。当 $[L:F]=8$ 时，$\tau,v$ 是原 $L$ 的 $K$-基，且对任意 $s,s'\in F$，映射

$$
\Psi_{s,s'}(k\tau+\ell v)
=k\tau+\ell v+\ell(s'-s)z\tau,
\qquad k,\ell\in K,
\tag{21.22}
$$

是可逆的 $K$-线性剪切，固定 $K\tau$ 中的每个点，在 $L/K\tau$ 上诱导恒等，并把 $W_s$ 送到 $W_{s'}$。但 $s\ne s'$ 时它不可能是原 $L^\times$ 的乘法：乘法若固定非零 $\tau$，该标量只能为 $1$，而此剪切并非恒等。故扩大到 $K$-线性等价会把整个最小族合并，不能把这种合并当成实际标量恢复。一般纤维的可用标量域则由 (21.10) 指定，并须按 (21.13) 比较；仿射图中的两个不同点本身不是一般情形下的不相似证明。

标准图坐标与普通向量空间分裂分别提供截面和坐标选择；稳定子成域及奇维稳定子没有在这里取得新的名称。Frobenius 乘法配对与饱和的成熟输入见 Bachoc–Serra–Zémor，[*Revisiting Kneser's theorem for field extensions*，arXiv:1510.01354v2，§§2.2–2.3](https://arxiv.org/pdf/1510.01354v2)；$HH=K$ 所用的乘积张成见 Eliahou–Lecouvey，[*On linear versions of some addition theorems*，arXiv:0802.3523v1，Proposition 6.5](https://arxiv.org/pdf/0802.3523v1)，该命题只要求有限交换域扩张及两维数之和大于总次数，没有可分性前件。这些内容及 $K\otimes_F(T/C)\cong KT/C$、$W\cap KT=HT$、两项维数公式均按 §20 直接复用。

四次纯不可分域本身也已有明确先例：Kussin，[*Parameter curves for the regular representations of tame bimodules*，arXiv:0712.3274v3，§2、Theorem 6.1(iii)、Examples 6.3(1)](https://arxiv.org/pdf/0712.3274v3) 使用四次无本原元的域扩张及相应 species。把一个窗口的包含映射写成 $F^m\to K^r$ 时，通常表示同构允许源端 $F$-线性换基和目标端 $K$-线性换基；后者已包含 (21.22)。这种表示等价与本节的原 $L^\times$ 群不同，不能从其参数曲线直接替代固定实际 $T,C,Q$ 的标量问题。Gulde–Stroppel 前引文 Theorem 2.10(b)–(e) 明确给出特征二的稳定子域结构，§6.10 还处理四次纯不可分情形及其指定外积商上的轨道；稳定子域或四次域不是这里的新输入，其外积商的作用也不直接等同于 (21.4) 的提升纤维作用。

Bartoli–Csajbók–Marino–Trombetti，[*Evasive subspaces*，arXiv:2005.08401v2，Definition 1.1](https://arxiv.org/pdf/2005.08401v2)，及 Marino–Neri–Trombetti，[*Evasive subspaces, generalized rank weights and near MRD codes*，arXiv:2204.11791v1，§§1–3](https://arxiv.org/pdf/2204.11791v1)，研究的是有限域扩张下的子空间交叠及其编码对应。这里 $K/F$ 为非平凡指数一扩张；若 $F$ 有限，则 $K$ 也有限且平方映射为双射，$K^2\subseteq F$ 将迫使 $K\subseteq F$，与四次条件矛盾。因此不能直接借用那些有限域的可达性或极值分类。

相对于这些成熟输入，本节推导的关系是固定实际数据的充要可实现条件、(21.9) 的实际共同见证提升、由原乘法确定的完整纤维标量作用，以及 (21.14) 与本观察自身准确首界的连接。不据这些来源范围主张历史首次性。§18 的旧端点与八次域继续作为已有实例使用；§19 的完整来源恢复也保持原范围。尤其由 (19.11) 与 (21.17)，最小族的不同参数具有不同的完整 $\operatorname{Src}$，不能声称它们保留相同完整来源；它们保留的是本节的固定 $T,C,Q$。

白话说，即使把共同见证的原位置、完整稳定部分和窗口在商中的位置都留下，原空间中仍可有不同的接回方式。若接回时没有缺失方向，或商中根本没有待接回的方向，窗口就被唯一确定；两者同时存在时，丢失的信息不能全部由原域的整体缩放消去。这个结论讨论的是指定纯不可分域中的实际子空间，不赋予商一个未定义的乘法，也不把抽象坐标变化当成原物理操作。若连接本卷的量子入口，仍须另有原 P+K、指定投影及其余前件；本节没有从这些窗口读数推出 Born 规则、复数域、物理三维、可实施门或全部量子起源。

## 追加锚（本行以下为增补区）

## 22　同一实际域中的余项维数与窗口充要谱

**定义 22.1（零共同见证与实际次数）。** 设 $\operatorname{char}F=2$、$K^2\subseteq F$、$[K:F]=4$，固定任意三维 $F$-子空间 $H\le K$，不要求 $1\in H$。对有限维实际 $K$-向量空间 $E$ 及 $Q\le_F E$，记

$$
Z_H^E(Q)=\{v\in E:hv\in Q\text{ 对每个 }h\in H\}.
\tag{22.1}
$$

这里 $hv$ 只用给定的同一 $K$-模作用。接回定义 20.1 时，仍固定原来的实际 $L,K,H$，并记 $N=[L:K]$、$n=[L:F]=4N$。$N$ 是这份实际扩张的次数，不是可任意另选的正整数。

**定理 22.2（原窗口的完整整数谱及其位置条件）。** 对每份固定实际 $L,K,H$，存在窗口 $W\le_F L$ 使

$$
\dim_FW=m,\qquad \dim_F(W:H)=j,\qquad \dim_F(W:K)=c
$$

当且仅当存在非负整数 $r,t,q$ 满足

$$
\boxed{
\begin{gathered}
c=4r,\qquad j=4r+t,\qquad m=4r+3t+q,\\
r+t\le N,\qquad
0\le q\le\left\lfloor\frac{8(N-r-t)}3\right\rfloor.
\end{gathered}}
\tag{22.2}
$$

更精确地，若预先固定实际 $F$-子空间 $C\subseteq T\le L$，则它们能作为某个窗口的 $(W:K)$、$(W:H)$，当且仅当 $C$ 是 $K$-子空间，且定理 21.2 的自然乘法映射

$$
K\otimes_F(T/C)\longrightarrow KT/C
\tag{22.3}
$$

是同构。这些条件成立时，令 $r=\dim_KC$、$t=\dim_F(T/C)$、$d=N-r-t$；保持这两个实际子空间不变的全部窗口维数恰为

$$
m=4r+3t+q,\qquad 0\le q\le\left\lfloor\frac{8d}3\right\rfloor.
\tag{22.4}
$$

若还固定实际 $Q\le_F L/KT$，则须进一步满足 $Z_H^{L/KT}(Q)=0$，且 $m=4r+3t+\dim_FQ$；仅有 $0\le\dim_FQ\le\lfloor8d/3\rfloor$ 不够。这里直接使用定理 21.2 的全部提升结论，不另作提升纤维或标量轨道分类。

证明。先将所需 evasive 输入落实到给定实际域与指定 $H$。有限域中，Bartoli–Csajbók–Marino–Trombetti，[*Evasive subspaces*，arXiv:2005.08401v2，Definition 1.1、Theorem 2.11、Proposition 4.5、Corollary 4.9 及 §5 的 $n=4$ 情形](https://arxiv.org/pdf/2005.08401v2)，已给出相应交叠性质、直和、上界及低维极大空间。其 Corollary 4.9 代入扩张次数 $n=4$、环境维数 $r=d$、$h=1,k=2$，上界就是 $8d/3$；Proposition 4.5 代入 $r=2,n=4,k=2$ 给五维块，§5 给三维环境中的八维块，一维环境的二维块是定义中的直接情形。取子空间的遗传性也已在该文 Definition 1.1 后明确指出。这些维数与操作不作为新的承重结论。

任意域的框架亦已有 Neri–Zullo，[*Rank-metric codes over arbitrary fields: Bounds and constructions*，Art Discrete Appl. Math. 9，P2.09，DOI 10.26493/2590-9770.1852.9ca，Definition 2.15、Theorems 2.13、2.19](https://adam-journal.eu/index.php/ADAM/article/download/1852/1710)。其扩张域 $L$、底域 $K$ 在这里分别对应我们的 $K,F$，扩张次数 $m=4$；不能把其 Example 2.18 的循环 Galois 自同构直接搬到本设定。以下只给成熟配对与单校验构造在这个实际域中的参数对应和共同乘法核对，不另建一般域框架。

取 $F$-线性泛函 $\rho:K\to F$，使 $\ker\rho=H$。由 §20 使用的 Frobenius 乘法配对，$a\mapsto(k\mapsto\rho(ak))$ 将 $K$ 同构到其 $F$-线性对偶。因此每个三维子空间 $J\le_F K$ 都是某个 $aH$，$a\in K^\times$：若 $J=\ker\sigma$，写 $\sigma(k)=\rho(bk)$，即有 $J=b^{-1}H$。对任意 $K$-模 $E$，这给出准确对应

$$
Z_H^E(Q)=0
\quad\Longleftrightarrow\quad
\dim_F(Q\cap Kx)\le2\quad(0\ne x\in E).
\tag{22.5}
$$

确实，非零见证 $v$ 给出三维 $Hv\subseteq Q\cap Kv$；反之，若交叠维数至少三，在系数空间中取三维 $J$ 使 $Jx\subseteq Q$，再写 $J=aH$，便得非零见证 $ax$。使用的是同一个实际 $H$ 的标量倍，并未改变域或乘法。式 (22.5) 是 $(1,2)$-evasive 的交叠性质；这里不要求 $Q$ 张成整个 $E$，也包括 $Q=0$ 和一维 $K$-环境，不将它们硬套到要求张成且 $h<k$ 的 system 定义。

设 $d=\dim_KE$、$q=\dim_FQ$。若 $Z_H^E(Q)=0$，则原乘法给出的 $F$-线性映射

$$
E\longrightarrow\operatorname{Hom}_F(H,E/Q),
\qquad v\longmapsto\bigl(h\mapsto hv+Q\bigr)
\tag{22.6}
$$

单射，因为其核正是 (22.1)。所以 $4d\le3(4d-q)$，即 $q\le\lfloor8d/3\rfloor$。这个维数论证保留原域全部点，无有限域计数前件。

为核对充分性，在 $K^s$ 中取 $s=1,2,3$，并选 $a_1,\ldots,a_s\in K$ 使 $1,a_1,\ldots,a_s$ 在 $F$ 上独立。记标准 $K$-基为 $e_1,\ldots,e_s$，置

$$
\begin{aligned}
u_s&=\sum_{i=1}^s a_i e_i,\qquad
R_s=Fe_1+\cdots+Fe_s+Fu_s,\\
B_s(x,y)&=\rho\left(\sum_{i=1}^s x_i y_i\right),\qquad
Q_s=R_s^{\perp_{B_s}}.
\end{aligned}
\tag{22.7}
$$

$B_s$ 是 §20 同一成熟乘法配对的逐坐标使用，非退化且满足 $B_s(hx,y)=B_s(x,hy)$。$R_s$ 的指定 $s+1$ 个向量在 $F$ 上独立：任何含非零 $u_s$ 系数的关系都会迫使每个 $a_i\in F$。所以

$$
\dim_FR_s=s+1,\qquad \dim_FQ_s=4s-(s+1)=3s-1.
\tag{22.8}
$$

这也就是普通单校验秩码的坐标形式。矩阵 $G_s=[I_s\mid(a_1,\ldots,a_s)^{\mathsf T}]$ 生成长度 $s+1$、$K$-维数 $s$、最小 $F$-秩距离 $2$ 的码，校验行为 $(-a_1,\ldots,-a_s,1)$。若码字有秩一，可将其写成 $\xi(f_1,\ldots,f_s,f_0)$，其中 $\xi\ne0$、$f_i\in F$；校验式给 $f_0=\sum a_i f_i$，由独立性迫使全部 $f_i=0$。只取一个非零输入坐标则得到秩恰为二的码字。因此 Neri–Zullo Theorem 2.13 的参数正是 $n=s+1,k=s,m=4$，关联 system 为 $R_s$。这是成熟秩码的实际构造，不声称产生新的码族。

还须核对它与指定 $H$ 的共同关系。考虑

$$
K/F\longrightarrow\operatorname{Hom}_F(H,F),
\qquad a+F\longmapsto\bigl(h\mapsto\rho(ah)\bigr).
\tag{22.9}
$$

该映射定义良好，因为 $\rho(H)=0$。非退化乘法配对下 $H$ 的正交补为一维，且包含 $F1$，所以从 $K$ 出发的限制映射 $a\mapsto\rho(a\,\cdot)|_H$ 的核恰为 $F1$。因此商映射 (22.9) 单射；两边维数同为三，它是同构。由 $a_1+F,\ldots,a_s+F$ 独立，映射

$$
\gamma_s:H\longrightarrow F^s,
\qquad h\longmapsto\bigl(\rho(a_1h),\ldots,\rho(a_sh)\bigr)
\tag{22.10}
$$

满射：其对偶映射把标准对偶基送到 (22.9) 下的这 $s$ 个独立泛函，因而单射。

令 $A_s=He_1\oplus\cdots\oplus He_s$。$K^s/A_s$ 由逐坐标的 $\rho$ 同构到 $F^s$，而 $Hu_s$ 在这个商中的像正是 $\gamma_s(H)$。因此

$$
HR_s=A_s+Hu_s=K^s,\qquad
Z_H^{K^s}(Q_s)=(HR_s)^{\perp_{B_s}}=0.
\tag{22.11}
$$

第二式逐元素来自 $B_s(hv,r)=B_s(v,hr)$。在 (22.10) 中一次选择同一个 $h$，就同时指定了全部 $s$ 个商坐标；不是先分别取各坐标的原像再假设它们相容。这证明 (22.7) 的二维、五维、八维块在每份实际 $K,H$ 中都可用，包括 $1\notin H$。其中八维块直接复用命题 20.3 的配对—联合乘积形式，(22.9) 给出任意 $H$ 所需的坐标对应。

对任意 $d$，写 $d=3a+b$，$a\ge0$、$b\in\{0,1,2\}$。在给定 $E$ 的一份实际 $K$-基上，取 $a$ 个三维 $K$-块，若 $b>0$ 再取一个 $b$ 维块；把各块的 $Q_3$、$Q_b$ 作直和。由于 $H$ 的作用保持这些 $K$-直和分量，共同见证逐投影也作直和，所以所得 $Q_{\max}$ 满足

$$
Z_H^E(Q_{\max})=0,\qquad
\dim_FQ_{\max}=
\begin{cases}
8a,&b=0,\\
8a+2,&b=1,\\
8a+5,&b=2
\end{cases}
=\left\lfloor\frac{8d}3\right\rfloor.
\tag{22.12}
$$

这正是前引有限域 Theorem 2.11 的直和性质在当前原乘法中的直接使用。取 $Q_{\max}$ 的任意一份 $F$-基，其初始片段张成嵌套旗标；每个子空间 $Q$ 都有 $Z_H^E(Q)\subseteq Z_H^E(Q_{\max})=0$。所以在同一个实际 $E,K,H$ 中，所有整数均实现，得到所需的精确输入

$$
\{\dim_FQ:Q\le_F E,\ Z_H^E(Q)=0\}
=\{0,1,\ldots,\lfloor8d/3\rfloor\}.
\tag{22.13}
$$

$d=0$ 时取空直和与零空间，上下两边都只有零。这一结论只需要实际 $K$-模；没有要求 $E$ 本身为域。

现在接回原窗口。对任意实际 $W$，定理 20.2 与定理 21.2 已给出 $C=(W:K)$、$T=(W:H)$ 的乘法同构、$W\cap KT=HT$ 及商余项 $Q=\pi(W)\le L/KT$ 的零共同见证条件。令 $r=\dim_KC$、$t=\dim_F(T/C)$，直接引用其维数公式，有

$$
\dim_KKT=r+t,\qquad
\dim_K(L/KT)=N-r-t,
\qquad m=4r+3t+\dim_FQ.
\tag{22.14}
$$

把 (22.13) 应用于实际 $K$-模 $L/KT$，便得到 (22.2) 的全部必要条件。这一步使用 §21 已证的商见证提升必要性，未把商中的包含关系当作其替代证明。

反之，给定满足 (22.2) 的整数，在原 $L$ 中选一份 $K$-基，取其中 $r$ 个方向的 $K$-张成为 $C$，另取 $t$ 个基向量 $v_i$，令

$$
T=C\oplus\bigoplus_{i=1}^t Fv_i,
\qquad D=KT=C\oplus\bigoplus_{i=1}^t Kv_i.
\tag{22.15}
$$

乘法同构 (22.3) 由这些实际基向量保证。余下基向量给出实际 $K$-补空间 $U$，$L=D\oplus U$、$\dim_KU=N-r-t$。按 (22.13) 在 $U$ 中选择所需维数 $q$ 的 $Q_0$，其商像 $Q\le L/D$ 仍无共同见证。定理 21.2 即保证实际窗口

$$
W=C\oplus\bigoplus_{i=1}^t Hv_i\oplus Q_0
\tag{22.16}
$$

具有恰好的 $T,C$，并有 (22.2) 的 $m,j,c$。所有分量都在同一个原 $L$ 内，$H$ 和乘法从未更换。这证明存在性的充分方向。

若固定实际 $T,C$，其相容性正由定理 21.2 的前两项决定。条件成立后，(22.14) 自动给 $r+t\le N$；在实际商空间中用 (22.13) 选 $Q$，再引用同一定理的普通线性提升，即实现 (22.4) 的每个 $m$。特别取 $Q=0$ 就得到一个窗口，所以这里没有额外的存在性条件。若还固定 $Q$，则直接保留定理 21.2 的第三项及维数式，得到陈述中的准确判据；没有把 $Q$ 的位置条件消成一个整数。

这两个量词区别有实际反例。若 $N\ge2$，在原 $L$ 中取 $K$-独立的 $x,y$ 及 $a\in K\setminus F$。$C=0$、$T_-=Fx+Fax$ 的维数数据 $r=0,t=2,q=0$ 满足 (22.2)，但 $KT_-=Kx$，故 (22.3) 不可能是同构：其定义域的 $K$-维数为二，值域的 $K$-维数为一。因此没有窗口实现这个实际 $T_-$。同样维数的 $T_+=Fx+Fy$ 则相容，$W=Hx\oplus Hy$ 给出 $m=6,j=2,c=0$。这证明只固定整数允许选择位置，固定实际 $T$ 后必须检验位置。

同理，若相容 $T,C$ 的商空间 $V=L/KT$ 有 $K$-维数 $d\ge2$，取 $0\ne v\in V$，则 $Q_-=Hv$ 为三维，且 $3\le\lfloor8d/3\rfloor$，但 $v\in Z_H^V(Q_-)$。它不能作为保持这份实际 $T,C$ 的余项。另一方面，(22.13) 在同一个 $V$ 中给出三维 $Q_+$，满足 $Z_H^V(Q_+)=0$，所以它能够提升。维数相同不替代零共同见证性质。

边界亦由同一谱支付。$r+t=N$ 时只有 $q=0$；$W=0$ 对应 $r=t=q=0$，$W=L$ 对应 $r=N,t=q=0$。$N=1$ 时，所得窗口读数正是 §20 已给出的 $m=0,1,2$ 时 $j=c=0$、$m=3$ 时 $(j,c)=(1,0)$、$m=4$ 时 $(j,c)=(4,4)$。若实际 $N=2$，旧必要界允许的 $(m,j,c)=(6,0,0)$ 被 (22.2) 排除，因为此时 $d=2$ 而 $q=6>5$；旧界不能代替充分谱。

最后，$L^2\subseteq F$ 使每次添入一个尚不在当前中间域的元素，其次数均为二；有限扩张因而给 $[L:F]$、$N=[L:K]$ 为二的幂。本证明对每份已经给定的实际 $L$ 使用其 $N$，并未构造任意整数 $N$ 的指数一域。若 $F$ 有限，$K$ 也有限且平方映射满射，$K^2\subseteq F$ 将迫使 $K=F$，所以非平凡四次设定没有有限底域实例。以上充分性不用有限域 Frobenius 自同构、域迹、泛点或扩域。$\square$

**定义 22.3（谱、来源与白话释义）。** 原窗口的维数预算分成三部分：完整 $K$-稳定部分每个 $K$ 方向占四维；模去它后的每个独立共同见证迫使窗口再保留一个三维 $H$ 片；余下商空间可以容纳一些不产生额外共同见证的方向。前两部分正是 §20 的结构；§21 保证第三部分有没有非零共同见证，准确控制提升后会不会长出新的见证。式 (22.13) 说明第三部分的容量恰为其 $K$-维数的 $8/3$ 向下取整，而且每个更小整数都能取到。因此 (22.2) 把旧结构与实际余项容量接成了双向可实现条件。

这里“同一实际”意味着先固定 $F,K,H,L$，然后在它们内部选择窗口。把存在量词中的实际 $T,C$ 也固定下来，就必须要求它们真由原乘法组成 (22.3)，只有维数相等不能保证这一点；再固定 $Q$，还必须逐向量保留 (22.1) 的零条件。式 (22.10) 解释了可达性为何是共同的：三个输出方向来自同一个输入 $h$ 的三个独立线性读数，故能同时填满缺失的商坐标。块的直和与取子空间均在这份原 $K$-模内进行，所有维数的旗标使用原域实际 $F$ 点。

前引有限域来源的 $2/5/8$ 维块、$8d/3$ 界、直和及遗传性均保留其成熟输入身份。Marino–Neri–Trombetti，[*Evasive subspaces, generalized rank weights and near MRD codes*，arXiv:2204.11791v1，Theorem 3.3](https://arxiv.org/pdf/2204.11791v1)，已给有限域的秩权—交叠对应；Neri–Zullo 前引文 Theorems 2.13、2.19 则给任意有限次域扩张的对应，其 §4.2 还明确区分一般域与循环 Galois 构造。Giannoni，[*Evasive subspaces, minimal rank-metric codes and subspace designs via auxiliary fields*，arXiv:2611.08627v1，Theorem 1.1、引言与 Remark 6.3](https://arxiv.org/pdf/2611.08627v1)，明确将 $h=1<k$ 的结论列为已知或初等；这里的有限域参数是 $n=4,h=1,k=2$，不从其充分大维数定理冒领任意实际纯不可分域或全部余数类。

本条承接的是原窗口 $(m,j,c)$ 的完整充要谱、指定 $H$ 的共同满射与 §21 实际商提升的连接，以及固定位置和只固定整数的量词差异；没有把一般域框架、成熟单校验码或已有配对另立为新理论。四次纯不可分域、奇维稳定子及 species 的来源继续按 §21 的 Gulde–Stroppel、Kussin 对应使用。不主张全球首次性或一般全部标量轨道分类；本谱也不推出 Born 规则、物理三维、复数域或全部量子起源。

## 追加锚（本行以下为增补区）

## 23　四次实际域塔上线性结构的任意特征适用范围

**推论 23.1（§§20–22 的范围及来源边界）。** 固定交换域的有限次扩张塔 $F\subset K\subseteq L$，$[L:F]<\infty$、$[K:F]=4$，令 $N=[L:K]$、$n=4N$，固定任意三维 $F$-子空间 $H\le K$。不要求 $1\in H$，不要求可分、正规、循环、特征二或平方落在 $F$。以下沿用 (20.1)、(21.1)–(21.3)、(22.1) 的子空间公式，均在这份实际域塔与原乘法中解释；不改变旧条目的前件，也不把原商空间赋予新的域乘法。

（一）对每个实际窗口 $W\le_F L$，$T=(W:H)$、$C=(W:K)$ 满足 $C$ 为 $W$ 中最大的 $K$-子空间及 $(T:H)=C$，且

$$
\begin{gathered}
K\otimes_F(T/C)\xrightarrow[\ k\otimes(x+C)\mapsto kx+C\ ]{\ \sim\ }KT/C,\\
W\cap KT=HT,\\
c=\dim_F C=4r,\quad t=\dim_F(T/C),\quad j=\dim_FT=4r+t,\\
\dim_FKT=4r+4t,\quad\dim_FHT=4r+3t,\\
4r+3t\le m=\dim_FW,\quad 4r+4t\le n,\quad m+t\le n.
\end{gathered}
\tag{23.1}
$$

因而 $m\le11$ 或 $n<16$ 时仍有 $c=4\lfloor j/4\rfloor$；后一范围现在包括 $n=12$。

（二）预先给定实际 $C\subseteq T\le_F L$，置 $D=KT$、$A=HT$、$V=L/D$、$\pi:L\to V$。再固定实际 $Q\le_F V$，令 $B=\pi^{-1}(Q)$、$R=D/A$、$q=\dim_FQ$。存在具有这份 $(T,C,Q)$ 的窗口，当且仅当

$$
C\text{ 是 }K\text{-子空间},\qquad
K\otimes_F(T/C)\longrightarrow D/C\text{ 是乘法同构},\qquad
Z_H^V(Q)=(Q:_V H)=0.
\tag{23.2}
$$

第二项在第一项成立后解释为 $K$-线性映射。给定 $C\not\subseteq T$ 时纤维为空。前两项成立时令 $r=\dim_KC$、$t=\dim_F(T/C)$。满足 (23.2) 时，全部普通提升 $W\cap D=A$、$\pi(W)=Q$ 恰为全部合格窗口；它们是

$$
0\longrightarrow R\longrightarrow B/A\longrightarrow Q\longrightarrow0
\tag{23.3}
$$

的 $F$-线性截面，组成 $\operatorname{Hom}_F(Q,R)$ 的仿射挠子，$\dim_FR=t$、$\dim_FW=4r+3t+q$、$\dim_FB=4r+4t+q$。仅满足前两项时，每个普通提升仍有准确的共同见证正合列

$$
0\longrightarrow T\longrightarrow(W:H)\xrightarrow{\pi}Z_H^V(Q)\longrightarrow0.
\tag{23.4}
$$

因此第三项是全部普通提升保留 $T$ 的充要条件。

（三）对非空纤维，原域内的

$$
E=\{x\in L:xT\subseteq T,\ xB\subseteq B\}
\tag{23.5}
$$

是实际中间域；恰好 $E^\times$ 是能将纤维中某个窗口乘到该纤维的全部 $L^\times$ 标量。选截面 $\sigma$，以 $W_\phi/A=(\sigma+\phi)(Q)$ 记窗口。对 $x\in E^\times$，以 $a_x,b_x,m_x$ 记原乘法在 $R,Q,B/A$ 上的作用，令 $c_x=m_x\sigma-\sigma b_x$，则

$$
x\cdot\phi=(a_x\phi+c_x)b_x^{-1},\qquad
W_\phi\sim_{L^\times}W_\psi
\ \Longleftrightarrow\ 
\exists x\in E^\times:\ \psi b_x=a_x\phi+c_x.
\tag{23.6}
$$

可取 $E$-线性截面使全部 $c_x=0$。固定实际 $(T,C,Q)$ 的纤维只含一个标量轨道，当且仅当 $tq=0$；此时实际窗口也唯一：$t=0$ 时为 $B$，$q=0$ 时为 $HT$。当 $tq>0$，至少有两个轨道；一般不宣称不同仿射坐标两两不相似。

（四）对任何给定的有限维实际 $K$-模 $M$，$d=\dim_KM$，余项容量仍准确为

$$
\{\dim_FQ:Q\le_FM,\ Z_H^M(Q)=0\}
=\{0,1,\ldots,\lfloor8d/3\rfloor\}.
\tag{23.7}
$$

故在固定的实际 $L,K,H$ 中，存在维数读数 $(m,j,c)$ 的窗口，当且仅当有非负整数 $r,t,q$ 满足

$$
\boxed{\quad c=4r,\quad j=4r+t,\quad m=4r+3t+q,\quad
r+t\le N,\quad 0\le q\le\lfloor8(N-r-t)/3\rfloor.\quad}
\tag{23.8}
$$

若固定实际 $T,C$，须且只须 (23.2) 的前两项；相容时，令 $d=N-r-t$，保持它们的窗口维数恰为 $4r+3t+q$、$0\le q\le\lfloor8d/3\rfloor$。再固定实际 $Q$ 时，须保留第三项，不能以容量不等式替代。这里 $N$ 始终是原 $L/K$ 的实际次数，无二幂限制；不声称任意给定 $K/F$ 都有任意次数的上层域扩张。

（五）两种观察的首界分别保持如下：同一实际 $L,K,H$ 中，$(m,j)$ 不能决定 $c$ 的最小窗口维数和环境次数为 $(12,16)$；固定实际 $(T,C,Q)$ 不能决定窗口标量轨道的相应首界为 $(4,8)$。更具体地，前一种碰撞在每份 $N\ge4$ 的塔中存在，$N<4$ 时不存在；后一种在每份 $N\ge2$ 的塔中存在，$N=1$ 时不存在。后一种的所有四维非恢复纤维，仍恰为

$$
\begin{gathered}
W_s=H\tau\oplus F\cdot(v+s z\tau),\quad s\in F,\quad
0\ne\tau\in L,\quad v\notin K\tau,\quad z\in K\setminus H,\\
T=F\tau,\quad C=0,\quad Q=F\cdot(v+K\tau),\qquad
W_s\sim_{L^\times}W_{s'}\ \Longleftrightarrow\ s=s'.
\end{gathered}
\tag{23.9}
$$

这些首界也可在特征零达到，且有 $N=3$、$1\notin H$ 的实际实例。

（六）上述范围扩张限于指定 $H$ 的共同乘法、普通提升和窗口谱。旧全域公式 $\kappa(u\wedge v)=uv+F$ 存在为交替线性映射，当且仅当 $L^2\subseteq F$；在这里的非平凡塔中，它还强制 $\operatorname{char}F=2$。实际二次子域的可见性及其标量不变性可保留；§18 的记录—二次来源绑定与 §19 的完整来源恢复不能随本推论同步扩张。

证明。先在原 $K$ 中取非零 $F$-线性泛函 $\rho$，$\ker\rho=H$。所用成熟输入是 Eliahou–Lecouvey，[arXiv:0802.3523v1，Proposition 6.5](https://arxiv.org/pdf/0802.3523v1) 的有限交换域乘积张成，以及 Bachoc–Serra–Zémor，[arXiv:1510.01354v2，§2.2](https://arxiv.org/pdf/1510.01354v2) 的非退化乘法配对 $\rho(ab)$。前者代入 $H,H\le K$，由 $3+3>4$ 得 $HH=K$；后者不以域迹或可分性为前件。于是结合律给

$$
((W:H):H)=(W:HH)=(W:K)=C.
\tag{23.10}
$$

先补足两处旧证明中的平方用法。有限维子空间 $U$ 若满足 $xU\subseteq U$、$x\ne0$，则原乘法在 $U$ 上单射，故 $xU=U$、$x^{-1}U=U$；$U=0$ 也成立。保持给定子空间的标量集合含 $F$，对和、积封闭；上述逆元性质使它成为原 $L$ 内的子域，亦可取若干这种集合的交。这正是 Bachoc–Serra–Zémor 的 Corollary 14 前有限维稳定子说明；不将该推论对饱和类的对偶等式套给任意子空间。特别对

$$
S_H=\{k\in K:kH\subseteq H\}
$$

有 $[S_H:F]\mid[K:F]=4$，且 $H$ 是 $S_H$-空间给 $[S_H:F]\mid3$，故 $S_H=F$。这替代旧证明中“$k\notin F$ 则 $F(k)/F$ 二次”的论证，也替代 (21.10) 后的 $x^{-1}=x/x^2$；两者均不再需要平方条件。

现在核对结构，而非仅将旧前件删去。$C$ 是 $W$ 中最大 $K$-空间，$C\subseteq T$、$HC=C$。取 $z\in K$ 使 $\rho(z)=1$，令 $p:L\to L/W$。对 $x\in T$，由 $k-\rho(k)z\in H$ 得

$$
p(kx)=\rho(k)p(zx),\qquad k\in K.
\tag{23.11}
$$

映射 $T/C\to L/W$、$x+C\mapsto p(zx)$ 单射：若像为零，(23.11) 给 $Kx\subseteq W$。取 $T/C$ 的 $F$-基 $t_i+C$，则 $p(zt_i)$ 独立。若 $\sum k_it_i\in C$，将它乘以每个 $s\in K$ 再用 (23.11)，得到每个 $i$ 的 $\rho(sk_i)=0$ 对全部 $s$ 成立；配对非退化给 $k_i=0$。所以在原 $L$ 中

$$
KT=C\oplus\bigoplus_{i=1}^t Kt_i,\qquad
W\cap KT=C\oplus\bigoplus_{i=1}^t Ht_i=HT.
\tag{23.12}
$$

第二式由 $p(c_0+\sum k_it_i)=\sum\rho(k_i)p(zt_i)$ 得到。两份直和证明乘法同构与 (23.1)；$\dim_F(W+KT)=m+t$ 给最后一界。$m\le11$ 迫使 $t\le3$；$n<16$ 时 $t\le N\le3$。将 $j=4r+t$ 除以四即得恢复式。所有运算均未要求 $1\in H$；任选 $h_0\in H\setminus\{0\}$ 时，同时缩放 $(H,W)\mapsto(h_0^{-1}H,h_0^{-1}W)$ 也保持 $T,C,m,j,c$，但这里不必改变原 $H$。

对预先给定的 $C,T$，假定 (23.2) 前两项，仍有 (23.12) 中 $D=C\oplus\bigoplus Kt_i$、$A=C\oplus\bigoplus Ht_i$。用刚证的 $S_H=F$ 逐坐标得

$$
(A:H)=T,\qquad (A:K)=C,\qquad (T:H)=C.
\tag{23.13}
$$

这些等式也排除 $D$ 外的向量：$xH\subseteq D$ 蕴涵 $x=h_0^{-1}(h_0x)\in D$，因为 $D$ 为 $K$-空间。对最后一式，非零系数不能将三维 $H$ 乘进一维 $F$。因此原乘法诱导

$$
\beta:D/T\longrightarrow\operatorname{Hom}_F(H,R),\qquad
\beta(d+T)(h)=hd+A
\tag{23.14}
$$

为单射；两边维数同为 $3t$，故它为同构。这是全部共同方向能由同一个原向量修正的步骤。

普通 $F$-线性截面存在，且其图与 $W\cap D=A$、$\pi(W)=Q$ 的窗口双向唯一对应，这是 (23.3) 的普通线性代数，也对应 [Stacks，Tag 089R，Lemma 27.22.1](https://stacks.math.columbia.edu/tag/089R) 的 Grassmann 仿射图。对任一截面 $\sigma$，(23.4) 中映射的核由 (23.13) 恰为 $T$。为证满射，取 $v\in Z_H^V(Q)$ 及原提升 $y\in L$；则

$$
e(h)=\sigma(hv)-(hy+A)\in R,\qquad h\in H,
$$

是一份 $F$-线性映射。由 (23.14) 取一个 $d\in D$，同时满足 $hd+A=e(h)$ 对全部 $h$；于是 $h(y+d)+A=\sigma(hv)$，即 $y+d\in(W:H)$。这证明完整正合列，包括其必要方向。$Z_H^V(Q)=0$ 时 $(W:H)=T$；又 $C\subseteq(W:K)\subseteq T\subseteq D$，用 $W\cap D=A$ 及 (23.13) 得 $(W:K)=C$。反之，实际窗口的前两项来自 (23.12)，第三项由 (23.4) 强制。截面之差为 $\operatorname{Hom}_F(Q,R)$，故挠子与维数公式全部成立。

有限维逆元论证同时证明 (23.5) 的 $E$ 为子域。若 $xW=W'$ 且二者在同一纤维，原乘法的交换性给 $xT=T$，继而 $xD=D$，由 $B=W+D=W'+D$ 得 $xB=B$。故 $x\in E^\times$。反之，$x\in E^\times$ 保持 $T,D,A$，由 $C=(T:H)$ 保持 $C$，并在 $B/D$ 中保持 $Q$，所以作用于整个纤维。特别这里没有让任意 $L$ 标量作用于未被它保持的商 $L/D$。在截面坐标中计算

$$
m_x(\sigma(v)+\phi(v))
=\sigma(b_xv)+c_x(v)+a_x\phi(v)
$$

即得 (23.6) 的两个方向。$A,D,B$ 是 $E$-空间，故 (23.3) 在 $E$ 上分裂；取 $E$-线性 $\sigma$ 即令 $c_x=0$。其零图 $W_0$ 被每个 $E^\times$ 标量固定。$tq>0$ 时，原 $F$ 上存在非零 $\phi$，图 $W_\phi\ne W_0$；若有原 $L^\times$ 标量相连，它须在 $E^\times$ 中，矛盾。$tq=0$ 时截面唯一，给出所述恢复公式。这里 $R$ 使用 $E$-结构；通常 $A$ 不为 $K$-空间，不能把 $R$ 当作 $K$-空间。

为将余项容量接回任意特征，保留 §22 的成熟构造，仅核对它对原 $H$ 的适用性。乘法配对将 $K$ 同构到其 $F$-对偶，所以每个三维 $J\le_FK$ 都有 $J=aH$、$a\in K^\times$。因此

$$
Z_H^M(Q)=0\quad\Longleftrightarrow\quad
\dim_F(Q\cap Kx)\le2\quad(0\ne x\in M).
\tag{23.15}
$$

非零见证给出 $Hv$；反向在三维交叠中取 $Jx$，写 $J=aH$ 即得见证 $ax$。这是任意域上的 $(1,2)$ 交叠条件；零空间及不张成 $M$ 的子空间也包括在内。映射 $M\to\operatorname{Hom}_F(H,M/Q)$、$v\mapsto(h\mapsto hv+Q)$ 的核为 $Z_H^M(Q)$，故零核给 $4d\le3(4d-q)$，即 (23.7) 的上界。

充分性使用 §22 的二维、五维、八维块。对 $s=1,2,3$，选 $1,a_1,\ldots,a_s\in K$ 在 $F$ 上独立，在一份实际 $K^s$ 坐标中置

$$
R_s=\operatorname{span}_F\{e_1,\ldots,e_s,\sum a_ie_i\},\quad
B_s(x,y)=\rho(\sum x_iy_i),\quad Q_s=R_s^{\perp_{B_s}}.
\tag{23.16}
$$

这仍是单校验矩阵 $[I_s\mid(a_1,\ldots,a_s)^{\mathsf T}]$ 的成熟列空间构造。其 $s+1$ 个指定向量独立：若 $\sum f_ie_i+f_0\sum a_ie_i=0$，$f_i\in F$，$f_0\ne0$ 将迫使所有 $a_i\in F$，矛盾；$f_0=0$ 又迫使所有 $f_i=0$。所以 $\dim_FR_s=s+1$；逐坐标的非退化配对给 $\dim_FQ_s=3s-1$。其与原 $H$ 的共同关系由

$$
K/F\xrightarrow{\ \sim\ }\operatorname{Hom}_F(H,F),\qquad
 a+F\longmapsto(h\mapsto\rho(ah))
\tag{23.17}
$$

承担：$H$ 在乘法配对下的正交补恰为 $F1$，所以此映射的核已恰被模去，两边维数同为三。$a_i+F$ 独立使 $h\mapsto(\rho(a_1h),\ldots,\rho(a_sh))$ 满射到 $F^s$。令 $A_s=\bigoplus He_i$，则同一个 $h$ 对 $h\sum a_ie_i+A_s$ 给出上述全部商坐标，故

$$
HR_s=K^s,\qquad Z_H^{K^s}(Q_s)=(HR_s)^{\perp_{B_s}}=0.
\tag{23.18}
$$

没有使用 $a_i^2\in F$ 或有限域的 Frobenius 自同构。写 $d=3u+b$、$b\in\{0,1,2\}$，在实际 $M$ 的 $K$-基上用 $u$ 个三维块及一个 $b$ 维余块，得到零共同见证的直和，维数为 $8u$、$8u+2$ 或 $8u+5$，恰为 $\lfloor8d/3\rfloor$。取其一份 $F$-基的初始片段得到所有更小维数；零共同见证由子空间包含关系遗传。$d=0$ 时取空直和。这证明 (23.7) 的全部充分方向，使用的点均为原 $F$ 点。

对任意原窗口，(23.1)–(23.4) 给出商 $L/KT$ 的 $K$-维数 $d=N-r-t$ 及 $m=4r+3t+q$，将 (23.7) 代入即得 (23.8) 的必要性。反向在原 $L$ 的一份 $K$-基中取 $r$ 个完整方向为 $C$，另取 $t$ 个基向量 $t_i$，令 $T=C\oplus\bigoplus Ft_i$；余下实际 $K$-补空间 $U$ 的维数为 $d$。在 $U$ 中按 (23.7) 选所需维数的 $Q_0$，则

$$
W=C\oplus\bigoplus Ht_i\oplus Q_0
\tag{23.19}
$$

由 (23.2) 恰有指定读数。固定实际 $C,T$ 时，在实际商 $L/KT$ 中同样选择 $Q$ 并提升即可；取 $Q=0$ 已保证存在一个窗口。固定实际 $Q$ 时则必须保留零共同见证条件。这给出三个不同量词层次的充分性。

位置不能消成整数。若 $N\ge2$，取原 $K$-独立的 $x,y\in L$ 及 $a\in K\setminus F$，$C=0$、$T_-=Fx+Fax$ 虽具有 (23.8) 允许的 $r=0,t=2,q=0$，但 $KT_-=Kx$ 的 $K$-维数仅一，乘法映射不可能为同构；$T_+=Fx+Fy$ 则由 $W=Hx\oplus Hy$ 实现。对相容 $T,C$ 的实际商 $V$，若 $\dim_KV=d\ge2$，取 $v\ne0$，$Q_-=Hv$ 的维数三在容量内，却有见证 $v$，不可提升为这份读数；(23.7) 在同一 $V$ 中给出三维零见证的 $Q_+$，可以提升。这两个比较都保持原域和实际乘法。

对相容数据，全部退化边界由同一论证覆盖：$T=C$ 时 $D=A=C$；$Q=0$ 时窗口恰为 $A$；$r+t=N$ 时只能有 $q=0$；$W=0$ 对应 $r=t=q=0$，$W=L$ 对应 $r=N,t=q=0$。$N=1$ 时 $m=0,1,2$ 的窗口有 $j=c=0$，$m=3$ 时 $(j,c)=(1,0)$，$m=4$ 时 $(j,c)=(4,4)$。$N=2$ 时 $(m,j,c)=(6,0,0)$ 仍不可能，因为 $q=6>\lfloor16/3\rfloor=5$。这些边界不依赖底域是否有限。

现证两种首界。若同一 $(m,j)$ 对应 $c<c'$，则 $c'-c\ge4$、$j\ge c'$，故稳定部分较小的窗口有 $t=j-c\ge4$；(23.1) 给 $m\ge12,n\ge16$。在任何 $N\ge4$ 的实际塔内，取 $K$-独立的 $e_1,e_2,e_3,e_4$，令

$$
W_0=\bigoplus_{i=1}^4 He_i,\qquad
W_1=Ke_1\oplus Q_3,
\quad Q_3\le Ke_2\oplus Ke_3\oplus Ke_4
\text{ 如 (23.16)}.
\tag{23.20}
$$

$S_H=F$ 及 $Z_H(Q_3)=0$ 给两窗口的 $(m,j,c)$ 分别为 $(12,4,0)$、$(12,4,4)$；共同见证不可能落在该四维 $K$-子空间外，因为可用 $h_0^{-1}$。这证明第一首界，并将旧特殊实例的联合乘积计算接成每份实际 $K,H$ 均适用的形式。

对第二种，非恢复恰有 $t,q\ge1$，所以 $m=4r+3t+q\ge4$、$n\ge4r+4t+q\ge5$；由 $4\mid n$ 得 $n\ge8$。给定 (23.9) 的 $\tau,v,z$，$T=F\tau,C=0$ 满足乘法同构；商中任何非零向量的 $H$ 倍为三维，不能落入一维 $Q$，故 $Z_H(Q)=0$。$K/H$ 的基 $z+H$ 使全部截面恰按 $s\in F$ 列出。若 $xW_s=W_{s'}$，共同见证给 $xF\tau=F\tau$，所以 $x\in F^\times$，它固定每个 $F$-子空间；再比较指定商生成元的提升，得 $(s-s')z\in H$，即 $s=s'$。反向四维非恢复纤维满足 $4=4r+3t+q$、$t,q\ge1$，只能 $r=0,t=q=1$，所以全由 (23.9) 给出。$N\ge2$ 时所需 $v$ 总在原域内存在；$N=1$ 时不存在。若 $N=2$，保持 $K\tau$ 和商不动的 $K$-线性剪切仍可将不同 $s$ 互移，但乘法若固定 $\tau\ne0$ 就只能为恒等，故不能用该剪切替代原标量群。

明确的特征零对应如下。在实代数数中取正根 $a=2^{1/4}$，对 $N\in\{2,3,4\}$ 取 $\theta_N=2^{1/(4N)}$，固定

$$
F=\mathbb Q,\quad K=\mathbb Q(a),\quad
L_N=\mathbb Q(\theta_N),\quad a=\theta_N^N,\quad
H=\mathbb Qa+\mathbb Qa^2+\mathbb Qa^3.
\tag{23.21}
$$

$X^4-2$、$X^{4N}-2$ 在素数 $2$ 处 Eisenstein，故 $[K:F]=4$、$[L_N:F]=4N$、$[L_N:K]=N$；$1,a,a^2,a^3$ 为实际 $F$-基，所以 $1\notin H$。对 $N=2,3$，取 $\tau=1,v=\theta_N,z=1$，得到实际四维窗口

$$
W_s=H\oplus\mathbb Q\cdot(\theta_N+s),\qquad s\in\mathbb Q.
\tag{23.22}
$$

它们共同的实际读数为 $T=\mathbb Q,C=0,Q=\mathbb Q\cdot(\theta_N+K)$，不同参数不能由任何 $L_N^\times$ 标量相连。$N=2$ 达到 $(4,8)$；$N=3$ 给出非二幂实际次数。对 $N=4$，用 $e_i=\theta_4^{i-1}$ 及取常数系数的 $\rho:K\to\mathbb Q$ 构造 (23.20)；(23.16) 可取 $a_1=a,a_2=a^2,a_3=a^3$。此时三个共同读数为 $2$ 倍的反序系数，(23.18) 确实满射，遂在同一十六次特征零域中达到 $(12,16)$。

最后检验来源边界。对任意域，双线性公式 $uv+F$ 下降到 $\Lambda_F^2L$ 的充要条件是对角恒零，即每个 $u^2\in F$。若此条件成立且 $\operatorname{char}F\ne2$，由 $(u+1)^2-u^2-1=2u\in F$ 得所有 $u\in F$，与四次子域矛盾。因此旧全域 $\kappa$ 的平方与特征限制确有承重；本推论的线性结构没有沿用这个交替性。

所有失败可在 (23.21) 的同一 $L_3$ 中看见。$a^2\notin\mathbb Q$，所以对角输出 $a^2+\mathbb Q$ 非零。独立输入 $u=a,v=a^{-1}$ 却有 $uv=1$，因而记录为零，而 $F(u/v)=\mathbb Q(a^2)\ne\mathbb Q=F(uv)$；取 $u=1,v=a$ 的比值域又是四次而非二次。令 $U_a=\mathbb Q+\mathbb Qa$，则 $U_a\cap aU_a=\mathbb Qa$，不对 $\mathbb Q(a)$ 稳定，故不能把 (18.8) 用到任意非标量 $h=a$。

若只保留实际二次标签，定义 $\operatorname{Src}_2(W)=\{J\subseteq L:[J:F]=2,\ \exists v\in L^\times:vJ\subseteq W\}$，则 $\operatorname{Src}_2(xW)=\operatorname{Src}_2(W)$ 在任意特征仍由乘 $x$ 给出。对每个真正二次的 $J=F(h)$，$J$ 可见仍等价于 $W\cap hW\ne0$：确实，写 $h^2=bh+c$、$b,c\in F$，若 $x=hy\in W\cap hW$、$y\in W$，则 $hx=bx+cy\in W$ 且 $hx\in hW$，故该交对 $J$ 稳定，非零交即含一条 $J$ 直线；反向可见的 $vJ$ 本身包含于这个交。失去的是所有独立对都来自二次域，以及这种标签集合的旧恢复能力。

具体地，在同一 $L_3$ 中，$U_a$ 与 $U_\theta=\mathbb Q+\mathbb Q\theta_3$ 的维数均为二，且 $\operatorname{Src}_2(U_a)=\operatorname{Src}_2(U_\theta)=\varnothing$。若有 $vJ\subseteq U$，两者维数均二迫使相等；又 $1\in U=vJ$ 使 $v\in J$，于是 $U=J$ 为二次域，矛盾于 $a$ 的次数四或 $\theta_3$ 的次数十二。即使逐字保留 (18.2) 而允许任意 $F(h)$，维数二仍只容得下二次域，故两者的该集合也同为空。它们却不标量相似：比值集合 $R(xU)=R(U)$，而 $F(R(U_a))=\mathbb Q(a)$、$F(R(U_\theta))=L_3$，次数不同。故旧 (19.5) 的比值并集、来源生成域等式及已知维数下的恢复，均不能由 (23.1)–(23.8) 推出。若仅删除平方条件而保留特征二，$F=\mathbb F_2(t)$、$K=L=F(\alpha)$、$\alpha^4=t$ 也满足本条前件（取 $H=F+F\alpha+F\alpha^2$）；$X^4-t$ 在 $\mathbb F_2[t]$ 对 $t$ Eisenstein，而 $\alpha^2\notin F$，故同样不存在旧 $\kappa$。

成熟文献的覆盖范围保持明确。上引 Eliahou–Lecouvey 与 Bachoc–Serra–Zémor 覆盖普通乘积张成、配对、饱和定义和有限维稳定子；Stacks 覆盖普通图坐标。Neri–Zullo，[DOI 10.26493/2590-9770.1852.9ca](https://adam-journal.eu/index.php/ADAM/article/download/1852/1710)，Definitions 2.11、2.15，Theorems 2.13、2.19，已给任意有限次域扩张的 system、秩码与 evasive 对应；其扩张域、底域在这里分别是 $K,F$，扩张次数为四。(23.16) 的码参数为长度 $s+1$、$K$-维数 $s$、最小 $F$-秩二，其列空间为 $R_s$：校验行为 $(-a_1,\ldots,-a_s,1)$；秩一的非零码字若写成 $\xi(f_1,\ldots,f_s,f_0)$，$f_i\in F$，校验式将给 $f_0=\sum a_if_i$，与 $1,a_i$ 独立矛盾；仅取一个非零输入坐标则得到秩二。Definition 2.11 要求张成，Definition 2.15 还要求交叠指标小于环境维数，故没有用它们排除本条的零空间、一维环境或非张成余项。其 Example 2.18 使用循环 Galois 生成元；§4.2 讨论这种构造的范围，不能代替 (23.17)–(23.18) 对指定实际 $H$ 的联合核对。

Bartoli–Csajbók–Marino–Trombetti，[arXiv:2005.08401v2](https://arxiv.org/pdf/2005.08401v2)，Definition 1.1、Theorem 2.11、Proposition 4.5、Corollary 4.9、§5 的 $n=4$ 情形，覆盖有限域的交叠、直和、$2/5/8$ 块及 $8d/3$ 界；Marino–Neri–Trombetti，[arXiv:2204.11791v1，Theorem 3.3](https://arxiv.org/pdf/2204.11791v1)，覆盖有限域秩权对应；Giannoni，[arXiv:2611.08627v1，Theorem 1.1 前后及 Remark 6.3](https://arxiv.org/pdf/2611.08627v1)，明确将 $h=1<k$ 的情形列作已知或初等。本条不将这些块、数字或对应另立为新结果；增补的是它们与原窗口实际位置、全部共同提升及原 $L^\times$ 恢复条件的任意特征连接。有限底域在本条允许，旧 $K^2\subseteq F$ 排除非平凡有限底域的论证不再适用。

Gulde–Stroppel，[arXiv:1012.0502v1，Theorem 2.10(b)–(e)、§6.10](https://arxiv.org/pdf/1012.0502v1)，的特征二二次形式相似群及指定外积商作用，和 Kussin，[arXiv:0712.3274v3，Theorem 6.1(iii)、Examples 6.3](https://arxiv.org/pdf/0712.3274v3)，的无本原元四次域及 species 曲线结论，各有自身前件；本条不用它们推出任意特征的形式相似群、外积来源或曲线结论。表示同构允许的目标端 $K$-线性换基也始终区别于 (23.6) 的原域乘法。上述原始文献的这些结果并未给出固定实际 $(T,C,Q)$ 的整套原标量恢复判据；本条是对 §§20–22 的范围推论，不附历史首次性断言。$\square$

直观地说，四次域中的三个方向占了除一槽以外的全部位置；乘法配对保证这个缺槽能检测其余三个独立系数。每个非稳定共同见证于是强迫窗口保留三维，并占用一个独立的四维 $K$ 方向；完整稳定方向占四维。余项能放多少，取决于是否把某个三维 $Hx$ 整块藏进去，其容量是 (23.7)。位置读数还会漏掉每个商方向接回缺槽的偏移；同一个向量能联合修正三个方向，却不表示不同偏移都能被一个域标量消掉。这一机制只依赖实际四次乘法和有限维性；“两次相乘的记录就是二次来源”另需平方关系，不能混用。特征零例子只给出所列有限扩张中的实际子空间与标量结论，不推出 $\mathbb Z$ 在 $\mathbb Q$ 中的丢番图定义、$H10(\mathbb Q)$、Born 规则、复数域或完整量子起源。

## 追加锚（本行以下为增补区）

## 24　同一有理数八次域中的二元观察碰撞与共同见证分离

**定义 24.1（原域内带比例标签的观察）。** 固定实数中的正根 $\theta=2^{1/8}$ 及实际域 $L=\mathbb Q(\theta)$，始终使用原域乘法。窗口是 $L$ 的四维 $\mathbb Q$-子空间，所比较的等价关系恰为

$$
W'\sim W\quad\Longleftrightarrow\quad
W'=xW\text{，其中 }x\in L^\times.
\tag{24.1}
$$

对窗口 $W$ 定义

$$
\begin{aligned}
R(W)&=\{u/v:u,v\in W,\ v\ne0\}\subseteq L,\\
d_W(r)&=\dim_{\mathbb Q}(W\cap rW),\qquad r\in L^\times,\\
J_W(r,s)&=\dim_{\mathbb Q}(W\cap rW\cap sW),
\qquad (r,s)\in(L^\times)^2.
\end{aligned}
\tag{24.2}
$$

$R(W)$ 包含 $0$。二元观察是保留原比例标签的整份函数 $r\mapsto d_W(r)$，不是只记各维数出现几次。$J_W(r,s)$ 要求同一个 $z\in L$ 同时满足 $z,z/r,z/s\in W$；其非零性要求这样的 $z\ne0$，不允许为两个比例各选一个不相关的 $z$。全部标签和标量均取原 $L$，不重标比例、不扩域，也不用一般线性等价替代 (24.1)。

**命题 24.2（四维成对反例及指定三重交叠）。** 在定义 24.1 的同一实际域中取

$$
U=\operatorname{span}_{\mathbb Q}\{1,\theta,\theta^3,\theta^4\},\qquad
V=\operatorname{span}_{\mathbb Q}\{1,\theta,\theta^2,\theta^5\}.
\tag{24.3}
$$

两者均为四维，且

$$
\begin{gathered}
d_U(r)=d_V(r)\quad\text{对每个 }r\in L^\times,\qquad R(U)=R(V),\\
V\ne xU\quad\text{对每个 }x\in L^\times,\\
U\cap\theta U\cap\theta^3U=\mathbb Q\theta^4,\qquad
V\cap\theta V\cap\theta^3V=0.
\end{gathered}
\tag{24.4}
$$

所以完整二元观察，甚至与 $R(W)$ 一同给出，也不能在原域全部四维窗口上恢复 (24.1) 的轨道；而 $J_U(\theta,\theta^3)=1$、$J_V(\theta,\theta^3)=0$ 分开这一对轨道。

证明。$X^8-2$ 在素数 $2$ 处 Eisenstein，故 $[L:\mathbb Q]=8$，且

$$
1,\theta,\theta^2,\ldots,\theta^7
\tag{24.5}
$$

是原域的一组 $\mathbb Q$-基。这同时证明 (24.3) 的两个实际维数。令 $\lambda:L\to\mathbb Q$ 取 (24.5) 中的 $\theta^7$ 系数，记 $B(a,b)=\lambda(ab)$。所用非退化乘法配对是成熟输入，见 Bachoc–Serra–Zémor，[*Revisiting Kneser's theorem for field extensions*，arXiv:1510.01354v2，§2.2，式 (2)](https://arxiv.org/pdf/1510.01354v2)。在此实际基上，

$$
B(\theta^i,\theta^j)=
\begin{cases}1&i+j=7,\\0&i+j\ne7,\end{cases}
\qquad 0\le i,j\le7.
\tag{24.6}
$$

确实 $i+j\le14$，达到八时用 $\theta^8=2$ 约去，只留下至多六次项。因此矩阵为反对角单位矩阵；消去与 $1,\theta,\theta^3,\theta^4$ 的配对，恰消去次数 $7,6,4,3$ 的系数，给出原域中的准确对应 $U^\perp=V$。

现在固定任意 $r\in L^\times$，不限制其在 (24.5) 中的系数。乘法自伴随及普通正交补恒等式给

$$
\begin{aligned}
(U+rU)^\perp&=V\cap r^{-1}V,\\
d_U(r)&=8-\dim_{\mathbb Q}(U+rU)
=\dim_{\mathbb Q}(V\cap r^{-1}V)
=d_V(r).
\end{aligned}
\tag{24.7}
$$

最后一步是乘以同一个 $r$，将 $V\cap r^{-1}V$ 同构到 $rV\cap V$。这是半维对偶的既有维数推导在 (24.3) 上的直接应用，不是一条新的一般对偶定理。对每个非零 $r$，条件 $r=u/v$、$u,v\in W\setminus\{0\}$ 恰等价于 $0\ne u=rv\in W\cap rW$。因此

$$
R(W)=\{0\}\cup\{r\in L^\times:d_W(r)>0\},
\qquad W\in\{U,V\},
\tag{24.8}
$$

从而得到包含零的实际集合等式 $R(U)=R(V)$。这一步不涉及有限域计数或距离直方图。

为排除全部原域标量，假设 $xU=V$。因 $1,\theta,\theta^3\in U$，有 $x,\theta x,\theta^3x\in V$。先由 $x\in V$ 唯一写成

$$
x=a_0+a_1\theta+a_2\theta^2+a_5\theta^5,
\qquad a_0,a_1,a_2,a_5\in\mathbb Q.
$$

比较 $\theta x\in V$ 在 (24.5) 中的 $\theta^3,\theta^6$ 系数，得 $a_2=a_5=0$；再比较 $\theta^3x=a_0\theta^3+a_1\theta^4\in V$，得 $a_0=a_1=0$。于是 $x=0$，与 $x\in L^\times$ 矛盾。这里直接约束任意 $x$ 的全部可能系数，没有把标量限制为单项式。

最后仍用同一实际基，$\theta^3V=\operatorname{span}_{\mathbb Q}\{1,\theta^3,\theta^4,\theta^5\}$，其中常数项来自 $\theta^8=2$。逐项相交得到

$$
\begin{aligned}
U\cap\theta U&=\operatorname{span}_{\mathbb Q}\{\theta,\theta^4\},&
U\cap\theta^3U&=\operatorname{span}_{\mathbb Q}\{\theta^3,\theta^4\},\\
V\cap\theta V&=\operatorname{span}_{\mathbb Q}\{\theta,\theta^2\},&
V\cap\theta^3V&=\operatorname{span}_{\mathbb Q}\{1,\theta^5\}.
\end{aligned}
\tag{24.9}
$$

第一行的两个平面交于 $\mathbb Q\theta^4$，第二行的两个平面交于零。这证明 (24.4) 的最后两式。对任意 $x\in L^\times$，乘以 $x$ 将 $W\cap rW\cap sW$ 同构到 $xW\cap r(xW)\cap s(xW)$；二元交叠也如此，且比值中的 $x$ 可约去。因此 $R,d,J$ 均保留 (24.1) 的轨道，指定 $J$ 的差异确实分开这两个轨道。$\square$

文献与实际差额。Gluesing-Luerssen–Lehmann，[*Distance Distributions of Cyclic Orbit Codes*，arXiv:1912.05522v1，Definition 3.1(4)、Proposition 3.2](https://arxiv.org/pdf/1912.05522v1)，已在 $\mathbb F_{q^n}/\mathbb F_q$ 中把分式支持与非零标量交叠相联。其分式取非零分子、分母，并在底域非零标量下射影化，轨道由 $\mathbb F_{q^n}^\times$ 作用；这里 (24.8) 使用原 $L$ 内逐字相等的分式并补上零。Castello–Gluesing-Luerssen–Polverino–Zullo，[*Quasi-optimal cyclic orbit codes*，DOI 10.1007/s10623-025-01751-4，式 (4)、(5)、Proposition 4.1](https://doi.org/10.1007/s10623-025-01751-4)，已将 $U\times U$ 的射影线点权写成 $\dim(U\cap\alpha U)=\dim(U\cap\alpha^{-1}U)$，并逐每个 $\alpha\in\mathbb F_{q^n}^\times$ 给出标量乘法与迹正交补的对应。这比只有距离分布的陈述更精确；本条不把这一机制算作新增，也不将其有限域计数结论用于 $\mathbb Q$。

§20 所引 Ueoka–Nagi–Akari–Sui，[*Weak Vishik Equivalence and Linear 2-Basis Blindness for Totally Singular Quadratic Forms*，Zenodo 21758447，Lemma 4.1、Theorem 4.2](https://zenodo.org/records/21758447)，已经给出乘法配对及半维正交补对所有非零标量的交叠维数相等。其全文二次型语境为特征二、$k=K^2$；(24.7) 只复用不依赖该特征的维数推导，不搬用添平方根的二次型解释。其 Lemma 6.1 的不相似对是 $K=\mathbb F_2(s,t,u,v)$、$k=K^2$ 中的两个八维值空间，排除的是全部 $K^\times$ 标量；Proposition 6.5 用实际四次中间域 $k(t,su)$ 的乘积张成维数分离它们。它没有给出 (24.3) 的有理数八次域四维对，或 (24.9) 的指定三重交叠。Bachoc–Serra–Zémor 的上述配对适用于任意域扩张，不要求可分性；它提供 (24.7) 所需的乘法自伴随性，不提供这对窗口的选取与非相似性。

相对于这些指定原文及本卷 §§18–23，本条新增的数学内容限于 (24.3) 这一个实际成对反例：原 $\mathbb Q(2^{1/8})$ 中全部比例标签上的相同二元观察、全部原域标量下的不相似，以及 (24.9) 的共同见证分离。半维对偶、乘法配对、分式支持与普通基论证只作中间工具；不主张它们的新颖性，也不据这些来源范围主张全球首次。§19 的恢复结论带有特征二及平方条件，§23 的位置观察则固定 $H$ 并保留实际 $T,C,Q$；它们都没有断言定义 24.1 的二元函数足以恢复这里的四维窗口。

白话说，二元读数逐个比例回答“窗口与它的这次倍乘共享几维”，甚至让每个原比例都保留名字。这对窗口对每一道这样的提问给出相同数字，可用的全部比值也相同；但一个原域数无法把整个窗口一起搬成另一个。丢掉的是不同提问之间的见证如何重合：在 $U$ 中，$z=\theta^4$ 同时以 $z/\theta=\theta^3$、$z/\theta^3=\theta$ 留在窗口内；在 $V$ 中，(24.9) 的两个二元见证平面各自仍有二维，却没有共同非零向量。$J$ 保留的是同一个原向量同时通过两次比例要求的关系，恰好切开二元观察中容纳这两个轨道的同一纤维。

这里的分离仅针对这一对四维窗口。它既没有证明全部函数 $(r,s)\mapsto J_W(r,s)$ 能恢复原域全部四维窗口，也没有给出三维窗口在完整二元观察下的恢复或反例，更未证明三重观察是全局恢复所需的最小阶数。这些恢复命题在本条均未解决。本条的“同源”只指固定同一实际域及其乘法中的代数实现；它没有从代数入射推出 Born 规则、复 Hilbert 空间、量子测量公理、实际可取得的控制、$\mathbb Z$ 在 $\mathbb Q$ 中的丢番图定义或 $H10(\mathbb Q)$。这些结论各需另给相应的概率、内积、操作或算术桥梁。

## 追加锚（本行以下为增补区）

## 25　原有理数八次域中全部四维窗口的三重观察恢复

**定义 25.1（稳定子与最小正行）。** 沿用定义 24.1 的实际 $L=\mathbb Q(\theta)$、$\theta=2^{1/8}>0$、四维窗口及逐标签函数 $d_W,J_W$，记

$$
E_W=\{a\in L:aW\subseteq W\},\qquad e_W=\dim_{\mathbb Q}E_W,\qquad
\delta_W=\min\{d_W(r):r\in L^\times,\ d_W(r)>0\}.
\tag{25.1}
$$

因 $d_W(1)=4$，此最小值存在。称满足 $d_W(r_0)=\delta_W$ 的原标签 $r_0$ 为最小正行的标签；对该标签仅由观察定义

$$
T_{J_W,r_0}=\{0\}\cup\{s^{-1}:s\in L^\times,\ J_W(r_0,s)>0\}.
\tag{25.2}
$$

**定理 25.2（全部窗口的恢复与单行支持分离）。** 对定义 24.1 的每一个四维窗口 $W$，$E_W$ 是 $L$ 的子域，且

$$
\delta_W=e_W\in\{1,2,4\}.
\tag{25.3}
$$

任取最小正行标签 $r_0$ 及证明中任一 $0\ne z\in W\cap r_0W$，则 $W\cap r_0W=E_Wz$，并有原域内的等式

$$
T_{J_W,r_0}=z^{-1}W.
\tag{25.4}
$$

特别地，对任意另一个四维窗口 $V\subseteq L$，即使未假设 $r_0$ 对 $V$ 也是最小正行，仍有

$$
\bigl[\ \forall s\in L^\times,\ J_V(r_0,s)>0\ \Longleftrightarrow\ J_W(r_0,s)>0\ \bigr]
\quad\Longleftrightarrow\quad \exists x\in L^\times,\ V=xW.
\tag{25.5}
$$

因此，对所有这样的 $W,V$，

$$
\bigl[\ \forall(r,s)\in(L^\times)^2,\ J_V(r,s)=J_W(r,s)\ \bigr]
\quad\Longleftrightarrow\quad \exists x\in L^\times,\ V=xW.
\tag{25.6}
$$

证明。以下固定任意实际 $W$，缩写 $E,e,\delta$。先消费有限维稳定子的通常事实：$E$ 包含 $\mathbb Q$ 且对加法、减法、乘法封闭；若 $0\ne a\in E$，则乘以 $a$ 在有限维 $W$ 上单射，故 $aW=W$，从而 $a^{-1}W=W$。所以 $E$ 成域，$W$ 是 $E$-向量空间，$e\mid4$；又因乘法交换，$W\cap rW$ 对每个 $r$ 都是 $E$-线性的。因此每个正交叠维数均为 $e$ 的正倍数，$\delta\ge e$。此处所用稳定子事实见 Bachoc–Serra–Zémor，[arXiv:1510.01354v2，§3，Lemma 13 后的有限维说明](https://arxiv.org/pdf/1510.01354v2)。若 $\delta=1$，已得 $e=1$。以下设 $\delta\ge2$，证明反向不等式。

使用 (24.5) 的基将 $L$ 写成 $\mathbb Q^8$。取列空间为 $W$ 的秩四矩阵 $B\in M_{8,4}(\mathbb Q)$，并取秩四矩阵 $H\in M_{4,8}(\mathbb Q)$ 使 $\ker H=\operatorname{im}B$。令 $M_a$ 是原域乘以 $a$ 的 $8\times8$ 矩阵。乘法表由 $\theta^8=2$ 给出整数结构常数，$M_a$ 对 $a$ 的八个坐标线性。将 $4\times4$ 矩阵的条目排成十六个坐标，得到一个 $16\times8$ 有理矩阵 $A$，其线性映射为

$$
a\longmapsto HM_aB,\qquad \ker_{\mathbb Q}A=E,\qquad
\operatorname{rank}_{\mathbb Q}A=8-e.
\tag{25.7}
$$

选取 $B,H$ 各一个非零四阶子式和 $A$ 的一个非零 $(8-e)$ 阶子式。取正偶数 $D$，使它被所选子式分子的每个素因子及 $B,H,A$ 全部条目分母的每个素因子整除。置 $R=\mathbb Z[1/D]$。于是这些矩阵定义于 $R$；对每个 $p\nmid D$，所选子式保持非零，而 $A$ 的全部更大子式恒为零，故约化后的 $B_p,H_p,A_p$ 的秩分别仍为 $4,4,8-e$。又 $HB=0$ 保持为 $H_pB_p=0$，所以 $\ker H_p=\operatorname{im}B_p$。这里只用了有限多个分母和子式。

还须把所有正交叠的下界传给有限域的全部新参数。令 $X,Y$ 为各有四个坐标的独立变量，令 $u=BX,v=BY$，并在 $R[X,Y]$ 上组成

$$
N(X,Y)=[\,M_vB\mid M_uB\,].
\tag{25.8}
$$

对所有非零有理向量 $X,Y$，$u,v\in W\setminus\{0\}$，且 $u\in W\cap(u/v)W$，故

$$
\operatorname{rank}N(X,Y)=\dim_{\mathbb Q}(vW+uW)
=8-d_W(u/v)\le8-\delta.
\tag{25.9}
$$

每个 $(8-\delta+1)$ 阶子式因此在 $(\mathbb Q^\times)^8$ 上恒零。逐变量使用一元非零多项式只有有限个根，得这些子式全是零多项式；它们在 $R$ 中的系数也全为零。因此对每个 $p\nmid D$，(25.8) 的约化在全部 $X,Y\in\mathbb F_p^4$ 上均有秩至多 $8-\delta$。恒等式对有限域的全部新参数与比值同时成立，无须为无限多个比例标签逐个排除素数。

现在为这个有限的坏素集选择使约化仍为域的素数。令 $P$ 为 $D$ 的所有奇素因子的乘积，空积取一。数 $4P^2+1$ 的每个素因子 $\ell$ 均不整除 $2P$，且 $-1$ 是模 $\ell$ 的平方，故 $\ell\equiv1\pmod4$；又 $4P^2+1\equiv5\pmod8$，其素因子中至少一个 $p\equiv5\pmod8$。此 $p\nmid D$，所以在任意上述有限坏素集外均可选到所需素数。

对该 $p$，二次互反律的补充公式给出 $2$ 在 $\mathbb F_p$ 中非平方。因 $p-1$ 的二部分为四，$2$ 的乘法阶的二部分恰为四。若 $\alpha^8=2$ 是代数闭包中的任一根，则 $\operatorname{ord}(\alpha^8)=\operatorname{ord}(\alpha)/\gcd(\operatorname{ord}(\alpha),8)$，故 $\operatorname{ord}(\alpha)$ 的二部分恰为三十二。另一方面，$p\equiv5\pmod8$ 蕴含 $p^4\equiv17\pmod{32}$、$p^8\equiv1\pmod{32}$，所以 $p$ 模三十二的乘法阶为八。设 $f=[\mathbb F_p(\alpha):\mathbb F_p]$，则 $32\mid p^f-1$ 强迫 $8\mid f$；而 $\alpha$ 满足八次多项式，故 $f\le8$。于是 $f=8$，$T^8-2$ 在 $\mathbb F_p[T]$ 中不可约，

$$
K_p=\mathbb F_p[T]/(T^8-2)\cong\mathbb F_{p^8}.
\tag{25.10}
$$

在此域中令 $W_p=\operatorname{im}B_p$，则 $\dim_{\mathbb F_p}W_p=4$。由于原乘法矩阵的条目按同一整数乘法表约化，(25.7) 的约化恰为 $a\mapsto H_pM_aB_p$，其核恰是原约化窗口的整个稳定子

$$
E_p=\{a\in K_p:aW_p\subseteq W_p\},\qquad
\dim_{\mathbb F_p}E_p=8-\operatorname{rank}A_p=e.
\tag{25.11}
$$

任意 $r\in K_p^\times$ 若 $W_p\cap rW_p\ne0$，可取 $0\ne u\in W_p\cap rW_p$ 并置 $v=r^{-1}u\in W_p\setminus\{0\}$，从而 $r=u/v$。写 $u=B_pX,v=B_pY$，由 (25.8)–(25.9) 的多项式约化及域内乘法可逆，得到 $\dim_{\mathbb F_p}(W_p\cap rW_p)\ge\delta$。因此没有遗漏任何有限域中的新正交叠标签。

取实际子空间 $U_p=W_p\times W_p\subseteq K_p^2$，其 $\mathbb F_p$-维数为八，且张成 $K_p^2$。在 $\mathrm{PG}(1,p^8)$ 中，$U_p$ 定义的线性集的两个坐标轴点权均为四；其余点 $K_p(a,b)$（$ab\ne0$）的点权，借 $t\mapsto ta$，恰为 $\dim_{\mathbb F_p}(W_p\cap(a/b)W_p)$。所以最小正点权 $w$ 满足 $w\ge\delta\ge2$。应用 Csajbók–Marino–Pepe，[arXiv:2306.07488v2，Theorem 1](https://arxiv.org/pdf/2306.07488v2)，参数精确为 $q=p,n=8,r=2,a=1$，rank $an=8$，得到 $w\mid8$ 且原 $U_p$ 本身对 $\mathbb F_{p^w}$ 线性。于是对任意 $c\in\mathbb F_{p^w}$ 及 $x\in W_p$，$c(x,0)\in U_p$，即 $cx\in W_p$；故 $\mathbb F_{p^w}\subseteq E_p$。结合 (25.11)，

$$
e\ge w\ge\delta\ge e,
\tag{25.12}
$$

从而 $\delta=e$，证明 (25.3)。此处 Theorem 1 没有 $q\ge n$ 前件；带有该前件、允许改用另一子空间定义同一点集的 Theorem 2 未被使用。也无需保存原域的最小交叠见证或预先证明约化最小值恰为 $\delta$。

回到原 $L$。由 $W\cap r_0W$ 对 $E$ 线性及其 $\mathbb Q$-维数为 $e$，任取其中的 $z\ne0$ 即得 $W\cap r_0W=Ez$。对每个原 $s\in L^\times$，$Ez\cap sW\ne0$ 等价于存在 $c\in E^\times$ 使 $cz/s\in W$；因 $W$ 对 $E$ 及其逆元封闭，这又等价于 $z/s\in W$。因此

$$
J_W(r_0,s)>0\ \Longleftrightarrow\ z/s\in W,\qquad
\{0\}\cup\{s^{-1}:J_W(r_0,s)>0\}=z^{-1}W,
\tag{25.13}
$$

证明 (25.4)。$z$ 只在证明中选择；(25.2) 的输入没有获得它或实际交空间，且输出集合、取逆及缩放均留在原 $L$。

为证 (25.5) 的充分性，设两行支持相等。由 $J_W(r_0,1)>0$，得 $V\cap r_0V\ne0$，取其中任一 $y\ne0$。对任意 $v\in V\setminus\{0\}$，令 $s=y/v$，则 $y\in V\cap r_0V\cap sV$，故 $J_V(r_0,s)>0$；支持相等和 (25.13) 给出 $v/y=s^{-1}\in z^{-1}W$。连同零，得到 $y^{-1}V\subseteq z^{-1}W$；两者都是四维 $\mathbb Q$-子空间，故相等，$V=(y/z)W$，其中 $y/z\in L^\times$。此包含—等维论证没有要求 $V\cap r_0V$ 最小。反之，乘以同一个 $x\in L^\times$ 同构全部 $W\cap rW\cap sW$ 与 $xW\cap r(xW)\cap s(xW)$，所以标量相似保持整份 $J$，也保持指定行支持。最后，整份 $J$ 给出 $d_W(r)=J_W(r,1)$，因而给出 $\delta$ 及最小正行标签的集合；两份 $J$ 相等时可取同一个 $r_0$，由 (25.5) 得 (25.6)。$\square$

文献对应与实质差额。Gluesing-Luerssen–Lehmann，[*Distance Distributions of Cyclic Orbit Codes*，arXiv:1912.05522v1，Definition 2.1、Definition 3.1(4)、Proposition 3.2](https://arxiv.org/pdf/1912.05522v1)，已给有限域稳定子子域、分式支持与非零交叠的对应；Bachoc–Serra–Zémor 的上述原文给普通域扩张中的有限维稳定子事实。CMP 的上述 Theorem 1 已承担有限域最小正权的全部线性结论；标准子式、有限域乘法阶和一条域直线的支持取逆也仅在本证明中消费，不另立为新基础。本条的仓内推导（repo-derived）内容是 (25.7)–(25.12) 在固定实际有理数八次域上连接全部四维窗口的迁回论证，以及由此得到的 (25.3)–(25.6) 全量词恢复。所列原文给出的成熟机制和 §24 的一对窗口分离均未包含这一整体结论；本条不据此作全球首次性断言。

白话说，最窄的非零共享部分恰好是一条稳定子域直线。沿它固定第一道比例要求后，第二道要求能否通过，已足以把窗口的所有元素逐一列成某个共同缩放后的集合；隐藏向量只解释这个共同缩放，无须交给观察者。证明中迁到有限域时，两道关口分别控制“稳定子有没有偷偷增维”和“新出现的比例有没有漏检”：前者由完整线性核保持秩解决，后者由对所有参数恒真的子式解决。恢复任意竞争窗口时，只需它在该行有一个共同非零向量，所得包含再由四维等维性变成相等。

这里成立的是整份无限、无噪声、逐标签精确读数的集合论可识别性，没有给出有限查询、有效找到最小正行、最小有限标签菜单、噪声鲁棒性或实际取得方法。结论限于定义 24.1 的原 $L$ 与四维窗口，不扩大为任意域任意维数的 $\delta=e$、三维二元恢复或最小观察阶数；也不推出 Born 规则、复 Hilbert 空间、测量、张量或控制公理，以及 $\mathbb Z$ 在 $\mathbb Q$ 中的丢番图定义或 $H10(\mathbb Q)$。

## 追加锚（本行以下为增补区）
