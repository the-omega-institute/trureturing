# 续篇：AURIC FIB ATOM 的隐藏坐标、kappa-荷与 5040 编码的统一

**Reference input: open.** 本卷保存完整用户供文，包含全部声明、证明、例子、表格、项目对应和拟议接口。原文的定理及证明语言归属开放参考输入；本卷没有新增 Lean、Blueprint、Reg 或 Frozen 声明。Lean 声明、证明项及其经内核核验的公理闭包承载本库形式系统内的数学真值。

**来源。** Author kind: mixed user-supplied material; original author and model unknown. Receipt date: 2026-10-10. 来源标识为本会话供文 auric-fib-atom-kappa-charge-exponent-fibers-and-golden-norm-readout。接收原文 SHA-256 为 `8657cbfa09d620147d11ac89824a946003bec0a2de223adcc05f3fe52dd773d9`，字节数为 18865。全部原句与公式内容保留，只规范 Markdown 数学入口、标题层级和结构空行。声明地址用于本文定位。按用户指定，本卷是纯理论添加，不运行消化，不新增 atom 或覆盖主张。

**既有结果与归属。** 供文关于 dev、PR 和公开研究列表的当前性归属其引用的历史快照，不认证移动分支的交付状态。线性核、运输环空间、Zeckendorf 唯一性、Caratheodory 表示和 finite-instrument 观测方法属于既有数学；此处保留其在指定 AURIC 合同中的综合推导，不将重述计作原创。参见 [Output-Resolved Instrument Closure](AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md)、[Boundary, Transport Fibers and Loop Closure](AURIC_FIB_ATOM_BOUNDARY_TRANSPORT_FIBERS_AND_LOOP_CLOSURE.md) 及 [Joint Projection, Multiwindow Order and Response Fibers](AURIC_FIB_ATOM_JOINT_PROJECTION_MULTIWINDOW_ORDER_AND_RESPONSE_FIBERS.md)。本文未认证抽象模型的 native 实现、资源等价或物理解释。

## 编者限定与开放义务

以下限定同完整供文分开；它们不替代原句，也不认证原文定理。

- **Q1** （§§1、9）delta_null+delta_13=delta_1+delta_3 仅指一阶投影商中的相等，不是完整 signed measures 相等。pi_prob 的 kernel 是归一化仿射空间的零质量差核，不能把单纯形当作线性空间；整数层的 kernel 在 Z^4 中计算，再同非负盒约束相交。
- **Q2** （§2）独立截面除法要求 1-Z>0；Z=1 时条件律未定义。实际概率纤维可为空或单点。kappa 是边坐标，相对固定边界下规范点的差才给出零边界环流系数；名称荷不证明量子化或物理守恒。
- **Q3** （§§3–4）指数取非负整数，盒上界取非负整数并另外要求 0<=v<=A_3。整数区间也可能为空；一次移动需要 a_2,a_5>=1，并遵守目标容量。概率实区间与整数盒纤维只有相似的核结构，本文未给出全局或自然的范畴同构。
- **Q4** （§4 的 5040 情形）若指数域是 5040 的除数盒 A_2=4,A_3=2,A_5=1,A_7=1，则边界 (5,2,2) 的下界 max(0,5-4,2-1)=1、上界 1，只有 5040 一点，7200 不合法。两个候选例要求放宽到允许 a_2=5,a_5=2 的域，并另声明 a_7<=1；仅知道基础叶投影并不自动提供该盒。
- **Q5** （§5）U 是专门定义的编码，不是从实际整数 n 的乘法结构自动产生的天然 golden-ring 嵌入；因子 1 使 a_2 被 U 遗忘。对非负指数 N(U)=(-1)^(a_3)5^(a_7) 非零，v_5 才按正整数范数绝对值定义。p_13、a_7 与 v_5 是不同载体上的量，盒装连等式是类比，除 a_7=v_5 外没有共同来源证明数值相等。
- **Q6** （§§5–6）R(h) 非零的 iff 需要新增 R 线性，或在仿射纤维上的限制为已知非零斜率；一般非线性读出不能通过在带符号方向 h 上的一个值判全局单射。norm 的恢复依靠其组合读数恰为 a_7 的专门公式，不能只把非线性范数当作线性 signed-law 读口。
- **Q7** （§6）固定边界已知且实际纤维有两个点时，一维线性对比非零给出律级识别；单点纤维无需新读出。统计可识别、有限样本恢复、可取得和资源成本是不同结论。未来响应仍须同一事件空间和固定共同核。
- **Q8** （§7）运输 graph 是左右顶点分开的二部图；pair-state 名称相同的左右顶点不合并。若合并成有向 overlap graph，V、c 和核都改变，010 也不能沿用二部桥的论证。square cycle 是有符号的零边界关系，不是正向概率轨迹。
- **Q9** （§§7、10）E-V+c 是完整允许支持的线性核维数，实际非负纤维可能在较低维面。长窗口自由内部词 q 要求外端都可取值，条件独立还要求该分量质量正。称三态应读作三位置或三 pair-state，ATOM 有五态。
- **Q10** （§8）嵌套纤维须沿同一实际对象的相容读数 b_t=A_t b_(t+1) 比较；任意不同 b 的纤维不嵌套。核维数下降 r_t 是线性 rank-nullity，实际纤维可为空或退化；对于实际方向的秩应在其仿射切空间上取。观察过滤是数学时间模型，不是物理时间产生的证明。
- **Q11** （§11）任意基础 pi 的核不自动等于任意支持 graph 的 circulation kernel，必须有已证 boundary-map adapter。多维纤维联合恢复需要响应族共同核同实际切空间交为零；逐个基方向各自非零并不充分。未提供 adapter 时四层分解只是拟议接口。
- **Q12** （§§11–12）intersection(ker R) 表示经新增读出后仍然隐藏的部分，原始隐藏空间则是基础 projection kernel。完整未来应使用逐输出 M_(a,o) 的合法词与 Stop/guard。范数、概率、指数、未来律的共同实现与资源等价均未由同名 kappa 证明，形式化对象保持拟议状态。

## 完整供文

## 续篇：AURIC FIB ATOM 的隐藏坐标、$\kappa$-荷与 5040 编码的统一

这一轮继续推进一个更深的结论：

> AURIC 金字塔中的 $\kappa$，以及 5040 乘法编码中的 $a_7$，实际上是同一种“基础投影无法看到、需要额外读出恢复”的纤维坐标。

它们出现于不同空间：

- AURIC 概率空间：$\kappa=p_{13}$；
- Fibonacci 乘法指数空间：$\kappa=a_7$；
- Golden ring 范数空间：$\kappa=v_5(|N(U)|)$；
- 未来动态空间：$\kappa$ 由响应对比 $J_{\mathscr L}$ 是否非零决定。

因此可以提出一个统一命题：

$$
\boxed{
\text{同一个隐藏关系，可以在不同观察切面上表现为概率、指数、范数或未来响应。}
}
$$

当前 trureturing 的公开主线正在把 information escape、FIB escape-audit、AURIC FIB pyramid、acquired circulation 与 generated boundary laws 接到一起。公开 PR 列表中已经出现“AURIC FIB pyramid to escape dynamics and thermodynamic action”“verified FIB escape-audit applications”以及“acquired circulation to generated boundary laws”等工作线。[GitHub](https://github.com/the-omega-institute/trureturing/pulls?utm_source=chatgpt.com) 项目 README 对 information escape 的定义也正是：确定哪些状态在当前读出下不可区分，增加何种读出可以恢复区别，以及恢复后还有哪些信息继续逃逸。[GitHub](https://github.com/the-omega-institute/trureturing?utm_source=chatgpt.com)

---

## 1. 一、定义：AURIC 的关系矩阵

仍沿用：

$$
F[\mathrm{null}]=\mathrm{null},
\qquad
F[1]=[2],
\qquad
F[2]=[3],
\qquad
F[3]=[5],
\qquad
F[1,3]=[2,5].
$$

五个状态依次记为

$$
\Omega_{\mathrm{FIB}}=
\{
\mathrm{null},
1,
2,
3,
13
\}.
$$

对应概率向量

$$
p=
(p_0,p_1,p_2,p_3,p_{13}).
$$

一阶金字塔投影为

$$
X=p_1+p_{13},
$$

$$
Y=p_3+p_{13},
$$

$$
Z=p_2.
$$

加入归一化以后，定义线性关系矩阵

$$
A_{\mathrm{FIB}}=
\begin{pmatrix}
1&1&1&1&1\\
0&1&0&0&1\\
0&0&0&1&1\\
0&0&1&0&0
\end{pmatrix}.
$$

于是

$$
A_{\mathrm{FIB}}p=
\begin{pmatrix}
1\\
X\\
Y\\
Z
\end{pmatrix}.
$$

---

### theorem 1.1: 定理 1：AURIC 隐藏空间是一维

有

$$
\ker A_{\mathrm{FIB}}=
\operatorname{span}
\left\{
(1,-1,0,-1,1)
\right\}.
$$

#### 证明

设

$$
h=(h_0,h_1,h_2,h_3,h_{13})
$$

满足

$$
A_{\mathrm{FIB}}h=0.
$$

由后三个坐标：

$$
h_1+h_{13}=0,
$$

$$
h_3+h_{13}=0,
$$

$$
h_2=0.
$$

由第一行：

$$
h_0+h_1+h_2+h_3+h_{13}=0.
$$

令

$$
h_{13}=t.
$$

则

$$
h_1=-t,\qquad
h_3=-t,\qquad
h_2=0.
$$

代回归一化关系：

$$
h_0-t-t+t=0,
$$

故

$$
h_0=t.
$$

因此

$$
h=t(1,-1,0,-1,1).
$$

证毕。

---

这个方向满足

$$
\delta_{\mathrm{null}}
+
\delta_{13}=
\delta_1+\delta_3
$$

在所有一阶投影下完全相同。

这里出现的不是普通的坐标遗漏，而是一个严格的关系核：

$$
\boxed{
h_{\mathrm{AURIC}}=
\delta_{\mathrm{null}}
-\delta_1-\delta_3+\delta_{13}.
}
$$

---

## 2. 二、概率纤维中的 $\kappa$

令

$$
\kappa=p_{13}.
$$

那么

$$
p_0=1-X-Y-Z+\kappa,
$$

$$
p_1=X-\kappa,
$$

$$
p_2=Z,
$$

$$
p_3=Y-\kappa,
$$

$$
p_{13}=\kappa.
$$

所以概率纤维为

$$
\mathcal F_{\mathrm{prob}}(X,Y,Z)=
\left\{
p(\kappa):
\kappa_-\le\kappa\le\kappa_+
\right\},
$$

其中

$$
\kappa_-=\max(0,X+Y+Z-1),
$$

$$
\kappa_+=\min(X,Y).
$$

此处的下界来自空状态 $p_0$ 的非负性，上界来自单态 $p_1,p_3$ 的非负性。

定义

$$
\Delta=
p_0p_{13}-p_1p_3.
$$

代入上式：

$$
\Delta=(1-Z)\kappa-XY.
$$

所以

$$
\kappa_0=\frac{XY}{1-Z}
$$

是条件独立截面。

---

## 3. 三、整数 Fibonacci 指数中的同一个隐藏方向

现在转向 5040 结构。

定义指数向量

$$
a=(a_2,a_3,a_5,a_7)
$$

并考虑乘法数

$$
n=2^{a_2}3^{a_3}5^{a_5}7^{a_7}.
$$

定义基础叶子投影：

$$
u=a_2+a_7,
$$

$$
v=a_3,
$$

$$
w=a_5+a_7.
$$

写成矩阵：

$$
A_{\mathrm{int}}=
\begin{pmatrix}
1&0&0&1\\
0&1&0&0\\
0&0&1&1
\end{pmatrix}.
$$

于是

$$
A_{\mathrm{int}}
\begin{pmatrix}
a_2\\a_3\\a_5\\a_7
\end{pmatrix}=
\begin{pmatrix}
u\\v\\w
\end{pmatrix}.
$$

---

### theorem 3.1: 定理 2：5040 乘法编码的隐藏空间也是一维

有

$$
\ker A_{\mathrm{int}}=
\operatorname{span}
\left\{
(-1,0,-1,1)
\right\}.
$$

#### 证明

设

$$
A_{\mathrm{int}}h=0.
$$

则

$$
h_2+h_7=0,
$$

$$
h_3=0,
$$

$$
h_5+h_7=0.
$$

令

$$
h_7=t.
$$

则

$$
h_2=-t,\qquad
h_3=0,\qquad
h_5=-t.
$$

因此

$$
h=t(-1,0,-1,1).
$$

证毕。

---

这个整数隐藏方向表示：

$$
(a_2,a_3,a_5,a_7)
\longmapsto
(a_2-1,a_3,a_5-1,a_7+1)
$$

不会改变

$$
(u,v,w).
$$

因为

$$
(a_2-1)+(a_7+1)=a_2+a_7,
$$

$$
(a_5-1)+(a_7+1)=a_5+a_7.
$$

但是它会改变实际乘法数：

$$
2^{a_2}5^{a_5}7^{a_7}
\longmapsto
2^{a_2-1}5^{a_5-1}7^{a_7+1}.
$$

两者比值为

$$
\frac{7}{10}.
$$

所以 $7$ 与 $10$ 具有相同的基础叶子投影：

$$
C(7)=(1,0,1),
$$

$$
C(10)=(1,0,1),
$$

但它们的隐藏坐标不同：

$$
\kappa(7)=1,
\qquad
\kappa(10)=0.
$$

这与概率 AURIC 中“相同 $(X,Y,Z)$，不同 $\kappa$”完全同构于同一种关系结构：

$$
\boxed{
\text{基础投影相同}
\quad+\quad
\text{内部复合关系不同}.
}
$$

---

## 4. 四、双纤维定理：概率 $\kappa$ 与指数 $\kappa$

### 定义 1：整数编码纤维

固定

$$
(u,v,w),
$$

定义

$$
\kappa=a_7.
$$

则

$$
a_2=u-\kappa,
$$

$$
a_3=v,
$$

$$
a_5=w-\kappa,
$$

$$
a_7=\kappa.
$$

若指数上界为

$$
0\le a_2\le A_2,\quad
0\le a_3\le A_3,\quad
0\le a_5\le A_5,\quad
0\le a_7\le A_7,
$$

则 $\kappa$ 必须满足

$$
\kappa\ge0,
$$

$$
\kappa\ge u-A_2,
$$

$$
\kappa\ge w-A_5,
$$

以及

$$
\kappa\le A_7,
$$

$$
\kappa\le u,
$$

$$
\kappa\le w.
$$

因此

$$
\boxed{
\kappa_-^{\mathrm{int}}=
\max(0,u-A_2,w-A_5)
}
$$

和

$$
\boxed{
\kappa_+^{\mathrm{int}}=
\min(A_7,u,w).
}
$$

允许的整数隐藏纤维为

$$
\mathcal F_{\mathrm{int}}(u,v,w)=
\left\{
\kappa\in\mathbb Z:
\kappa_-^{\mathrm{int}}
\le\kappa\le
\kappa_+^{\mathrm{int}}
\right\}.
$$

---

### theorem 4.1: 定理 3：AURIC 概率纤维与 5040 指数纤维具有相同的区间核结构

AURIC 概率纤维为

$$
\kappa\in
\left[
\max(0,X+Y+Z-1),
\min(X,Y)
\right].
$$

5040 指数纤维为

$$
\kappa\in
\left[
\max(0,u-A_2,w-A_5),
\min(A_7,u,w)
\right]\cap\mathbb Z.
$$

二者都由以下结构决定：

1. 基础线性投影；
2. 一维关系核；
3. 非负性或容量约束；
4. 一个截断的仿射纤维。

#### 证明

前者由矩阵 $A_{\mathrm{FIB}}$ 的一维核与概率非负性得到；后者由矩阵 $A_{\mathrm{int}}$ 的一维核与指数盒约束得到。两者的差别只在于：

- 概率纤维是实数区间；
- 指数纤维是整数区间。

二者的仿射核均为一维，且纤维端点均由线性不等式的最大值与最小值决定。证毕。

---

### 5040 的特殊情形

对于

$$
5040=2^4\cdot3^2\cdot5\cdot7,
$$

有

$$
(a_2,a_3,a_5,a_7)=(4,2,1,1).
$$

所以

$$
(u,v,w)=(5,2,2),
$$

并且

$$
\kappa=a_7=1.
$$

若只知道

$$
(u,v,w)=(5,2,2),
$$

则由于 $a_7\in\{0,1\}$，仍有两个候选点：

$$
(a_2,a_3,a_5,a_7)=
(5,2,2,0)
$$

或

$$
(4,2,1,1).
$$

对应乘法数分别是

$$
2^5\cdot3^2\cdot5^2=7200
$$

和

$$
2^4\cdot3^2\cdot5\cdot7=5040.
$$

因此基础投影把 $5040$ 与 $7200$ 视为同一叶子结构，而 $\kappa$ 恢复了差别。

---

## 5. 五、Golden ring 范数是 $\kappa$ 的非线性读出

定义黄金整数环

$$
R=\mathbb Z[\theta]/(\theta^2-\theta-1).
$$

定义范数

$$
N(a+b\theta)=a^2+ab-b^2.
$$

四个基础因子对应：

$$
1,\qquad
\theta,\qquad
\theta^2,\qquad
2+\theta.
$$

它们的范数分别为

$$
N(1)=1,
$$

$$
N(\theta)=-1,
$$

$$
N(\theta^2)=1,
$$

$$
N(2+\theta)=5.
$$

定义

$$
U(a)=
1^{a_2}
\theta^{a_3}
(\theta^2)^{a_5}
(2+\theta)^{a_7}.
$$

由于范数是乘法的，

$$
N(U(a))=
(-1)^{a_3}5^{a_7}.
$$

所以

$$
\boxed{
v_5\left(|N(U(a))|\right)=a_7=\kappa.
}
$$

---

### theorem 5.1: 定理 4：Golden ring 范数精确恢复乘法隐藏坐标

在指数编码中，基础坐标 $(u,v,w)$ 一般不能恢复 $\kappa=a_7$，但 Golden ring 范数满足

$$
\kappa=v_5(|N(U)|).
$$

#### 证明

由范数乘法性：

$$
N(U)=
N(1)^{a_2}
N(\theta)^{a_3}
N(\theta^2)^{a_5}
N(2+\theta)^{a_7}.
$$

代入四个原子范数：

$$
N(U)=1^{a_2}(-1)^{a_3}1^{a_5}5^{a_7}=
(-1)^{a_3}5^{a_7}.
$$

取绝对值并取 $5$-进赋值：

$$
v_5(|N(U)|)=a_7=\kappa.
$$

证毕。

对于 $5040$，此前得到

$$
U(5040)=7+11\theta,
$$

并且

$$
N(U(5040))=5.
$$

因此

$$
v_5(|N(U(5040))|)=1.
$$

这与

$$
\kappa=a_7=1
$$

一致。

这里出现一个非常漂亮的三重对应：

$$
\boxed{
\kappa=
p_{13}=
a_7=
v_5(|N(U)|)
}
$$

它们不是同一个对象，但它们都是同一个隐藏关系在不同代数切面上的坐标。

---

## 6. 六、统一可见性定理

现在可以把概率、指数、范数、未来响应统一起来。

### 定义 2：隐藏方向的读出

设 $\mathcal K$ 是基础投影的隐藏空间，设 $R$ 是新增读出。

称 $R$ 对隐藏方向 $h\in\mathcal K$ 可见，如果

$$
R(h)\neq0.
$$

对于一维隐藏空间，称 $R$ 完整恢复隐藏关系，如果

$$
R(h)\neq0
$$

对任意非零 $h\in\mathcal K$ 成立。

---

### theorem 6.1: 定理 5：一维隐藏关系的恢复判据

设隐藏空间为

$$
\mathcal K=\operatorname{span}\{h\}.
$$

则新增读出 $R$ 能唯一恢复隐藏坐标，当且仅当

$$
\boxed{
R(h)\neq0.
}
$$

#### 证明

任意同一基础纤维内的两个状态差异都形如

$$
p-q=th.
$$

若

$$
R(h)=0,
$$

则

$$
R(p)-R(q)=tR(h)=0,
$$

所以 $R$ 不能区分任何不同 $t$。

若

$$
R(h)\neq0,
$$

则

$$
R(p)-R(q)=tR(h)
$$

唯一确定 $t$，从而唯一确定隐藏坐标。证毕。

---

该定理在不同切面上分别给出：

### AURIC 加法均值

$$
R_{\mathrm{mean}}(h_{13})=
7-2-5+0=0.
$$

因此均值看不见 $\kappa$。

### AURIC 二阶矩

$$
R_{S^2}(h_{13})=
49-4-25+0=20.
$$

因此二阶矩看见 $\kappa$。

### 乘法指数基础投影

$$
A_{\mathrm{int}}(-1,0,-1,1)=0.
$$

因此 $(u,v,w)$ 看不见 $\kappa=a_7$。

### Golden ring 范数

$$
v_5(|N(U)|)=a_7.
$$

因此范数读出看见 $\kappa$。

### 未来响应

$$
R_{\mathscr L}(h_{13})=
J_{\mathscr L}.
$$

因此未来律看见 $\kappa$ 的充要条件为

$$
J_{\mathscr L}\neq0.
$$

---

## 7. 七、AURIC $\kappa$ 是一种“环流荷”

前面把 $\kappa$ 称为隐藏坐标。现在可以进一步把它定义为一种离散环流荷。

将三位状态视为 pair-state 运输图的边：

$$
000:00\to00,
$$

$$
100:10\to00,
$$

$$
001:00\to01,
$$

$$
101:10\to01,
$$

以及桥边

$$
010:01\to10.
$$

前四条边构成一个方形环：

$$
00\to01\leftarrow10\to00
$$

的边界流关系。

隐藏方向

$$
h=(1,-1,0,-1,1)
$$

正好只在这个四环上产生循环流，而桥边 $010$ 的系数为零。

---

### 定义 3：环流荷

设 $G$ 是一个带边概率的二部支持图，$\partial$ 是边流到顶点边界的映射。

若

$$
\partial h=0,
$$

则称 $h$ 为边界不可见的内部环流。

在 AURIC 中定义

$$
\mathfrak k(p)=
p_{13}
$$

为唯一基本方形环的坐标，称为 AURIC 环流荷。

---

### theorem 7.1: 定理 6：环流荷由图的第一循环空间决定

对于有限二部支持图 $G$，固定所有顶点边界流后，内部隐藏空间为

$$
\ker\partial.
$$

其维数为

$$
\boxed{
|E|-|V|+c
}
$$

其中 $c$ 是连通分量数。

若 $G$ 是森林，则隐藏空间为零；若 $G$ 含有一个独立环，则产生一个独立隐藏荷。

#### 证明

边—顶点关联矩阵在每个连通二部组件上秩为

$$
|V_i|-1.
$$

总秩为

$$
|V|-c.
$$

因此

$$
\dim\ker\partial=
|E|-(|V|-c)=
|E|-|V|+c.
$$

森林满足 $|E|=|V|-c$，因此核维数为零。每增加一个独立环，$|E|-|V|+c$ 增加一。证毕。

---

所以可以把三种结构统一：

$$
\boxed{
\text{AURIC }\kappa=
\text{局部方形环的流量}=
\text{边界不可见的内部荷}.
}
$$

这也解释了为什么长窗口中会出现一组

$$
\kappa_q
$$

而不是单个 $\kappa$：每个内部词 $q$ 产生一个独立 square-cycle。

---

## 8. 八、时间可以被形式化为读出精化序

在不把它直接宣称为物理定律的前提下，可以给出一个严格的数学模型。

### 定义 4：观察过滤

设有一列读出：

$$
R_0\preceq R_1\preceq R_2\preceq\cdots
$$

满足

$$
R_t=A_t\circ R_{t+1}.
$$

定义第 $t$ 层状态纤维：

$$
\mathcal F_t(b)=
\{p:R_t(p)=b\}.
$$

由读出精化序：

$$
\mathcal F_{t+1}(b')
\subseteq
\mathcal F_t(b).
$$

---

### theorem 8.1: 定理 7：观察时间的纤维收缩定理

若观察过程不断加入新的独立读出，则隐藏纤维形成嵌套链：

$$
\mathcal F_0
\supseteq
\mathcal F_1
\supseteq
\mathcal F_2
\supseteq\cdots.
$$

若某一步新增读出对隐藏空间的限制秩为 $r_t$，则局部隐藏维数至少下降 $r_t$。

#### 证明

每个新增读出增加一个线性约束。若其限制在当前隐藏空间上的秩为 $r_t$，则核维数下降 $r_t$。由于新纤维是旧纤维与新增约束的交集，所以纤维单调收缩。证毕。

这给出一个严格的“观察产生时间”的离散数学版本：

$$
\boxed{
\text{时间步}=
\text{一次新的可区分性约束}.
}
$$

在这个模型中：

- 尚未观察到的 $\kappa$ 是未来可继续区分的方向；
- 加入 $S^2$ 后，$\kappa$-纤维收缩为单点；
- 加入完整 Fibonacci 光谱后，整个局部状态纤维收缩为单点；
- 对闭环系统，即使局部纤维已确定，仍可能有全局 holonomy 约束尚未满足。

因此“知道局部状态”和“知道全局可实现状态”是两个不同层次。

---

## 9. 九、FIB 金字塔与 5040 的共同信息结构

现在可以把两种编码写成同一个抽象形式。

### 概率层

$$
p
\in
\Delta^4,
$$

$$
\pi_{\mathrm{prob}}(p)=(X,Y,Z),
$$

$$
\ker \pi_{\mathrm{prob}}=
\mathbb R h_{\mathrm{AURIC}}.
$$

### 整数层

$$
a
\in
\mathbb Z_{\ge0}^4,
$$

$$
\pi_{\mathrm{int}}(a)=(u,v,w),
$$

$$
\ker \pi_{\mathrm{int}}=
\mathbb Z\eta,
$$

其中

$$
\eta=(-1,0,-1,1).
$$

二者都满足：

$$
\boxed{
\text{完整对象}=
\text{基础投影}
+
\text{一维纤维坐标}.
}
$$

对应关系可以写成：

| 概率 FIB 层 | 乘法 5040 层 |
|---|---|
| $p_{13}$ | $a_7$ |
| $(X,Y,Z)$ | $(u,v,w)$ |
| $7=2+5$ | $7$ 与 $10=2\cdot5$ 的碰撞 |
| $S^2$ | Golden ring norm |
| $\Delta$ | $v_5(|N(U)|)$ 的隐藏指数 |
| square-cycle flow | exponent kernel move |
| future contrast $J_{\mathscr L}$ | norm/readout contrast |

需要注意，它们不是同一个数值系统，而是同一个**关系核结构**在不同代数中的表现。

---

## 10. 十、目前仍然逃逸的信息

即使恢复了三态 $\kappa$，更长窗口中仍有新的隐藏层。

对长度 $n$ 的 Fibonacci 词：

$$
W_n=
\{w\in\{0,1\}^n:\text{不含 }11\}.
$$

只观察单点占用时，隐藏维数为

$$
d_n=N_n-1-n.
$$

观察完整 prefix/suffix 后，剩余运输环流维数为

$$
g_n=N_n-2N_{n-1}+N_{n-2}.
$$

所以：

$$
d_3=1,
\qquad
g_3=1,
$$

但

$$
d_5=13-1-5=7,
$$

而

$$
g_5=13-2\cdot8+5=2.
$$

这说明：

- 一阶读出隐藏了大量高阶独立集交互；
- separator 读出已经恢复了大部分信息；
- 仍剩下两个独立 square-cycle 荷；
- 完整词读出才彻底消除所有隐藏。

因此，信息逃逸不是一次性的：

$$
\boxed{
\text{一阶逃逸}
\supset
\text{separator 之后的环流逃逸}
\supset
\text{未来律仍不可见的逃逸}.
}
$$

---

## 11. 十一、最终统一命题

### theorem 11.1: 定理 8：Auric FIB ATOM 纤维化定理

设一个有限合法关系系统具有：

1. 一个有限状态集 $\Omega$；
2. 一个基础投影 $\pi:\Delta(\Omega)\to B$；
3. 一个边界运输图 $G$；
4. 一个未来读出族 $\mathscr R$。

则其结构可以分解为四层：

$$
\boxed{
\text{基础商空间}
\quad+\quad
\text{局部纤维}
\quad+\quad
\text{运输环流}
\quad+\quad
\text{未来可观测商}.
}
$$

具体地：

### 基础商空间

$$
B=\pi(\Delta(\Omega)).
$$

### 局部纤维

$$
\mathcal F_b=\pi^{-1}(b).
$$

### 环流空间

$$
\mathcal C_G=\ker\partial_G,
$$

其维数为

$$
|E(G)|-|V(G)|+c(G).
$$

### 未来可观测商

若两个局部律 $p,q$ 满足

$$
\mathscr R(p)=\mathscr R(q),
$$

则它们在未来观察下属于同一等价类。

若未来响应对每个隐藏方向均非零，则未来读出可以恢复局部纤维；若某些隐藏方向被全部响应湮灭，则这些方向仍属于未来商的核。

#### 证明

基础投影将完整状态压缩到 $B$，其逆像给出局部纤维。边界运输约束的零空间给出边界不可见的环流。未来读出进一步对该环流空间取商，保留能够改变未来律的方向，消除对当前仪器不可见的方向。四层依次由线性代数、运输图理论和读出等价关系确定。证毕。

---

## 12. 十二、下一步最重要的形式化对象

结合当前项目的 AURIC、escape-audit、acquired circulation 和 future quotient 方向，最值得定义的不是更多例子，而是以下三个统一对象。

### 1. RelationKernel

$$
\mathrm{RelationKernel}(\pi)=
\ker\pi
\cap
\{\text{总质量为零的关系}\}.
$$

AURIC 中应证明：

$$
\mathrm{RelationKernel}(\pi_{\mathrm{AURIC}})=
\operatorname{span}\{h_{\mathrm{AURIC}}\}.
$$

### 2. CirculationBasis

对任意支持运输图 $G$，定义其独立环流基：

$$
\mathrm{CirculationBasis}(G).
$$

Fibonacci 长窗口中，每个自由内部词 $q$ 对应一个：

$$
h_q=
\delta_{0q0}
-\delta_{0q1}
-\delta_{1q0}
+\delta_{1q1}.
$$

### 3. ReadoutSeparation

给定读出族 $\mathscr R$，定义：

$$
\mathrm{Visible}(h)
\Longleftrightarrow
\exists R\in\mathscr R,\ R(h)\neq0.
$$

然后证明：

$$
\mathrm{FutureKernel}=
\bigcap_{R\in\mathscr R}\ker R.
$$

这样就能把“基础元素之间隐藏关系”严格写成：

$$
\boxed{
\text{隐藏关系}=
\text{基础投影的核}
\cap
\text{未来读出族的共同核}.
}
$$

最终，AURIC FIB ATOM 金字塔可以被理解为一种递归的关系编码：

$$
\boxed{
\text{原子}
\longrightarrow
\text{合法组合}
\longrightarrow
\text{基础投影}
\longrightarrow
\text{隐藏纤维}
\longrightarrow
\text{环流}
\longrightarrow
\text{未来可见性}.
}
$$

在三位窗口中，这条链的唯一非平凡坐标是

$$
\kappa=p_{13}.
$$

在 5040 乘法编码中，它变成

$$
\kappa=a_7.
$$

在 Golden ring 中，它变成

$$
\kappa=v_5(|N(U)|).
$$

在动态未来系统中，它变成

$$
\kappa
\longmapsto
J_{\mathscr L}\kappa.
$$

这四个表达式共同说明：$\kappa$ 不是某一套坐标系统里的偶然参数，而是基础投影与完整关系之间的一维缺失自由度。

## 追加锚（本行以下为增补区）
