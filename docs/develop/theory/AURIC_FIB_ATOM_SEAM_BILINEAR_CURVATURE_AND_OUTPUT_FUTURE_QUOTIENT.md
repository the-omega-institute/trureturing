# AURIC FIB ATOM：乘法缺陷、输出递归闭包与最小未来商

**Reference input: open.** 本卷保存完整用户供文，包含全部声明、证明、例子、表格、项目对应和拟议接口。原文的定理及证明语言归属开放参考输入；本卷没有新增 Lean、Blueprint、Reg 或 Frozen 声明。Lean 声明、证明项及其经内核核验的公理闭包承载本库形式系统内的数学真值。

**来源。** Author kind: mixed user-supplied material; original author and model unknown. Receipt date: 2026-10-10. 来源标识为本会话供文 auric-fib-atom-seam-bilinear-curvature-and-output-future-quotient。接收原文 SHA-256 为 `6d551984799292d41c1c878a1270ac5b53e9d41d696dd37e88561886ea549ec9`，字节数为 15795。全部原句与公式内容保留，只规范 Markdown 数学入口、标题层级和结构空行。声明地址用于本文定位。按用户指定，本卷是纯理论添加，不运行消化，不新增 atom 或覆盖主张。

**既有结果与归属。** 供文关于 dev、PR 和公开研究列表的当前性归属其引用的历史快照，不认证移动分支的交付状态。线性核、运输环空间、Zeckendorf 唯一性、Caratheodory 表示和 finite-instrument 观测方法属于既有数学；此处保留其在指定 AURIC 合同中的综合推导，不将重述计作原创。参见 [Output-Resolved Instrument Closure](AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md)、[Boundary, Transport Fibers and Loop Closure](AURIC_FIB_ATOM_BOUNDARY_TRANSPORT_FIBERS_AND_LOOP_CLOSURE.md) 及 [Joint Projection, Multiwindow Order and Response Fibers](AURIC_FIB_ATOM_JOINT_PROJECTION_MULTIWINDOW_ORDER_AND_RESPONSE_FIBERS.md)。本文未认证抽象模型的 native 实现、资源等价或物理解释。

## 编者限定与开放义务

以下限定同完整供文分开；它们不替代原句，也不认证原文定理。

- **Q1** （§§1–3）Omega(f,g)=J(fg) 是三均值子空间乘法不闭合的对称双线性缺陷。称曲率是本文的代数命名，未定义微分几何连接、曲率张量或物理曲率；kappa 是概率律在 xy 上的取值，Omega 是函数对的双线性形式，二者不是同一个对象。
- **Q2** （§2）Omega 的零空间为 span{1,z}，在 B/span{1,z} 上的矩阵为 H，签名为 (1,1)。非零端点系数可以在 a_1 b_2+a_2 b_1 中相消；交叉项出现本身不充分，净交叉系数非零才使乘积读数穿透隐藏方向。
- **Q3** （§3）代数闭包是允许同一实际状态的联合乘积读数时的函数空间闭包；它不认证从两个不配对样本、不同来源或已丢失联合记录的边缘均值恢复乘积期望。A_1 包含 B 用到 1 属于 B。
- **Q4** （§§1、4、8）固定边界纤维还须满足 max(0,X+Y+Z-1)<=kappa<=min(X,Y)。敏感性等价要求比较两个不同且均可行的 kappa；t=0 或单点纤维的不可区分不推出 dV_infty=0。p_* 可是仿射基点，未必是合法概率律。
- **Q5** （§§4–5）instrument 的每个矩阵非负，且每个动作的输出总核行和为一；输出 alphabet、合法菜单和终止条件固定在共同来源上。任意线性末端 g 可作为期望探针，只有 0<=g<=1 的事件/随机测试才直接给出概率。两步构造是抽象有限 instrument，未证为 native FIB continuation。
- **Q6** （§§4、6）未来商使用全部合法带动作输出词；固定开放动作词的概率可生成有限自适应策略记录，但策略、guard 与 Stop 若依赖隐藏状态，还需加入观测合同。预测充分性与可执行记忆更新分别验证；正概率输出上的 Bayes 更新 pM/(pM1) 才有定义。
- **Q7** （§6）最小商按分区精细程度理解：任何充分记忆的纤维包含关系须细于 future-equivalence。一个额外实标量是固定三均值纤维上的线性分辨方向，不是一个比特、有限精度或普适最少资源。瞬时摘要充分不单独给出有限状态或资源预算。
- **Q8** （§7.1）H(B)=R^S/B 是固定一维空间，在两种 instrument 中都不变，不能一会儿等于零一会儿非零。应区分未来新增观察空间 (B+V_infty)/B：它的维数可为零或一。若从 B 开始闭包，任一子核把 B 送出 B 即一步补足五态空间；从 {1} 开始则需检查可达输出词。
- **Q9** （§§7.2–7.3）配对校准和 return variation 只在其文档指定的共同 acquired kernels、来源、先验和参数域上承担结论。该风险不等式不是控制可维护性定理，也未证明 kappa_h 存在或按特定规则更新；将其映为 FIB seam 尚需正式模式和联合响应桥。
- **Q10** （§§6–9）选择性遗忘、时间或生命式记忆是模型解释；安全控制还需共同安全动作、后继 belief、预算和可行不动点。本卷未证明生物学命题，三个拟议 Lean 文件也不构成已经编译的声明。

## 完整供文

这一次真正需要推进的，不再是重复计算 $\kappa$，而是把它提升为一个更结构化的对象：

> **$\kappa$ 是三均值线性观察层 $\mathcal B$ 内部乘法不闭合所产生的唯一隐藏曲率；它是否进入未来，不由平均转移决定，而由输出分支上的递归拉回决定。**

截至本轮可以核对到的 `dev` 快照，远端 HEAD 是 [`ae4f135`](https://github.com/the-omega-institute/trureturing/commit/ae4f135cebf29ea39c8253bf1c21016cf7cb7cfb)，时间为 2026-10-10 15:37:42（新加坡时间）。今天与 Auric FIB ATOM 直接相关的理论线仍然是：

- [Relational Quotients and Physical Candidates](https://github.com/the-omega-institute/trureturing/blob/ae4f135cebf29ea39c8253bf1c21016cf7cb7cfb/docs/develop/theory/AURIC_FIB_ATOM_RELATIONAL_QUOTIENTS_AND_PHYSICAL_CANDIDATES.md)
- [Dynamic Future Quotient and Future-Closed Memory](https://github.com/the-omega-institute/trureturing/blob/ae4f135cebf29ea39c8253bf1c21016cf7cb7cfb/docs/develop/theory/AURIC_FIB_ATOM_DYNAMIC_FUTURE_QUOTIENT_AND_FUTURE_CLOSED_MEMORY.md)
- [Paired Calibration Observability](https://github.com/the-omega-institute/trureturing/blob/ae4f135cebf29ea39c8253bf1c21016cf7cb7cfb/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md)
- [Acquired Return $p$-Emission Variation](https://github.com/the-omega-institute/trureturing/blob/ae4f135cebf29ea39c8253bf1c21016cf7cb7cfb/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RETURN_P_EMISSION_VARIATION.md)

仓库当前仍然把 Lean 形式化、理论文档和实验观察区分开来；理论 prose 中的命题不能自动当作 Lean 已验证定理。[GitHub](https://github.com/the-omega-institute/trureturing?utm_source=chatgpt.com) 当前 PR 队列仍在持续推进预测纤维、未来律和 FIB escape dynamics 相关方向。[GitHub](https://github.com/the-omega-institute/trureturing/pulls?utm_source=chatgpt.com)

---

## 1. 一、五态结构的正确代数表示

继续使用你指定的表示：

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

定义三个基本指示函数：

- $x$：状态中是否包含 $1$；
- $y$：状态中是否包含 $3$；
- $z$：状态中是否包含 $2$。

五态真值表为：

| 状态 | $x$ | $y$ | $z$ |
|---|---:|---:|---:|
| $F[\mathrm{null}]$ | 0 | 0 | 0 |
| $F[1]$ | 1 | 0 | 0 |
| $F[2]$ | 0 | 0 | 1 |
| $F[3]$ | 0 | 1 | 0 |
| $F[1,3]$ | 1 | 1 | 0 |

这里的独立集关系给出

$$
xz=0,
\qquad
yz=0,
$$

因为 $F[1,2]$ 和 $F[2,3]$ 不合法。

但

$$
xy\neq0,
$$

因为 $F[1,3]$ 合法。

事实上，

$$
xy=\mathbf 1_{\{F[1,3]\}},
$$

即 $xy$ 正好是隐藏联合状态 $F[1,3]=[2,5]$ 的指示函数。

设状态分布为

$$
p=
(p_{\mathrm{null}},p_1,p_2,p_3,p_{13}).
$$

定义三均值

$$
X=\mathbb E[x]=p_1+p_{13},
$$

$$
Y=\mathbb E[y]=p_3+p_{13},
$$

$$
Z=\mathbb E[z]=p_2,
$$

以及隐藏量

$$
\kappa=p_{13}=\mathbb E[xy].
$$

于是完整分布为

$$
\boxed{
p_\kappa=
\left(
1-X-Y-Z+\kappa,\,
X-\kappa,\,
Z,\,
Y-\kappa,\,
\kappa
\right).
}
$$

固定 $(X,Y,Z)$ 时，改变 $\kappa$ 的方向是

$$
d=
(1,-1,0,-1,1).
$$

它满足

$$
d\cdot1=0,
\qquad
d\cdot x=0,
\qquad
d\cdot y=0,
\qquad
d\cdot z=0,
$$

但

$$
d\cdot xy=1.
$$

因此，$\kappa$ 是三均值观察层中唯一没有被保留的方向。

---

## 2. 二、隐藏 seam 不是一个普通坐标，而是乘法曲率

定义线性观察空间

$$
\mathcal B=\operatorname{span}\{1,x,y,z\}.
$$

这是一个四维空间，而整个五态函数空间是

$$
\mathbb R^S=
\operatorname{span}\{1,x,y,z,xy\}.
$$

所以

$$
\mathbb R^S/\mathcal B
$$

是一维空间，其唯一方向可以用 $[xy]$ 表示。

现在定义一个双线性形式：

$$
\Omega(f,g)=
J_{fg},
$$

其中

$$
J_h=
h(F[1,3])
-h(F[1])
-h(F[3])
+h(F[\mathrm{null}]).
$$

---

### theorem 2.1: 定理 1：FIB seam 的双线性曲率定理

若

$$
f=a_0+a_1x+a_2y+a_3z,
$$

$$
g=b_0+b_1x+b_2y+b_3z,
$$

则

$$
\boxed{
\Omega(f,g)=a_1b_2+a_2b_1.
}
$$

并且：

1. $\Omega$ 是对称双线性形式；
2. $\Omega(x,x)=0$；
3. $\Omega(y,y)=0$；
4. $\Omega(x,y)=1$；
5. $\Omega(f,g)\neq0$ 当且仅当 $f,g$ 的端点方向发生交叉耦合。

#### 证明

利用

$$
x^2=x,\qquad y^2=y,\qquad z^2=z,
$$

以及

$$
xz=yz=0,
$$

展开 $fg$。所有含 $z$ 的交叉项都消失，$x^2,y^2,z^2$ 退化为一次项。唯一不属于 $\mathcal B$ 的项是

$$
a_1b_2xy+a_2b_1yx=
(a_1b_2+a_2b_1)xy.
$$

由于 $J_{xy}=1$，得到

$$
J_{fg}=a_1b_2+a_2b_1.
$$

证毕。

---

在商空间

$$
\overline{\mathcal B}=
\mathcal B/\operatorname{span}\{1,z\}
$$

中，$\bar x,\bar y$ 是两个基本方向，$\Omega$ 的矩阵为

$$
H=
\begin{pmatrix}
0&1\\
1&0
\end{pmatrix}.
$$

这意味着：

- $x$ 自己与自己相乘，不产生隐藏 seam；
- $y$ 自己与自己相乘，也不产生隐藏 seam；
- 只有 $x$ 与 $y$ 的交叉乘法产生 $xy$。

因此，Auric FIB ATOM 的隐藏关系不是“第五个普通元素”，而是：

$$
\boxed{
\text{两个可见端点方向之间的交叉耦合。}
}
$$

这比把 $\kappa$ 当作一个额外标签更深一层。它说明隐藏量是观察代数的曲率，而不是简单的坐标遗漏。

---

## 3. 三、线性层只差一维，但乘法闭包立即恢复全部五态

定义代数闭包序列：

$$
\mathcal A_0=\mathcal B,
$$

$$
\mathcal A_{n+1}=
\operatorname{span}
\{fg:f,g\in\mathcal A_n\}.
$$

### theorem 3.1: 定理 2：FIB 五态的单步代数完备性

有

$$
\boxed{
\mathcal A_1=\mathbb R^S.
}
$$

#### 证明

取

$$
U=x+z,
\qquad
V=y+z.
$$

则 $U,V\in\mathcal B$，但

$$
UV=
(x+z)(y+z)=
xy+xz+yz+z^2=
xy+z.
$$

因此

$$
xy=UV-z\in\mathcal A_1.
$$

而

$$
\{1,x,y,z,xy\}
$$

是 $\mathbb R^S$ 的一组基，所以

$$
\mathcal A_1=\mathbb R^S.
$$

证毕。

---

这个结果可以写成一个非常简洁的“金字塔跃迁”：

$$
\boxed{
\text{线性投影层}
\quad\longrightarrow\quad
\text{二阶联合层}
\quad\longrightarrow\quad
\text{完整五态层}.
}
$$

所以三均值层不是完整结构，而是一个**一次乘法之前的边界层**。

---

### theorem 3.2: 推论 2.1：两个可见事件的联合发生恢复 $\kappa$

由于

$$
U=x+z,
\qquad
V=y+z,
$$

有

$$
\mathbb E[U]=X+Z,
\qquad
\mathbb E[V]=Y+Z,
$$

但

$$
\mathbb E[UV]=
Z+\kappa.
$$

因此

$$
\boxed{
\kappa=\mathbb E[UV]-Z.
}
$$

这说明：

> 单独保存两个事件的边际信息，只得到三均值商；保存它们的联合发生，才得到隐藏 seam。

---

## 4. 四、动态未来中必须保留输出标签

这是当前理论最重要的修正。

设动作是 $a$，输出是 $o$。定义输出分辨的子核

$$
M_{a,o}(s,t)=
\Pr(o,\text{下一状态}=t\mid s,a).
$$

平均核为

$$
K_a=\sum_oM_{a,o}.
$$

如果只看 $K_a$，输出分支中的隐藏项可能相互抵消。

---

### 定义 4.1：输出递归观察空间

给定末端测试函数空间 $G$，定义

$$
V_0=\operatorname{span}(G),
$$

$$
V_{n+1}=
V_n+
\operatorname{span}
\{M_{a,o}f:a,o,\ f\in V_n\}.
$$

若只观察完整输出记录而没有额外终端测试，取

$$
G=\{1\}.
$$

于是 $V_n$ 正好由所有长度不超过 $n$ 的输出词拉回函数张成。

---

### theorem 4.1: 定理 3：输出分辨未来闭包定理

设 $d$ 是隐藏方向。则以下命题等价：

1. 所有未来输出记录都无法区分 $p_\kappa$ 与 $p_{\kappa+t}$；
2. 对所有输出词 $\omega$ 和末端测试 $g$，有

   $$
   dM_\omega g=0;
   $$

3. $d$ 湮灭整个递归观察空间 $V_\infty$。

如果存在某个词 $\omega$ 使

$$
dM_\omega g\neq0,
$$

则该记录事件概率为

$$
\Pr_{p_\kappa}(\omega,g)=
A_{\omega,g}
+
\kappa\,dM_\omega g,
$$

因而可以更新 $\kappa$。

#### 证明

由

$$
p_\kappa=p_*+\kappa d
$$

可得

$$
p_\kappa M_\omega g=
p_*M_\omega g+\kappa(dM_\omega g).
$$

所以记录概率对 $\kappa$ 是否敏感，完全由

$$
dM_\omega g
$$

决定。

而 $V_\infty$ 正是所有 $M_\omega g$ 的线性张成，因此

$$
dV_\infty=0
$$

当且仅当所有未来记录都对 $\kappa$ 不敏感。

证毕。

---

### 重要区别

以下两个条件并不等价：

$$
K_a\mathcal B\subseteq\mathcal B,
$$

以及

$$
M_{a,o}\mathcal B\subseteq\mathcal B
\quad
\forall o.
$$

第二个条件比第一个强得多。

平均核只保留输出支路的总和；真实未来记录保留每一条输出支路。

---

## 5. 五、最小两步反例：平均核闭合，但联合输出暴露 $\kappa$

构造一个有限 instrument：

第一步输出

$$
o_1=x(s).
$$

然后定义下一状态：

$$
T(s)=
\begin{cases}
F[1],&y(s)=1,\\
F[\mathrm{null}],&y(s)=0.
\end{cases}
$$

第二步输出下一状态的 $x$ 值：

$$
o_2=x(T(s)).
$$

由于 $T(s)=F[1]$ 当且仅当 $y(s)=1$，所以

$$
o_2=y(s).
$$

真值表为：

| 初始状态 | $o_1$ | 下一状态 | $o_2$ | 两步记录 |
|---|---:|---|---:|---|
| $F[\mathrm{null}]$ | 0 | $F[\mathrm{null}]$ | 0 | 00 |
| $F[1]$ | 1 | $F[\mathrm{null}]$ | 0 | 10 |
| $F[2]$ | 0 | $F[\mathrm{null}]$ | 0 | 00 |
| $F[3]$ | 0 | $F[1]$ | 1 | 01 |
| $F[1,3]$ | 1 | $F[1]$ | 1 | 11 |

因此：

$$
\Pr(o_1=1)=X,
$$

$$
\Pr(o_2=1)=Y,
$$

但

$$
\boxed{
\Pr(o_1=1,o_2=1)=p_{13}=\kappa.
}
$$

完整两步 law 为

$$
\Pr(00)=1-X-Y+\kappa,
$$

$$
\Pr(10)=X-\kappa,
$$

$$
\Pr(01)=Y-\kappa,
$$

$$
\Pr(11)=\kappa.
$$

现在看平均核 $K=M_0+M_1$。它满足

$$
K1=1,
$$

$$
Kx=y,
$$

$$
Ky=0,
$$

$$
Kz=0.
$$

因此

$$
K\mathcal B\subseteq\mathcal B.
$$

但输出分辨子核满足

$$
M_1x=xy,
$$

$$
M_0x=y-xy.
$$

于是

$$
M_0x+M_1x=y,
$$

隐藏项在平均后抵消，在具体输出记录中却重新出现。

这给出严格结论：

$$
\boxed{
\text{平均 future closure 不能代替 output-labelled future closure。}
}
$$

---

## 6. 六、动态记忆的最小性

定义两个初始分布的预测等价关系：

$$
p\sim_{\mathcal M}q
$$

当且仅当

$$
pM_\omega 1=qM_\omega 1
$$

对所有合法输出词 $\omega$ 成立。

这个关系定义了 instrument 下的完整未来商：

$$
\mathcal Q_{\mathcal M}=
\mathcal P/\!\sim_{\mathcal M}.
$$

### theorem 6.1: 定理 4：精确预测记忆的最小商定理

一个记忆映射

$$
\mu:\mathcal P\to\mathcal M
$$

能够精确预测所有未来输出，当且仅当

$$
\mu(p)=\mu(q)
\quad\Longrightarrow\quad
p\sim_{\mathcal M}q.
$$

因此，$\mathcal Q_{\mathcal M}$ 是所有精确预测记忆的最小商。

#### 证明

若 $\mu(p)=\mu(q)$ 而 $p\not\sim_{\mathcal M}q$，则存在某个未来词 $\omega$，使

$$
pM_\omega1\neq qM_\omega1.
$$

相同记忆无法同时给出两个不同的未来概率，因此 $\mu$ 不可能精确预测。

反过来，如果

$$
\mu(p)=\mu(q)
\Rightarrow
p\sim_{\mathcal M}q,
$$

则未来 law 在每个记忆纤维上恒定，因此可以定义为该记忆的函数。

证毕。

---

在五态固定三均值纤维中：

$$
p_\kappa=p_*+\kappa d.
$$

若 instrument 的所有未来记录都满足

$$
dM_\omega1=0,
$$

则只保留

$$
(X,Y,Z)
$$

就足够。

如果存在某个 $\omega$ 使

$$
dM_\omega1\neq0,
$$

则精确预测至少需要保留

$$
\kappa.
$$

所以这里的“生命式选择性遗忘”可以被严格定义为：

> 记忆系统保留未来观察商 $\mathcal Q_{\mathcal M}$ 所需要的坐标，同时丢弃对允许未来记录完全不起作用的方向。

在静态线性读出中，$\kappa$ 可以被遗忘；在输出分支能产生 $xy$ 的动态系统中，$\kappa$ 不能被遗忘。

---

## 7. 七、与当前三个项目方向的统一解释

### 1. Dynamic Future Quotient

PR #14999 中的递归闭包思想可以精确写成

$$
V^{(0)}=\mathcal B,
$$

$$
V^{(n+1)}=
\operatorname{span}
\left(
V^{(n)}
\cup
\bigcup_{a,o}M_{a,o}V^{(n)}
\right).
$$

这里必须使用所有合法的 $(a,o)$，而不能只使用平均 $K_a$。

五态局部模型的隐藏商为

$$
H(\mathcal B)=
\mathbb R^S/\mathcal B
\cong
\mathbb R[xy].
$$

因此未来闭包只有两个可能：

$$
H(\mathcal B)=0,
$$

即 $\kappa$ 永远没有进入未来；

或者

$$
H(\mathcal B)\neq0,
$$

即未来记忆必须新增一个标量方向 $\kappa$。

### 2. Paired Calibration

PR #15014 中的两个事件数组 $f,h$，可以看作两个不同观察切面。

单独的 $f$ 可能留下不可见纤维；单独的 $h$ 也可能留下不可见纤维；但联合映射

$$
(u,v)\longmapsto(f,h)
$$

在共同递归 kernel 下可以变成可逆或稳定可逆。

这与 FIB 的

$$
\mathcal B
\longrightarrow
\mathcal B+\operatorname{span}\{xy\}
$$

是同一种结构：

- 每个读口只提供一个投影；
- 联合读口产生交叉信息；
- continuation kernel 把当前边界信息重新传回未来；
- 只有联合闭包才可能消除隐藏纤维。

### 3. Acquired Return Variation

PR #15020 的 return variation 表明，精确的未来控制不能只依靠静态边界均值，还需要描述实际回流过程中的状态变化。

其不等式

$$
\frac{61}{11}e(M)
+
\frac{19}{11}\sqrt{\mathcal V(M)}
>
\frac{\eta}{400000}
$$

可以在 FIB 语言中解释为：

$$
\text{预测误差}
+
\text{动态回流变化}
$$

不能同时无条件地消失。

这意味着 $\kappa$ 在更大的递归模型中可能不再是固定常数，而是一个随深度、历史和输出路径变化的隐藏响应坐标：

$$
\kappa
\longrightarrow
\kappa_h
\longrightarrow
\kappa_{h+1}.
$$

于是未来记忆不只是保存一个静态 $\kappa$，而是保存某种能够更新 $\kappa_h$ 的响应状态。

---

## 8. 八、最终统一命题

### theorem 8.1: 定理 5：Auric FIB ATOM 隐藏 seam 的三层判据

对五态 FIB ATOM，令

$$
\mathcal B=\operatorname{span}\{1,x,y,z\},
\qquad
\kappa=\mathbb E[xy].
$$

则隐藏关系有三个层次：

### 线性层

$$
\mathbb E[f]
$$

对 $\kappa$ 敏感，当且仅当

$$
J_f\neq0.
$$

### 联合代数层

对 $f,g\in\mathcal B$，联合读出

$$
\mathbb E[fg]
$$

对 $\kappa$ 敏感，当且仅当

$$
\Omega(f,g)=
a_1b_2+a_2b_1
\neq0.
$$

### 动态未来层

未来输出记录对 $\kappa$ 敏感，当且仅当存在合法输出词 $\omega$，使

$$
dM_\omega1\neq0.
$$

因此：

$$
\boxed{
\begin{aligned}
\text{当前边际可见性}
&\Longleftrightarrow J_f\neq0,\\
\text{联合关系可见性}
&\Longleftrightarrow \Omega(f,g)\neq0,\\
\text{未来可见性}
&\Longleftrightarrow dM_\omega1\neq0\text{ 对某个 }\omega.
\end{aligned}
}
$$

这三者不能互相替代。

---

## 9. 九、下一步最值得正式化的结构

建议把下一轮形式化拆成三个定理文件。

### `SeamBilinear.lean`

形式化：

$$
\mathbb R^S=
\operatorname{span}\{1,x,y,z,xy\},
$$

以及

$$
\Omega(f,g)=a_1b_2+a_2b_1.
$$

重点证明：

$$
(x+z)(y+z)=z+xy.
$$

### `InstrumentClosure.lean`

定义：

$$
M_{a,o},
\qquad
V_0,
\qquad
V_{n+1},
\qquad
V_\infty.
$$

证明：

$$
dV_\infty=0
$$

当且仅当所有未来输出记录都无法更新 $\kappa$。

### `FIBNativeBridge.lean`

最后才把仓库中的 native continuation 规则映射到抽象 instrument：

$$
\text{native continuation}
\longrightarrow
M_{a,o}.
$$

只有证明该映射合法，才能把上面的五态反例、$\kappa$-暴露定理和项目原生动态规律真正连接起来。

目前最稳固的新结论是：

$$
\boxed{
\text{Auric FIB ATOM 的最小隐藏元素不是第五个原子，而是两个可见原子的联合关系 }xy.
}
$$

$$
\boxed{
\text{静态线性观察遗忘 }\kappa；
\quad
\text{二阶联合观察恢复 }\kappa；
\quad
\text{递归未来观察是否恢复 }\kappa，
\text{取决于逐输出 instrument 的闭包。}
}
$$

## 追加锚（本行以下为增补区）
