# 续篇：把 AURIC FIB ATOM 金字塔提升为“观察分辨率—隐藏环流—信息逃逸”理论

**Reference input: open.** 本卷保存完整用户供文，包含全部声明、证明、例子、表格、项目对应和拟议接口。原文的定理及证明语言归属开放参考输入；本卷没有新增 Lean、Blueprint、Reg 或 Frozen 声明。Lean 声明、证明项及其经内核核验的公理闭包承载本库形式系统内的数学真值。

**来源。** Author kind: mixed user-supplied material; original author and model unknown. Receipt date: 2026-10-10. 来源标识为本会话供文 auric-fib-atom-observation-resolution-circulation-and-information-escape。接收原文 SHA-256 为 `494345cda093f2916a75609cbc5072d78129048a9a3f50e0d8ba477773dfd314`，字节数为 18635。全部原句与公式内容保留，只规范 Markdown 数学入口、标题层级和结构空行。声明地址用于本文定位。按用户指定，本卷是纯理论添加，不运行消化，不新增 atom 或覆盖主张。

**既有结果与归属。** 供文关于 dev、PR 和公开研究列表的当前性归属其引用的历史快照，不认证移动分支的交付状态。线性核、运输环空间、Zeckendorf 唯一性、Caratheodory 表示和 finite-instrument 观测方法属于既有数学；此处保留其在指定 AURIC 合同中的综合推导，不将重述计作原创。参见 [Output-Resolved Instrument Closure](AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md)、[Boundary, Transport Fibers and Loop Closure](AURIC_FIB_ATOM_BOUNDARY_TRANSPORT_FIBERS_AND_LOOP_CLOSURE.md) 及 [Joint Projection, Multiwindow Order and Response Fibers](AURIC_FIB_ATOM_JOINT_PROJECTION_MULTIWINDOW_ORDER_AND_RESPONSE_FIBERS.md)。本文未认证抽象模型的 native 实现、资源等价或物理解释。

## 编者限定与开放义务

以下限定同完整供文分开；它们不替代原句，也不认证原文定理。

- **Q1** （§1）本卷维数、有限 signed measure 坐标和多面体结论取有限 Omega。K_R 是在零质量切空间中的核；实际纤维维数等于它需要在全部允许坐标上严格正的可行点，边界纤维可降维或为空。
- **Q2** （§§2–3）kappa 是当前一阶观察合同下的隐藏坐标，不是观察无关的信息荷。未来响应只在固定共同来源、共同事件空间和共同核下沿纤维线性变化；J 非零恢复可变一维纤维，零长度纤维已被边界确定。有限样本与完整律级恢复须分开。
- **Q3** （§4）Fibonacci 权重须来自 Zeckendorf 非重复正规权重的连续段，例如 1,2,3,5,... 的段或本文 2,3,5,...；不能把两个重复的 1 当作两个可区分位置。完整谱是完整概率分布，不是单个均值或有限实验记录；这不是光或物理频谱的结论。
- **Q4** （§5）树状缝合要求窗口的 junction tree/running-intersection：每个变量出现的窗口子树连通。任意树形连接图不单独满足该要求。共同 separator 的零质量点可任选条件核而不影响可达质量。环路支持固定点/正迹仍不证明全部指定局部边缘质量可实现。
- **Q5** （§6）separator 维数公式取整数 n>=3，g_n=N_(n-4) 取 n>=4；一般纤维维数须按有效正支持计算。一阶与完整 separator 的隐藏维数是不同线性观察合同，不能据维数直接推动态可执行记忆。
- **Q6** （§7）Fréchet 区间比较要求两组数据都满足 0<=R_q,C_q<=s_q 且 epsilon>=0，使两个区间非空；空区间的 Hausdorff 距离不能套用该式。宽度公式依赖同一可行性条件；本结论是端点的确定性扰动界，不是抽样误差或 return variation 原生桥。
- **Q7** （§8）P 为非空有限维 polytope，p 属于 P_b。Caratheodory 的 d_b+1 是每个点可选的表示大小，不保证一个共同的至多 d_b+1 元集合覆盖整个纤维；共同覆盖可用全部纤维顶点。纤维极点通常是有边界约束的混合律，未必是原始硬状态。
- **Q8** （§8）需要表达所有 g_n 方向指生成器的仿射张成包含目标纤维的实际切方向；固定单个完整 law 的表示不必张成所有可能 law 的方向。该有限多面体结论未认证仓库 complete-law flow 的共同来源、同预算、收缩条件或操作实现。
- **Q9** （§9）K、L 取正整数，通常 K>=2；若窗口按不同周期位置读取，取 L>=K，短周期需显式按重复索引的周期词解释。总占用上界可由全部 L 个圆窗不等式求和后取整得到；模障碍是必要排除证书，不宣称穷尽任意局部 law 的全局闭合障碍。
- **Q10** （§10）可实现性与可观测恢复是不同判据。多参数响应 map 为 sum_q J_q kappa_q；每个 J_q 单独非零只保证该方向一维切片可见，联合恢复要求这些对比在实际切空间上共同单射，不能以逐基向量非零替代满列秩。
- **Q11** （§§10–11）周期质量闭合应以指定全部边缘的 loop-coupling 可行性定义；支持 holonomy 或 transfer trace 只是较弱证书。完整未来需逐输出 instrument 与合法菜单/Stop，而不是无标签平均 transfer。有限维、有限生成器、有限状态和有限比特不相同。
- **Q12** （§11）information escape 与仓库审计术语的对应是参考模型：本文没有提供四槽注册、内核证明或 native bridge。不同层摘要的共同实现、资源、控制与历史更新仍须逐项证明；统一命名不把数个未证桥接为一个已证系统。

## 完整供文

## 续篇：把 AURIC FIB ATOM 金字塔提升为“观察分辨率—隐藏环流—信息逃逸”理论

这一轮继续推进的核心不是再增加一个新的符号，而是把此前的五态结构放进一个更一般的框架：

$$
\boxed{
\text{观察分辨率}
\longrightarrow
\text{隐藏关系}
\longrightarrow
\text{可见响应}
\longrightarrow
\text{全局闭合}.
}
$$

当前 trureturing 的公开研究方向已经明确把“信息在哪里逃逸、增加什么读出可以找回、还剩哪些不可区分状态”作为一个独立判据系统。[GitHub](https://github.com/the-omega-institute/trureturing?utm_source=chatgpt.com) 当前开放工作列表中也仍然包含 AURIC FIB 金字塔与 escape dynamics、thermodynamic action 以及 typed bridge 的连接任务。[GitHub](https://github.com/the-omega-institute/trureturing/pulls?utm_source=chatgpt.com)

这与 AURIC 的隐藏坐标 $\kappa$ 正好对应：

- $\kappa$ 是信息逃逸的位置；
- $S^2$、$\chi$ 或未来响应律是新增读出；
- $J_{\mathscr L}$ 是新增读出对逃逸信息的灵敏度；
- 环路 holonomy 是信息在全局拼接后是否仍然闭合的条件。

仍然使用固定约定：

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

其中 $1,2,3$ 是索引，$2,3,5$ 是 Fibonacci 取值。

---

## 1. 一、定义：观察读出与信息逃逸

设 $\Omega$ 是合法局部状态集合，$\mathcal M(\Omega)$ 是其上的有限 signed measure 空间。

对任意线性读出

$$
R:\mathcal M(\Omega)\to V_R,
$$

定义读出 $R$ 的隐藏空间为

$$
\mathcal K_R=
\ker R\cap
\left\{
h:\sum_{\omega\in\Omega}h(\omega)=0
\right\}.
$$

若两个概率律 $p,q$ 满足

$$
R(p)=R(q),
$$

则它们的差

$$
h=p-q
$$

属于 $\mathcal K_R$。

因此，固定读出值后的概率纤维是

$$
\mathcal F_R(b)=
\left\{
p\in\Delta(\Omega):R(p)=b
\right\}.
$$

在一般内部点附近，其仿射维数就是

$$
\dim \mathcal K_R.
$$

---

### 定义 1：读出精化序

若两个读出 $R_1,R_2$ 满足

$$
R_1=A\circ R_2
$$

其中 $A$ 是线性映射，则称 $R_2$ 比 $R_1$ 更精细。

此时

$$
\ker R_2\subseteq\ker R_1,
$$

因此

$$
\boxed{
\mathcal K_{R_2}\subseteq\mathcal K_{R_1}.
}
$$

读出越精细，隐藏空间越小。

---

### theorem 1.1: 定理 1：观察分辨率单调定理

若 $R_2$ 精化 $R_1$，则：

1. $R_1$ 能区分的状态，$R_2$ 一定能区分；
2. $R_2$ 仍然无法区分的状态，$R_1$ 一定也无法区分；
3. 隐藏维数满足
   $$
   \dim\mathcal K_{R_2}
   \le
   \dim\mathcal K_{R_1}.
   $$

#### 证明

由

$$
R_1=A\circ R_2
$$

可得

$$
R_2(h)=0
\quad\Longrightarrow\quad
R_1(h)=A(R_2(h))=0.
$$

所以

$$
\ker R_2\subseteq\ker R_1.
$$

与总质量零条件相交后仍有包含关系，因此隐藏空间维数单调不增。证毕。

---

## 2. 二、AURIC 的三个观察层

对三位 Fibonacci 窗口，存在三个自然读出。

### 1. 一阶金字塔读出

$$
R_1(p)=(X,Y,Z).
$$

它只记录

$$
X=\mathbb E[x],
\qquad
Y=\mathbb E[y],
\qquad
Z=\mathbb E[z].
$$

隐藏方向为

$$
h_{13}=
\delta_{101}
-\delta_{100}
-\delta_{001}
+\delta_{000}.
$$

也就是

$$
h_{13}=
(1,-1,0,-1,1)
$$

按状态顺序

$$
(000,100,010,001,101).
$$

所以

$$
\dim \mathcal K_{R_1}=1.
$$

### 2. 二阶联合读出

增加

$$
\kappa=\mathbb E[xy].
$$

于是

$$
R_2(p)=(X,Y,Z,\kappa).
$$

因为五态分布满足归一化约束，所以

$$
(X,Y,Z,\kappa)
$$

已经可以唯一恢复整个概率律：

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

因此

$$
\dim \mathcal K_{R_2}=0.
$$

### 3. 未来律读出

给每个模式赋予一个未来概率律：

$$
\mathscr L_0,\quad
\mathscr L_1,\quad
\mathscr L_2,\quad
\mathscr L_3,\quad
\mathscr L_{13}.
$$

未来混合律为

$$
\overline{\mathscr L}(p)=
\sum_I p_I\mathscr L_I.
$$

沿隐藏方向变化为

$$
\frac{d}{dt}
\overline{\mathscr L}(p+th_{13})=
\mathscr L_{13}-\mathscr L_1-\mathscr L_3+\mathscr L_0.
$$

定义

$$
\boxed{
J_{\mathscr L}=
\mathscr L_{13}-\mathscr L_1-\mathscr L_3+\mathscr L_0.
}
$$

则

$$
J_{\mathscr L}=0
$$

意味着未来律仍然看不见 $\kappa$，而

$$
J_{\mathscr L}\neq0
$$

意味着未来读出可以恢复 $\kappa$。

---

## 3. 三、信息逃逸定理

trureturing 当前“information escape”框架可以在 AURIC 中精确翻译为以下定义。

### 定义 2：读出逃逸对

给定完整读出 $R_{\mathrm{full}}$ 和当前读出 $R$，若存在两个状态 $p\neq q$，满足

$$
R_{\mathrm{full}}(p)\neq R_{\mathrm{full}}(q),
$$

但

$$
R(p)=R(q),
$$

则称 $(p,q)$ 是相对于 $R$ 的信息逃逸对。

在 AURIC 中：

- 完整读出为 $(X,Y,Z,\kappa)$；
- 当前金字塔读出为 $(X,Y,Z)$；
- 任意两个不同 $\kappa$ 的同一基础纤维点，都是信息逃逸对。

---

### theorem 3.1: 定理 2：AURIC 信息逃逸的唯一生成元

对于三位 AURIC 五态系统，所有相对于一阶读出 $R_1=(X,Y,Z)$ 的信息逃逸方向，都由

$$
h_{13}=
\delta_{101}
-\delta_{100}
-\delta_{001}
+\delta_{000}
$$

线性生成。

#### 证明

概率分布有五个坐标，归一化给出一个约束。三个一阶坐标再给出三个独立约束。因此剩余维数为

$$
5-1-3=1.
$$

而 $h_{13}$ 保持总质量、$X$、$Y$、$Z$ 不变，因此它是非零隐藏方向。由于隐藏空间维数为 $1$，它生成整个隐藏空间。证毕。

这说明 AURIC 的“隐藏关系”不是很多个未命名的偶然关系，而是一个精确的一维信息逃逸通道。

---

## 4. 四、隐藏关系的谱结构：均值看不见，完整 Fibonacci 光谱能看见

设模式 $w$ 的 Fibonacci 加法值为

$$
S(w)=\sum_i a_i x_i,
$$

其中 $a_i$ 取连续 Fibonacci 值，例如三位窗口取

$$
(a_1,a_2,a_3)=(2,3,5).
$$

于是五个状态的取值为

$$
0,\quad 2,\quad 3,\quad 5,\quad 7.
$$

对隐藏方向 $h_{13}$，其矩母函数贡献为

$$
H_{13}(t)=
e^{7t}-e^{2t}-e^{5t}+1.
$$

在 $t=0$ 处：

$$
H_{13}(0)=1-1-1+1=0.
$$

一阶导数为

$$
H_{13}'(0)=7-2-5=0.
$$

二阶导数为

$$
H_{13}''(0)=49-4-25=20.
$$

所以：

$$
\boxed{
\text{总质量看不见 }\kappa,
\qquad
\text{均值看不见 }\kappa,
\qquad
\text{二阶矩看见 }\kappa.
}
$$

这并不是数值巧合，而是隐藏方向本身满足：

$$
7=2+5.
$$

因此

$$
\delta_{[2,5]}-\delta_{[2]}-\delta_{[5]}+\delta_{\mathrm{null}}
$$

自动消去所有一阶加法读出。

---

### theorem 4.1: 定理 3：完整 Fibonacci 光谱的可恢复性

若 $a_1,a_2,\dots,a_n$ 是连续 Fibonacci 取值，并限制合法状态不含相邻 $1$，则映射

$$
w\longmapsto S(w)=\sum_i a_iw_i
$$

在合法词集合上是单射。

因此完整的 $S$-分布

$$
\Pr(S=s)
$$

可以恢复每个合法模式的概率；而单独的均值

$$
\mathbb E[S]
$$

一般不能恢复隐藏联合坐标。

#### 证明

合法词的 $1$ 出现位置构成一个无相邻的 Fibonacci 子集。Zeckendorf 唯一性说明每个正整数至多有一个不含相邻 Fibonacci 项的表示。因此不同合法词给出不同的 $S$ 值。

如果知道完整分布 $\Pr(S=s)$，则每个 $s$ 对应唯一合法词，所以可以反推出每个状态概率。

但均值只给出一个线性泛函。对于 $h_{13}$，

$$
\langle S,h_{13}\rangle=
7-2-5+0=0.
$$

所以均值不能区分同一 $(X,Y,Z)$ 纤维中的不同 $\kappa$。证毕。

这给出了一个重要区分：

$$
\boxed{
\text{Fibonacci 标量平均读出}
\neq
\text{Fibonacci 完整谱读出}.
}
$$

前者是低分辨率投影，后者在合法状态上可以成为完整坐标。

---

## 5. 五、边界—体定理：AURIC 金字塔是局部边界读出

把一个长度为 $n$ 的合法词

$$
w=a_1a_2\cdots a_n
$$

看成一条运输边：

$$
a_1\cdots a_{n-1}
\longrightarrow
a_2\cdots a_n.
$$

左端和右端就是两个 boundary separator。

### 定义 3：边界映射

设

$$
\mathcal P_n=
\Delta(W_n)
$$

是所有合法长度 $n$ 词的概率单纯形。

定义 prefix-suffix 边界映射：

$$
B_n:\mathcal P_n
\to
\Delta(W_{n-1})\times\Delta(W_{n-1})
$$

将一个 $n$-词分布送到其 prefix 和 suffix 边缘。

固定边界后，内部所有可能分布构成

$$
\mathcal F_n(b)=
B_n^{-1}(b).
$$

---

### theorem 5.1: 定理 4：树上边界充分性，环上边界不充分性

若多个局部窗口的连接图是树，并且相邻 separator 边缘一致，则局部概率律可以通过 Markov gluing 组成全局概率律。

若连接图含环，则边缘一致性一般只保证局部可拼接，不保证全局闭合；还必须满足环路 holonomy 条件。

#### 证明

对树结构，从一个根窗口开始。若相邻窗口 $p_{AB}$ 和 $p_{BC}$ 的共同边缘 $p_B$ 一致，则在 $p_B>0$ 处定义条件核

$$
K_{C|B}(c|b)=
\frac{p_{BC}(b,c)}{p_B(b)}.
$$

然后递归构造

$$
p_{ABC}(a,b,c)=
p_{AB}(a,b)K_{C|B}(c|b).
$$

由于树上每增加一个窗口只连接到一个已有 separator，局部相容性足以保证递归构造不产生矛盾。

如果连接图含环，最后一个窗口会同时受到两个方向的边界条件约束。此时必须满足 transfer product 的固定点或周期闭合条件。局部边缘相容并不能自动保证这一点。证毕。

因此：

$$
\boxed{
\text{树：边界相容}\Rightarrow\text{可延拓};
\qquad
\text{环：还需要 holonomy 闭合}.
}
$$

这正好对应 trureturing 中“局部 agreement 可能失败于全局”的总体研究方向。

---

## 6. 六、观察分辨率与隐藏维数的严格差别

对于长度 $n$ 的 Fibonacci 合法词，令

$$
N_n=|W_n|,
\qquad
N_0=1,\quad N_1=2,\quad N_n=N_{n-1}+N_{n-2}.
$$

三种读出对应三种不同的隐藏维数。

### 一阶读出

只固定

$$
m_i=\mathbb E[x_i].
$$

则

$$
\boxed{
d_n=N_n-1-n.
}
$$

这几乎与整个状态空间同阶增长。

### 完整 prefix/suffix 读出

固定所有长度 $n-1$ 的 prefix 和 suffix 边缘，隐藏维数为

$$
\boxed{
g_n=N_n-2N_{n-1}+N_{n-2}.
}
$$

对于 $n\ge4$，

$$
g_n=N_{n-4}.
$$

因此：

$$
g_3=1,\qquad
g_4=1,\qquad
g_5=2,\qquad
g_6=3,\qquad
g_7=5.
$$

### 全量读出

若直接读出每个合法词的概率，则

$$
\dim\mathcal K_{\mathrm{full}}=0.
$$

于是出现一个严格的“投影分辨率阶梯”：

$$
\boxed{
N_n-1-n
\;\ge\;
N_n-2N_{n-1}+N_{n-2}
\;\ge\;
0.
}
$$

第一项是被一阶占用读出隐藏的高阶关系总量；第二项是完整 separator 已经消掉大部分高阶关系后剩余的运输环流；最后的零表示完整状态读出没有隐藏。

---

## 7. 七、隐藏纤维的稳定性定理

当前项目对 return compatibility 和 response variation 的研究可以在 AURIC 层面转化为一个简单但重要的稳定性定理。

对某个固定内部词 $q$，记：

- $s_q$：总质量；
- $R_q$：左端 $1$ 的质量；
- $C_q$：右端 $1$ 的质量。

则

$$
\kappa_{q,-}=
\max(0,R_q+C_q-s_q),
$$

$$
\kappa_{q,+}=
\min(R_q,C_q).
$$

假设边界数据扰动为

$$
|s_q-s_q'|\le\varepsilon,
\qquad
|R_q-R_q'|\le\varepsilon,
\qquad
|C_q-C_q'|\le\varepsilon.
$$

### theorem 7.1: 定理 5：Fréchet 纤维稳定性

有

$$
|\kappa_{q,+}-\kappa_{q,+}'|
\le\varepsilon,
$$

以及

$$
|\kappa_{q,-}-\kappa_{q,-}'|
\le3\varepsilon.
$$

因此两个隐藏区间的 Hausdorff 距离满足

$$
\boxed{
d_H(I_q,I_q')\le3\varepsilon.
}
$$

若宽度定义为

$$
w_q=
\kappa_{q,+}-\kappa_{q,-}=
\min(R_q,C_q,s_q-R_q,s_q-C_q),
$$

则

$$
\boxed{
|w_q-w_q'|\le2\varepsilon.
}
$$

#### 证明

因为 $\min$ 和 $\max$ 都是 $1$-Lipschitz，

$$
|\min(R_q,C_q)-\min(R_q',C_q')|
\le\varepsilon.
$$

又

$$
|(R_q+C_q-s_q)-(R_q'+C_q'-s_q')|
\le3\varepsilon.
$$

再次使用 $\max(0,\cdot)$ 的 Lipschitz 性，得到下端点的 $3\varepsilon$ 上界。

对于宽度，四个候选量的变化分别不超过

$$
\varepsilon,\quad
\varepsilon,\quad
2\varepsilon,\quad
2\varepsilon.
$$

最小值的变化不超过最大变化量 $2\varepsilon$。证毕。

这个结果的意义是：边界测量有小误差时，隐藏 $\kappa_q$ 不是任意跳跃的；其可行区间以显式常数稳定变化。

---

## 8. 八、有限共同生成器与 AURIC 纤维

当前项目关于 compatible complete-law flows 和 finite common generators 的工作，可以在有限 AURIC 窗口中先得到一个完全严格的有限版本。

设 $P$ 是一个有限维概率多面体，$b$ 是边界读出。定义边界纤维

$$
P_b=\{p\in P:B(p)=b\}.
$$

若 $P_b$ 的仿射维数为 $d_b$，则 Carathéodory 定理给出：

### theorem 8.1: 定理 6：有限边界纤维的共同生成器界

每个 $p\in P_b$ 都可以表示为至多

$$
d_b+1
$$

个极点或生成状态的凸组合。

对于只观察 AURIC 的基础金字塔 $P$，其维数为 $3$，所以每个基础点至少存在一个至多四个顶点的凸表示。

但是，如果要求共同生成器同时保留 $\kappa$，则必须让生成器张成隐藏方向

$$
h_{13}.
$$

只保留 $(X,Y,Z)$ 的生成器不能区分不同 $\kappa$。

因此：

$$
\boxed{
\text{共同生成器只保留边界}
\Rightarrow
\text{可丢失 }\kappa;
}
$$

$$
\boxed{
\text{共同生成器保留完整局部律}
\Rightarrow
\text{必须覆盖每个环流方向}.
}
$$

在长窗口中，若完整 separator 后还有 $g_n$ 个独立环流，那么任何精确的共同生成器结构都必须能够表达这 $g_n$ 个方向，除非未来仪器本身将其中某些方向商掉。

这连接了两个看似不同的问题：

- 兼容 complete-law flows 如何由有限共同生成器实现；
- AURIC 的隐藏 $\kappa_q$ 如何在边界拼接后保留下来。

它们的共同核心都是：

$$
\boxed{
\text{共同边界不等于共同内部律}.
}
$$

---

## 9. 九、KBonacci 环路中的模障碍

把 Fibonacci 禁止相邻 $1$ 推广为禁止连续 $K$ 个 $1$。

设周期长度为 $L$，局部圆窗条件为

$$
\sum_{j=i}^{i+K-1}x_j\le K-1.
$$

该局部条件允许均匀软点

$$
x_i=\frac{K-1}{K}.
$$

但任意合法硬周期词中，每个连续块最多有 $K-1$ 个 $1$，所以每个周期块至少需要一个 $0$。因此零的数量至少为

$$
\left\lceil\frac LK\right\rceil.
$$

硬周期词的总占用最多为

$$
L-\left\lceil\frac LK\right\rceil=
\left\lfloor\frac{L(K-1)}K\right\rfloor.
$$

而均匀软点的占用为

$$
\frac{L(K-1)}K.
$$

因此定义环路缺口

$$
\eta_{K,L}=
\frac{L(K-1)}K
-
\left\lfloor\frac{L(K-1)}K\right\rfloor.
$$

则：

$$
\eta_{K,L}>0
\quad\Longleftrightarrow\quad
K\nmid L.
$$

### theorem 9.1: 定理 7：KBonacci 周期刚化障碍

当

$$
K\nmid L
$$

时，均匀软点不能表示为合法硬周期词的凸组合。

#### 证明

软点总占用严格大于所有硬周期词的最大总占用：

$$
\frac{L(K-1)}K
>
\left\lfloor\frac{L(K-1)}K\right\rfloor.
$$

线性占用泛函在凸组合下不超过各顶点的最大值，因此该软点不属于硬周期词凸包。证毕。

Fibonacci 情形是

$$
K=2.
$$

当 $L$ 为奇数时，

$$
\eta_{2,L}=\frac12.
$$

所以 C5 的半填充障碍不是孤立现象，而是一般模 $K$ 环路缺口的最小实例。

---

## 10. 十、统一定理：AURIC 的四层可判定结构

现在可以把整个理论压缩成一个统一命题。

### theorem 10.1: 定理 8：AURIC 四层可判定定理

给定一个 AURIC 或 KBonacci 局部概率系统，其全局状态能否被当前观察模型完整恢复，必须分别检查以下四层：

### 层 1：支持层

基础软坐标是否属于合法硬状态凸包。

例如 Fibonacci 路径需要满足稳定集约束；周期图还需要额外环路不等式。

### 层 2：边界层

相邻窗口的 separator 边缘是否一致。

这决定局部 law 是否能够进行边界拼接。

### 层 3：纤维层

隐藏环流 $\kappa_q$ 是否位于其 Fréchet 区间：

$$
\kappa_{q,-}
\le
\kappa_q
\le
\kappa_{q,+}.
$$

### 层 4：未来层

未来响应是否能区分隐藏方向。

对响应律 $\mathscr L$，检查

$$
J_{\mathscr L,q}=
\mathscr L_{1q1}
-\mathscr L_{1q0}
-\mathscr L_{0q1}
+\mathscr L_{0q0}.
$$

若

$$
J_{\mathscr L,q}=0,
$$

该环流方向对该响应不可见；若非零，则可以恢复相应的 $\kappa_q$。

在周期系统中，还要额外检查所有 transfer product 的 holonomy 闭合。

#### 证明

层 1 失败时不存在任何全局硬状态实现，隐藏纤维无法修复它。

层 1 成立但层 2 失败时，局部 law 不能进行 seam gluing。

层 2 成立但层 3 失败时，局部边界相容但概率质量可能出现负值。

层 3 成立但层 4 的响应对比为零时，系统可以存在多个不同内部 law，却被当前未来仪器识别为同一个状态。

对于闭环，还需检查 transfer product 的周期闭合；因此四层条件共同组成完整判定链。证毕。

---

## 11. 十一、对当前项目的直接解释

按照 trureturing 当前的 information-escape 语言，AURIC 五态结构可以直接写成：

| 项目问题 | AURIC 对应物 |
|---|---|
| 信息在哪里逃逸？ | $\kappa=p_{13}$，或者长窗口的 $\kappa_q$ |
| 为什么逃逸？ | 当前读出只保留 $(X,Y,Z)$，没有保留合法独立集的二阶联合 |
| 加什么读出可以找回？ | $\chi=z+xy$、$S^2$、完整 Fibonacci 光谱或未来响应 $\mathscr L$ |
| 新信息是什么？ | $\kappa$、$\Delta$、局部 square-cycle flow |
| 还有什么继续逃逸？ | 长窗口的高阶独立集矩、环路 holonomy、无界历史计数 |
| 什么时候可形成有限记忆？ | 只有当 separator、cycle 和 history 三层都被有限可辨识地商掉 |

所以 AURIC FIB ATOM 金字塔的更深定义可以写成：

$$
\boxed{
\text{金字塔不是完整状态空间，而是完整关系几何的一个观察切面。}
}
$$

它保留了：

$$
\text{单点占用}
$$

却可能丢失：

$$
\text{端点联合、局部环流、未来响应差异和全局 holonomy}.
$$

因此 $\kappa$ 不是一个附加参数，而是“边界读出无法唯一代表内部”的最小数学证据。

下一步最值得形式化的对象是：

$$
\mathrm{EscapeKernel}(R)=
\ker R\cap\{\text{总质量为零的 signed laws}\},
$$

以及：

$$
\mathrm{CycleBasis}(B_n)=
\{h_q:q\text{ 产生 }2\times2\text{ square cycle}\}.
$$

一旦这两个对象在 Lean 中建立起来，AURIC、信息逃逸、common-law flow 和 future quotient 就不再是四套叙事，而会成为同一个边界—内部—读出理论的不同投影。

## 追加锚（本行以下为增补区）
