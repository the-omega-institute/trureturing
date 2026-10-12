# AURIC FIB ATOM：环流读出、控制接口、KL 作用量与 toric 关系

**Reference input: open.** 本卷保存完整用户供文，包含全部声明、证明、例子、表格、项目对应和拟议接口。原文的定理及证明语言归属开放参考输入；本卷没有新增 Lean、Blueprint、Reg 或 Frozen 声明。Lean 声明、证明项及其经内核核验的公理闭包承载本库形式系统内的数学真值。

**来源。** Author kind: mixed user-supplied material; original author and model unknown. Receipt date: 2026-10-10. 来源标识为本会话供文 auric-fib-atom-circulation-control-kl-action-and-toric-relations。接收原文 SHA-256 为 `c2c8ea634f379eab68c9da29f0d2e1cc2e11c45bb22dcd824ebd5a3325f0e421`，字节数为 31352。全部原句与公式内容保留，只规范 Markdown 数学入口、标题层级和结构空行。声明地址用于本文定位。按用户指定，本卷是纯理论添加，不运行消化，不新增 atom 或覆盖主张。

**既有结果与归属。** 供文关于 dev、PR 和公开研究列表的当前性归属其引用的历史快照，不认证移动分支的交付状态。线性核、运输环空间、Zeckendorf 唯一性、Caratheodory 表示和 finite-instrument 观测方法属于既有数学；此处保留其在指定 AURIC 合同中的综合推导，不将重述计作原创。参见 [Output-Resolved Instrument Closure](AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md)、[Boundary, Transport Fibers and Loop Closure](AURIC_FIB_ATOM_BOUNDARY_TRANSPORT_FIBERS_AND_LOOP_CLOSURE.md) 及 [Joint Projection, Multiwindow Order and Response Fibers](AURIC_FIB_ATOM_JOINT_PROJECTION_MULTIWINDOW_ORDER_AND_RESPONSE_FIBERS.md)。本文未认证抽象模型的 native 实现、资源等价或物理解释。

## 编者限定与开放义务

以下限定同完整供文分开；它们不替代原句，也不认证原文定理。

- **Q1** （供文第一部分 §§1–2）运输图取左右顶点分开的二部 graph，010 是另一个组件的一条桥，不是把两个组件连接起来的桥。合并同名 pair-state 得到的有向 overlap graph 是另一对象。h 是零边界 signed direction，kappa=p_13 是边坐标，沿固定边界的差才是环流系数。E-V+c 是线性核维数，实际非负纤维可能退化。
- **Q2** （第一部分 §2）定理 2 证明的是线性读出的识别维数，不是实际控制数。满列秩 iff 在完整 g 维可行切空间上成立；实际纤维低维或单点时必须取其仿射方向。读出可见不自动证明对应动作可取得、可执行或可改变状态；需要控制 map、允许幅度及可行域。
- **Q3** （第一部分 §§2、7）保持基础边界的控制方向应属于 ker pi，且在实际隐藏切空间有非零分量；源 §7 的 c 不属于 ker pi 并非必要条件，c=h 正好属于 ker pi。观察与控制的非零配对不构成可观测且可控制的自动定理。可控仅限被声明可执行、且在非负纤维中有可行增量的方向。
- **Q4** （第一部分 §3）取 r=1-Z>0，固定合法边界，且底层四格 p_0,p_1,p_3,p_13 在非退化纤维内部严格正；独立参考四格也正。p_2=Z 可为零，以共同支持的 0 log(0/q)=0 约定定义 KL。边界处梯度可能无穷，不沿用内部导数式；Z=1 的条件截面除法未定义。
- **Q5** （第一部分 §§3、6–7）KL 作用量是 dimensionless relative entropy，沿该纤维为 r 倍的条件 mutual information；它不是已定义的轨迹作用量、耗散能量、控制成本或自由能。Delta 与 log odds ratio 在内部同号，下降驱动还需具体动力学或梯度流的符号和 mobility。log n 的算术变化也未证明任何物理能耗解释。
- **Q6** （第一部分 §4、第二部分 §§10–11）原联合质量 transfer 矩阵 T 的乘积一般不以特征值 1 为周期全局律存在的必要条件。若要使用周期核固定点，须先规定行/列归一化及时间约定；即便归一化，固定点也不充分：奇环交换 product 有均匀不变向量，但没有对应闭合支持轨迹。指定全部局部质量的精确判据是 loop-coupling polytope 非空；正迹仅保证某个支持闭环。
- **Q7** （第一部分 §4）在线性化闭合解处 H=0，右端为零不代表已有非零缺陷被消除。若固定 v，并要求控制覆盖全部 Im D_kappa H，控制有效秩须等于该像维数；仅修复一个指定缺陷不必需要该维数个方向。任意 r 维缺陷空间可达需要它包含于控制 Jacobian 的像。非线性局部可解还需完整 IFT 的目标满秩、允许扰动、归一化和正性条件，不能由像内满秩自动推出。
- **Q8** （第一部分 §§4–6）采用行向量传播时一般按时间顺序乘 T_1...T_L，不能无约定反转非交换乘积。局部有一个 kappa 不决定全局控制维数；长窗 separator rank 公式限于其指定有限支持与 n>=3。整数比 n(kappa+1)/n(kappa)=7/10 只在两个相邻指数点都满足盒约束时作为合法交换。
- **Q9** （第一部分 §8）所有长度的一阶参数导数在一个点为零，只证明该点的一阶不可见，不证明不同参数的精确 future law 相等。应比较全合法词级响应，并递归使用每个输出子核 M_(a,o)，包含动作、guard 和 Stop。源定理 8 的 U(p+h)-U(p)=Uh 要求 U 是 signed-law 上的线性更新；若 U 原指函数拉回，须使用对偶 pushforward。
- **Q10** （第一部分 §9、第二部分 §11）任意基础 projection kernel 不自动等于任意运输 graph 的 circulation kernel，需明确边缘 adapter。p_13、a_7 与范数赋值来自不同载体，连等式是结构类比；只有专门构造 U 下 a_7=v_5(|N(U)|) 是数值等式。统一叙事不认证共同来源、控制实现或资源等价。
- **Q11** （第二部分开头、§§9–11）供文的 BIND-ONLY 是自定证据标签；仓库的 proof_shape: bind-only 则按证明形状判断既有结果的实例化、投影和规范化。一个 bind-only 证明仍可经 Lean kernel 验证，不能同未验证草案或 PR 标题混为一类；是否允许新增声明另依仓库 consumed-helper 等准入规则。本卷不写机器 Verified/Computed 状态，纸面证明也不自动升级为内核结果。
- **Q12** （第二部分 §§2–3）线性关系属于模式列向量配置，并非完整五态单位质量彼此相等。toric 核是指定 monomial parametrization 的理想，Delta=0 刻画该独立子模型的 Zariski closure，不是所有合法五态概率都必须满足的恒等式。条件独立解释要求 1-Z>0；二次 hypersurface 不一般是仿射面。
- **Q13** （第二部分 §3）核理想结论还需把任意多项式按其单项式像的指数分组，利用目标多项式的 monomial 线性独立性得到每组系数和为零，进而将组内差写成 binomials。关系格为 Z h、h primitive 且正负支持不交时，binomial 在除去共同 monomial 后为 A^t-B^t，是 A-B 的倍数。只说明一条关系在核中或核格 rank 为一，不能跳过这一核生成论证。
- **Q14** （第二部分 §§5、8）补充读出判据取线性 R，或在实际仿射纤维上已知斜率的仿射 R；任意非线性函数不能由 R(h) 的一个值判全局单射。Golden norm 组合读数依其专门恒等式等于 a_7，恢复不等于将 norm 直接延拓为 signed-law 线性读口。固定可变纤维、共同来源和完整律级观察仍为前提。
- **Q15** （第二部分 §§9–11）自定证据传播规则只在有明确 sound inference rule 和已核验前提/证明闭包时给出形式结果。本卷完整保留源证据标签、拟议接口与有限推导，不将其写成仓库证明状态，也没有证明 native continuation、common cyclic control、escape dynamics 或实际热力学定理。

## 完整供文

## 续篇：从隐藏坐标到环流控制、热力学作用量与全局闭合

这一轮可以把 AURIC FIB ATOM 金字塔再提升一层：

$$
\boxed{
\text{隐藏关系}
\longrightarrow
\text{环流荷}
\longrightarrow
\text{控制自由度}
\longrightarrow
\text{热力学作用量}
\longrightarrow
\text{全局 holonomy}.
}
$$

当前 trureturing 的公开工作线已经出现了几个与这一结构直接对应的方向：

- AURIC FIB 金字塔与 escape dynamics、thermodynamic action 的连接；
- acquired circulation 与 generated boundary laws 的关系；
- exact common cyclic control minimum；
- verified FIB escape-audit applications。[GitHub](https://github.com/the-omega-institute/trureturing/pulls?utm_source=chatgpt.com)

这些仍然是开放研究方向，不能直接视为已经合并并由 Lean 完成的定理。下面把其中能够从 AURIC 五态结构严格推出的部分形式化出来。

---

## 1. 一、AURIC $\kappa$ 不只是隐藏坐标，而是“环流荷”

仍然使用：

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

五个合法状态为：

$$
000,\quad 100,\quad 010,\quad 001,\quad 101.
$$

概率向量为：

$$
p=(p_0,p_1,p_2,p_3,p_{13}).
$$

基础投影为：

$$
X=p_1+p_{13},
$$

$$
Y=p_3+p_{13},
$$

$$
Z=p_2.
$$

隐藏坐标为：

$$
\kappa=p_{13}.
$$

对应的隐藏方向是：

$$
h=
(1,-1,0,-1,1).
$$

这意味着一个概率律可以沿着

$$
p\longmapsto p+t h
$$

变化，而不改变

$$
(X,Y,Z).
$$

---

### 定义 1：AURIC 环流荷

把五个局部状态看成 pair-state 运输图上的边：

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

$$
010:01\to10.
$$

前四条边构成一个方形环，$010$ 是连接另一分量的桥边。

定义 AURIC 环流荷为方形环上的内部流量：

$$
\mathfrak k(p):=p_{13}.
$$

对应的环流方向为：

$$
h_{\square}=
\delta_{000}
-\delta_{100}
-\delta_{001}
+\delta_{101}.
$$

于是：

$$
\boxed{
\kappa=\mathfrak k(p)
}
$$

不是单纯的状态概率，而是一个边界不可见的内部环流坐标。

---

### theorem 1.1: 定理 1：环流荷由支持图的循环空间决定

对于有限二部支持图 $G$，固定所有顶点的边界流量后，内部隐藏变化空间的维数为：

$$
\boxed{
\dim \ker\partial_G=
|E(G)|-|V(G)|+c(G)
}
$$

其中：

- $E(G)$ 是边数；
- $V(G)$ 是顶点数；
- $c(G)$ 是连通分量数；
- $\partial_G$ 是边流到顶点边界流的映射。

#### 证明

二部图关联矩阵在每个连通分量上有一个行依赖，因此：

$$
\operatorname{rank}(\partial_G)=|V(G)|-c(G).
$$

由秩—零度定理：

$$
\dim\ker\partial_G=
|E(G)|-\operatorname{rank}(\partial_G)=
|E(G)|-|V(G)|+c(G).
$$

若 $G$ 是森林，则

$$
|E(G)|=|V(G)|-c(G),
$$

于是隐藏维数为零。

每增加一个独立环，边数相对于顶点数增加一，隐藏维数增加一。证毕。

---

AURIC 五态图满足：

$$
|E|=5,
\qquad
|V|=6,
\qquad
c=2.
$$

因此：

$$
\dim\ker\partial=
5-6+2=1.
$$

这就是为什么三位 AURIC 只剩一个隐藏坐标 $\kappa$。

---

## 2. 二、控制的最小维数等于隐藏环流维数

当前项目出现“exact common cyclic control minimum”这一方向。它可以先在有限维 AURIC 纤维上形式化。

设基础边界已经固定，隐藏空间为

$$
K=\operatorname{span}\{h_1,\dots,h_g\}.
$$

任意局部律可以写成：

$$
p=p_\star+\sum_{j=1}^g \kappa_jh_j.
$$

这里

$$
\kappa=(\kappa_1,\dots,\kappa_g)
$$

是隐藏环流坐标。

假设有 $m$ 个标量控制或读出：

$$
R_i(p)=\ell_i(p),
\qquad i=1,\dots,m.
$$

它们在隐藏空间上的作用由矩阵

$$
M_{ij}=\ell_i(h_j)
$$

给出。

---

### theorem 2.1: 定理 2：隐藏环流的最小控制维数

若要通过 $m$ 个线性读出唯一恢复 $g$ 个隐藏环流坐标，则必须满足：

$$
m\ge g.
$$

并且当且仅当

$$
\operatorname{rank}(M)=g
$$

时，这些读出能够完整识别隐藏环流。

#### 证明

两个隐藏坐标 $\kappa,\kappa'$ 对应同一个读出，当且仅当：

$$
M(\kappa-\kappa')=0.
$$

若 $M$ 的核非零，则存在不同的隐藏坐标仍然不可区分，因此不能完整恢复。

要使读出映射在 $g$ 维隐藏空间上单射，必须有：

$$
\ker M=\{0\}.
$$

由秩—零度定理：

$$
\operatorname{rank}(M)=g.
$$

而矩阵秩不超过行数 $m$，所以必有：

$$
m\ge g.
$$

当 $m=g$ 且 $M$ 可逆时，恢复最小。证毕。

---

### AURIC 的最小控制

三态 AURIC 中：

$$
g=1.
$$

因此一个独立标量读出就足够恢复 $\kappa$，只要它对隐藏方向不为零。

例如：

### 加法均值

$$
S=2x+3z+5y.
$$

有：

$$
\ell_S(h)=
7-2-5+0=0.
$$

所以均值不能控制或识别 $\kappa$。

### 二阶矩

$$
S^2=4x+9z+25y+20xy.
$$

有：

$$
\ell_{S^2}(h)=20\neq0.
$$

因此一个二阶读出就足够恢复 $\kappa$。

### 指示读出

定义：

$$
\chi=z+xy.
$$

五个状态上的取值为：

$$
(0,0,1,0,1).
$$

于是：

$$
\ell_\chi(h)=1.
$$

所以 $\chi$ 也是最小隐藏坐标读出。

---

### 推论：控制与观察在一维纤维上是对偶的

对于一维隐藏纤维：

- 若一个读出满足 $\ell(h)\neq0$，它能够观察 $\kappa$；
- 若一个控制方向含有 $h$ 分量，它能够改变 $\kappa$。

因此：

$$
\boxed{
\text{一个非零隐藏方向配一个非零配对，就同时具有可观测性与可控制性。}
}
$$

这为 acquired circulation 与 generated boundary laws 之间建立了一个线性代数接口。

---

## 3. 三、热力学作用量：$\Delta$ 是 $\kappa$ 的内部驱动力

固定 $(X,Y,Z)$ 后，概率律由 $\kappa$ 决定：

$$
p(\kappa)=
\left(
1-X-Y-Z+\kappa,\,
X-\kappa,\,
Z,\,
Y-\kappa,\,
\kappa
\right).
$$

条件独立点为：

$$
\kappa_0=\frac{XY}{1-Z}
$$

在 $Z<1$ 时成立。

定义相对于最大熵截面的 KL 作用量：

$$
\mathcal A(\kappa)=
D_{\mathrm{KL}}
\left(
p(\kappa)\,\middle\|\,p(\kappa_0)
\right).
$$

显式写为：

$$
\mathcal A(\kappa)=
\sum_{i\in\{0,1,2,3,13\}}
p_i(\kappa)
\log
\frac{p_i(\kappa)}{p_i(\kappa_0)}.
$$

---

### theorem 3.1: 定理 3：AURIC 作用量的梯度等于相关对数优势

在纤维内部，即所有相关概率均为正时：

$$
\boxed{
\mathcal A'(\kappa)=
\log
\frac{p_0p_{13}}{p_1p_3}
}
$$

并且：

$$
\boxed{
\mathcal A''(\kappa)=
\frac1{p_0}
+
\frac1{p_1}
+
\frac1{p_3}
+
\frac1{p_{13}}
>0.
}
$$

#### 证明

由于

$$
p'(\kappa)=(1,-1,0,-1,1),
$$

且

$$
\sum_i p_i'(\kappa)=0,
$$

KL 散度的导数为：

$$
\mathcal A'(\kappa)=
\sum_i p_i'(\kappa)
\log
\frac{p_i(\kappa)}{p_i(\kappa_0)}.
$$

展开：

$$
\mathcal A'(\kappa)=
\log\frac{p_0}{p_0(\kappa_0)}
-\log\frac{p_1}{p_1(\kappa_0)}
-\log\frac{p_3}{p_3(\kappa_0)}
+\log\frac{p_{13}}{p_{13}(\kappa_0)}.
$$

在 $\kappa_0$ 处满足条件独立：

$$
p_0(\kappa_0)p_{13}(\kappa_0)=
p_1(\kappa_0)p_3(\kappa_0).
$$

所以参考点的比值相消，得到：

$$
\mathcal A'(\kappa)=
\log\frac{p_0p_{13}}{p_1p_3}.
$$

再求导：

$$
\frac{d}{d\kappa}\log p_0=\frac1{p_0},
$$

$$
\frac{d}{d\kappa}\log p_{13}=\frac1{p_{13}},
$$

$$
\frac{d}{d\kappa}(-\log p_1)=\frac1{p_1},
$$

$$
\frac{d}{d\kappa}(-\log p_3)=\frac1{p_3}.
$$

因此：

$$
\mathcal A''(\kappa)=
\frac1{p_0}
+\frac1{p_1}
+\frac1{p_3}
+\frac1{p_{13}}
>0.
$$

证毕。

---

由于

$$
\Delta=p_0p_{13}-p_1p_3,
$$

所以：

$$
\frac{p_0p_{13}}{p_1p_3}=
1+\frac{\Delta}{p_1p_3}.
$$

因此：

$$
\boxed{
\mathcal A'(\kappa)=
\log
\left(
1+\frac{\Delta}{p_1p_3}
\right).
}
$$

这说明 $\Delta$ 不是单纯的代数判别式，而是热力学作用量沿隐藏方向的驱动力。

- $\Delta>0$：作用量沿增大 $\kappa$ 的方向上升；
- $\Delta<0$：作用量沿增大 $\kappa$ 的方向下降；
- $\Delta=0$：作用量驻点，也是最大熵条件独立点。

---

### theorem 3.2: 定理 4：条件独立点是唯一作用量极小点

在非退化纤维内部：

$$
\boxed{
\mathcal A(\kappa)\ge\mathcal A(\kappa_0)=0
}
$$

且等号当且仅当

$$
\kappa=\kappa_0.
$$

#### 证明

KL 散度非负，并且当且仅当两个概率律完全相同时取零。

又因为

$$
p(\kappa)=p(\kappa_0)
$$

当且仅当

$$
\kappa=\kappa_0,
$$

所以结论成立。严格凸性也由

$$
\mathcal A''(\kappa)>0
$$

直接给出。证毕。

---

## 4. 四、闭环控制：局部 $\kappa$ 可能无法同时满足全局 holonomy

对于一个长度为 $L$ 的周期 AURIC 链，令第 $i$ 个局部 transfer 矩阵为：

$$
T_i(\kappa_i).
$$

全局 transfer 为：

$$
\Pi(\kappa_1,\dots,\kappa_L)=
T_L(\kappa_L)\cdots T_1(\kappa_1).
$$

存在全局闭合状态的必要条件是存在非零向量 $v\ge0$，满足：

$$
\Pi(\kappa_1,\dots,\kappa_L)v=v.
$$

定义 holonomy 缺陷：

$$
H(\kappa,v)=
\Pi(\kappa)v-v.
$$

---

### theorem 4.1: 定理 5：闭环控制的线性化秩条件

设某个局部闭合解为 $(\kappa^\star,v^\star)$，并假设 $H$ 在该点可微。

若需要通过隐藏坐标的微小调整消除 $r$ 个独立闭合缺陷，则任意局部控制至少需要：

$$
\operatorname{rank}
D_\kappa H(\kappa^\star,v^\star)
$$

个独立控制方向。

若控制矩阵在该像空间上满秩，则这些控制在局部足以消除 holonomy 缺陷。

#### 证明

线性化为：

$$
D_\kappa H\,\delta\kappa
+
D_vH\,\delta v=
-\;H(\kappa^\star,v^\star).
$$

若固定闭合向量 $v^\star$，则需要通过 $\delta\kappa$ 解决一个线性方程。

可被隐藏坐标调整的缺陷空间正是

$$
\operatorname{Im}(D_\kappa H).
$$

因此需要的独立控制方向至少等于该像空间的维数，也就是：

$$
\operatorname{rank}D_\kappa H.
$$

若控制矩阵在此像空间上满秩，则线性方程可解。由隐函数定理，在适当正则条件下可得到局部非线性闭合。证毕。

---

### AURIC 单环的含义

三位 AURIC 的局部隐藏纤维只有一维：

$$
g=1.
$$

因此，若全局闭环只有一个独立 holonomy 缺陷，则一个非退化的 $\kappa$-控制足够。

但如果系统包含多个独立内部词 $q$，则隐藏坐标变成：

$$
(\kappa_q)_q.
$$

完整 separator 下的隐藏维数为：

$$
g_n=N_n-2N_{n-1}+N_{n-2}.
$$

若全局闭环使这些坐标彼此耦合，则“最小控制数”不再是一个，而至少与闭环缺陷矩阵的秩相同。

所以：

$$
\boxed{
\text{局部只有一个 }\kappa
\quad\not\Rightarrow\quad
\text{长窗口只需要一个全局控制}.
}
$$

---

## 5. 五、基础障碍无法由隐藏控制修复

设基础坐标为 $b$，隐藏坐标为 $\kappa$。整个状态写成：

$$
p=p(b,\kappa).
$$

由于所有 $\kappa$-变化都在投影核中：

$$
\pi(p(b,\kappa))=b.
$$

---

### theorem 5.1: 定理 6：基础投影障碍与隐藏闭合障碍分离

若基础坐标 $b$ 不属于全局基础多面体，则不存在任何 $\kappa$ 使系统成为全局合法状态。

#### 证明

假设存在 $\kappa$，使得 $p(b,\kappa)$ 是全局合法分布。由于基础投影保持不变：

$$
\pi(p(b,\kappa))=b.
$$

但任何全局合法分布的投影都必须属于基础多面体。因此 $b$ 必须属于基础多面体，矛盾。证毕。

---

这意味着判定顺序必须是：

$$
\boxed{
\text{先检查基础多面体，再检查 }\kappa\text{，最后检查 holonomy}.
}
$$

例如 C5 中每个局部窗口都可以采用：

$$
\frac12\delta_{101}
+
\frac12\delta_{010},
$$

局部边缘全部相容，但每个站点占用率为 $1/2$，总占用为：

$$
\frac52.
$$

而 C5 的独立集数上界是 $2$，所以：

$$
\frac52>2.
$$

这属于基础投影障碍，任何 $\kappa$-调整都无法修复。

---

## 6. 六、离散 5040 纤维中的作用量

在整数指数空间中，固定 $(u,v,w)$ 后：

$$
a_2=u-\kappa,
\qquad
a_3=v,
\qquad
a_5=w-\kappa,
\qquad
a_7=\kappa.
$$

对应乘法数为：

$$
n(\kappa)=
2^{u-\kappa}
3^v
5^{w-\kappa}
7^\kappa.
$$

整理得：

$$
n(\kappa)=
2^u3^v5^w
\left(\frac7{10}\right)^\kappa.
$$

因此：

$$
\log n(\kappa)=
u\log2+v\log3+w\log5
+
\kappa\log\frac7{10}.
$$

---

### theorem 6.1: 定理 7：5040 隐藏坐标是离散乘法作用量方向

在固定 $(u,v,w)$ 的整数纤维中，每增加一个 $\kappa$，乘法值按固定比例变化：

$$
\boxed{
\frac{n(\kappa+1)}{n(\kappa)}=
\frac7{10}.
}
$$

#### 证明

直接由：

$$
n(\kappa)=
2^u3^v5^w
\left(\frac7{10}\right)^\kappa
$$

得到：

$$
\frac{n(\kappa+1)}{n(\kappa)}=
\frac7{10}.
$$

证毕。

因此在 5040 编码中，$\kappa$ 不仅是碰撞解除位，也是一个离散作用量方向：

$$
\Delta\log n=
\log\frac7{10}.
$$

AURIC 概率纤维中的作用量是严格凸的 KL 函数；5040 纤维中的作用量在整数方向上是线性的。两者共同表达：

$$
\boxed{
\text{基础投影固定时，隐藏坐标沿一个内部方向改变整体对象的代价。}
}
$$

---

## 7. 七、统一的“可见性—控制—作用量”三元组

现在可以把三个概念写成同一个隐藏方向 $h$ 的三个性质。

### 1. 可见性

给定读出 $\ell$：

$$
\ell(h)\neq0
$$

意味着隐藏关系可被观察。

### 2. 可控制性

给定控制方向 $c$：

$$
c\notin\ker\pi
$$

并且其投影到隐藏空间非零，意味着可以改变隐藏坐标。

### 3. 作用量

给定参考截面 $p_\star$，定义：

$$
\mathcal A(p)=
D_{\mathrm{KL}}(p\|p_\star)
$$

或整数版本：

$$
\mathcal A_{\mathrm{int}}(\kappa)=\log n(\kappa).
$$

它度量沿隐藏方向移动的代价。

因此：

$$
\boxed{
\text{读出回答“能否看到”}
}
$$

$$
\boxed{
\text{控制回答“能否改变”}
}
$$

$$
\boxed{
\text{作用量回答“改变需要付出什么代价”}.
}
$$

在 AURIC 中：

- $S$ 的均值：不可见；
- $S^2$：可见；
- $\kappa$ 本身：可控；
- $\mathcal A(\kappa)$：度量偏离最大熵截面的代价。

在 5040 中：

- $(u,v,w)$：不可见 $a_7$；
- $v_5(|N(U)|)$：可见 $a_7$；
- 改变 $a_7$：需要交换 $2\cdot5\leftrightarrow7$；
- $\log(7/10)$：是该离散交换的乘法作用量。

---

## 8. 八、对动态未来商的推进

设动态系统的隐藏坐标为

$$
\kappa_t.
$$

未来读出为：

$$
f_\ell(\kappa_t)=
\lambda T(\kappa_t)^\ell O.
$$

如果存在某个 $\ell$ 使：

$$
\frac{\partial f_\ell}{\partial\kappa_t}\neq0,
$$

那么当前 $\kappa_t$ 会影响未来。

如果对所有 $\ell$ 都有：

$$
\frac{\partial f_\ell}{\partial\kappa_t}=0,
$$

则该隐藏坐标可以被当前 future quotient 商掉。

但是，若动态维护规则会在下一步重新生成新的边界或新的环流，则一次性 future blindness 不等于长期 memory blindness。

定义：

$$
\Sigma^{(0)}=\text{当前可见摘要},
$$

$$
\Sigma^{(t+1)}=
\Sigma^{(t)}
\cup
\mathrm{Closure}\bigl(\Sigma^{(t)}\bigr).
$$

若存在某个 $t$ 使：

$$
\Sigma^{(t+1)}\neq\Sigma^{(t)},
$$

则当前摘要还没有 future-closed。

---

### theorem 8.1: 定理 8：局部不可见不推出迭代不可见

若某个隐藏方向 $h$ 在一步未来读出下满足：

$$
R_1(h)=0,
$$

但动态更新算子 $U$ 满足：

$$
R_1(Uh)\neq0,
$$

则 $h$ 虽然对一步预测不可见，但对两步预测可见。

#### 证明

一步读出不能区分 $p$ 与 $p+h$。

经过动态更新后，两者差异变为：

$$
U(p+h)-U(p)=Uh.
$$

若

$$
R_1(Uh)\neq0,
$$

则第二步未来读出可以区分它们。证毕。

因此，动态 future quotient 必须至少检查：

$$
\kappa
\longrightarrow
U\kappa
\longrightarrow
U^2\kappa
\longrightarrow
\cdots.
$$

这正是静态 AURIC 纤维与项目中 dynamic future quotient 之间最关键的连接。

---

## 9. 九、最终统一定理

### theorem 9.1: 定理 9：Auric FIB ATOM 隐藏关系的四重结构定理

对于一个由合法 Fibonacci 模式构成的有限关系系统，若基础读出具有非平凡核，则每个隐藏方向同时具有四种可能结构：

1. **投影核方向**
   $$
   h\in\ker\pi;
   $$

2. **运输环流方向**
   $$
   h\in\ker\partial_G;
   $$

3. **未来读出方向**
   $$
   R(h)\neq0
   $$
   时可被恢复，所有 $R(h)=0$ 时被 future quotient 商掉；

4. **作用量方向**
   $$
   \mathcal A(p+th)
   $$
   描述沿隐藏纤维移动的代价。

对于三位 AURIC：

$$
h=h_{\mathrm{AURIC}}=
(1,-1,0,-1,1),
$$

并且：

$$
\kappa=p_{13}
$$

是唯一纤维坐标。

对于 5040 指数编码：

$$
\eta=(-1,0,-1,1),
$$

并且：

$$
\kappa=a_7
$$

是唯一指数纤维坐标。

二者虽不属于同一个状态空间，但都满足：

$$
\boxed{
\text{完整对象}=
\text{基础投影}
+
\text{一维关系纤维}.
}
$$

#### 证明

AURIC 情形由定理 1 得到一维投影核，由运输图循环空间定理得到一维环流空间，由二阶读出或未来对比得到可见性，由 KL 散度得到作用量。

5040 情形由整数投影矩阵的核得到一维指数纤维，由 $v_5(|N(U)|)$ 得到隐藏坐标恢复，由 $\log(7/10)$ 得到离散作用量方向。

两者的共同结构由秩—零度定理和仿射纤维参数化保证。证毕。

---

因此，AURIC FIB ATOM 金字塔的真正基本元素，不只是五个状态：

$$
\mathrm{null},\quad
[2],\quad
[3],\quad
[5],\quad
[2,5].
$$

更深的基本元素是：

$$
\boxed{
\text{状态}
+
\text{关系}
+
\text{投影}
+
\text{核}
+
\text{环流}
+
\text{读出}
+
\text{作用量}.
}
$$

而 $\kappa$ 是最小的非平凡实例：

$$
\boxed{
\kappa=
p_{13}=
a_7=
v_5(|N(U)|)
}
$$

分别从概率、整数、黄金环和动态响应四个切面揭示同一个内部关系。

## 证据边界先行：拒绝 BIND-ONLY 信息

这一轮采用严格的“证据类型系统”。

当前公开仓库把理论 prose、实验、Lean 形式证明和开放问题分开，并明确说明：理论叙述与数值一致性本身不构成 Lean 定理；可复用的结果必须有明确声明、假设、证明和依赖闭包。[github.com](https://github.com/the-omega-institute/trureturing?utm_source=chatgpt.com) 当前公开 PR 列表虽然包含 AURIC FIB、FIB escape-audit、common cyclic control、future laws 等方向，但 PR 标题和绑定关系只能说明研究意图，不能自动成为已证明事实。[github.com](https://github.com/the-omega-institute/trureturing/pulls?utm_source=chatgpt.com)

定义三类证据：

$$
\mathrm{EvidenceLevel}
\in
\{\mathrm{BIND\text{-}ONLY},\mathrm{COMPUTED},\mathrm{VERIFIED}\}.
$$

其中：

- $\mathrm{BIND\text{-}ONLY}$：绑定、标题、未验证 Blueprint、理论草案、未闭合引用；
- $\mathrm{COMPUTED}$：有限枚举、矩阵秩、可复核计算；
- $\mathrm{VERIFIED}$：明确形式定义、无 `sorry` 的 Lean 证明、依赖闭包可检查。

本回答拒绝使用 BIND-ONLY 信息作为证明前提。项目进展只用来确定待形式化问题，下面的数学结论独立来自有限代数、概率和图论。

---

## 10. 一、AURIC 五态关系的代数本体

继续使用：

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

定义五个模式：

$$
\Omega=
\{
\mathrm{null},1,2,3,13
\}.
$$

对应概率坐标：

$$
p_0,p_1,p_2,p_3,p_{13}.
$$

基础投影为：

$$
X=p_1+p_{13},
\qquad
Y=p_3+p_{13},
\qquad
Z=p_2.
$$

令：

$$
\kappa=p_{13}.
$$

则：

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

---

## 11. 二、定理一：唯一的线性隐藏关系

定义模式列向量：

$$
c_{\mathrm{null}}=(1,0,0,0),
$$

$$
c_1=(1,1,0,0),
$$

$$
c_2=(1,0,0,1),
$$

$$
c_3=(1,0,1,0),
$$

$$
c_{13}=(1,1,1,0).
$$

四个坐标分别表示：

1. 总质量；
2. $X$；
3. $Y$；
4. $Z$。

直接计算：

$$
c_{\mathrm{null}}+c_{13}=
(2,1,1,0),
$$

$$
c_1+c_3=
(2,1,1,0).
$$

因此存在基本关系：

$$
\boxed{
c_{\mathrm{null}}+c_{13}=
c_1+c_3.
}
$$

### theorem 11.1: 定理 1

模式列向量之间的整数关系空间是一维，并由原始关系：

$$
\boxed{
(1,-1,0,-1,1)
}
$$

生成。

#### 证明

设整数关系为：

$$
r_0c_{\mathrm{null}}
+r_1c_1
+r_2c_2
+r_3c_3
+r_{13}c_{13}=0.
$$

由 $Z$ 坐标：

$$
r_2=0.
$$

由 $X$ 坐标：

$$
r_1+r_{13}=0.
$$

由 $Y$ 坐标：

$$
r_3+r_{13}=0.
$$

由总质量坐标：

$$
r_0+r_1+r_2+r_3+r_{13}=0.
$$

令：

$$
r_{13}=t.
$$

则：

$$
r_1=-t,
\qquad
r_3=-t,
\qquad
r_2=0,
\qquad
r_0=t.
$$

所以所有关系都是：

$$
t(1,-1,0,-1,1).
$$

取 $t=1$ 得到原始整数关系。证毕。

---

这个结论比“$\kappa$ 没有被观测到”更强：

> 五个 AURIC 原子之间只有一个独立的线性依赖，而 $\kappa$ 正是该依赖的坐标。

---

## 12. 三、定理二：隐藏关系生成唯一的二次代数关系

线性关系可以进一步提升为一个二次关系。

定义多项式映射：

$$
\varphi:
\mathbb R[p_0,p_1,p_2,p_3,p_{13}]
\longrightarrow
\mathbb R[s,x,y,z]
$$

其中：

$$
\varphi(p_0)=s,
$$

$$
\varphi(p_1)=sx,
$$

$$
\varphi(p_2)=sz,
$$

$$
\varphi(p_3)=sy,
$$

$$
\varphi(p_{13})=sxy.
$$

因为：

$$
\varphi(p_0p_{13})=
s^2xy,
$$

而：

$$
\varphi(p_1p_3)=
(sx)(sy)=
s^2xy,
$$

所以：

$$
p_0p_{13}-p_1p_3
$$

属于 $\ker\varphi$。

### theorem 12.1: 定理 2：AURIC 的 toric 关系理想

有：

$$
\boxed{
\ker\varphi=
\left\langle
p_0p_{13}-p_1p_3
\right\rangle.
}
$$

#### 证明

前面的列向量关系空间为一维，并由原始关系：

$$
c_{\mathrm{null}}+c_{13}=c_1+c_3
$$

生成。

对于由有限整数列配置生成的单项式映射，每一个整数关系

$$
u-v=0
$$

对应一个二项式：

$$
p^u-p^v.
$$

这里唯一原始关系对应：

$$
p_0p_{13}-p_1p_3.
$$

由于关系格为一维，任意其他二项式关系都是该原始二项式的多项式倍数。因此核理想由该二项式生成。证毕。

---

定义：

$$
\Delta=
p_0p_{13}-p_1p_3.
$$

于是 $\Delta=0$ 不仅是一个相关性公式，而是 AURIC 五态代数的唯一不可约二项式关系。

代入 $\kappa$ 参数化：

$$
\Delta=
(1-X-Y-Z+\kappa)\kappa
-
(X-\kappa)(Y-\kappa),
$$

从而：

$$
\boxed{
\Delta=(1-Z)\kappa-XY.
}
$$

因此：

$$
\Delta=0
$$

定义的是一个代数簇；在概率单纯形内部，它正好对应：

$$
x\perp y\mid z=0.
$$

这给出更精确的表述：

$$
\boxed{
\text{条件独立面}=
\text{AURIC 唯一 toric 关系面}.
}
$$

---

## 13. 四、隐藏关系的阶数结构

AURIC 中存在三个不同层级。

### 0 阶：归一化

$$
p_0+p_1+p_2+p_3+p_{13}=1.
$$

这只规定总质量。

### 1 阶：基础金字塔

$$
X=p_1+p_{13},
\qquad
Y=p_3+p_{13},
\qquad
Z=p_2.
$$

这保留单点占用。

### 2 阶：联合关系

$$
\kappa=p_{13}=
\mathbb E[xy].
$$

这保留端点联合。

### 2 阶代数关系

$$
\Delta=p_0p_{13}-p_1p_3.
$$

这判断端点是否在条件层上独立。

因此：

$$
\boxed{
\text{一阶投影丢失 }\kappa，
\qquad
\text{二阶联合恢复 }\kappa，
\qquad
\text{二次二项式判断 }\Delta.
}
$$

这不是三个独立现象，而是同一个关系核在不同阶数上的展开。

---

## 14. 五、定理三：任何基础读出都无法恢复 $\kappa$

设 $\ell$ 是一个线性读出，且它只通过基础投影 $(1,X,Y,Z)$ 因子化：

$$
\ell(p)=L(1,X,Y,Z).
$$

### theorem 14.1: 定理 3

若读出只通过基础投影因子化，则：

$$
\ell(p+th)=\ell(p)
$$

对所有允许的 $t$ 都成立，其中：

$$
h=(1,-1,0,-1,1).
$$

#### 证明

因为：

$$
Ah=0,
$$

所以基础坐标不变：

$$
A(p+th)=Ap.
$$

若：

$$
\ell=L\circ A,
$$

则：

$$
\ell(p+th)=
L(Ap+tAh)=
L(Ap)=
\ell(p).
$$

证毕。

---

这个定理说明：

- 任何只使用 $X,Y,Z$ 的线性统计量都不能恢复 $\kappa$；
- 不存在通过重新排列一阶金字塔坐标来恢复隐藏联合的方法；
- 必须引入不经过基础投影因子化的新读出。

例如：

$$
\chi=z+xy
$$

不经过一阶投影因子化，因此：

$$
\chi(h)=1.
$$

而：

$$
S=2x+3z+5y
$$

虽然使用了 Fibonacci 权重，但它仍然是一阶线性读出，因此：

$$
S(h)=0.
$$

---

## 15. 六、定理四：AURIC 与 5040 编码具有相同的原始关系核

5040 指数向量为：

$$
a=(a_2,a_3,a_5,a_7).
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

对应四个原子列向量：

$$
b_2=(1,0,0),
$$

$$
b_3=(0,1,0),
$$

$$
b_5=(0,0,1),
$$

$$
b_7=(1,0,1).
$$

显然：

$$
b_2+b_5=b_7.
$$

因此：

$$
\boxed{
[2]+[5]=[2,5]
}
$$

是基础叶子投影的唯一复合关系。

对应的指数核方向为：

$$
\eta=(-1,0,-1,1).
$$

因为：

$$
(a_2,a_3,a_5,a_7)
\longmapsto
(a_2-1,a_3,a_5-1,a_7+1)
$$

保持：

$$
(u,v,w)
$$

不变。

---

### theorem 15.1: 定理 4：概率 AURIC 与整数 5040 的关系核具有相同的结构类型

AURIC 的唯一原始关系为：

$$
c_{\mathrm{null}}+c_{13}=c_1+c_3.
$$

5040 叶子投影的唯一原始关系为：

$$
b_2+b_5=b_7.
$$

二者都满足：

1. 关系格秩为 $1$；
2. 基础投影不变；
3. 完整对象沿一维纤维变化；
4. 需要额外读出恢复隐藏坐标。

#### 证明

AURIC 关系格由定理 1 得到，秩为 $1$。

5040 关系格由：

$$
b_2+b_5-b_7=0
$$

生成，亦为秩 $1$。

两者的具体对象不同：

- AURIC 是概率单纯形中的 signed relation；
- 5040 是整数半群中的 exponent relation。

但二者的投影核结构相同，均为一维原始关系。证毕。

---

因此：

$$
\boxed{
\kappa_{\mathrm{prob}}=p_{13}
}
$$

和：

$$
\boxed{
\kappa_{\mathrm{int}}=a_7
}
$$

可以看作同一个“复合原子是否被显式记录”的两种实现。

---

## 16. 七、Golden ring 范数是 5040 隐藏坐标的可验证读出

定义：

$$
R=\mathbb Z[\theta]/(\theta^2-\theta-1).
$$

范数为：

$$
N(a+b\theta)=a^2+ab-b^2.
$$

原子对应：

$$
1,\qquad
\theta,\qquad
\theta^2,\qquad
2+\theta.
$$

其范数分别是：

$$
1,\qquad
-1,\qquad
1,\qquad
5.
$$

定义：

$$
U(a)=
1^{a_2}\theta^{a_3}(\theta^2)^{a_5}(2+\theta)^{a_7}.
$$

由于范数乘法性：

$$
N(U(a))=
(-1)^{a_3}5^{a_7}.
$$

所以：

$$
\boxed{
v_5(|N(U(a))|)=a_7.
}
$$

这提供了一个严格的额外读出：

$$
(u,v,w)
\quad+\quad
v_5(|N(U)|)
$$

可以恢复完整指数向量。

---

## 17. 八、定理五：最小补充读出定理

设基础投影的隐藏空间为：

$$
K=\operatorname{span}\{h\}.
$$

设新增读出为 $R$。

### theorem 17.1: 定理 5

若：

$$
R(h)\neq0,
$$

则 $(\text{基础投影},R)$ 可以唯一恢复隐藏坐标。

若：

$$
R(h)=0,
$$

则该读出不能减少隐藏纤维。

#### 证明

同一基础纤维中的状态差异都形如：

$$
p-q=th.
$$

因此：

$$
R(p)-R(q)=tR(h).
$$

若 $R(h)=0$，所有不同 $t$ 仍给出同一读出。

若 $R(h)\neq0$，则由读出差异唯一确定 $t$。证毕。

---

具体例子：

### AURIC 二阶矩

$$
R_{S^2}(h)=20\neq0.
$$

### AURIC 指示函数

$$
R_\chi(h)=1\neq0.
$$

### 5040 Golden ring 范数

$$
R_{\mathrm{norm}}(a)=v_5(|N(U(a))|)=a_7.
$$

### 动态未来律

设五个模式对应未来律 $\mathscr L_I$，则：

$$
R_{\mathrm{future}}(h)=
\mathscr L_{13}
-\mathscr L_1
-\mathscr L_3
+\mathscr L_{\mathrm{null}}=
J_{\mathscr L}.
$$

因此：

$$
J_{\mathscr L}\neq0
$$

是未来响应恢复 $\kappa$ 的必要充分条件。

---

## 18. 九、BIND-ONLY 信息不能参与定理传播

可以把证据规则形式化为一个简单的类型系统。

定义：

$$
\mathrm{Status}(P)
\in
\{
\mathrm{BindOnly},
\mathrm{Computed},
\mathrm{Verified}
\}.
$$

规定证明传播规则：

$$
\frac{
\Gamma\vdash_{\mathrm{Verified}}P_1
\quad\cdots\quad
\Gamma\vdash_{\mathrm{Verified}}P_n
}{
\Gamma\vdash_{\mathrm{Verified}}Q
}
$$

只有当推理规则本身明确，并且所有前提都属于可承重层，结论才能获得 `Verified` 状态。

对于 BIND-ONLY 前提 $B$，允许的唯一操作是：

$$
B
\longmapsto
\mathrm{Candidate}(B).
$$

不允许：

$$
\mathrm{BindOnly}(B)
\Longrightarrow
\mathrm{Verified}(Q).
$$

这意味着：

- PR 标题不能证明定理；
- 文档中的“连接”不能证明连接已经完成；
- 未验证的 typed reference 不能证明目标对象存在；
- 绑定成功不能证明数学命题成立；
- 生成的 Blueprint 不能替代 Lean theorem；
- 数值实验不能替代全称命题证明。

---

## 19. 十、当前 AURIC 结论的证据分级

### 可以直接承重的有限数学

以下结论完全来自显式定义和有限证明：

$$
\ker A=
\operatorname{span}\{(1,-1,0,-1,1)\};
$$

$$
\kappa\in
[
\max(0,X+Y+Z-1),
\min(X,Y)
];
$$

$$
\Delta=(1-Z)\kappa-XY;
$$

$$
\det T=-Z\Delta;
$$

$$
\mathcal A'(\kappa)=
\log\frac{p_0p_{13}}{p_1p_3};
$$

$$
\mathcal A''(\kappa)>0;
$$

$$
\mathbb E[S^2]=
4X+9Z+25Y+20\kappa;
$$

$$
v_5(|N(U)|)=a_7;
$$

以及：

$$
\dim\ker\partial_G=|E|-|V|+c.
$$

### 仍然必须标为开放的内容

以下内容不能因为项目当前 PR 或理论文档提到，就自动视为完成：

1. AURIC 与实际 escape dynamics 的完整动态等价；
2. thermodynamic action 在真实动态系统中的唯一物理解释；
3. common cyclic control 的一般最小性定理；
4. future quotient 在无界历史计数下的有限性；
5. 具体 complete-law flow 是否已经有有限 common generator；
6. AURIC 结构是否已经解释某个物理系统或时空规律。

这些都需要明确：

$$
\text{状态空间}
+
\text{转移算子}
+
\text{假设}
+
\text{证明}
+
\text{依赖闭包}.
$$

---

## 20. 十一、最终定理：AURIC 隐藏关系的严格核心

### theorem 20.1: 定理 6：AURIC 一维隐藏纤维定理

在五态 AURIC FIB 系统中：

1. 基础投影的整数关系格为一维；
2. 其原始关系为
   $$
   \delta_{\mathrm{null}}+\delta_{13}
   -
   \delta_1-\delta_3;
   $$
3. 该关系生成唯一的概率隐藏坐标 $\kappa=p_{13}$；
4. 其二次 toric 关系为
   $$
   p_0p_{13}-p_1p_3;
   $$
5. 其条件独立截面为
   $$
   (1-Z)\kappa=XY;
   $$
6. 任何只依赖基础投影的读出都湮灭该关系；
7. 一个非零隐藏读出即可恢复该关系；
8. 在周期系统中，该局部关系还必须满足全局 holonomy；
9. 所有只来自 BIND-ONLY 层的信息不参与上述证明。

#### 证明

第 1、2、3 点由基础关系矩阵的整数核计算得到。

第 4 点由对应单项式映射的 toric 核得到。

第 5 点由二次关系代入 $\kappa$ 参数化得到。

第 6、7 点由隐藏方向与读出的线性配对得到。

第 8 点由周期 transfer 的固定点条件得到。

第 9 点是证据类型规则：未验证绑定不能成为形式证明前提。证毕。

---

所以当前能够严格承重的核心不是某个项目绑定，而是以下结构本身：

$$
\boxed{
\text{Fibonacci 原子}
\longrightarrow
\text{唯一原始关系}
\longrightarrow
\text{一维隐藏纤维}
\longrightarrow
\text{二次 toric 约束}
\longrightarrow
\text{额外读出}
\longrightarrow
\text{全局闭合}.
}
$$

在概率 AURIC 中：

$$
\kappa=p_{13}.
$$

在 5040 指数编码中：

$$
\kappa=a_7.
$$

在 Golden ring 中：

$$
\kappa=v_5(|N(U)|).
$$

但只有当这些映射、读出和证明依赖被明确写出并验证后，才能把它们称为已建立的数学关系。任何 BIND-ONLY 信息都只能停留在候选命题层，不能穿透到定理层。

## 追加锚（本行以下为增补区）

## 21. 同源接缝的强制信息、额外信息与长历史

**定义 21.1（实际低到高支持与分组参考）。**

置 $\Sigma=(O,L,T,R,J)$，按此顺序印刷位串 $(000,100,010,001,101)$。若印刷坐标是 (x,z,y)，则 xz=yz=0；J 代表两个端点同时占位。O 是实际空窗口，不能代替 Stop、End 或吸收错误标签。

本章 $U,V$ 按连续不重叠窗口的低到高位置顺序排列。置 a(U)=末位=y(U)，b(V)=首位=x(V)，则 a=1 恰在 {R,J}，b=1 恰在 {L,J}。唯一跨窗条件是 a(U)b(V)=0。因此
$$
E=\Sigma^2\setminus(\{R,J\}\times\{L,J\}),\qquad |E|=25-4=21.
$$
禁止格恰为 (R,L),(R,J),(J,L),(J,J)。

Hidden C-16–C-17 与原生接续卷的原生高到低接口采用 x(第一窗)y(第二窗)=0；对同一完整双窗将次序反转，便得到这里 y(U)x(V)=0。相应联合表须转置；换读向须保留各窗的实际位置和外端条件。若将整个印刷长词反转，还须反转窗口次序及每窗内部位序，并同步重标低、高占位。此双射不等同在线前缀回复。以下只使用 E，没有增加远程、算术、环境或封口约束；若实际域另受这些限制，须另算可用支持。

给完整概率边缘 p_i、q_j，置
$$
R_0=\{O,L,T\},\ R_1=\{R,J\},\quad
C_0=\{O,T,R\},\ C_1=\{L,J\},
\quad r=p_R+p_J,\quad s=q_L+q_J,\quad c=1-r-s.
$$
a、b 不可同时为 1，故合法耦合存在必有 r+s≤1，并且所有合法耦合均有
$$
\rho_{00}=c,\quad \rho_{01}=s,\quad \rho_{10}=r,\quad \rho_{11}=0.
$$
00 表示完整的九格 R₀×C₀，不能缩成 (O,O)。

充分性由显式补全证明。令 r_a=(1-r,r)_a，s_b=(1-s,s)_b；只在 r_a>0、s_b>0 的条件组内定义 α_i=p_i/r_a、β_j=q_j/s_b，取
$$
P^*_{ij}=\rho_{ab}\alpha_i\beta_j\quad(i\in R_a,j\in C_b).
$$
零组整组删去，ρ_ab=0 的块置零，不使用 0/0。对正条件组，∑_{j∈C_b}β_j=1，故行和为 α_i∑_bρ_ab=p_i，列和同理，给非负归一化合法耦合。这证明 r+s≤1 既必要又充分。

当 r,s<1 时三块也可写为
$$
P^*_{ij}=\begin{cases}
c\,p_iq_j/[(1-r)(1-s)] &(a,b)=(0,0),\\
p_iq_j/(1-r)&(a,b)=(0,1),\\
p_iq_j/(1-s)&(a,b)=(1,0),\\
0&(a,b)=(1,1).
\end{cases}
$$
r=1 强制 s=0，仅 R₁×C₀ 有质量，取 p_iq_j；s=1 对称。r=0 或 s=0 删除其零质量组；r+s=1 删 00 块。分组没有假设真实 P 的条件独立，它只是提供一份合法参考耦合。

同边缘核直接采用《AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS》C-17.1–C-17.4：将该卷高到低联合表转置，模式 $0,1,2,3,13$ 对应本章 $O,L,T,R,J$。合法内部格的十二方向为 $Z^{ij}=E_{ij}-E_{iO}-E_{Oj}+E_{OO}$；目标差为 $\sum\theta_{ij}(f_{ij}-f_{iO}-f_{Oj}+f_{OO})$。含全正点的纤维维数十二，目标恒定恰在合法格为行势加列势。一般非空纤维必须在全部相容律支持的并集 $E_{\rm adm}$ 上应用该判据，其维数为 $|E_{\rm adm}|-|V_{\rm adm}|+k_{\rm adm}$，不是单点支持的维数。

**定理 21.3（原生合法接缝的最小互信息与额外配对结构）。**

a=a(U)、b=b(V) 是同源确定函数。由下述对数加性步骤 和固定边缘，
$$
I_P(U;V)=H(p)+H(q)-H(P)
=I_\rho(a;b)+D(P\Vert P^*).
$$
P* 在每个有质量的组内是 α_iβ_j，链式熵给
$$
H(P^*)=H(\rho)+\sum_a r_aH(\alpha^{(a)})+\sum_b s_bH(\beta^{(b)}),
$$
而 H(p)=H(r_a)+∑r_aH(α)、H(q) 同理，故第一项确是接缝互信息。展开三格得
$$
I_{\rm seam}(r,s)
=c\log c-(1-r)\log(1-r)-(1-s)\log(1-s).
$$
它是固定 p,q 的合法最小互信息，唯一最小律为 P*。r=0 或 s=0 时值为 0；r+s=1 时为 −r log r−s log s；端点 (1,0),(0,1) 为 0。所有这些采用连续的 0 log 0 约定。rs>0 时独立 p_iq_j 给禁止块质量 rs，因而非法；rs=0 时独立乘积合法且等于 P*。在 c>0 的三角内部，∂²I_seam/∂r∂s=1/c；这是函数响应，未赋予物理或量子曲率含义。

证明。以下对数加性和最大熵是 Hidden C-17.6 的同域应用；以本章分组坐标展开，作为信息分解的中间步骤。

P* 的正支持恰为 E_adm：零边缘强制删行列，固定零块质量强制删块；余下每个正边缘、正块的格，显式 P* 为正。因此所有 P∈C(p,q) 都满足 P≪P*，D 有限。

对于 c>0、r,s<1，只在合法正格上有
$$
\log P^*_{ij}=\log p_i+\log q_j+
\kappa_0+a(i)\kappa_a+b(j)\kappa_b,
$$
$$
\kappa_0=\log{c\over(1-r)(1-s)},\quad
\kappa_a=\log{1-r\over c},\quad
\kappa_b=\log{1-s\over c}.
$$
它逐块给 00、10、01 的真实系数对数；禁止的 11 块未被赋正概率或取对数。这个表达在合法支持上是行势加列势，未声称任意全矩阵块项都全局可分。等价证明是固定三块质量 ρ 时，所有 P 的 ∑P logρ_ab、∑P log(p_i/r_a)、∑P log(q_j/s_b) 都由固定边缘与固定块律决定。

饱和 c=0 时，只在剩余实际矩形分量内取对数：10 块 logP*=logp+logq−log(1-s)，01 块为 logp+logq−log(1-r)。r=1 或 s=1 的专门块为乘积。零质量组不参加对数求和。以上均使 ∑P logP*=∑P* logP*，故
$$
D(P\Vert P^*)=H(P^*)-H(P)\ge0.
$$
有限概率 KL 的非负性可由 log t≤t−1 在正 P 格求和证明，等号 iff P=P*；即使 P 有零格，漏掉的正 P* 质量也使非相等情形严格。故 P* 是所有同完整边缘合法耦合的唯一最大熵律，边界与单点情形均包括。参考选择本身没有确定未知真实来源。

**命题 21.4（均匀完整边缘与相同KL的相反目标）。**

按 (O,L,T,R,J) 行列顺序，p=q=(1/5,…,1/5)，r=s=2/5。代入得
$$
P^*={1\over45}
\begin{pmatrix}
1&3&1&1&3\\1&3&1&1&3\\1&3&1&1&3\\
3&0&3&3&0\\3&0&3&3&0
\end{pmatrix},\qquad
I_{\rm seam}=\log5-\frac65\log3\approx0.2911031660.
$$
该小数是精确表达的近似值。

必须固定目标的循环顺序：令 C₅ 为无向五环 O−L−T−R−J−O 的邻接矩阵（非归一化 Markov 核），A=11ᵀ−2C₅+(1/10)11ᵀ=(11/10)11ᵀ−2C₅。定义
$$
Q(P)=\sum_{i,j,k,l}A_{ik}A_{jl}P_{ij}P_{kl},
$$
即两份数学上独立同分布 P 样本的函数期望；这是声明的目标，未声称已取得复制资源。

P_- 等权取 (O,T),(L,J),(T,L),(R,R),(J,O)，P_+ 等权取 (O,J),(L,O),(T,L),(R,T),(J,R)。每份恰有每行每列一个合法格，因而都有均匀完整边缘，熵皆为 log5。每份支撑上恰有一项 P*=1/45、四项 P*=1/15，所以
$$
D(P_\pm\Vert P^*)=\frac15\log9+\frac45\log3=\frac65\log3.
$$

为给 Q 数值的符号推导，置 T(P)=∑C_{ik}C_{jl}P_ijP_kl。均匀边缘下两单边邻接期望各为 2/5，故 Q=−11/20+4T(P)。P_- 的行相邻所对应列均不相邻，T(P_-)=0；P_+ 保持五环邻接，T(P_+)=2/5。对 P* 的整行分子 u=(1,3,1,1,3)、v=(3,0,3,3,0)，五条无向行边中两条 u,u、两条 u,v、一条 v,v，且
$$
u^TC_5u=26,\quad u^TC_5v=42,\quad v^TC_5v=18,
\quad T(P^*)=\frac{2(2\cdot26+2\cdot42+18)}{45^2}=\frac{308}{2025}.
$$
于是
$$
Q(P^*)=\frac{473}{8100},\qquad Q(P_-)=-\frac{11}{20},\qquad
Q(P_+)=\frac{21}{20}.
$$
相同局部边缘、相同熵及相同额外 KL 不能决定这个目标的符号或组织；等 KL 不是目标极值证明。这里不外推到未声明目标域的全局最优性。

该目标与 [共同来源正性卷 C-30.6](AURIC_FIB_ATOM_COMMON_SOURCE_POSITIVITY_AND_HISTORICAL_PREFIXES.md) 的参数对应为同一五环邻接 $C_5$、$\varepsilon=1/10$、$A_\varepsilon=(11/10)11^{\mathsf T}-2C_5$；此处额外保留共同最大熵参考的散度计算。

**命题 21.5（参考点的八维可见与十二维隐藏Fisher分解）。**

先限 r>0、s>0、c>0，四个条件模式组都严格正，因而 P* 全 E 正。在三格接缝单纯形中 dρ=(-dr-ds,ds,dr)，所以
$$
g_{\rm seam}={dr^2\over r}+{ds^2\over s}+{(dr+ds)^2\over c},
\qquad \det g_{\rm seam}={1\over rsc}.
$$
P* 参考族采用 (r,s,α^{(0)},α^{(1)},β^{(0)},β^{(1)}) 坐标。条件组维数分别 2,1,2,1，加接缝 2，共 8。各条件组 Fisher 为 ∑(dα_i)²/α_i 或 ∑(dβ_j)²/β_j，故
$$
g_{P^*}=g_{\rm seam}+
(1-r)g_{\alpha^{(0)}}+r g_{\alpha^{(1)}}+
(1-s)g_{\beta^{(0)}}+s g_{\beta^{(1)}}.
$$
证明用实际 score d logρ_ab+d logα_i+d logβ_j：条件 score 在每组的均值为 ∑dα_i=0、∑dβ_j=0；P* 在每块条件独立，故组内 α/β 交叉均值也为零。权重分别是同一 ρ 的边缘 r_a、s_b，不能删掉或置为常数。坐标仅在这些开放正组中有效。

在全 E 的质量零切空间，以
$$
g_{P^*}(u,Z)=\sum_{E}u_{ij}Z_{ij}/P^*_{ij}
$$
为 Fisher 内积。对参考族切向量 u，微分定理21.3证明内的合法格对数表达，得 u_ij/P*_ij=α'_i+β'_j（这里 α'、β' 是行列势，不是条件概率）。因此对每个零行列和 Z，g(u,Z)=0。参考族的边缘恢复映射为 (p,q)，其导数单射，故参考切空间确有 8 维；纤维核有 12 维。全 E 正的归一化切空间遂为 20=8⊥12，正交只断言于 P*。条件权重依 r,s 变化，不推出全局乘积结构。

固定有限正支持 P* 及固定边缘的零和 Z，若 |εZ_ij|≤P*_ij/2，则
$$
D(P^*+\varepsilon Z\Vert P^*)=
{\varepsilon^2\over2}\sum_E {Z_{ij}^2\over P^*_{ij}}+R,\qquad
|R|\le {2|\varepsilon|^3\over3}\sum_E {|Z_{ij}|^3\over(P^*_{ij})^2}.
$$
一阶项因 ∑Z=0 消失；三阶导数为 −Z_ij³/(P*_ij+tZ_ij)²，给此界。有限正支撑固定、Z 有界时这是局部一致 O(ε³)，没有趋零概率或跨支持的一致全局结论。

若仍 p_i,q_j>0 但 r+s=1，则 00 九格被强制零，剩余支持为 K₂,₃⊔K₃,₂，边缘秩 10−2=8，纤维维数 12−8=4；其归一化支持空间是 11 维，不能继续用开放 20 维或八维内部坐标。零 p/q 还会缩小支持、秩与参考方向数，按 Hidden C-17.1–C-17.4 的 E_adm 判据重算。

**定理 21.6（原生合法链的配对项与长历史项）。**

证明先在同一真实来源上构造相邻律的Markov补全。

令 N≥1，Ω_N 为按 定义21.1 顺序的合法 N 窗口词，仅施加每条相邻接缝。给同一实际 P 在 Ω_N 上的单窗边缘 p_i 与相邻联合边缘 P_i；故 P_i 左边缘为 p_i、右边缘为 p_{i+1}。也可从一组非负归一化、相邻一致并满足接缝支持的 P_i 起始；没有一致性则不使用下式。

正质量行定义 K_i(t|s)=P_i(s,t)/p_i(s)。零质量行任取一个概率转移（可取到 O），记作不可达行；一致性保证从 p₁ 开始永不进入它，该选择对路径律无影响。取
$$
\widehat P(s_1,\ldots,s_N)=p_1(s_1)\prod_{i=1}^{N-1}K_i(s_{i+1}|s_i).
$$
N=1 时定义为 p₁；有可达正路径时才写概率比乘积式。逐步归纳行和为 1、下一边缘为 ∑_sP_i(s,t)=p_{i+1}(t)，故补全归一化并保留全部真实 p_i、P_i。每条正转移合法。

P 的每条正路径令所有所需 P_i、p_i 为正，故 P≪P̂。对 N≥2，
$$
H(\widehat P)=\sum_{i=1}^{N-1}H(P_i)-\sum_{i=2}^{N-1}H(p_i),
$$
$$
D(P\Vert\widehat P)=H(\widehat P)-H(P)
=\sum_{i=2}^{N-1}I_P(S_{i+1};S_1,\ldots,S_{i-1}\mid S_i).
$$
证明：log P̂ 是初始项与相邻转移项之和，其在 P 和 P̂ 下的期望由同一 p_i、P_i 固定；再用 H(P)=H(p₁)+∑H(S_{i+1}|S₁…S_i)，相减得所列 CMI。它们非负，可逐正 S_i 条件下应用有限 KL 证明。等号 iff P=P̂，故 P̂ 是固定相邻边缘的唯一最大熵律，也是满足这些边缘的唯一一阶 Markov 律。N=2 时 P=P₁=P̂、CMI 空和为 0；N=1 时熵为 H(p₁)，散度同为 0。

该 Markov 性是指定被动链的条件独立性质。它不自动覆盖干预、反馈、持久环境、资源与停止权限；全部实际未来菜单的充分状态另需操作合同。

由这些补全得到以下同源分解。

从 定理21.6的Markov补全 的同一实际 p_i，逐接缝取 P_i*=P*(p_i,p_{i+1})，每对要求 r_i+s_{i+1}≤1（实际合法 P 已保证）。用同样零行约定定义
$$
Q_N^*=p_1\prod_{i=1}^{N-1}(P_i^*/p_i).
$$
正路径的比式成立，其余用转移定义。Q* 归一化、保单窗边缘，每对相邻律为 P_i*。定理21.3证明内的对数加性给 $`P_i\ll P_i^*`$，所以 P≪P̂≪Q*，有限离散情形的以下散度均有限。

对正 P 路径，
$$
\log{\widehat P\over Q_N^*}
=\sum_{i=1}^{N-1}\log {P_i(S_i,S_{i+1})\over P_i^*(S_i,S_{i+1})};
$$
初始与所有单窗分母是同一 p_i，故消去。按实际 P 求期望得到
$$
D(P\Vert Q_N^*)=
\sum_{i=1}^{N-1}D(P_i\Vert P_i^*)+
\sum_{i=2}^{N-1}I_P(S_{i+1};S_1,\ldots,S_{i-1}\mid S_i).
$$
第一项是超出合法接缝参考的配对结构，第二项是超出真实相邻律 Markov 补全的长历史结构。不能把真实 P_i 为方便换成 P_i* 再称为原来源分解；固定真实相邻律时 D(P‖P̂) 只剩历史项。N=1 为 0，N=2 只有配对项。若更换为任意不支配 P 的参考，散度可为无穷，本有限比值证明不能直接套用。

在已声明的这条被动链里，所有相应 CMI 为零才给当前模式对其链未来的 Markov 充分性；若要对所有来源或未来干预成立，仍须实际任务的共同模型与纤维条件。最大熵不免费给最坏路径界。

此原生链的KL预算可转换为有界目标误差。以下Pinsker步骤是该应用中的经典中间不等式。

令 Δ_N=D(P‖Q_N*)，TV(P,Q)=½∑|P−Q|。当 m_f≤f≤M_f 时，以正负概率差各总质量 TV 得
$$
|\mathbb E_Pf-\mathbb E_{Q_N^*}f|
\le(M_f-m_f)\,\mathrm{TV}(P,Q_N^*)
\le(M_f-m_f)\min\{1,\sqrt{\Delta_N/2}\}.
$$
KL 使用自然对数；若无支持支配而为无穷，最后仅剩全范围界。本章的同源补全有 定理21.6 的有限支配保证。

所用经典先例是 Clément L. Canonne, “A short note on an inequality between KL and TV”, arXiv:2202.07198v2，定义段和 §1 Lemma 2、式 (2)：TV=½L¹、KL 为 nats、TV≤√(KL/2)。以下采用这组自然对数约定。有限源亦可自证：取正差事件 B，使 P(B)−Q(B)=TV；对 B 与补集分别用 log-sum，D(P‖Q)≥d(P(B)‖Q(B))。二元散度对第一参数的二阶导为 1/[x(1−x)]≥4，且在 x=Q(B) 时函数与一阶导数为零，故 d≥2TV²；边界由连续或无穷情形处理。

这是给定 Δ_N 预算后的误差界。局部边缘自身不能供给一个小 Δ_N，平均目标为正也不推出每条路径为正，更不推出普遍 Robin 结论。

若目标改为逐路径算术剩余，则使用另一份实际状态合同，而非最大熵平均；有限Bellman望远镜是此条件应用的中间步骤。

对整数 n>5040，令
$$
C(n)=\log {e^\gamma\log\log n\over \sigma(n)/n}.
$$
分子分母在该范围为正，C(n)>0 等价于 Robin 严格不等式；“对所有整数 n>5040 都成立”等价于 RH 是既有 Robin 判据的量词。此定义本身不供应全整数正性。

给实际有限时域 N、各时刻的合法状态与合法边，真实路径代价
$$
F(s_1,\ldots,s_N)=\sum_{i=1}^{N-1}c_i(s_i,s_{i+1})+g_N(s_N).
$$
若每个合法终态有 V_N≤g_N，且对每条实际合法时刻边 s→t 均有 V_i(s)≤c_i(s,t)+V_{i+1}(t)，则
$$
F-V_1(s_1)=\sum_{i=1}^{N-1}[c_i+V_{i+1}-V_i]+[g_N-V_N]\ge0.
$$
有限时域只需这些实际有限实值和全部合法边覆盖，不需来源 Markov 性或正边成本。N=1 直接为终端不等式；没有以抽样或平均条件代替逐边量词。若要固定所有初态都给正目标，还需所有相应 V₁(s₁)>0。

对原 Robin 目标应用前，须证明 F 真正表示 C(n) 且实际状态保留合法后继、剩余代价、停止及覆盖所需信息。《RoughPrimeSuffixBellman》的原算术状态 的 rough-prime suffix 原状态为截点 y、素数序号 i、整数预算 b、前一指数上限 h；素数是截点以上的连续素数，实际指数列表有正、反单调和数值预算守卫。若目标还依已处理前缀，其整数尺度、素数指数及已累计 σ/n 因子亦需保留，尤其 log log n 不由五个模式名决定。

有限时域望远镜证明自足；它不需要引用无限时域 all-policy termination 定理，亦未把最大熵参考当成最坏界。

**命题 21.7（同真子集边缘的奇偶历史与两种纤维维数）。**

N≥3 时仅取 O,T；两模式端点皆零，故 {O,T}^N 中任意词都合法。令 P_e、P_o 分别均匀于 T 数量为偶、奇的 2^{N-1} 个词。任一真子集 A⊊[N] 的每种配置都有 2^{N-|A|-1} 份延拓，故两律在 A 上均为公平独立边缘。特别全部相邻对独立、r=s=0、P_i=P_i*，Q_N*=公平产品律 2^{-N}。于是
$$
D(P_e\Vert Q_N^*)=D(P_o\Vert Q_N^*)=\log2,
\quad \mathbb E_{P_e}(-1)^{\#T}=1,\quad
\mathbb E_{P_o}(-1)^{\#T}=-1.
$$
由 定理21.6，此 $\log2$ 全在长历史项；N≥3 是保证每对为真子集的条件。

令 U_N 为整个 Ω_N 上均匀律，$\widetilde P_{e/o}=(4/5)P_{e/o}+(1/5)U_N$。每条合法路径有至少 1/(5|Ω_N|) 的正质量，且所有真子集边缘在两律间仍相同。函数 (-1)^{#T} 定义于整个 Ω_N，共同背景消去，期望差精确为 8/5。此混合改变共同单窗与相邻律；它不延续原来的公平产品 Q*、$\log2$ 散度或“配对项为零”结论，后者须针对混合后的真实边缘重新计算。

自由外端、仅相邻无相邻一限制下 |Ω_N|=F_{3N+2}，F₀=0,F₁=1，N=1,2,3,4 为 5,21,89,377。含总质量与每窗四个非 O 指示函数的单窗边缘矩阵秩为 1+4N：全 O 路径与“恰一个窗改为任一非 O 模式”的 4N 条路径全合法，将任意线性行关系在这些路径求值，先得常数为零，再逐项得系数为零。完整单窗边缘固定且确有全 Ω_N 正实现时，
$$
\dim{\cal C}_N(p_1,\ldots,p_N)=F_{3N+2}-1-4N;
$$
四个数为 0,12,76,360。若只有边界实现，须在整个可用路径支持上重算秩与维数。

三窗固定完整相邻律的纤维是另一合同。在全 89 路径正实现条件下，按中间模式 (O,L,T,R,J) 的左右合法矩形，核维数分别 16,8,16,8,4，总计 52（《AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION》定理14.2，反转次序保持此计数）。76 是固定单窗，52 是固定相邻对，不能混同。此长链秩与维数均是线性概率模型结论，未约束任意无限来源。

**命题 21.10（单位端点矩的首次缺项与指数响应）。**

端点矩直接采用 `RealL2FirstReturnMoments.endpoint_moments` 的单位端点和路径算子；其指数响应推论如下。

实际载体是实 Hilbert 空间 ℓ²(ℕ,ℝ)（坐标 j 对应源坐标 j+1）和 ℝ^n 的 EuclideanSpace；端点分别是单位向量 e₀（源坐标 e₁）及 b_n。令 S 为单边移位，A_∞=S+S*，A_n 为 n 点路径的单位邻接矩阵，K_X=3I_X−A_X，n≥1。已有声明的矩为
$$
m_X(k)=\langle e_X,K_X^k e_X\rangle,\quad
m_\infty(k)=m_n(k)\ (0\le k<2n),\qquad
m_\infty(2n)-m_n(2n)=1.
$$
这里不是将邻接矩或指数核重新归一化为概率。

普通解释：k<n 时 K_∞^k e_∞ 等于有限迭代的零延拓；第 n 次迭代增加 (-1)^n e_n（源位置 n+1）。自伴性把第 2n 阶端点矩写成第 n 次迭代的范数平方，新增正交单位坐标贡献恰为 1。较低阶可拆成至少一项尚未到边界的两迭代内积，因此相同。

置 c_X(k)=⟨e_X,A_X^k e_X⟩。由 A_X=3I_X−K_X 的二项式展开，c_∞(k)=c_n(k) 对 k<2n 成立，第 2n 阶的差也为 1，因为最高次项的系数为 (-1)^{2n}=1。对任意实 t，
$$
M_X(t)=\langle e_X,e^{-tK_X}e_X\rangle
=e^{-3t}\sum_{k=0}^\infty {t^k\over k!}c_X(k).
$$
A_∞ 有界（范数≤2），故级数在有界 t 集上一致绝对收敛。特别
$$
M_\infty(t)-M_n(t)=e^{-3t}\bigl(t^{2n}/(2n)!+O(t^{2n+1})\bigr).
$$
n=1、k=0 均包括在内。有限阶或有限前缀相同不能推出全部未来响应相同；本式是指定算子的端点响应，没有新增物理或 CTMC 解释。

相干历史的来源对应。经典链与《AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION》定义110.1、定理110.2–110.3和命题110.4的相干合同不同：该合同保留同一实际持续环境及正迹一块态 $\Omega_n=\sum_{h,k}|h\rangle\langle k|\otimes\Xi^{(n)}_{hk}$，同一相位相容等距实现给 $\Xi^{(n+1)}_{ha,kb}=K_{a|h}\Xi^{(n)}_{hk}K_{b|k}^{\dagger}$。这里历史 $h$ 对应完整分支序列，不能只以当前模式替代。命题110.4的同环境两次CNOT满足 $W^2=I$；新独立环境两次退相干则不同。块态、相位和环境由该所有者完整定义，本章不重复另立相干理论。

完整未来的来源对应。被动链的条件互信息为零，只给上述链的Markov充分性。全部允许操作的充分摘要采用 Hidden C-28.11.1–C-28.11.4 及《AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE》的输出分支合同：在同一实际可达域内，每个摘要纤维须有相同目标、合法菜单、守卫、后继摘要和全部允许记录律；未归一化分支线性、正质量后的后选择才归一化。相同局部边缘或相同KL不提供这些量词。Robin的 $n>5040$ 目标还须原整数、素数指数、预算与停止合同；本章不提供从五模式到完整算术状态的识别映射。

数学引文。Canonne，*A short note on an inequality between KL and TV*，[arXiv:2202.07198v2](https://arxiv.org/abs/2202.07198v2)，§1 Lemma2、式(2)，提供自然对数Pinsker先例；有限支撑证明已附于原生链应用。Richard Bellman，*Dynamic Programming*，Princeton University Press，有限时域最优性原理，提供逐边势函数先例；上文仅使用明示的有限望远镜恒等式。G. Robin，*Grandes valeurs de la fonction somme des diviseurs et hypothèse de Riemann*，J. Math. Pures Appl.63，187–213，定理1的量词是全部整数 $n>5040$；有限链预算没有改变该量词。

## 追加锚（本行以下为增补区）

## 22. 保留全部素数地址的有限 Robin 目标与条件十二轴界

**定义 22.1（完整有限素数路径及真实终端）。** 固定整数 $B>5040$，列全体 $p_1<\cdots<p_K\le B$。可达状态 $(k,m)$ 满足 $1\le k\le K+1$、$1\le m\le B$，$m$ 的素因子均在前 $k-1$ 轴。它保留全部前缀整数与指数。第 $k\le K$ 步使用每个 $a\ge0$ 且 $mp_k^a\le B$，含零指数；下一阶段为 $k+1$。置 $R(m)=\sigma(m)/m$、$S_p(a)=\sum_{j=0}^ap^{-j}>0$、$H(m)=e^\gamma\log\log m$，并定义

$$
W_{K+1}(m)=\begin{cases}H(m)^{-1}&m>5040,\\0&m\le5040,\end{cases}
\qquad
W_k(m)=\max_{a:\,mp_k^a\le B}S_{p_k}(a)W_{k+1}(mp_k^a).
$$

被排除终端不求嵌套对数。所有状态和分支有限，每步阶段严格增加；零指数不造成自环。

**定理 22.2（有限完整目标、误差锚与十二轴条件分解）。** 定义22.1的根值精确为

$$
W_1(1)=\max_{5040<n\le B}\frac{R(n)}{H(n)}.
$$

所以根值严格小于一 iff 该完整有限区间的每个整数满足 Robin。任何逐终端、逐合法分支支配 $W$ 的上解亦提供同方向的界。这个有限目标区别于只最大化 $R$ 的 rough 后缀及概率平均；十二素数压缩只把未覆盖整数送入指定的实际小素数域，并不供应该域的 Robin 证书。

证明。每个约数由独立指数选择给出，故 $R(n)=\prod_pS_p(v_p(n))$。设 $D_k(m)$ 是 $md\le B$、素因子仅在第 $k,\ldots,K$ 轴的整数。后向归纳证明

$$
W_k(m)=\max\left(\{0\}\cup\{R(d)/H(md):d\in D_k(m),\ md>5040\}\right).
$$

终端只含 $d=1$，给显示的分情形。任何剩余 $d$ 唯一分解为 $p_k^ad'$，$R(d)=S_{p_k}(a)R(d')$，即为递推。前缀与后缀互素，完整内部风险为 $R(m)W_k(m)$，不能漏掉前缀。根处唯一分解使路径与所有 $1\le n\le B$ 一一对应。eligible 区间非空、分母正，最大值取得，给 strict iff；没有断言已求出它的数值。

有限最优性原理是 Bellman，*Dynamic Programming* 的经典中间步骤。若同一全体终端有 $U_{K+1}\ge W_{K+1}$，每个状态有 $U_k(m)\ge\max_a S_{p_k}(a)U_{k+1}(mp_k^a)$，正边权乘以子界再取最大值，后向归纳给 $U\ge W$。正的下分母 $h_-(m)\le H(m)$ 给上终端 $1/h_-(m)$；排除终端取非负上值而不求 $H$。近似边上界须乘非负子上界。对同一 eligible 剩余集合，若 $V_0\ge R(d)$ 且 $0<L_0\le H(md)$，则 $W_k\le V_0/L_0$，完整风险至多 $R(m)V_0/L_0$；空 eligible 集值零仍满足。

实际 rough 接口复用 `RoughPrimeSuffixBellman.rough_prime_suffix_complete`：取 $b=\lfloor B/m\rfloor$，首轴前取 $y=1$，其余取 $y=p_{k-1}$，所有余下 $d$ 是 $y$-rough，其根值在 $(y,0,b,\operatorname{rootCap}(y,b))$ 供应 $V_0$。该所有者的正非增指数、连续粗素数及终端一完整保留；定义22.1的零指数可跳过某轴，是不同路径合同。$H$ 在 $(1,\infty)$ 递增，任何 $0<L_0\le H(\max(m,5041))$ 可供应分母下界。raw 最大值含额外小整数只使界变松，不等于本 normalized 最大值。

同一个 $\beta>0$ 用于全部节点的 log-sum-exp，非法／零值 score 为 $-\infty$，不填有限 logit；eligible 根路径恰有 $B-5040$ 条。逐阶段指数展开给

$$
F=\log W_1(1),\quad F_\beta=\beta^{-1}\log\sum_{5040<n\le B}(R(n)/H(n))^\beta,
\qquad F\le F_\beta\le F+\log(B-5040)/\beta.
$$

最大项给左界、所有项不超过最大项给右界。不同温度或局部误差 $\varepsilon_v$ 时，对数误差预算须递推 $E_v\le\varepsilon_v+\max_wE_w$；raw 值则为 $E_v\le\varepsilon_v+\max_wS_{vw}E_w$，不能无权求层和。若每 logit 误差绝对值至多 $\eta$，逐项指数比较给 log-sum-exp 误差至多 $\eta$。没有正路径的节点为 $-\infty$、没有归一化 softmax。多条语法路径对应一个整数时求和计其重数，本章固定素数顺序避免它。只给 softmax 概率会丢公共 score 平移，须另保留绝对 partition 锚，见《信息逃逸与热力学作用》定理16.1。

编码每个实际指数的 Fibonacci 位时，采用《观察者与算术关系》A-16.1–A-16.3 的固定长唯一表示：长 $L$ 无相邻一词与 $0,\ldots,F_{L+2}-1$ 一一对应，$a=\sum b_jF_{j+2}$。最高位零与一分别给相邻不交区间 $[0,F_{L+1}-1]$ 与 $[F_{L+1},F_{L+2}-1]$，证明完整性。为界 $a\le a_{\max}$ 取足够 $L$ 后删 decoded 超界值；继续状态保留素数／行身份、位次、上一位、累计指数和终止。三位块按高、中、低顺序守卫 $gb_H=b_Hb_M=b_Mb_L=0$，输出 $b_L$，组为 $00=\{000,100,010\},01=\{001,101\},10=\{000,010\},11=\{001\}$。同一行跨块带守卫，新素数行重置；$n=6$ 的两个指数一不受跨轴无相邻限制。完成指数后才用 $S_p(a)$，或增量用 $S_p(a+\Delta)/S_p(a)$；$S_2(2)=7/4\ne S_2(1)^2=9/4$。重复 padding 必须规范化才能保持路径和。

对同一个有限整数区间 $I=[5041,10000]\cap\mathbb Z$，还可直接应用上述唯一位码作为整数自身的地址，不与逐素数指数码混同。取 $L=21$，递推给 $F_{23}=28657>10000$。状态 $(A,r,g)$ 保留已读高位贡献 $A$、剩余位数 $r\in3\mathbb N$ 和旧守卫 $g\in\{0,1\}$，其完整来源像为

$$
I(A,r,g)=[A,A+F_{r+2-g}-1]\cap I.
$$

初态 $(0,21,0)$ 覆盖全部 $I$。$r=0$ 时两守卫均为值 $A$ 的叶；目标外为空。只在 $r\ge3$ 时遍历全部受旧守卫允许的最高三位 $(b_H,b_M,b_L)$，更新

$$
A'=A+b_HF_{r+1}+b_MF_r+b_LF_{r-1},\qquad
r'=r-3,\qquad g'=b_L.
$$

每个合法词唯一拆为这三位和余下词；接缝守卫恰为 $g'$，位权分解恰为 $A'$。既有唯一整数码使各子来源像互斥，完整性使其并集为父像；与 $I$ 相交仍保持这两项。只有 $\max(A',5041)>\min(A'+F_{r'+2-g'}-1,10000)$ 才可删空支。包括 $000$ 在内，每边的秩 $r/3$ 都严格下降一；空块的数值增量零不意味着停止或自环。按物理位置，$000,001,010,100,101$ 对应 $O,L,T,R,J$。这里最低三位数值权是 $1,2,3$；原生零窗口数量权是 $2,3,5$，单位位及读口不能由共同无相邻语法自动认同。这是同一有限算术来源的无损地址分解，不供应新的 Robin 数值余量。

关于有限区间，直接引用 `FewDistinctPrimes.robin_lt_223092870` 的 $5040<n<223092870$：$5041\le n\le10000$ 在此域，不另作数值最大值或 margin 声明。其八素因子与九最小素数乘积排除的原条件不扩大。全整数 Robin 等价于每个整数 $B>5040$ 的上述根小于一：反向取 $B=n$。每个有限问题有定义、能终止，不等于其根小于一；逐点严格性也不要求全域统一正 gap。

对于十二轴边界，令 $P=(2,3,5,7,11,13,17,19,23,29,31,37)$，$0\le a_p\le A_p$，其中 $A=(63,40,27,22,18,17,15,15,14,13,12,12)$ 覆盖所有此支持上 $n<2^{64}$。完整实际响应为 $t(a)=\sum a_p\log p,h(a)=\sum\log S_p(a_p)$。其支持线 $h-\lambda t$ 的增量斜率 $\theta_p(a)=\log[S_p(a+1)/S_p(a)]/\log p$ 沿同轴严格递减且正，因为 $S_p(a+1)/S_p(a)=1+(p-1)/(p(p^{a+1}-1))$。最大化按各轴前缀取正增量，负增量不取，零增量可取可不取，跨轴并列组取端点才给极端顶点。排序链因并列可以不唯一，零填充不是新顶点。

对同源有限状态块加性响应 $E^k_{ab}$，$\operatorname{conv}(E^{k\star l}_{ac})=\operatorname{conv}\bigcup_b(K^k_{ab}+K^l_{bc})$，其中 $K^k=\operatorname{conv}E^k$；有限凸组合展开给 $\operatorname{conv}(A+B)=\operatorname{conv}A+\operatorname{conv}B$。中间 $b$ 必须为同一完整守卫、预算及会影响后继的状态；跨块非线性项须另供状态。裁切的真实 $\operatorname{conv}(S\cap\{t\ge a\})$ 仅包含于 $\operatorname{conv}(S)\cap\{t\ge a\}$，后者可有虚拟切交顶点，须全部检查。Robin 余量 $\gamma+\log\log t-h$ 在 $t>1$ 凹且沿 $h$ 仿射；安全外包络所有顶点的严格余量和实际全点包含，才使整个被包含域安全。此步骤对应《Robin约数尺度几何》定义11.1、命题11.2–11.5，参数为同一整数的 $t=\log n,h=\log R(n)$，上包络给的是余量下界。

在全部素因子不超过三十七时，逐项有限几何和给

$$
R(n)<\prod_{p\le37}\frac p{p-1}=\frac{3212440751}{477757440}.
$$

若另外供应精确前提 $e^\gamma>89/50$ 和 $\log\log(2^{64})>379/100$，则乘积下界 $33731/5000$ 大于显示的饱和值，故 $n\ge2^{64}$ 的这一支持域满足 Robin。前一常数对应 `ElevenSmooth.exp_gamma_lower`；第二常数仍是这里明确条件，不以小数或有限盒枚举供应。任意至多十二个不同素数的 $n=\prod_{i=1}^kq_i^{a_i}$，按升序压缩为 $n_0=\prod_{i=1}^kp_i^{a_i}$，有 $n_0\le n,R(n)\le R(n_0)$；每个 Euler 因子随素数下降而上升证明它。若 $5040<n_0<223092870$ 可用已有有限域和对数单调性；若 $n_0\ge2^{64}$ 可用上述额外尾前提；中间十二轴域和 $n_0\le5040$ 的比较仍分别需要有限盒证书或公开全域小整数上界。没有把压缩引理称为全部 $\omega(n)\le12$ 的证明。

数学引文。G. Robin，*Grandes valeurs de la fonction somme des diviseurs et hypothèse de Riemann*，J. Math. Pures Appl.63，187–213，承担全整数判据；Washington–Yang，*Analogues of the Robin-Lagarias Criteria for the Riemann Hypothesis*，[arXiv:2008.04787v1](https://arxiv.org/abs/2008.04787v1)，Introduction(1.1)、reference[13]，只作该判据归属，不使用其另一个奇整数类比。有限路径最优性、max 与 sum 的步骤均在本实际完整素数应用内给出，没有把统计因子图或位词 partition 当作算术最大值。

## 追加锚（本行以下为增补区）
