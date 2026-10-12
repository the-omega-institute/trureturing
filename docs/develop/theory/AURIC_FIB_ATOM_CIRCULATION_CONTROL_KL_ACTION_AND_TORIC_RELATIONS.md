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
