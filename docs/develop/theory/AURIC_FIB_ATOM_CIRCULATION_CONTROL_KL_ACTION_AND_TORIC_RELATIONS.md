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

## 23. 四角关系的有限量子实现、精确谱与概率平衡

### 23.1 五模式、整数回路与单窗 Fibonacci 运输

**定义 23.1（另供的五模式对称载体）。** 本章的模式顺序固定为

$$
\Sigma=(0,1,2,3,13)
=(F[\mathrm{null}],F[1],F[2],F[3],F[1,3]).
$$

它们的原印字分别为空、$[2]$、$[3]$、$[5]$、$[2,5]$。低、高、中占位按 $(x,y,z)$ 排列，模式列为

$$
v_0=(0,0,0),\quad v_1=(1,0,0),\quad v_2=(0,0,1),
\quad v_3=(0,1,0),\quad v_{13}=(1,1,0).
$$

归一化及三个占位评价组成矩阵

$$
A=\begin{pmatrix}
1&1&1&1&1\\
0&1&0&0&1\\
0&0&0&1&1\\
0&0&1&0&0
\end{pmatrix},\qquad d=(1,-1,0,-1,1)^{\mathsf T}.
$$

本卷 §11 的整数关系和[《基础公式与关系》](AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)命题 12.3 已给出 $\ker_{\mathbb Z}A=\mathbb Z d$。后者的标签对应为

$$
(0,2,3,5,25)_{\rm old}\longmapsto(0,1,2,3,13)_{\rm here}.
$$

具体地，关系向量 $\xi$ 的末分量取整数 $t$，其余分量被原结果固定为 $\xi_1=\xi_3=-t,\xi_2=0,\xi_0=t$。因此所有保持质量及三个占位的整数交换都沿同一原始四角方向；这不是五个模式本身相同，也不是任意五态律都满足独立关系。计数多项式的主理想由该卷命题 12.4 承担，本卷 §12 须连同卷首 Q12、Q13 的模型条件和核生成补足一起使用。

为把此方向接回实际数量，令整数 $\ell\ge0$ 表示一个单窗之后追加的实际空窗数，置

$$
q=(2,3),\qquad M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad S=M^3.
$$

[《关联与原生接续》](AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md)§23.3 定理 23.1 和《基础公式与关系》§1.2 供应

$$
qM^{3\ell}=(F_{3\ell+3},F_{3\ell+4}),\qquad
c_s=(x(s)+y(s),y(s)+z(s))^{\mathsf T}.
$$

这里 $F_0=0,F_1=1$。该对应使用单窗零初始化后的组成位移 $c_s$，故运输权重 $\varepsilon_s(\ell)=qS^\ell c_s$ 为

$$
\begin{aligned}
\varepsilon_0&=0,&\varepsilon_1&=F_{3\ell+3},&
\varepsilon_2&=F_{3\ell+4},\\
\varepsilon_3&=F_{3\ell+5},&
\varepsilon_{13}&=\varepsilon_1+\varepsilon_3.
\end{aligned}
$$

所有 $\ell$ 都有 $\varepsilon_0+\varepsilon_{13}=\varepsilon_1+\varepsilon_3$，在 $\ell=0$ 即 $0+7=2+5$。因而 $m$ 个对称副本的加和数量为

$$
\sum_s n_s\varepsilon_s
=F_{3\ell+3}U+F_{3\ell+5}V+F_{3\ell+4}W,
\quad U=n_1+n_{13},\ V=n_3+n_{13},\ W=n_2.
$$

这个式子只提升单副本运输量的和。原有序读者则逐窗执行 $C'=SC+c_s$ 并保留接缝守卫；两窗终组成是 $Sc_{s_1}+c_{s_2}$，一般不等于 $c_{s_1}+c_{s_2}$。对称副本的占位态不是任意长度 $3m$ 的合法位词或原树历史。基础卷 §13.2 的谱投影与复群属于另一连续组成表示，不承担这里整数空窗运输的出处。

### 23.2 复四角缺陷、熵补全与零能条件

另供归一化复振幅及其射线

$$
\psi_s=\sqrt{p_s}\,e^{-i\theta_s},\qquad
\sum_s p_s=1,\qquad [\psi]\in\mathbb{CP}^4,
$$

定义

$$
\mathfrak d(\psi)=\psi_1\psi_3-\psi_0\psi_{13},\qquad
h([\psi])=|\mathfrak d(\psi)|^2.
$$

对任意非零齐次代表 $z$，同一函数应写成

$$
h([z])=\frac{|z_1z_3-z_0z_{13}|^2}{(\sum_s|z_s|^2)^2}.
$$

因此不依赖代表的模长及整体相位。固定占位均值 $(X,Y,Z)$，设 $r=1-Z$，概率纤维仍由原有仿射反演给出

$$
p=(r-X-Y+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa),
\quad \kappa_- =\max(0,X+Y-r),\quad
\kappa_+=\min(X,Y).
$$

在四底角正时置

$$
b(\kappa)=(X-\kappa)(Y-\kappa),\qquad
\delta_c(\kappa)=\kappa(r-X-Y+\kappa),
\qquad \chi=\theta_0-\theta_1-\theta_3+\theta_{13}\pmod{2\pi}.
$$

[《隐藏关系》](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md) C-12.2 的振幅按 $c_s^{\rm old}=\psi_s$ 逐项相同，其相位记号满足 $\theta_s^{\rm old}=-\theta_s$、$\Phi^{\rm old}=-\chi$；条件底面矩阵中的因子 $1/\sqrt r$ 使 $h=r^2|\det\mathcal A|^2$。直接消费该四角展开，得到

$$
\begin{aligned}
h&=b+\delta_c-2\sqrt{b\delta_c}\cos\chi\\
&=(\sqrt b-\sqrt{\delta_c})^2
+2\sqrt{b\delta_c}(1-\cos\chi),\\
b-\delta_c&=XY-r\kappa.
\end{aligned}
$$

故在 $r>0$ 且四底角正的域内，$h=0$ 恰为

$$
\kappa=\kappa_*:=\frac{XY}{r},\qquad \chi=0\pmod{2\pi}.
$$

概率部分的最大熵结论已有《隐藏关系》C-4.6：以自然对数写 $\mathcal S=-\sum_s p_s\log p_s$，固定均值纤维上的

$$
\mathcal S'=-\log\frac{p_0p_{13}}{p_1p_3},\qquad
\mathcal S''=-I(\kappa),\qquad
I=\frac1{p_0}+\frac1{p_1}+\frac1{p_3}+\frac1{p_{13}}>0
$$

给唯一内部熵极大点 $\kappa_*$。本章仅将这一点用于复缺陷的概率平衡；熵没有相位参数，所以不决定 $\chi$。有零振幅时用齐次多项式 $\mathfrak d=0$ 判定，不定义 $\arg0$ 或把内部相位坐标延伸成边界坐标。

### 23.3 奇异二次簇与完整占位像

**命题 23.2（四角零缺陷射线的几何应用）。** 在上述另供复载体中，零缺陷集

$$
Q=\{[z_0:z_1:z_2:z_3:z_{13}]\in\mathbb{CP}^4:
 z_0z_{13}-z_1z_3=0\}
$$

只有一个奇异点 $[0:0:1:0:0]$；其光滑部分复维三、实维六，Fubini–Study 形式在光滑部分的限制非退化。占位矩映射

$$
\mu([z])=\frac{\sum_s|z_s|^2v_s}{\sum_s|z_s|^2}
$$

把 $Q$ 映到整个金字塔

$$
P=\{(X,Y,Z):0\le Z\le1,\ 0\le X,Y\le1-Z\}.
$$

证明。齐次方程的梯度按本章顺序为

$$
(z_{13},-z_3,0,-z_1,z_0).
$$

它在非零齐次代表处全零，只能让中模式坐标 $z_2$ 非零。其余点是 $\mathbb{CP}^4$ 中的光滑复超曲面，因此复维三；正定 Kähler 度量在复切空间的限制仍正定，给非退化的实六维辛形式。

任意射线的占位是五个 $v_s$ 的凸组合，故像包含于 $P$。反向给定 $P$ 中 $(X,Y,Z)$：若 $r=1-Z>0$，取 $\kappa_*=XY/r$，置

$$
\begin{aligned}
p_0&=\frac{(r-X)(r-Y)}r,& p_1&=\frac{X(r-Y)}r,\\
p_3&=\frac{Y(r-X)}r,& p_{13}&=\frac{XY}r,& p_2&=Z.
\end{aligned}
$$

它们非负、总和一、具有所需均值，并满足 $p_0p_{13}=p_1p_3$。取五个非负平方根为振幅即给 $Q$ 中原像。若 $r=0$，所需均值只能是 $(0,0,1)$，由中模式奇异射线实现。证毕。

计数代数的二次理想沿用《基础公式与关系》命题 12.4，并将其多项式系数扩到 $\mathbb C$；本命题增加的是复射线、奇异点和矩像之间的具体对应。$Q$ 是紧的奇异射影对象，其光滑部分不是完整的光滑紧流形。因此它不是以六维光滑紧 toric 流形为前提的 Delzant 分类的反例，金字塔矩像也不消除顶点奇异性。

### 23.4 代数 Fock 域、降阶荷与最小交换次数

**定义 23.3（有限次数正算子）。** 使用代数直和

$$
\mathcal F_{\rm alg}=\bigoplus_{m\ge0}^{\rm alg}\mathcal H_m,
\qquad \mathcal H_m=\operatorname{Sym}^m(\mathbb C^5),
\qquad \mathcal H_q=0\quad(q<0).
$$

每个向量只含有限多个次数。归一化占位基为

$$
|n\rangle=\prod_{s\in\Sigma}\frac{(a_s^\dagger)^{n_s}}{\sqrt{n_s!}}
|\mathrm{vac}\rangle,\qquad n_s\ge0,\quad \sum_s n_s=m.
$$

产生、湮灭算子在这个代数域上逐项定义为

$$
a_s|n\rangle=\sqrt{n_s}|n-e_s\rangle,\qquad
 a_s^\dagger|n\rangle=\sqrt{n_s+1}|n+e_s\rangle.
$$

零占位的湮灭项为零。此处 $[a_s,a_t^\dagger]=\delta_{st}I$，同类算子相互交换；这些关系连接不同次数。固定的有限维 $\mathcal H_m$ 本身不承载这些 CCR：例如有限矩阵交换子的迹为零，不能等于迹非零的恒等矩阵。模式 $0$ 是可占据的空窗模式，$|1,0,0,0,0\rangle$ 不是 Fock 真空 $|0,0,0,0,0\rangle$。

记 $n_s=a_s^\dagger a_s$ 及

$$
N=\sum_s n_s,\qquad U=n_1+n_{13},\qquad
V=n_3+n_{13},\qquad W=n_2,
$$

并定义

$$
\widehat A=a_1a_3-a_0a_{13},\qquad
\widehat H=\widehat A^\dagger\widehat A,
\qquad B=a_0^\dagger a_{13}^\dagger a_1a_3.
$$

$\widehat A$ 从 $\mathcal H_m$ 到 $\mathcal H_{m-2}$，更精确地将固定荷

$$
(m,U,V,W)\longmapsto(m-2,U-1,V-1,W).
$$

两个湮灭项具有同一降荷；目标含负荷时相应空间为空。$\widehat H_m=\widehat H|_{\mathcal H_m}$ 则是同次数上的有限线性 Hermitian 算子，并有

$$
\widehat H=n_1n_3+n_0n_{13}-B-B^\dagger,\qquad
\langle\Psi,\widehat H_m\Psi\rangle=\|\widehat A\Psi\|^2\ge0.
$$

$B$ 将占位移为 $n+d$，$B^\dagger$ 为逆移，故 $\widehat H$ 保持 $N,U,V,W$。在 $m=0,1$ 上 $\widehat A=0$，所以 $\widehat H_m=0$。所需伴随性和正性完全在有限次数空间中成立，不涉及完成 Fock 空间上的无界自伴扩张。算子对向量线性；后文振幅函数 $h$ 的四次性是其期望符号的性质。

**命题 23.4（四角守恒交换的最小算子次数）。** 若一个非零正规序单项式在代数 Fock 域上

$$
(a^\dagger)^u a^v=\prod_s(a_s^\dagger)^{u_s}\prod_s a_s^{v_s},
\qquad u,v\in\mathbb N_0^5
$$

保持四个荷并具有非零占位位移，则其总算子次数至少四。次数恰为四时，交换方向只能由 $B$ 或 $B^\dagger$ 实现，允许任意系数及同时存在的对角项。

证明。荷的交换子逐项乘以 $A(u-v)$，故守恒要求 $A(u-v)=0$。消费 §23.1 的既有整数核，得到 $u-v=td$，整数 $t\ne0$。于是

$$
|u|+|v|\ge\sum_s|u_s-v_s|=4|t|\ge4.
$$

等号为四时 $|t|=1$，每个坐标的产生与湮灭没有共同余量，因此 $u,v$ 正好是 $d$ 的正负部分，或次序相反。这分别给 $B,B^\dagger$。次数二的一体正规序项没有非平凡守恒交换；次数四的二体项可以交换四角。这个判据针对具有交换的项，对角单项式 $u=v$ 不受非零位移下界约束。证毕。

《隐藏关系》C-15.2 的两副本同荷碰撞是这一方向在指定比较接口中的已有消费者；它不把本章对称 Fock 空间识别为有序两份输入。《隐藏关系》C-29.2 的全输入五标签保持刚性也属于不同合同：这里保持的是多副本总荷，允许同荷扇区内部交换，并未满足那个单副本全输入保持条件。

### 23.5 固定荷纤维、边系数与正则面积

取整数

$$
m\ge0,\quad 0\le W\le m,\quad R=m-W,\quad 0\le U,V\le R.
$$

固定这四个荷的空间记为 $\mathcal H_{m;U,V,W}$。消费《基础公式与关系》§12.1–§12.3 的占位提升，取 $k=n_{13}$ 得到完整基

$$
|k\rangle=|R-U-V+k,\ U-k,\ W,\ V-k,\ k\rangle,
$$

$$
k_- =\max(0,U+V-R),\qquad k_+=\min(U,V),
\qquad k_-\le k\le k_+.
$$

此区间非空，维数 $D=k_+-k_-+1$。直接应用产生、湮灭的平方根系数，得

$$
B|k\rangle=t_k|k+1\rangle,\qquad
 t_k=\sqrt{(U-k)(V-k)(k+1)(R-U-V+k+1)}.
$$

每条内部边 $k_-\le k<k_+$ 的四个因子都正；边界外的项为零。因此扇区矩阵连通，且

$$
\begin{aligned}
\langle k|\widehat H|k\rangle&=(U-k)(V-k)+k(R-U-V+k),\\
\langle k+1|\widehat H|k\rangle&=-t_k.
\end{aligned}
$$

只有 $m>0$ 时归一化 $X=U/m,Y=V/m,Z=W/m$ 和 $\kappa=k/m$。此时无论是否正则，区间反演都给精确式

$$
D=1+m(\kappa_+-\kappa_-).
$$

面积解释另有条件。本章采用射影直线积分为 $2\pi$ 的 Fubini–Study 形式及与之相容的度量，度量是《隐藏关系》C-14.1–C-14.2 约定的两倍。固定均值的三占位环面作用，在

$$
0<Z<1,\quad 0<X,Y<r=1-Z,\quad X\ne Y,\quad X+Y\ne r
$$

时给正则约化球面；正的五模式支撑保证内部自由作用，末两条排除上下端的双零概率。其内部坐标及形式为

$$
\omega_{\rm red}=d\chi\wedge d\kappa,\qquad
 g_{\rm red}=\frac{I(\kappa)}2\,d\kappa^2+
 \frac2{I(\kappa)}\,d\chi^2.
$$

这里相位对应 $\Phi^{\rm old}=-\chi$，两倍度量把原面积 $\pi(\kappa_+-\kappa_-)$ 变为

$$
\operatorname{Area}_{\rm red}=2\pi(\kappa_+-\kappa_-),\qquad
 D=1+\frac{m\operatorname{Area}_{\rm red}}{2\pi}.
$$

形式的符号也可从归一化振幅核对：$\psi_s=\sqrt{p_s}e^{-i\theta_s}$ 给 $\sum_s d\theta_s\wedge dp_s$，而纤维上 $dp_s=d_s\,d\kappa$，故余项是 $d\chi\wedge d\kappa$。单零端点收缩相位圆而光滑封口；双零端点的锥角已由 C-14.3 给出，所以正则面积式不被用来宣告所有边界约化都是光滑球面。$m=0$ 只有一份零占位，不定义归一化位置。以上 $D$ 数的是占位扇区维数，不是原生有序历史数。

### 23.6 四角正算子的有限链实现与精确谱

**定理 23.5（全部固定扇区的概率平衡应用）。** 在 §23.5 的任意可行整数扇区上，定义作用于函数列 $f=(f(k))$ 的连续时间生成元

$$
(Lf)(k)=\beta_k[f(k+1)-f(k)]+\delta_k[f(k-1)-f(k)],
$$

$$
\beta_k=(U-k)(V-k),\qquad
\delta_k=k(R-U-V+k).
$$

只使用可行区间内的邻点，端点外率为零。则其唯一平衡律为

$$
\pi_k=\frac{\binom Uk\binom{R-U}{V-k}}{\binom RV},
\qquad k_-\le k\le k_+,
$$

并满足详细平衡。令 $S_\pi=\operatorname{diag}(\sqrt{\pi_k})$，有精确相似关系

$$
\widehat H_{m;U,V,W}=-S_\pi L S_\pi^{-1}.
$$

因此扇区唯一的归一化零能射线由

$$
|\Omega_{m;U,V,W}\rangle=\sum_{k=k_-}^{k_+}\sqrt{\pi_k}\,|k\rangle
$$

代表。该扇区的全部特征值为

$$
\lambda_j=j(R-j+1),\qquad j=0,1,\ldots,w,
\qquad w=k_+-k_-=\min(U,V,R-U,R-V).
$$

它们各重数一；只有 $D\ge2$ 的扇区才有正谱隙，且谱隙为 $R$。

证明中的平衡律。取 $R$ 个位置，其中一个固定 $U$ 元集合带标记，从所有 $V$ 元子集均匀选择。交集大小 $k$ 的选择数是 $\binom Uk\binom{R-U}{V-k}$，可行范围正是所列区间。按交集分组枚举全部 $\binom RV$ 个子集，证明归一化；每个区间内的 $\pi_k$ 正。

直接取相邻组合数的比值得

$$
\frac{\pi_{k+1}}{\pi_k}
=\frac{(U-k)(V-k)}{(k+1)(R-U-V+k+1)}
=\frac{\beta_k}{\delta_{k+1}},
$$

即 $\pi_k\beta_k=\pi_{k+1}\delta_{k+1}$。内部双向率正，因此有限区间连通。若 $\rho$ 是平衡概率列，方程是 $L^{\mathsf T}\rho=0$；下端方程令第一条边的净流为零，逐点方程继而令每条边净流为零。相邻比值和归一化便强迫 $\rho=\pi$，单点区间则直接成立。这既证明唯一性，也区分函数列和概率列的方向。

此分布的矩用于后文波动应用。令 $J_a$ 是第 $a$ 个标记位置被随机 $V$ 元子集选中的指标，则 $k=\sum_{a=1}^U J_a$。当 $R>0$ 时 $\mathbb E J_a=V/R$，故

$$
\mathbb E_\pi k=\frac{UV}{R}.
$$

当 $R>1$ 时，不同标记位置同时入选的概率是 $V(V-1)/[R(R-1)]$，于是

$$
\begin{aligned}
\operatorname{Var}_\pi k
&=U\frac VR\left(1-\frac VR\right)
+U(U-1)\left[\frac{V(V-1)}{R(R-1)}-\frac{V^2}{R^2}\right]\\
&=\frac{UV(R-U)(R-V)}{R^2(R-1)}.
\end{aligned}
$$

$R=0$ 只有 $U=V=k=0$，$\pi_0=1$；$R=1$ 的所有可行扇区也是单点，方差零，不使用显示的 $R-1$ 分母。

证明中的相似变换。$L$ 的对角元是 $-(\beta_k+\delta_k)$，上邻元为 $\beta_k$，下邻元为 $\delta_k$。所以 $-S_\pi L S_\pi^{-1}$ 的上邻元是

$$
-\frac{\sqrt{\pi_k}\beta_k}{\sqrt{\pi_{k+1}}}
=-\sqrt{\beta_k\delta_{k+1}}=-t_k,
$$

下邻元相同，对角元是 $\beta_k+\delta_k$，逐项等于 §23.5 的正算子矩阵。由于 $L\mathbf1=0$，$S_\pi\mathbf1$ 是归一化零能向量。唯一性还可直接由有限 Dirichlet 形式看出：

$$
\langle f,-Lf\rangle_\pi
=\sum_{k=k_-}^{k_+-1}\pi_k\beta_k|f(k+1)-f(k)|^2.
$$

其零空间只有常数；相似变换便给所列唯一射线。$\pi_k$ 是概率，$\sqrt{\pi_k}$ 是量子振幅，这两者不可交换。唯一性只在一个固定扇区内，未宣告整个 $\mathcal H_m$ 的唯一基态。

证明中的全可行区间谱。对 $j\ge1$，展开 $f(k)=k^j$ 的前两阶有限差分，最高可能的系数由

$$
j(\beta_k-\delta_k)k^{j-1}
+\frac{j(j-1)}2(\beta_k+\delta_k)k^{j-2}
$$

给出，其中 $j=1$ 时第二项为零。因

$$
\beta_k-\delta_k=UV-Rk,\qquad
\beta_k+\delta_k=2k^2+(R-2U-2V)k+UV,
$$

次数 $j+1$ 的项抵消，次数 $j$ 的系数是

$$
-jR+j(j-1)=-j(R-j+1).
$$

余下差分项的次数至多 $j-1$，而 $L1=0$，故 $L$ 保持次数过滤。即使端点的一项引用区间外的多项式值，该项率为零，因此这个多项式计算在原可行区间每一点仍完全有效，不要求下端点为零。

区间的 $D$ 个不同整数上，$1,k,\ldots,k^{D-1}$ 的评价矩阵是可逆 Vandermonde 矩阵。故它们构成全部函数空间的一组基，$L$ 在该基中是三角矩阵，所列对角系数就是全部特征值，没有漏掉其他函数。若 $U+V\le R$，宽度为 $\min(U,V)$；若 $U+V>R$，宽度为 $R-\max(U,V)$，两式一起给 $w=\min(U,V,R-U,R-V)\le R/2$。对 $0\le j<w$，

$$
\lambda_{j+1}-\lambda_j=R-2j>0.
$$

因此谱简单，$w\ge1$ 时首个正特征值 $\lambda_1=R$。$w=0$ 时只有零特征值，包括所有零尺度边界。相似关系把这些结论逐项传到 $\widehat H$，完成该四角应用的证明。

这个链是经典 Bernoulli–Laplace 交换及其 Hahn/dual Hahn 多项式机制的一个明确参数实例，不作为新的通用链定理。Lim–Pickering 的 *A Nonlinear Transform for the Diagonalization of the Bernoulli-Laplace Diffusion Model and Orthogonal Polynomials*，[arXiv:1812.01143v1](https://arxiv.org/abs/1812.01143v1) §2 式 (2.1)–(2.4) 的参数对应是

$$
(N,N_1,N_2,N_w,N_b,i)=(R,U,R-U,V,R-V,k).
$$

原文的上、下跳概率因此为 $p_k=\beta_k/[U(R-U)]$、$q_k=\delta_k/[U(R-U)]$。它的 $T$ 是概率列矩阵，故当 $0<U<R$ 时，本章函数列生成元为

$$
L=U(R-U)(T^{\mathsf T}-I).
$$

式 (3.25) 的离散特征值 $1-j(R-j+1)/[N_1N_2]$ 经该缩放给本章 $-\lambda_j$。原文 §4 的对称化是 $Z=S_\pi^{-1}TS_\pi$；详细平衡使 $S_\pi T^{\mathsf T}S_\pi^{-1}=Z$，这正与本章相似方向一致。

原文式 (6.1) 用另一等价抽样方向写平衡律，代入后为

$$
\frac{\binom Vk\binom{R-V}{U-k}}{\binom RU}
=\frac{\binom Uk\binom{R-U}{V-k}}{\binom RV}.
$$

等号按阶乘逐项约掉得到，体现同一交集而非两个不同概率模型。原文展示的 $i=0,\ldots,N_w\le N_1$ 范围还需下端非负率；在上述映射中，完整的零起点区间需要 $V\le U$、$U+V\le R$。其他边际使用真实可行区间 $[k_-,k_+]$，由本证明承担其端点和谱。$U=0$ 或 $U=R$ 时缩放因子零，扇区为单点，直接有 $L=\widehat H=0$，不用除以 $N_1N_2$；$R=0$ 同样直接处理。原文平衡情形的混合时间估计没有转移到这里任意边际或零尺度边界。

共享谱不等于共享时间律：量子态用 $e^{-it\widehat H}$，概率列用 $e^{tL^{\mathsf T}}$。此外，只取交换项 $B+B^\dagger$ 会丢掉本章对角项。在 $D\ge2$ 时，这个交换算子是非零 Hermitian 矩阵而对角全零，迹为零，因此必有负特征值；本章 $\widehat H$ 正半定，所以二者的谱不同。单点扇区两者都为零，直接按该退化情形处理。

### 23.7 全次数零空间、有限多项式伴随与格点计数

**定理 23.6（四角量子核对既有格点数的实现）。** 对每个整数 $m\ge0$，

$$
\begin{aligned}
\dim\ker\widehat H_m
&=\sum_{W=0}^m(m-W+1)^2\\
&=\frac{(m+1)(m+2)(2m+3)}6\\
&=\binom{m+4}{4}-\binom{m+2}{4}
=|mP\cap\mathbb Z^3|.
\end{aligned}
$$

二项式在上指标小于四时为零。这里的数列与恒等式由《基础公式与关系》§12.1–§12.4 所有，本定理增加的是它们与 $\widehat A^\dagger\widehat A$ 零空间的对应。

第一种证明：扇区基态计数。$\mathcal H_m$ 按 $(U,V,W)$ 正交分解。固定 $W$，所有 $0\le U,V\le R=m-W$ 都有 §23.5 的非空占位提升，定理 23.5 在每个扇区给恰一条零能射线。故零空间维数是 $\sum_W(R+1)^2$。同一整数位置 $(U,V,W)$ 正是 $mP$ 的格点，已有计数结果给所列多项式和二项式差，不重新建立一般 Ehrhart 定理。

第二种证明：有限阶乘内积。令 $\mathcal P_m$ 是五变量的次数 $m$ 齐次复多项式空间，$\mathcal P_q=0$ 对 $q<0$。在所有有限多项式上定义

$$
\langle z^n,z^{n'}\rangle=\delta_{n,n'}\,n!,
\qquad n!=\prod_s n_s!.
$$

映射 $|n\rangle\mapsto z^n/\sqrt{n!}$ 是各次数空间间的等距映射。对单项式，$\partial_s z^n=n_s z^{n-e_s}$，而

$$
n_s(n-e_s)!=n!,
$$

所以乘 $z_s$ 与 $\partial_s$ 互为伴随；不同次数正交。这给完全有限的多项式表示

$$
\widehat A=\partial_1\partial_3-\partial_0\partial_{13},\qquad
\widehat A^\dagger=M_f,\quad f=z_1z_3-z_0z_{13}.
$$

对 $m\ge2$，$M_f:\mathcal P_{m-2}\to\mathcal P_m$ 是单射，因为复多项式环无零因子且 $f\ne0$。有限维伴随关系于是给 $\widehat A:\mathcal P_m\to\mathcal P_{m-2}$ 满射：若一个目标向量正交于其像，便被 $\widehat A^\dagger=M_f$ 送到零，单射迫使该向量为零。由 $\ker(\widehat A^\dagger\widehat A)=\ker\widehat A$ 和 rank–nullity，

$$
\dim\ker\widehat H_m=\dim\mathcal P_m-\dim\mathcal P_{m-2}
=\binom{m+4}{4}-\binom{m+2}{4}.
$$

$m=0,1$ 时目标空间为零，$\widehat H_m=0$，维数分别为一、五，与第一种证明及已有计数一致。证毕。

同一伴随关系还解释齐次坐标环的应用。基础卷命题 12.4 的变量按 §23.1 改名、系数扩为复数后，$Q$ 的齐次理想为 $(f)$，符号相反不改变主理想。次数 $m$ 的商空间是

$$
(\mathbb C[z]/(f))_m=\mathcal P_m/(f\mathcal P_{m-2}),
\qquad
\ker\widehat A=(f\mathcal P_{m-2})^\perp.
$$

由阶乘内积，每个商类有唯一正交代表，故这两个空间等维且有此有限线性识别。零能向量是多项式空间中的向量，$Q$ 的点是复五振幅的射线；这里没有把所有零能向量逐点识别为 $Q$ 的点。Bargmann 的 *On a Hilbert space of analytic functions and an associated integral transform, Part I*（DOI [10.1002/cpa.3160140303](https://doi.org/10.1002/cpa.3160140303)）只归属解析 Fock 表示背景；此应用的伴随与满射由上述有限阶乘论证承担，不引用未经给出的原文定理编号。

全空间的谱隙也可从同一个扇区模型得到，而不把某个 $R$ 的谱隙移用成全空间谱隙。对 $R=0,\ldots,m$、$j=0,\ldots,\lfloor R/2\rfloor$，标记对 $(R,j)$ 的特征值是 $j(R-j+1)$，贡献的重数为

$$
(R-2j+1)^2.
$$

理由是该 $j$ 出现在扇区内当且仅当 $w\ge j$，等价于 $j\le U,V\le R-j$；固定 $R$ 已固定 $W=m-R$，故正好有该平方数个扇区，每个贡献一维。不同 $(R,j)$ 若数值相同，重数相加。$j=0$ 的重数总和恢复本节量子核计数。任意正特征值满足 $R\ge2j,j\ge1$，从而

$$
j(R-j+1)\ge j(j+1)\ge2.
$$

$m\ge2$ 时 $R=2,U=V=1,W=m-2,j=1$ 实现特征值二，故整个 $\widehat H_m$ 的正谱隙是二，$\widehat H_m/m$ 的正谱隙是 $2/m$。$m=0,1$ 没有正谱隙。

### 23.8 数固定相干态与零能扇区投影

**定理 23.7（复四角簇的相干符号应用）。** 对单位振幅 $\psi$ 及整数 $m\ge0$，定义数固定相干向量

$$
|\psi;m\rangle=\frac1{\sqrt{m!}}
\left(\sum_s\psi_s a_s^\dagger\right)^m|\mathrm{vac}\rangle.
$$

它归一化，且对 $m\ge2$ 有

$$
\widehat A|\psi;m\rangle
=\sqrt{m(m-1)}\,\mathfrak d(\psi)|\psi;m-2\rangle,
$$

$$
\langle\psi;m|\widehat H_m|\psi;m\rangle=m(m-1)h([\psi]).
$$

$m=0,1$ 的期望为零。若 $[\psi]\in Q$，任何非零固定荷投影在归一化后都等于定理 23.5 的对应基态射线。

证明。将产生算子的 $m$ 次幂展开，得到

$$
|\psi;m\rangle
=\sum_{\sum n_s=m}\sqrt{\frac{m!}{\prod_s n_s!}}
\prod_s\psi_s^{n_s}|n\rangle.
$$

多项式定理给范数平方 $(\sum_s|\psi_s|^2)^m=1$。由 $[a_s,\sum_t\psi_t a_t^\dagger]=\psi_s$，湮灭一次给 $\sqrt m\psi_s|\psi;m-1\rangle$，再湮灭一次给

$$
a_sa_t|\psi;m\rangle=\sqrt{m(m-1)}\psi_s\psi_t|\psi;m-2\rangle.
$$

相减得到 $\widehat A$ 的式子，再取范数平方得到期望。$m<2$ 两次湮灭为零。若 $\mathfrak d=0$，$\widehat H_m$ 消去该相干态；它又与荷扇区投影交换，所以每个投影也在该扇区零空间中。非零投影按定理 23.5 的一维性等于 $\Omega$ 射线。证毕。

在所有相关振幅非零时也能逐项核对：固定荷展开系数 $c_k$ 的相邻比为

$$
\frac{c_{k+1}}{c_k}
=\frac{\psi_0\psi_{13}}{\psi_1\psi_3}
\sqrt{\frac{(U-k)(V-k)}{(k+1)(R-U-V+k+1)}}.
$$

在 $Q$ 上复比值是一，剩下恰为 $\sqrt{\pi_{k+1}/\pi_k}$。此核对没有把概率本身当作振幅。有零振幅时一些扇区投影可为零；只能归一化实际非零的投影。

对 $m\ge2$，$\widehat H_m/[m(m-1)]$ 的相干期望严格等于 $h$，而 $\widehat H_m/m$ 的相干期望严格等于 $(m-1)h$。这两个归一化分别用于符号和后文扇区时间尺度，不互相替代。相干态是符号计算的向量族；有限 $m$ 的酉演化不因此必然保持该向量族。

### 23.9 Fisher 曲率与基态精确波动

**命题 23.8（正底面平衡的波动应用）。** 设

$$
0<r\le1,\qquad 0<X,Y<r,
$$

并取 §23.2 的 $\kappa_*=XY/r$。四底角都正，置

$$
c_*=p_1p_3=p_0p_{13}
=\frac{XY(r-X)(r-Y)}{r^2},\qquad I_*:=I(\kappa_*)=\frac r{c_*}.
$$

在可行整数扇区 $m>0,R>1,X=U/m,Y=V/m,r=R/m$ 的归一化基态中，

$$
\operatorname{Var}_{\Omega}\left(\frac{n_{13}}m\right)
=\frac{UV(R-U)(R-V)}{m^2R^2(R-1)}
=\frac r{(R-1)I_*}.
$$

沿任何存在的、保持这些正边际的可行整数序列 $m\to\infty$，有

$$
m\operatorname{Var}_{\Omega}(n_{13}/m)\longrightarrow\frac1{I_*}.
$$

证明。占位读数的基态概率是 $\pi$，所以第一等号是定理 23.5 的精确方差除以 $m^2$。平衡四概率给

$$
\frac1{p_0}+\frac1{p_1}+\frac1{p_3}+\frac1{p_{13}}
=\frac{r^3}{XY(r-X)(r-Y)}=\frac r{c_*}.
$$

代入 $U=mX,V=mY,R=mr$ 即得第二等号。序列上 $R=mr$，故 $mr/(R-1)\to1$，得到极限。证毕。

此处消费的是《隐藏关系》C-4.6 的熵 Hessian 与 Fisher 长度，增加的是同一曲率和有限基态占位方差之间的精确比例。固定边际必须确有整数序列：若 $X,Y,Z$ 都为有理数，可取公共分母的倍数；任意指定的无理边际不一定能精确保留。若改用趋向目标边际的有理近似序列，极限必须另按相应参数的收敛说明，不能称为精确保留。此结论是分布波动，不赋予物理不确定性原理的含义。

### 23.10 正平衡的局部振动、耗散与尺度区别

**命题 23.9（同一四角平衡附近的局部时间对应）。** 在命题 23.8 的正底面域内，以 $\Delta\kappa=\kappa-\kappa_*$、$\chi=0$ 附近的实相位坐标，有

$$
\begin{aligned}
h&=\frac{r^2}{4c_*}(\Delta\kappa)^2+c_*\chi^2
+O\bigl((|\Delta\kappa|+|\chi|)^3\bigr)\\
&=\frac r2\left[\frac{I_*}2(\Delta\kappa)^2+
\frac2{I_*}\chi^2\right]+O\bigl((|\Delta\kappa|+|\chi|)^3\bigr).
\end{aligned}
$$

在 $\omega_{\rm red}=d\chi\wedge d\kappa$ 和 $\iota_{X_h}\omega_{\rm red}=dh$ 的符号约定下，线性化方程为

$$
\dot\chi=\frac{rI_*}2\Delta\kappa,\qquad
\dot\kappa=-\frac{2r}{I_*}\chi,
$$

小振动角频率为 $r$。在选定函数生成元 $L/m$ 的连续时间链中则有精确均值方程

$$
\frac d{dt}\mathbb E(k/m)=XY-r\mathbb E(k/m).
$$

非单点扇区的 $\widehat H_m/m$ 正谱隙恰为 $R/m=r$。

证明。由 $b-\delta_c=XY-r\kappa=-r\Delta\kappa$，

$$
(\sqrt b-\sqrt{\delta_c})^2
=\frac{r^2(\Delta\kappa)^2}{(\sqrt b+\sqrt{\delta_c})^2}
=\frac{r^2}{4c_*}(\Delta\kappa)^2+O(|\Delta\kappa|^3).
$$

另有 $2\sqrt{b\delta_c}(1-\cos\chi)=c_*\chi^2+O((|\Delta\kappa|+|\chi|)^3)$，证明展开；$I_*=r/c_*$ 给度量系数的对应。收缩公式给 $\dot\chi=\partial_\kappa h$、$\dot\kappa=-\partial_\chi h$，再代入二次项，二阶方程是 $\ddot\chi=-r^2\chi$。

对链，$Lk=UV-Rk$，因而 $L(k/m)=(UV-Rk)/m$。生成元再除以 $m$，得到 $XY-r(k/m)$；有限空间上取期望即可得均值方程。谱隙是定理 23.5 除以 $m$ 的直接消费者。证毕。

正底面局部平衡允许 $Z=0$，也允许 $X=Y$ 或 $X+Y=r$；它只需四底角在 $\kappa_*$ 正，不需要 §23.5 的整个闭约化球面正则条件。所用 Fisher 及水平度量在平衡的实际支撑上定义，中模式零概率不进入四角 $I_*$。

这里的时间是模型中自定的无量纲参数。相同的 $r$ 分别表示 Hamilton 小振动频率、Markov 均值衰减率和固定扇区谱隙，并不使耗散、酉演化和非线性 Hamilton 流相等。特别是 §23.8 的严格符号归一化为 $\widehat H_m/[m(m-1)]$，本节谱与链的时间归一化为 $\widehat H_m/m,L/m$；后者相干期望为 $(m-1)h$，不能据此把有限 $m$ 的相干轨道认作 $h$ 的精确流。

全空间缩放还须保留 §23.7 的结论：$\widehat H_m/m$ 正谱隙为 $2/m$，不等于固定非平凡扇区的 $r$。对一列存在的扇区，若 $R/m\to r>0$ 且固定 $j$ 始终在允许范围内，则

$$
\frac{j(R-j+1)}m\longrightarrow jr.
$$

这只是逐个固定 $j$ 的极限。若 $j/m\to\eta>0$ 且 $R/m\to r$，允许范围要求 $\eta\le r/2$，并有

$$
\frac{j(R-j+1)}{m(m-1)}\longrightarrow\eta(r-\eta).
$$

两式直接分别除以相应尺度取极限，说明固定指标与随次数增长指标的谱尺度不同。有限范围和全空间简并仍存在，没有从前一式推出整条极限调和梯级。

### 23.11 两态演化与同均值的未来相干读出

**命题 23.10（最小扇区的两种时间律及未来分离）。** 取 $m=2,U=V=1,W=0$，基按

$$
|L\rangle=|0,1,0,1,0\rangle,\qquad
|R\rangle=|1,0,0,0,1\rangle
$$

排列。它们分别有 $k=0,1$。于是

$$
\widehat H=\begin{pmatrix}1&-1\\-1&1\end{pmatrix},\qquad
L=-\widehat H,\qquad \operatorname{spec}\widehat H=\{0,2\},
\qquad \pi=(1/2,1/2).
$$

由 $|L\rangle$ 出发的酉状态及 $R$ 的概率为

$$
e^{-it\widehat H}|L\rangle
=e^{-it}(\cos t\,|L\rangle+i\sin t\,|R\rangle),
\qquad P_R^{\rm quantum}(t)=\sin^2t.
$$

同一初始确定占位的连续时间链则给

$$
P_R^{\rm Markov}(t)=\frac{1-e^{-2t}}2\qquad(t\ge0).
$$

另取

$$
|\Psi_\pm\rangle=\frac{|L\rangle\pm i|R\rangle}{\sqrt2}.
$$

两态所有五个平均占位相同，$\mathbb E n_{13}=1/2$，但在上述同一酉演化下

$$
\left.\frac d{dt}\langle n_{13}\rangle_{\Psi_\pm(t)}\right|_{t=0}=\pm1.
$$

证明。两点率为 $\beta_0=\delta_1=1$，代入扇区矩阵得显示式；对称和反对称向量给特征值零、二。写 $\widehat H=I-\sigma_x$ 得酉式。概率方程 $\dot P_R=1-2P_R,P_R(0)=0$ 给链的指数式。

两个 $\Psi_\pm$ 在占位基的对角概率都为 $(1/2,1/2)$，故每个对角占位读数都相同，五均值为 $(1/2,1/2,0,1/2,1/2)$。而

$$
n_{13}=\begin{pmatrix}0&0\\0&1\end{pmatrix},\qquad
 i[\widehat H,n_{13}]=\begin{pmatrix}0&-i\\i&0\end{pmatrix}=\sigma_y.
$$

$\Psi_\pm$ 是 $\sigma_y$ 的正、负本征态，Heisenberg 导数即为 $\pm1$。更具体地，未来概率是 $(1\pm\sin2t)/2$，所以在一般的同一个未来时刻也可分离。证毕。

这是在明确给定相干态、酉演化和占位观测的有限模型里，当前完整平均占位不足以决定未来读数的成对例子。它不自动供应原有概率读者、原生位词守卫或比较装置的实现。量子振荡和经典衰减虽有同谱源，时间律已经在最小扇区上不同。

### 23.12 与四波文献的精确谱补对应

**命题 23.11（四个作用模式的文献谱补）。** Odzijewicz–Wawreniuk 的 *An integrable (classical and quantum) four-wave mixing Hamiltonian system*，[arXiv:2003.03060v1](https://arxiv.org/abs/2003.03060v1) 式 (3.1)，在其 $\hbar=g=1$、四个频率全为零的参数下，按

$$
(b_0,b_1,b_2,b_3)_{\rm paper}=(a_{13},a_1,a_0,a_3)_{\rm here}
$$

改名，成为本章四个作用模式上的算子

$$
K=n_{13}(n_3+1)+n_1(n_0+1)+B+B^\dagger.
$$

在固定 $(m,U,V,W)$ 扇区上，它与本章正算子满足

$$
\widehat H=U(R-U+1)I-K.
$$

原文式 (3.6)–(3.8)、(3.18) 的三个守恒荷对应为

$$
(c_1,c_2,c_3)=(U,R-U,U+V-R).
$$

证明。原文式 (3.1) 的两项对角因子是 $b_0^\dagger b_0(b_3^\dagger b_3+1)$ 和 $b_1^\dagger b_1(b_2^\dagger b_2+1)$，由所列映射即得 $K$ 的对角项。原文交互项 $b_0b_1^\dagger b_2b_3^\dagger$ 及其伴随给 $B^\dagger,B$。因此它与本章 $\widehat H$ 的交互符号和对角项都不同。

相加时交互项抵消；对角和利用 $n_1+n_{13}=U$、$n_0+n_3=R-U$ 得

$$
\begin{aligned}
\widehat H+K
&=n_1n_3+n_0n_{13}+n_{13}(n_3+1)+n_1(n_0+1)\\
&=(n_1+n_{13})(n_0+n_3+1)=U(R-U+1)I.
\end{aligned}
$$

原文荷为 $n_{b_0}+n_{b_1}$、$n_{b_2}+n_{b_3}$、$n_{b_0}-n_{b_2}$，逐项代入给所列对应；最后一项是 $k-(R-U-V+k)=U+V-R$。其非负可行条件 $c_1,c_2,c_1-c_3,c_2+c_3\ge0$ 分别为 $U,R-U,R-V,V\ge0$，与本章边际一致。原文式 (3.24) 的 $b_0$ 占位范围也正是本章 $[k_-,k_+]$。证毕。

因此固定扇区的 $K$ 特征值是 $U(R-U+1)-j(R-j+1)$，这是常数反射的谱补，并非声称两算子相同。本章中模式 $a_2$ 是独立守恒的额外 spectator，原文四模式系统没有该第五模式。其经典 §2 从四个振幅全非零的 $\Omega_4$ 出发，不供应本章 $\mathbb{CP}^4$ 的零振幅边界、奇异中模式或完整矩像；这些由命题 23.2 的齐次方程证明承担。这里的文献参数设置只建立代数对应，不作物理时钟、普朗克尺度或器件实现推断。

### 23.13 同一原始关系的消费者与数学边界

本章的具体应用以同一个 $d$ 连接不同载体：在概率纤维中是 $\kappa$ 的变化方向，在复振幅中是四角多项式，在对称占位中是 $B$ 的荷守恒交换，在有限链中是相邻整数步，在量子核中则经唯一扇区基态与既有金字塔格点对应。每个连接都保留了上述对象、参数及证明条件，既有通用结果保持原归属。

整数核及计数理想直接使用本卷 §11–§12 的适用边界与《基础公式与关系》§12.1–§12.4；后者的平方 minor 背景由 Sullivant，*Toric Fiber Products*，[arXiv:math/0602052v1](https://arxiv.org/abs/math/0602052v1) 例 1.2 归属。熵与 Fisher 曲率使用《隐藏关系》C-4.6，复概率—相位缺陷使用 C-12.2，完整相位商、水平度量及端点使用 C-13.1–C-14.3，并明确采用 $c_{\rm old}=\psi,\theta_{\rm old}=-\theta,\Phi_{\rm old}=-\chi$ 和两倍度量。单窗整数 Fibonacci 运输使用《关联与原生接续》§23.3 定理 23.1 及基础卷 §1.2；这些接续结论没有成为任意对称副本的有序历史结论。

Lim–Pickering 的一般边际跳率、特征值、相似方向和平衡律分别用于 §23.6 的参数应用；全原可行区间及零尺度例外由该节有限多项式证明承担。Odzijewicz–Wawreniuk 的式 (3.1) 用于 §23.12 的谱补，未把其四波对角项换成本章对角项。有限阶乘内积承担 §23.7 的伴随与量子核论证；Bargmann 仅作历史背景。所有这些是普通数学推导及文献应用，不据其共同术语宣称文献优先权。

空窗模式是四角交换的必要角，中模式则是独立守恒模式。有限数固定空间、齐次复射线、经典概率律、连续时间链和原有合法有序来源各有自己的载体；它们之间仅使用正文已给出的映射。占位守恒不恢复被对称化删去的顺序或接缝信息，同谱不统一时间律，波动极限不供应物理装置结论。

## 追加锚（本行以下为增补区）

## 24. 隐藏关系的最小守恒交换与校准局域钟

### 24.1 五标签、概率纤维与完整相位商

**定义 24.1（占位、振幅及关系坐标）。** 使用 §23.1 的同一五标签

$$
\Sigma=(0,1,2,3,13),\qquad
(v_0,v_1,v_2,v_3,v_{13})
=((0,0,0),(1,0,0),(0,0,1),(0,1,0),(1,1,0)).
$$

三坐标 $(x,y,z)$ 的次序是低、高、中；标签 $2$ 是中位，标签 $13$ 是低高同时占据。取概率律 $p$，令

$$
X=p_1+p_{13},\qquad Y=p_3+p_{13},\qquad Z=p_2,\qquad \kappa=p_{13}.
$$

本卷 §23.1–23.2 供应的反演在这里逐项为

$$
p_\kappa=(1-X-Y-Z+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa),
$$

$$
0\le Z\le1,\quad 0\le X,Y\le1-Z,\qquad
\max(0,X+Y+Z-1)\le\kappa\le\min(X,Y).
$$

五个非负条件分别给这个闭区间的下界、上界和 $Z\ge0$，总和恒为一。均值域中的 $X,Y\le1-Z$ 又保证下界不超过上界；故它给全部可行律，包括零宽度和零概率边界。

为避免与后面的交换算子 $A$ 混淆，将 §23.1 的质量—占位矩阵改记为 $W$：

$$
W=\begin{pmatrix}
1&1&1&1&1\\
0&1&0&0&1\\
0&0&0&1&1\\
0&0&1&0&0
\end{pmatrix},\qquad d=(1,-1,0,-1,1)^{\mathsf T}.
$$

精确的所有者对应是 $W=A_{\S23.1}$，而基础公式卷原标签 $(0,2,3,5,25)$ 对应 $(0,1,2,3,13)$；隐藏关系卷的 $(O,L,T,R,J)$ 也依次对应这些标签。原有核公式给

$$
\ker_{\mathbb R}W=\mathbb R d,\qquad
\ker_{\mathbb Z}W=\mathbb Z d.
$$

其参数对应可直接看出：若 $Wc=0$，中位行给 $c_2=0$，低、高行给 $c_1=c_3=-c_{13}$，质量行给 $c_0=c_{13}$。因此 $c=c_{13}d$，实系数和整数系数分别给两个核。$d$ 的非零分量互素，故为原始整数方向；概率纤维的切向量正是 $\partial_\kappa p=d$。列关系是 $v_0+v_{13}=v_1+v_3$，质量行也参与其中。

另供正交标签空间 $\mathcal H=\mathbb C^5$，按负相位约定嵌入

$$
|\psi\rangle=\sum_{s\in\Sigma}\sqrt{p_s}e^{-i\theta_s}|s\rangle,
\qquad \langle\psi|\psi\rangle=1,\qquad
[\psi]\in\mathbb{CP}^4.
$$

$|0\rangle$ 是范数一的空标签基向量，既不是零向量，也不是 §23.4 的零粒子 Fock 真空。共同相位只改变归一化代表，不改变射线。概率律没有独自规定这些相位或这一个复载体。

在全正图上取

$$
\chi=\theta_0-\theta_1-\theta_3+\theta_{13}\pmod{2\pi},\qquad
R=\sqrt{p_0p_1p_3p_{13}},\qquad
M=\psi_0\psi_{13}\overline{\psi_1}\,\overline{\psi_3}
=Re^{-i\chi}.
$$

四个底面模式都参加 $M$；空模式的振幅不能省略。若乘积为零，仍使用多项式 $M$，不赋予 $\arg0$ 一个角。

数学引文与完整商对应。[《辛预测完成》§35.3–35.5](SYMPLECTIC_PREDICTIVE_COMPLETION.md#353-五模式振幅局部原始形式与最小维数)使用完全相同的负相位、标签及概率坐标，射影直线面积取 $2\pi$，Hamilton 约定为 $\iota_{X_H}\Omega=dH$。其共同相位及占位相位作用在此合写为

$$
\theta_s\longmapsto\theta_s+\alpha+x_s\beta+y_s\gamma+z_s\eta,
\qquad (\alpha,\beta,\gamma,\eta)\in(\mathbb R/2\pi\mathbb Z)^4.
$$

由 $Wd=0$，$\chi$ 在整个作用下不变。更强的整周期说明如下：取

$$
\alpha=-\theta_0,\quad
\beta=\theta_0-\theta_1,\quad
\gamma=\theta_0-\theta_3,\quad
\eta=\theta_0-\theta_2
\pmod{2\pi}.
$$

变换后的 $\theta_0,\theta_1,\theta_2,\theta_3$ 全为零，$\theta_{13}=\chi$。保持这四个零角的变换依次强制四个参数全为零模 $2\pi$，所以没有遗漏的有限剩余规范类；这不是仅由微分得到的商。与隐藏关系卷正相位记号的对应是 $\theta_s^{\rm old}=-\theta_s$、$\Phi^{\rm old}=-\chi$。

令 $\vartheta_X=\theta_1-\theta_0$、$\vartheta_Y=\theta_3-\theta_0$、$\vartheta_Z=\theta_2-\theta_0$。消费上述辛形式的精确坐标式，

$$
\Omega=d\vartheta_X\wedge dX+d\vartheta_Y\wedge dY
+d\vartheta_Z\wedge dZ+d\chi\wedge d\kappa.
$$

也可由局部势 $\lambda=\sum_sp_s\,d\theta_s=d\theta_0+X\,d\vartheta_X+Y\,d\vartheta_Y+Z\,d\vartheta_Z+\kappa\,d\chi$ 取 $-d\lambda$ 读出该式。在含全正律的固定均值层，先限制 $X,Y,Z$，再商掉三个占位相位轨道，得到

$$
\Omega_{\rm red}=d\chi\wedge d\kappa.
$$

只固定均值而不取商时限制形式退化，不能称为这个二维辛空间。这里使用的是正部分圆柱；端点零支撑、稳定子和闭曲面的正则性仍按 §35.5 的条件处理。射影 Kähler 与 Schrödinger 的几何背景见 [Ashtekar–Schilling，Geometrical Formulation of Quantum Mechanics](https://arxiv.org/abs/gr-qc/9706069)及[既有文献条目](../../../Library/Geometry/ashtekar1997geometrical.md)；该背景不赋予 FIB 标签一个物理时钟。

### 24.2 固定单系统通道的已有刚性及其量词

**假设 24.2（严格的单系统保持与另供的双系统）。** 在同一个 $\mathcal H$ 上定义三个投影

$$
N_x=\operatorname{diag}(0,1,0,0,1),\quad
N_y=\operatorname{diag}(0,0,0,1,1),\quad
N_z=\operatorname{diag}(0,0,1,0,0).
$$

全输入单系统保持指一个固定、线性、同域 CPTP 通道 $\mathcal N$ 满足

$$
\operatorname{tr}(N_a\mathcal N(\rho))=\operatorname{tr}(N_a\rho)
\quad\text{对每个密度态 }\rho\text{ 及 }a=x,y,z.
$$

数学引文与应用。[HiddenRelations 定理 C-29.2](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md#29-同一五模式的全输入保真方形记录与稳定子块)已经给出更强的完整分类：在定义 24.1 的标签对应下，上述通道恰为

$$
\mathcal N(\rho)=\Gamma\circ\rho,\qquad
\Gamma\succeq0,\quad\Gamma_{ss}=1.
$$

因而所有 $p_s$ 和 $\kappa$ 都保持；通道仍可消去相干性，不必是恒等通道。这里消费这个 Schur 分类，不另把“不能改变 $\kappa$”作为较弱的新分类。

投影的核与像说明同一前提为何如此强。写 $\mathcal N(\rho)=\sum_\nu K_\nu\rho K_\nu^\dagger$。对任意占位投影 $P=N_a$，全输入条件等价于 $\sum_\nu K_\nu^\dagger P K_\nu=P$。若 $v\in\ker P$，则

$$
0=\sum_\nu\|PK_\nu v\|^2,
$$

所以每个 $K_\nu$ 保持 $\ker P$。迹保持还给 $\mathcal N^*(I-P)=I-P$；对 $v\in\operatorname{im}P=\ker(I-P)$ 同理得到 $K_\nu v\in\operatorname{im}P$。故所有 Kraus 算子同时保持三个投影的共同特征空间。五个联合特征标签 $v_s$ 互异，每个共同空间是一维，因而每个 $K_\nu$ 都在五标签基中对角。这正是原 Schur 分类的算子对应。

下文另供两个可区分系统 $\mathcal H_1\otimes\mathcal H_2$；$|s,t\rangle$ 与 $|t,s\rangle$ 是不同基向量，除非 $s=t$。在涉及乘积输入的条目中，假定两个系统由两次独立准备得到相同的态，联合输入为 $\rho\otimes\rho$。这是准备资源的假设，不是从一份未知态克隆出另一份。双系统只要求保持总加和占位，不满足上述固定单系统通道的全输入合同。

### 24.3 有序双系统交换、最小体积与 Fock 对应

**定理 24.3（最小非平凡直方图交换的有序实现）。** 定义

$$
A=|0,13\rangle\langle1,3|+|13,0\rangle\langle3,1|,
\qquad V=A+A^\dagger,
$$

$$
Q_a=N_a\otimes I+I\otimes N_a\quad(a=x,y,z),\qquad
\mathsf S|s,t\rangle=|t,s\rangle.
$$

则 $[Q_a,A]=[Q_a,V]=0$，且 $\mathsf S A\mathsf S=A$、$[\mathsf S,V]=0$。在质量与三占位加和均严格保持的同标签交换中，消去两侧相同副本后，非零直方图变化的每侧最小副本数为二，唯一无序二对二碰撞是

$$
\{0,13\}\longleftrightarrow\{1,3\}.
$$

证明。对任意有序基矩阵单位，

$$
[Q_a,|s,t\rangle\langle u,v|]
=(a_s+a_t-a_u-a_v)|s,t\rangle\langle u,v|.
$$

$A$ 的两项均用同一列关系 $v_0+v_{13}=v_1+v_3$，故交换子为零；取伴随给 $V$ 的结论。交换两个系统将 $A$ 的第一项变成第二项，反之亦然，故得交换对称性。

更一般地，设两个等长有序标签列表的直方图分别为 $h^+,h^-\in\mathbb N_0^5$，总质量及总占位相等。其差 $c=h^+-h^-$ 属于 $\ker_{\mathbb Z}W$，即 $c=kd$。逐标签取消共同副本后，剩余每侧体积为

$$
m(c)=\sum_s\max(c_s,0)
=\sum_s\max(-c_s,0)=\frac12\sum_s|c_s|=2|k|.
$$

非零变化要求 $k\ne0$，所以 $m(c)\ge2$；等号时 $k=\pm1$，恰为所列四角碰撞。若只是排列同一直方图，$c=0$，即使有序态互异也不算非零交换体积。共同旁观副本同样不计入 $m(c)$。

这个整数判据直接连接严格的算子守恒。对 $m$ 系统的总荷 $Q_a^{(m)}=\sum_jN_a^{(j)}$，任意算子 $K$ 满足

$$
\langle\mathbf s|[Q_a^{(m)},K]|\mathbf t\rangle
=(q_a(\mathbf s)-q_a(\mathbf t))K_{\mathbf s\mathbf t},
\qquad q_a(\mathbf s)=\sum_ja_{s_j}.
$$

因此 $[K,Q_a^{(m)}]=0$ 强制每个非零跃迁矩阵元两端的总荷相等。反向，一对总荷相等的列表所给的矩阵单位及其伴随都与荷交换。没有借用外部储库抵偿，也没有把“某个输入的期望相等”提升为这个全算子结论。$A$ 给出了达到二的具体实现。证毕。

**命题 24.4（同荷空间的维数与归一化对称嵌入）。** $V$ 在有序空间的两个不相交二维块

$$
\mathcal B_1=\operatorname{span}\{|0,13\rangle,|1,3\rangle\},\qquad
\mathcal B_2=\operatorname{span}\{|13,0\rangle,|3,1\rangle\}
$$

上各为 Pauli 矩阵 $\begin{pmatrix}0&1\\1&0\end{pmatrix}$，在其余二十一维上为零。总荷 $(1,1,0)$ 的有序空间为四维；在对称子空间中它为二维。$\operatorname{Sym}^2\mathbb C^5$ 的十五个直方图基具有十四个不同总荷，除该二维块外，其余荷块均一维。

证明。$A$ 从每块的第二基向量送到第一基向量，$A^\dagger$ 反向，二者消去其余基向量，得块形式。十五个无序对与总荷的完整对应为

$$
\begin{array}{c|ccccc}
\text{对}&00&01&02&03&0\,13\\\hline
\text{荷}&(0,0,0)&(1,0,0)&(0,0,1)&(0,1,0)&(1,1,0)
\end{array}
$$

$$
\begin{array}{c|ccccc}
\text{对}&11&12&1\,3&1\,13&22\\\hline
\text{荷}&(2,0,0)&(1,0,1)&(1,1,0)&(2,1,0)&(0,0,2)
\end{array}
$$

$$
\begin{array}{c|ccccc}
\text{对}&23&2\,13&33&3\,13&13\,13\\\hline
\text{荷}&(0,1,1)&(1,1,1)&(0,2,0)&(1,2,0)&(2,2,0).
\end{array}
$$

唯一重复是 $0\,13$ 与 $1\,3$。有序空间保留各自的两个顺序，所以此荷空间维数为四；其他含不同标签的无序对在有序空间也各有两个顺序，不能把“其余一维”套在整个有序空间上。

与 §23.4 的 Fock 算子比较，令 $\mathcal H_2=\operatorname{Sym}^2\mathbb C^5$ 使用该节归一化占位基，并定义等距嵌入 $J_2:\mathcal H_2\to\mathcal H\otimes\mathcal H$：

$$
J_2|2e_s\rangle=|s,s\rangle,\qquad
J_2|e_s+e_t\rangle=\frac{|s,t\rangle+|t,s\rangle}{\sqrt2}\quad(s\ne t).
$$

其像是 $\mathsf S=+1$ 的扇区。对于该节的 $B=a_0^\dagger a_{13}^\dagger a_1a_3$，两个湮灭与两个产生的系数在唯一可动基 $|e_1+e_3\rangle$ 上均为一，因此

$$
BJ_2^\dagger\frac{|1,3\rangle+|3,1\rangle}{\sqrt2}
=|e_0+e_{13}\rangle,
\qquad J_2^\dagger A J_2=B|_{\mathcal H_2},
$$

$$
J_2^\dagger VJ_2=(B+B^\dagger)|_{\mathcal H_2}.
$$

最后两式也在其余基向量上成立，因为两边均消去它们。§23 的正算子则是

$$
\widehat H_2=(n_1n_3+n_0n_{13})|_{\mathcal H_2}
-(B+B^\dagger)|_{\mathcal H_2}.
$$

在这唯一活动二维对称块内它为 $I-\sigma_x$，不是 $\sigma_x$：既有对角项，又有相反的交换符号。反对称向量 $|s,t\rangle_-=(|s,t\rangle-|t,s\rangle)/\sqrt2$ 还满足 $A|1,3\rangle_-=|0,13\rangle_-$，所以有序 $V$ 在反对称活动块也有一次 $\sigma_x$，这部分没有包含在 $J_2$ 中。以上是明示子空间上的算子比较，不是把可区分的两个系统宣告成物理玻色子。证毕。

### 24.4 独立同态准备后的精确双系统概率律

**定理 24.5（负相位约定下的有限交换）。** 设初态为两次独立准备的 $|\psi\rangle\otimes|\psi\rangle$，并令

$$
U(u)=e^{-iuV},\qquad u\in\mathbb R,
\qquad a=\psi_0\psi_{13},\quad b=\psi_1\psi_3,
\qquad \Delta=|a|^2-|b|^2=p_0p_{13}-p_1p_3.
$$

两个约化态相同；它们在标签基中的概率均为

$$
p'=p+\delta\kappa\,d,\qquad
\delta\kappa=-\Delta\sin^2u+\operatorname{Im}(\overline a b)\sin2u.
$$

当四底角概率均正时，等价写为

$$
\delta\kappa=-\bigl((1-Z)\kappa-XY\bigr)\sin^2u
+R\sin\chi\sin2u.
$$

所有 $u$ 都精确保留每个边缘的 $X,Y,Z$；归一化和非负性成立，包括零振幅边界。

证明。每个活动块上 $V^2=I$，故指数是 $I\cos u-iV\sin u$。初始两块的振幅列均为 $(a,b)^{\mathsf T}$，所以两块分别变成

$$
a'=a\cos u-ib\sin u,\qquad b'=b\cos u-ia\sin u.
$$

其余二十一个有序基振幅不变。这一陈述针对振幅；活动项与非活动项之间的密度矩阵交叉元一般会变化，不能据此说所有其他联合矩阵元不变。直接展开得到

$$
\begin{aligned}
|a'|^2&=|a|^2\cos^2u+|b|^2\sin^2u
+2\cos u\sin u\,\operatorname{Im}(\overline a b),\\
|b'|^2&=|b|^2\cos^2u+|a|^2\sin^2u
-2\cos u\sin u\,\operatorname{Im}(\overline a b).
\end{aligned}
$$

例如第一式的交叉项为 $2\operatorname{Re}(-i\overline a b)\cos u\sin u$，其符号是正的虚部。负相位约定给

$$
\overline a b=\overline M=Re^{i\chi},\qquad
\operatorname{Im}(\overline a b)=R\sin\chi.
$$

第一边缘的 $p_0$ 只有列 $(0,13)$ 的概率变化，增加 $|a'|^2-|a|^2$；$p_{13}$ 从 $(13,0)$ 增加同样的量。$p_1,p_3$ 分别从 $(1,3),(3,1)$ 减少此量，$p_2$ 不动。这正是所述 $d$ 方向，没有因两个有序块而再给单个边缘乘二。初态及 $U$ 都与系统交换相容，终态保持交换对称，故两边缘相同；也可逐列作同样求和得到第二边缘的式子。

将定义 24.1 的概率反演代入，

$$
\begin{aligned}
\Delta&=\kappa(1-X-Y-Z+\kappa)-(X-\kappa)(Y-\kappa)\\
&=(1-Z)\kappa-XY.
\end{aligned}
$$

由 $Wd=0$，更新保持质量及三个均值。更直接地，$U$ 幺正，联合密度态正且迹一，偏迹仍正且迹一，所以每个 $p_s'$ 非负，$\kappa'$ 仍在同一可行闭区间。使用 $\operatorname{Im}(\overline a b)$ 的式子不需要相位存在，故包含所有边界。证毕。

任意双系统输入都因 $[U,Q_a]=0$ 保持总占位；每个边缘各自保持则在本定理中使用了相同准备与交换对称性。对任意不对称输入，不能从总量保持推出两边各自保持。

### 24.5 相同概率的不同响应、关系读出与乘积边界

**命题 24.6（关系相位的响应与两个荷相容读数）。** 对初始均匀概率 $p_s=1/5$，有 $\Delta=0$、$R=1/25$。若 $\chi=0$，定理 24.5 给所有 $u$ 的 $\kappa'=1/5$；若 $\chi=\pi/2$，则

$$
\kappa'=\frac15+\frac1{25}\sin2u.
$$

两份准备的完整经典概率相同，有限交换响应却可不同。定义 Hermitian 算子

$$
O_c=A+A^\dagger=V,\qquad O_s=-i(A-A^\dagger).
$$

二者都与每个 $Q_a$ 交换。在实际初始乘积 $|\psi\rangle^{\otimes2}$ 上，

$$
\langle O_c\rangle=4R\cos\chi,\qquad
\langle O_s\rangle=4R\sin\chi.
$$

已知 $R>0$ 时，这两个期望确定 $\chi\bmod2\pi$。在 $V$ 运动下，$O_c$ 是动力学常量，$O_s$ 一般不是。

证明。均匀律有 $p_0p_{13}=p_1p_3=1/25$，故直接代入精确概率律得到两种响应。例如取其他角全零、$\theta_{13}=\pi/2$ 可实现第二种准备；$u=\pi/4$ 时两种 $\kappa'$ 分别为 $1/5$ 和 $6/25$。

对任意实际乘积输入，两个有序矩阵单位各贡献 $\overline a b$，所以

$$
\langle A\rangle=2\overline a b=2Re^{i\chi}.
$$

取实部与虚部给两个因子为四的期望。$[Q_a,A]=0$ 及伴随关系证明两读数都与荷相容。令

$$
P_a=AA^\dagger=|0,13\rangle\langle0,13|+|13,0\rangle\langle13,0|,
$$

$$
P_b=A^\dagger A=|1,3\rangle\langle1,3|+|3,1\rangle\langle3,1|.
$$

由于 $A^2=(A^\dagger)^2=0$，

$$
[V,O_c]=0,\qquad [V,O_s]=2i(P_a-P_b)\ne0.
$$

在参数 $u$ 下，Heisenberg 期望导数为 $d\langle O_s\rangle/du=i\langle[V,O_s]\rangle=-2\langle P_a-P_b\rangle$，初始值为 $-4\Delta$。因此与占位荷交换不等于沿交换运动保持。两象限读数本身也不对易；相位重构指分别在相同准备的样本上取得两个期望，并非一次同时尖锐测得它们。证毕。

单系统上若一个读出效果 $E$ 与 $N_x,N_y,N_z$ 全交换，则对 $s\ne t$ 选一个区分 $v_s,v_t$ 的占位，有 $(a_s-a_t)E_{st}=0$，从而 $E$ 对角。其期望只有 $\sum_sE_{ss}p_s$，不能区别上述同概率的两种相位。这一限制属于没有另供相位或荷参照、且读出效果保持这三个占位对称性的接口；它不排除另供参照后的单系统相干读出，也不是一般测量样本复杂度下界。$R=0$ 时两个乘积期望均为零，不能由它们识别一个本来就未定义的四角相位。

**命题 24.7（四次 Hamilton 函数的初始联系及边缘混合）。** 对常数 $g$，取双系统 Hamiltonian $H_2=gV$，从相同独立纯准备开始，令 $u=g\tau$。则

$$
\frac12\langle\psi\otimes\psi|H_2|\psi\otimes\psi\rangle
=2gR\cos\chi,
\qquad
\left.\frac{d\kappa'}{d\tau}\right|_{\tau=0}=2gR\sin\chi.
$$

这分别等于[《辛预测完成》命题 35.9](SYMPLECTIC_PREDICTIVE_COMPLETION.md#359-四次相互作用与同均值概率交换)的 $H_{\rm int}$ 及其初始 $\dot\kappa$，其中 $g_0=g$，同一 $\psi_s=\sqrt{p_s}e^{-i\theta_s}$，同一 $R$、$\chi$ 和辛尺度。它不意味着精确双系统演化始终沿该纯态非线性乘积轨道。

证明。命题 24.6 给 $\langle H_2\rangle=4gR\cos\chi$，除以系统数二即得第一式。定理 24.5 中 $\sin^2u$ 在零点导数为零，$\sin2u$ 导数为二，链式法则给第二式。已有纯态 Hamilton 方程按 $\Omega_{\rm red}=d\chi\wedge d\kappa$ 为 $\dot\kappa=-\partial_\chi H_{\rm int}=2gR\sin\chi$，故符号和因子一致。

乘积不闭合可由一个精确输入看出。取 $|\psi\rangle=(|0\rangle+|13\rangle)/\sqrt2$，在 $u=\pi/2$ 时联合态为

$$
|\Psi'\rangle=\frac12\bigl(|0,0\rangle+|13,13\rangle
-i|1,3\rangle-i|3,1\rangle\bigr).
$$

四项的第二系统标签两两不同，故偏迹消去全部交叉项，得到

$$
\rho_1'=\rho_2'
=\frac14\bigl(|0\rangle\langle0|+|1\rangle\langle1|
+|3\rangle\langle3|+|13\rangle\langle13|\bigr).
$$

它有四个特征值 $1/4$ 和一个零特征值，不是纯态；联合纯态也不是两个边缘的乘积。概率坐标仍满足定理 24.5，但不能给这个混合边缘任意填回一组纯态角，再继续冒充原联合幺正轨迹。证毕。

对于已独立供应两份同态输入的准备族，可定义边缘更新

$$
\mathcal F_u(\rho)=\operatorname{Tr}_2\bigl(U(u)(\rho\otimes\rho)U(u)^\dagger\bigr).
$$

这是对输入 $\rho$ 的非线性使用，不是一个未知单系统上的固定 CPTP 通道。例如在 $u=\pi/2$，$\rho_0=|0\rangle\langle0|$ 与 $\rho_{13}=|13\rangle\langle13|$ 各自固定，而 $\rho=(\rho_0+\rho_{13})/2$ 的乘积输入含两个活动对角格，各质量 $1/4$；更新后 $p_{13}'=1/4$，不同于 $\bigl(\mathcal F_u(\rho_0)+\mathcal F_u(\rho_{13})\bigr)/2$ 的 $p_{13}=1/2$。非仿射性来自另供第二份同态准备；它没有违反定义 24.2 所消费的单系统刚性，也没有构造克隆过程。上述载体与算子均为所声明的数学模型，不供给原生读者端口或器件实现。

### 24.6 对角输入、舍弃联合态与独立重配对

**定理 24.8（明确重配对合同下的仿射松弛）。** 令 $\rho_p=\sum_sp_s|s\rangle\langle s|$。每轮先独立准备 $\rho_p\otimes\rho_p$，执行 $U(\pi/2)$，保留其一个边缘作为下一轮的概率规格，舍弃原联合态及其配对记录；下一轮重新独立准备该边缘律的两份输入。则固定均值纤维上的轮间更新为

$$
\kappa'=\kappa-\Delta=Z\kappa+XY,\qquad
\Delta=(1-Z)\kappa-XY.
$$

若 $0\le Z<1$，令 $\kappa_*=XY/(1-Z)$，则

$$
\Delta'=Z\Delta,\qquad
\kappa_n-\kappa_*=Z^n(\kappa_0-\kappa_*).
$$

$Z=0$ 时一步到固定点；$0<Z<1$ 时该仿射映射在其像上可逆。$Z=1$ 时唯一可行律是 $p_2=1$，$X=Y=\kappa=0$，不使用含 $1-Z$ 分母的公式。

证明。对角乘积输入在每个活动块的两格质量为 $|a|^2=p_0p_{13}$ 和 $|b|^2=p_1p_3$，没有非对角干涉项。$U(\pi/2)=-i\sigma_x$ 在块内交换这两格，在块外恒等；故联合输出仍对角，第一边缘的 $0,13$ 各增加 $p_1p_3-p_0p_{13}=-\Delta$，$1,3$ 各减少该量，$2$ 不变。第二边缘相同。代入 $\Delta=(1-Z)\kappa-XY$ 即得仿射式。

固定点在可行区间内可由一份完整概率构造证明。记 $q=1-Z>0$，因 $0\le X,Y\le q$，取

$$
\begin{aligned}
p_0^*&=\frac{(q-X)(q-Y)}q,&
p_1^*&=\frac{X(q-Y)}q,\\
p_3^*&=\frac{(q-X)Y}q,&
p_{13}^*&=\frac{XY}q,&p_2^*&=Z.
\end{aligned}
$$

这些数非负，四底角总和为 $q$，均值恰为 $X,Y$。条件于非中位的底面后，低、高占位是参数 $X/q,Y/q$ 的两个独立 Bernoulli 变量。由此 $\kappa_*$ 合法，并且

$$
\kappa'=Z\kappa+(1-Z)\kappa_*
$$

是两个可行纤维点的凸组合，故每轮仍合法。相减得到 $\kappa'-\kappa_*=Z(\kappa-\kappa_*)$，迭代归纳给第 $n$ 轮公式，再乘 $1-Z$ 给 $\Delta'=Z\Delta$。

若 $Z=0$，首轮已是 $\kappa_*$，以后不动。若 $0<Z<1$，斜率为正，且在更新像中

$$
\kappa=\frac{\kappa'-XY}{Z}.
$$

所以纤维距离收缩不等于这个一维映射不可逆；它一般不是映满原可行区间的自同构。若 $Z=1$，其他四个概率因非负及归一化全为零，给所列唯一点和恒等更新。证毕。

这里被舍弃的是联合信息，下一轮的独立性是新准备条件。一般联合输出 $\rho_{12}'$ 不等于 $\rho_p'\otimes\rho_p'$；直接再用同一对系统作第二次 $U(\pi/2)$ 会返回原对角联合律，因为两个交换相继还原格位置，而不是再应用上述收缩。故 $Z^n$ 的衰减不是闭合幺正双系统的衰减，也不是无代价地把两个相关输出宣布为独立。中模式没有被 $V$ 交换，但其质量 $Z$ 通过 $\Delta$ 的纤维斜率决定这份重配对合同的收缩因子。此合同中的新准备资源不属于定理 24.3 的无储库闭合交换段。

### 24.7 校准相位速度、阶数区别与局域参数不变性

**定理 24.9（对角相位漂移与交换相容条件）。** 给定实五标签函数 $f$，令

$$
F=\operatorname{diag}(f_0,f_1,f_2,f_3,f_{13}),\qquad
D_f=F\otimes I+I\otimes F,\qquad
J_f=f_0-f_1-f_3+f_{13}.
$$

若 $f_s$ 是一段已校准局域参数 $\tau$ 上的相位速度，则单系统纯对角演化取 $\dot\theta_s=f_s$。已有[辛完成命题 35.8](SYMPLECTIC_PREDICTIVE_COMPLETION.md#358-同一目标缺口的相位读法)在本标签下给

$$
\frac{d}{d\kappa}\mathbb E_{p_\kappa}f=J_f,\qquad \dot\chi=J_f.
$$

它的具体消费为

$$
\mathbb E_{p_\kappa}f=f_0+(f_1-f_0)X+(f_3-f_0)Y+(f_2-f_0)Z+J_f\kappa,
$$

以及 $\dot\theta_0-\dot\theta_1-\dot\theta_3+\dot\theta_{13}=J_f$。在双系统上对应的交换子为

$$
[D_f,A]=J_fA,\qquad [D_f,A^\dagger]=-J_fA^\dagger,
\qquad [D_f,V]=J_f(A-A^\dagger).
$$

因此 $D_f$ 与 $V$ 交换恰当且仅当 $J_f=0$。

证明。$D_f$ 在 $|s,t\rangle$ 上的特征值为 $f_s+f_t$。$A$ 的每个矩阵单位都从特征值 $f_1+f_3$ 送到 $f_0+f_{13}$，差为 $J_f$，给第一式；取伴随并用 $D_f$ 自伴给第二式；相加得第三式。$A-A^\dagger$ 在活动块不为零，所以最后的充要条件成立。静态导数则由已给仿射反演精确消费，需在固定 $X,Y,Z$ 下取。证毕。

例如 $f=(0,2,3,5,7)$ 有 $J_f=0$，但逐标签平方 $f^2=(0,4,9,25,49)$ 有 $J_{f^2}=20$。这分别是既有数量均值 $2X+5Y+3Z$ 与平方矩 $4X+25Y+9Z+20\kappa$ 的相位对应。因此守住一阶数量关系不自动守住逐系统平方数量之和。

逐系统平方和必须与总量的平方区别：

$$
D_{f^2}=F^2\otimes I+I\otimes F^2,\qquad
(D_f)^2=D_{f^2}+2F\otimes F.
$$

若 $[D_f,V]=0$，则对每个整数 $j\ge0$ 都有 $[(D_f)^j,V]=0$，由逐次移过乘积即可证明。上例的两端数量列表是 $(0,7)$ 和 $(2,5)$，总量都为七，总量平方都为四十九；逐系统平方和却分别为四十九、二十九，交叉项分别为零、二十。故 $J_{f^2}=20$ 不表示一个守恒总量的平方遭破坏。

**定理 24.10（固定交换段的积分钟与重参数化）。** 给同一双系统、同一实际配对、指定的局域参数区间 $[\tau_0,\tau_1]$ 及固定算子 $V$。设 $g$ 为该区间上的实可积函数，Hamiltonian 为 $H(\tau)=g(\tau)V$，定义

$$
u(\tau)=\int_{\tau_0}^{\tau}g(s)\,ds,\qquad
U(\tau,\tau_0)=e^{-iu(\tau)V}.
$$

这里的 $u$ 就是定理 24.5 的交换参数。若 $\widetilde\tau=h(\tau)$ 是严格递增的 $C^1$ 重参数化，$h'>0$，并令

$$
\widetilde g(h(\tau))=\frac{g(\tau)}{h'(\tau)},
$$

则相应积分、传播算子及每个给定事件的概率不变。

证明。任意两时刻 $[g(s)V,g(t)V]=0$，$u$ 绝对连续且 $\dot u=g$ 几乎处处。有限维矩阵指数链式法则给 $\dot U=-ig(\tau)VU$ 几乎处处及 $U(\tau_0,\tau_0)=I$，所以它解该积分形式的 Schrödinger 方程。也可将任意另一解左乘 $e^{iu V}$，导数为零，得相同解。

对同一端点作变量代换，

$$
\int_{h(\tau_0)}^{h(\tau)}\widetilde g(t)\,dt
=\int_{\tau_0}^{\tau}\frac{g(s)}{h'(s)}h'(s)\,ds
=\int_{\tau_0}^{\tau}g(s)\,ds.
$$

故两种坐标给同一个 $U$。对于固定联合初态 $\rho_{12}$ 和事件效果 $0\le E\le I$，其概率

$$
\operatorname{tr}\bigl(EU\rho_{12}U^\dagger\bigr)
$$

完全相同。这里不需要乘积输入；乘积假设只用于前面的显式边缘公式。证毕。

这一积分钟结论要求运动方向是固定的 $V$。若实际 Hamiltonian 还含 $D_f+g(\tau)V$，则不能直接丢去 $D_f$。当 $J_f=0$ 时两部分交换，常 $f$ 的传播子才可分为 $e^{-i(\tau-\tau_0)D_f}e^{-iu V}$；若 $J_f\ne0$，相互作用绘景中的交换为

$$
e^{itD_f}Ae^{-itD_f}=e^{itJ_f}A,\qquad
V_I(t)=e^{itJ_f}A+e^{-itJ_f}A^\dagger,
$$

方向随 $t$ 变动，不能继续套用裸的 $e^{-iu V}$。即使 $g$ 常数而总 Hamiltonian 为常矩阵，也应指数化整个 $D_f+gV$，不能将不对易的两项拆开。一般时变 $f$ 的同一重参数化必须同时令 $\widetilde f_s(h(\tau))=f_s(\tau)/h'(\tau)$，从而整体 $\widetilde H(h(\tau))=H(\tau)/h'(\tau)$；只改 $g$ 而保留未变换的相位速度不是同一历史。

局域参数在本定义中标记一个已经配对、校准的相互作用段及其实际事件。$h$ 只重标这段历史，保留联合准备、端点和事件对应；它不提供远处系统间的瞬时耦合，不建立全局公共时钟，也不替代因果传播条件。负的 $g$ 或变号的 $g$ 允许 $u$ 倒行或回转，所以“积分钟”指累计交换参数，不额外声称它严格单调。

### 24.8 任意长度合法路径、整数 trade 与严格交换成本

**定义 24.11（关系矩、整数直方图及无储库合同）。** 给整数 $n\ge1$，令

$$
\Gamma_n=\{I\subseteq[n]:\text{不存在 }j\text{ 使 }j,j+1\in I\}.
$$

它是包含空集的向下闭合集族。对概率律 $(p_I)_{I\in\Gamma_n}$，定义

$$
\mu_S=\sum_{I\in\Gamma_n,\ I\supseteq S}p_I,\qquad \mu_\varnothing=1.
$$

非法 $S$ 的矩恒为零。两个相同长度的合法标签列表具有整数直方图差 $c=(c_I)_{I\in\Gamma_n}$；约定正系数为输出增加，负系数为输入减少。固定整数 $r\ge0$，保持直到 $r$ 阶指

$$
\sum_{I\in\Gamma_n,\ I\supseteq S}c_I=0
\quad\text{对所有 }S\subseteq[n],\ |S|\le r.
$$

其中 $S=\varnothing$ 就是质量条件。定义取消共同副本后的体积

$$
m(c)=\sum_I(c_I)_+=\sum_I(-c_I)_+
=\frac12\|c\|_1,\qquad (a)_+=\max(a,0).
$$

系数允许任意整数，所以同一合法标签可在列表中重复；排列变化和共同旁观副本均不增加 $m(c)$。

严格算子合同是在 $m$ 个可区分系统的空间 $(\mathbb C^{\Gamma_n})^{\otimes m}$ 上，使用关系投影与总荷

$$
N_S=\sum_{I\supseteq S}|I\rangle\langle I|,\qquad
Q_S^{(m)}=\sum_{j=1}^mN_S^{(j)}.
$$

没有外部储库、额外标签或另一个未计入的自由度抵偿荷。所讨论的 Hamiltonian 或幺正算子须与每个指定 $Q_S^{(m)}$ 交换。因此其每个非零有序矩阵元连接的两个列表具有相同的这些总荷；证明是定理 24.3 的矩阵元交换子式，将 $a_I$ 换成 $\mathbf1_{S\subseteq I}$。这才把整数直方图条件接到全输入的严格加和守恒；仅有某个输入的总期望相等不足以调用它，也不在此把它推广为任意 CPTP 期望保持通道的分类。

数学引文与相位对应。[辛完成定义 35.12、命题 35.13](SYMPLECTIC_PREDICTIVE_COMPLETION.md#3513-长路径关系矩与共轭差分相位)使用同一 $\Gamma_n$、同一矩 $\mu_S$ 及负相位 $\psi_I=\sqrt{p_I}e^{-i\theta_I}$，供应

$$
p_I=\sum_{T\in\Gamma_n,\ T\supseteq I}(-1)^{|T|-|I|}\mu_T,
\qquad
D_T(I)=(-1)^{|T|-|I|}\mathbf1_{I\subseteq T},
$$

$$
\Phi_T=\sum_{I\subseteq T}(-1)^{|T|-|I|}\theta_I,
\qquad
\theta_I=\sum_{T\subseteq I}\Phi_T\pmod{2\pi}.
$$

这里 $D_T$ 是第 $T$ 个矩坐标的反演列；正逆整数三角矩阵均对角为一，所以相位变换在完整周期环面互逆。以射影直线面积 $2\pi$ 和 $\iota_{X_H}\Omega=dH$ 为同一尺度，直接代入得到

$$
\lambda=\sum_Ip_I\,d\theta_I=\sum_T\mu_T\,d\Phi_T,
\qquad
\Omega=\sum_{\varnothing\ne T\in\Gamma_n}d\Phi_T\wedge d\mu_T.
$$

共同相位只对应 $\Phi_\varnothing$，其矩 $\mu_\varnothing=1$ 已归一化。在全正概率图上，固定合法低阶矩后，仍须除去相应的非空低阶相位平移，才得到高阶 $(\mu_T,\Phi_T)$ 的辛配对。该引用不把整个 $\Gamma_n$ 当成 Boolean 格；它使用的是每个合法 $T$ 的全体子集构成的 Boolean 区间。

**定理 24.12（FIB 支撑上的锐最小交换体积）。** 在定义 24.11 的整数合同中，若 $c\ne0$ 保持直到 $r$ 阶，则

$$
\|c\|_1\ge2^{r+1},\qquad m(c)\ge2^r.
$$

存在这样的非零 $c$ 当且仅当 $r<\lceil n/2\rceil$；在此范围内下界可达到。若 $r\ge\lceil n/2\rceil$，不存在非零合法直方图交换。

证明。先在任意有限坐标集 $E$ 的整个 Boolean 立方体上证明整数界：设 $c:2^E\to\mathbb Z$ 非零，且对所有 $|S|\le r$ 有 $\sum_{I\supseteq S}c_I=0$。对 $r$ 归纳，命题同时量化所有有限 $E$。

当 $r=0$，总和为零且 $c$ 非零，必有一个正整数系数和一个负整数系数。因此正质量、负质量各至少一，$\|c\|_1\ge2$。若 $E$ 为空，此前提本就不可能成立，不需添一个例外解。

现设 $r\ge1$，并已知所有坐标集上的 $r-1$ 阶结论。质量零保证支撑至少含两个不同集合 $I_0,I_1$，选一个区分它们的坐标 $j\in I_0\mathbin\triangle I_1$。在 $E'=E\setminus\{j\}$ 上定义两片

$$
c^{(0)}_B=c_B,\qquad c^{(1)}_B=c_{B\cup\{j\}},\qquad B\subseteq E'.
$$

所选两个非零支撑分处两片，所以每片都是非零整数函数。对任何 $S\subseteq E'$、$|S|\le r-1$，有

$$
\sum_{B\supseteq S}c^{(1)}_B
=\sum_{I\supseteq S\cup\{j\}}c_I=0,
$$

$$
\sum_{B\supseteq S}c^{(0)}_B
=\sum_{I\supseteq S}c_I-
\sum_{I\supseteq S\cup\{j\}}c_I=0.
$$

第一式使用 $|S\cup\{j\}|\le r$，第二式再使用原来的 $S$ 矩。故两片各满足归纳前提，各自 $\ell^1$ 范数至少 $2^r$。两片分割全部系数，得到

$$
\|c\|_1=\|c^{(0)}\|_1+\|c^{(1)}\|_1\ge2^{r+1}.
$$

这个证明不假定切片仍是某个路径的独立集族。回到 FIB 情形，将每个非法字 $I\notin\Gamma_n$ 的系数明确延拓为零。合法 $S$ 的矩条件就是原条件；非法 $S$ 不可能包含于任何合法 $I$，所以其矩也是零。于是整个 Boolean 立方体满足刚证明的假设，范数不变，整数界随即成立。整数性不能删掉：实数倍缩小一个非零方向会任意缩小范数。

为证明达到，令 $r<\lceil n/2\rceil$，取合法集合

$$
T=\{1,3,\ldots,2r+1\},\qquad |T|=r+1.
$$

这个范围保证 $2r+1\le n$；其所有子集均合法。使用已有 Möbius 反演列 $D_T$，对任意 $S\subseteq[n]$，若 $S\not\subseteq T$ 则其 $S$ 矩为零；若 $S\subseteq T$，则

$$
\begin{aligned}
\sum_{I\supseteq S}D_T(I)
&=\sum_{S\subseteq I\subseteq T}(-1)^{|T|-|I|}\\
&=(-1)^{|T|-|S|}\sum_{J\subseteq T\setminus S}(-1)^{|J|}
=\begin{cases}1,&S=T,\\0,&S\ne T.\end{cases}
\end{aligned}
$$

末式在 $S\ne T$ 时由任取 $j\in T\setminus S$、配对 $J$ 与 $J\mathbin\triangle\{j\}$ 消去得到。因此全部 $|S|\le r$ 的矩为零。任取 $j\in T$，在 $T$ 的子集中切换 $j$ 会翻转 $D_T$ 的符号，故正负各有 $2^r$ 个系数，每个绝对值一，得到 $m(D_T)=2^r$。

最后，合法集合最大阶数为 $\alpha=\lceil n/2\rceil$：把路径按相邻两点分组，每组至多选一点，奇数长度再容许末点，给上界；奇数位置集合达到该界。若 $r\ge\alpha$，则所有合法矩，包括质量，全都固定。将原反演应用于有符号数组，写 $m_S(c)=\sum_{I\supseteq S}c_I$，便有

$$
c_I=\sum_{T\supseteq I}(-1)^{|T|-|I|}m_T(c)=0.
$$

所以非零 $c$ 不存在，完成充要条件。证毕。

本定理中使用的整个 Boolean 立方体整数下界是既有 $[t]$-trade 结果。[Ghorbani–Kamali–Khosrovshahi–Krotov，On the volumes and affine types of trades，arXiv:1810.02296v2](https://arxiv.org/abs/1810.02296v2) 的 §2.1 将 trade 写成整数函数 $\sum_X\tau_XX$，正负系数分别为两侧块的重数，并要求式 (2) 的 $\sum_{X\supseteq S}\tau_X=0$。精确对应为 $E=V_{\rm lit}$、$c_I=\tau_I$、$r=t$、$m(c)=\operatorname{vol}(T_{\rm lit})$。原文 §3 的 Lemma 3 陈述 unitrade 的界并紧接说明 trade 同界；Lemma 4 明述非空 $[t]$-trade 的最小体积 $2^t$ 及极小结构。整数权重、重复块和一般体积界均不是这里新增的扩展。上述归纳作为当前守恒成本推导中的完整中间证明，另将非法字零延拓、合法 $T$ 的达到构造和路径最大阶数接到本章的算子合同。

### 24.9 单独一个高阶矩的交换及显式达到算子

**定理 24.13（孤立关系矩的唯一方向与有序实现）。** 固定合法 $T\in\Gamma_n$，$k=|T|\ge2$。若整数直方图差 $c\ne0$ 保持所有其他合法矩，包括质量，并且只允许 $\mu_T$ 改变，则存在唯一非零整数 $a$ 使

$$
c=aD_T,\qquad m(c)=|a|2^{k-1}.
$$

最小体积 $2^{k-1}$ 可由 $m=2^{k-1}$ 个可区分系统上的一个显式 Hermitian 矩阵实现，并严格保持所有 $S\ne T$ 的总关系荷。

证明。设 $m_S(c)=0$ 对每个合法 $S\ne T$ 成立，令 $a=m_T(c)$。矩是整数系数的和，故 $a\in\mathbb Z$。消费定义 24.11 的 Möbius 反演得到

$$
c_I=\sum_{S\supseteq I}(-1)^{|S|-|I|}m_S(c)
=a(-1)^{|T|-|I|}\mathbf1_{I\subseteq T}=aD_T(I).
$$

若 $a=0$ 则所有 $c_I=0$，矛盾；反演也给唯一性。定理 24.12 证明中的矩计算表明 $m_S(D_T)=\mathbf1_{S=T}$，因而 $D_T$ 确实保持所有其他矩，不仅仅保持比 $k$ 小的那些矩。切换一个 $T$ 内坐标给正负各 $2^{k-1}$ 项，故体积公式成立。

为具体达到，按任意固定顺序列出 $D_T=+1$ 的全部子集 $I_1^+,\ldots,I_m^+$，以及 $D_T=-1$ 的全部子集 $I_1^-,\ldots,I_m^-$，定义两个有序正交标签态

$$
|\mathbf I_+\rangle=|I_1^+,\ldots,I_m^+\rangle,\qquad
|\mathbf I_-\rangle=|I_1^-,\ldots,I_m^-\rangle,
$$

$$
A_T=|\mathbf I_+\rangle\langle\mathbf I_-|,\qquad
H_T=A_T+A_T^\dagger.
$$

两个列表没有共同标签；其直方图差恰为 $D_T$。对任意合法 $S$，对应总荷本征值之差为

$$
q_S(\mathbf I_+)-q_S(\mathbf I_-)
=\sum_{I\supseteq S}D_T(I)=\mathbf1_{S=T}.
$$

故

$$
[Q_S^{(m)},A_T]=\mathbf1_{S=T}A_T,\qquad
[Q_S^{(m)},H_T]=0\quad(S\ne T).
$$

$S=T$ 时交换子为 $A_T-A_T^\dagger\ne0$，所以算子确有改变该目标的能力。在这两个列表张成的二维空间，$H_T=\sigma_x$；在正交补上为零，因而

$$
e^{-iuH_T}|\mathbf I_-\rangle
=\cos u\,|\mathbf I_-\rangle-i\sin u\,|\mathbf I_+\rangle.
$$

初态为确定的负侧列表时，目标总矩期望增加 $\sin^2u$，其他总矩严格不变；在 $u=\pi/2$ 完全交换到正侧列表。这直接实现了体积下界，不需要储库，也不要求每个系统采用相同的输入态。整数 $a>0$ 可把每个侧标签重复 $a$ 次作同一构造；$a<0$ 则互换两侧，给一般体积的实现。证毕。

**命题 24.14（三阶实例及相位单项式的精确方向）。** 在包含 $T=\{1,3,5\}$ 的合法路径上，四对四交换

$$
\{\varnothing,13,15,35\}\longleftrightarrow\{1,3,5,135\}
$$

保持全部二阶及以下矩，只改变三阶矩 $\mu_{135}$；实际上它保持所有其他合法矩。一般 $k$ 阶方向 $D_T$ 的相位单项式为

$$
M_T=\prod_{D_T(I)=+1}\psi_I
\prod_{D_T(I)=-1}\overline{\psi_I}.
$$

若这些振幅均非零，则 $\arg M_T=-\Phi_T$；其总次数为 $2^k$，正振幅及共轭振幅的因子数各为 $2^{k-1}$。

证明。当 $k=3$，$D_T$ 在单点和三点子集上为正，在空集和二点子集上为负，因此上式从左到右的直方图差正是 $D_T$。两侧质量都是四；每个 $T$ 内坐标在两侧各出现两次，每个二点集在两侧各出现一次，其他位置和二点关系出现零次。三点关系左侧零次、右侧一次。全部其他更高阶或不同关系也不变，这是 $m_S(D_T)=\mathbf1_{S=T}$ 的完整计算，不是仅检查三个一阶均值。

例如按显示顺序选择 $|\mathbf I_-\rangle=|\varnothing,13,15,35\rangle$、$|\mathbf I_+\rangle=|1,3,5,135\rangle$，定理 24.13 的 $A_T$ 就是这两个明确有序四系统态之间的矩阵单位，给上述交换的无储库实现。

在非零支撑上乘入负相位表达式，

$$
M_T=\left(\prod_{I\subseteq T}\sqrt{p_I}\right)
\exp\left(-i\sum_{I\subseteq T}D_T(I)\theta_I\right)
=\left(\prod_{I\subseteq T}\sqrt{p_I}\right)e^{-i\Phi_T}.
$$

全部 $2^k$ 个子集各贡献一个因子，正负各半，给次数与等长副本数。共同相位因两侧因子数相同而抵消。更一般地，在 $\theta_I\mapsto\theta_I+\sum_S t_S\mathbf1_{S\subseteq I}$ 下，$\Phi_T$ 只增加 $t_T$，因为 $m_S(D_T)=\mathbf1_{S=T}$；因此保持所有其他关系的相位作用也保持此单项式。若有零振幅，仍使用这个多项式，其辐角不再定义。证毕。

若额外独立准备 $m$ 份相同的 $|\psi\rangle$，单个有序矩阵单位的期望是

$$
\langle\psi^{\otimes m}|A_T|\psi^{\otimes m}\rangle
=\overline{\prod_{D_T(I)=+1}\psi_I}
\prod_{D_T(I)=-1}\psi_I=\overline{M_T},
$$

$$
\langle H_T\rangle=2\operatorname{Re}M_T.
$$

没有自动多出来的第二个有序方向。$T=\{1,3\}$ 时 $M_T=M$，而定理 24.3 的 $A$ 还特意加入交换系统后的第二项，所以其期望是 $2\overline M$，$V$ 的期望为 $4\operatorname{Re}M$；这解释了两种公式的因子差。相同准备只用于这一相位期望式，达到交换下界的确定列表准备不需要它。次数和体积衡量的是所声明的多系统关系交换，不能据此宣称一般相位估计必需同样多的样本。

### 24.10 九位路径的关系维数与三种最小体积

**命题 24.15（九位合法支撑中的独立方向和实际约化）。** 对 $n=9$ 的路径，合法集合总数为八十九，按阶数 $k=0,1,2,3,4,5$ 分别为

$$
1,\quad9,\quad28,\quad35,\quad15,\quad1.
$$

固定质量、一阶和二阶关系后，有五十一个独立实概率方向；在含全正律的层上再作对应的辛商，得到五十一个概率—相位对。只要求保持这些低阶矩的非零交换最小体积为四；若单独改变一个三阶、四阶或五阶矩而保持所有其他矩，则最小体积分别为四、八、十六。

证明。已有路径计数通过 $i_1<\cdots<i_k$、$i_{j+1}\ge i_j+2$ 到 $i_j-(j-1)$ 的双射，将合法 $k$ 元集对应为 $[n-k+1]$ 的普通 $k$ 元集；逆式是加回 $j-1$，所以数目为 $\binom{n-k+1}{k}$。在 $n=9$ 代入得

$$
\binom{10}{0}=1,\quad\binom91=9,\quad\binom82=28,
\quad\binom73=35,\quad\binom64=15,\quad\binom55=1,
$$

总和八十九。依定义 24.11 的可逆矩变换，全部八十九个矩坐标在未归一化实数组空间中独立，固定的 $1+9+28=38$ 行亦独立；其核维数为 $89-38=51$。更明确地，核的基为全部 $|T|\ge3$ 的 $D_T$，因为任意核向量的反演只含这些列，而它们的矩像是互不相同的单位坐标。

相位侧精确消费辛完成命题 35.13：全部正振幅射线实维 $2(89-1)=176$；质量对应的共同相位已经除去，另有 $9+28=37$ 个非空低阶矩。固定它们减去三十七维，再商去其自由周期相位作用减去三十七维，得到

$$
176-37-37=102=2\cdot51,
\qquad
\Omega_{\rm red}=\sum_{|T|\ge3}d\Phi_T\wedge d\mu_T.
$$

在这个正部分层内，高阶矩的可行域由逆概率全部严格正的不等式给出；它是包含给定全正点的开域，故五十一个方向确为局部概率自由度。边界支撑可能降维，不沿用此正层结论。

由定理 24.12 取 $r=2<5$，一般低阶保持交换的锐下界为 $2^2=4$，可选 $T=\{1,3,5\}$ 达到。若要求孤立某个给定高阶矩，定理 24.13 则逐个给

$$
\begin{array}{c|c|c}
\text{孤立目标阶数}&\text{合法目标数}&\text{每侧最小变化副本数}\\\hline
3&35&4\\
4&15&8\\
5&1&16
\end{array}
$$

唯一五阶目标是 $T=\{1,3,5,7,9\}$。它的三十二个子集按 $D_T$ 的符号分成两侧各十六项，定理 24.13 的有序矩阵单位恰实现该十六对十六交换，同时保持其余八十八个矩，包括全部三阶、四阶矩。若只规定一二阶不变、允许其他高阶矩联动，则不能把“孤立五阶”的十六当作那一较弱问题的下界。证毕。

这里的五十一个方向属于概率纤维的线性坐标，也在真正的辛商后各配一个角；它们不是五十一个基配置的身份列表。保留哪一个联合配对、怎样准备输入、是否舍弃相关性，以及用哪段局域历史标记算子，始终是不同的数学条件。五标签回路、已有 Schur 刚性和辛矩坐标在本章通过明示映射被消费；新增的双系统精确律、重配对公式和有序多系统构造只在各自给定条件内连接这些对象，不给出硬件、因果传播或全局时间的实现结论。

## 追加锚（本行以下为增补区）
