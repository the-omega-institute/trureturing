# 续篇：把 AURIC FIB ATOM 金字塔提升为“边界—纤维—闭合”理论

**Reference input: open.** 本卷完整保存用户供文，包括全部声明、证明、例子、表格、项目对应说明和拟议接口。原文的“定理”“已经证明”“正式冻结”等语言均属开放参考输入；本卷未新增 Lean、Blueprint、Reg 或 Frozen 声明。Lean 声明、证明项及其内核核验的公理闭包承载本库形式系统内的数学真值。

**来源。** Author kind: mixed user-supplied material; original author and model unknown. Receipt date: 2026-10-10. 来源标识为本会话供文 auric-fib-atom-boundary-transport-fibers-and-loop-closure。接收原文 SHA-256 为 `8e72ef09c22cb4c26b590669b8f27fc5c5373c8eff8e735f1f3374a5a85ae9f0`，原始字节数为 29024。全部原句及公式内容保留，只规范 Markdown 数学入口与标题层级，声明地址仅用于本文定位。按用户指定，本卷是纯理论添加，不运行消化，不新增 atom 或覆盖主张。

**既有结果与历史归属。** 原文关于 dev、#15044 和 README 的最新状态判断归属其供文引用的历史提交与阅读，不认证交付时移动分支的状态。图关联矩阵核、运输表 square move、最大熵独立补全和树状概率缝合属于既有数学方法；本卷不将这些方法或重述计作原创。对应参考包括 [Foundational Formulas](AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)、[Correlation and Native Continuation](AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md)、[Output-Resolved Instrument Closure](AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md) 与 [Local Fillings, Soft to Rigid and Odd-Cycle Obstructions](AURIC_FIB_ATOM_PYRAMID_LOCAL_FILLINGS_SOFT_TO_RIGID_AND_ODD_CYCLE_OBSTRUCTIONS.md)。本文没有证明这些对象与共同生成器工程或物理系统之间的 native 实现桥。

## 编者限定与开放义务

以下限定与完整供文分开；它们不替代原句，不认证原文定理。

- **Q1（§§2、11）：** E-V+c 是固定支持图上边缘映射核的线性维数。实际非负运输纤维还可能为空、退化或落在较低维面上；存在在全部允许边上严格正的可行流时，才直接取得该核维数。一般应在实际可行纤维的有效支持上计算维数。五态仿射隐藏方向为一维，不表示每个 kappa 区间都长于零，也不自动给出恒定维数的拓扑纤维丛。
- **Q2（§§2–3）：** 有向关联矩阵在左右边缘使用相反符号；固定正边缘与固定带符号边界通过该约定对应。所有支持边统一从左向右时，没有实际的有向闭环；这里的“环流”是允许正负分量的零边界环空间方向。kappa 是一个内部边坐标，其相对规范的变化才沿该方向。Markov 基元的整数统计意义与任意实数可行增量应分别量化。
- **Q3（§§3–4、12、接口 C）：** Q 是未归一化的底面质量表，条件律为 Q/r，独立、条件熵最大和 kappa_0 的等价式要求 r=1-Z>0，并固定合法的边缘。r=0 时条件事件零概率，相关条件律及除法未定义。将最大熵与 transfer 可逆性联系时还需 Z>0；Z=0 时无论 Delta 是否为零，T 都不可逆。退化边缘的独立规范仍可唯一，但没有可变隐藏纤维。
- **Q4（§§4–5、12）：** T 是局部联合质量矩阵，不是已经指定的 Markov 转移核；其行和是左边界边缘。正行上条件核需按行边缘归一化，零行另定。矩阵可逆性只刻画该线性映射的输入方向，不证明隐参数可取得、完整输出记录可辨识或 native future law 可恢复。transfer rank 只区分秩层，不能在同秩层中恢复 kappa 数值；完整未来观察仍需逐输出 instrument 与目标探针。J_f=0 的必要性若限定在单个固定纤维，要求纤维有至少两个可行点；全体概率律上的判据另行量化。
- **Q5（§6）：** 路径基空间还要求各 (X_i,Y_i,Z_i) 属于局部金字塔、L 是正整数，并有同一带标号路径上的归一化非负局部律。原归纳式的随机变量索引应整体后移一位：下一窗口为 Pr(x_(i+1)=b,x_(i+2)=c,x_(i+3)=d)=q_(i+1)(b,c,d)，公共状态来自窗口 i 的后两位。零质量公共状态上的任意条件转移只在不可达状态上使用。
- **Q6（§§6、11–12）：** 乘积 I_1×...×I_L 描述可实现的局部律集合在固定一阶边界上的纤维；全局联合律本身还可有不由局部三元边缘决定的更高阶自由度。树状延拓需要明确窗口/因子系统的 junction-tree 或 running-intersection 条件；仅称原冲突图为树或覆盖超图为树不足以略去这些条件。
- **Q7（§7、接口 F）：** 周期词长度与周期窗口数须一致，简单环域取 n=L>=3；Gamma 包含归一化和所有指定三元边缘的线性约束。对非负质量矩阵，零迹说明指定顺序的支持中没有闭合轨迹；正迹只说明存在支持轨迹。按原文行向量的时间约定，一般按时间顺序乘 T_1...T_L；C5 示例各矩阵相同，反向书写不改变该示例，不能据此交换一般矩阵。迹不是给定全部边缘质量的可行性判据。
- **Q8（§§5、9、12）：** 用 S 的方差恢复 kappa 仍需共同概率律上的 X,Y,Z 等已知边缘；方差一个读数不能独立恢复全部五态概率。Delta 数值在 r>0 且边界已知时可恢复 kappa，transfer rank 一个离散标签不能替代 Delta。静态局部律、动态取得历史和边界菜单的最小性不能直接相乘。
- **Q9（§8）：** 几何 tau 的变化会改变壁面可行性和冲突边，未证明它保持某个几何一阶边界读数。它与零边界 kappa 变形的表格是研究类比；要取得严格共同结构须明确对象、观察、操作及保持量的对应。冲突图和左右边界运输图是不同图，不能凭共同词“边界”或“环路”互换。
- **Q10（§9）：** 动态无穷状态结论限于同一次抽样、共同固定深度先验、同一合法取得合同和实际可达历史。乘法可识别性须明确：对两个实际不同计数的差，支持中至少一对正概率深度的似然比非一；r_k,s_k 和后验比的分母为正。计数无界不单独证明 future laws 互异。原定理另假设完整未来律分离不同后验，这仍是必须核验的桥梁；近似有限生成器与全部历史精确有限摘要是不同目标。
- **Q11（§§10–13）：** 共同生成器、complete-law flow 和有限原子化与本运输模型的对应尚需参数映射和共同实现证据。“曲率”“体”及 holonomy 名称不认证微分几何或物理意义。loop-coupling 非空是全局实现的定义性判据；取得可计算证书、复杂度界及 Lean 接口仍为拟议工作。

## 完整供文

这一轮不再重复方锥本身的基本证明，而是继续向更深一层推进：

> AURIC FIB ATOM 金字塔的真正本体不是一个三维图形，而是一个由“局部运输图”产生的纤维化对象。  
>   
> 金字塔坐标描述可见的一阶边界；$\kappa$ 描述内部运输图中的环路流；$\Delta$ 描述该环路流是否破坏条件独立；transfer matrix 的秩描述这些隐藏关系是否还能被未来延拓恢复；开放路径可以缝合，闭环还必须通过 holonomy 检验。

这会把几件此前分开的事情统一起来：

$$
\boxed{
\text{AURIC 金字塔}=
\text{边界投影}
+
\text{运输纤维}
+
\text{环路闭合}.
}
$$

当前项目的 `dev` 分支在上一轮的 `b40c4b1` 之后已经继续合并了 #15044，最新相关提交的主题是“用有限共同生成器实现相容的 complete-law flows”。 这与下面的结构高度对应：项目正在从单个局部律、单个预测器，推进到带有共同边界、共同流和有限实现的整体系统。

相关源文件：

- [AURIC FIB ATOM foundational formulas](https://github.com/the-omega-institute/trureturing/blob/dev/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)
- [AURIC FIB ATOM correlation and native continuation](https://github.com/the-omega-institute/trureturing/blob/dev/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md)
- [AURIC FIB ATOM hidden relations, statistics, phase and seams](https://github.com/the-omega-institute/trureturing/blob/dev/docs/develop/theory/AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md)
- [AURIC FIB ATOM dynamic future quotient](https://github.com/the-omega-institute/trureturing/blob/dev/docs/develop/theory/AURIC_FIB_ATOM_DYNAMIC_FUTURE_QUOTIENT_AND_FUTURE_CLOSED_MEMORY.md)
- [latest merged compatible-flow commit](https://github.com/the-omega-institute/trureturing/commit/6ebcd08fd122ed8c588c56090d0c07a8046e1685)

项目 README 仍然把“定义、假设、证明依赖和观察边界”视为核心方法，并明确区分局部一致与全局可延拓，强调树状覆盖与带环覆盖必须分开处理。[GitHub](https://github.com/the-omega-institute/trureturing?utm_source=chatgpt.com)

---

## 1. 一、固定五态和三维投影

仍然使用固定记号：

$$
F[\mathrm{null}]=\mathrm{null},
$$

$$
F[1]=[2],
$$

$$
F[2]=[3],
$$

$$
F[3]=[5],
$$

$$
F[1,3]=[2,5].
$$

占位变量仍为：

- $x$：位置 $1$，即数值 $2$；
- $y$：位置 $3$，即数值 $5$；
- $z$：位置 $2$，即数值 $3$。

印刷位序为：

$$
(x,z,y).
$$

合法性为：

$$
xz=0,
\qquad
yz=0.
$$

五个合法模式是：

$$
000,\qquad100,\qquad010,\qquad001,\qquad101.
$$

概率律写成：

$$
p=(p_0,p_1,p_2,p_3,p_{13}),
$$

其中顺序对应：

$$
F[\mathrm{null}],F[1],F[2],F[3],F[1,3].
$$

金字塔坐标为：

$$
X=p_1+p_{13},
\qquad
Y=p_3+p_{13},
\qquad
Z=p_2.
$$

隐藏联合坐标为：

$$
\kappa=p_{13}.
$$

完整反解为：

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

金字塔为：

$$
\mathcal P=
\left\{
(X,Y,Z):
X,Y,Z\ge0,\;
X+Z\le1,\;
Y+Z\le1
\right\}.
$$

此前已经证明：

$$
\max(0,X+Y+Z-1)
\le
\kappa
\le
\min(X,Y).
$$

接下来要解释这个区间为什么必然是一条“运输环路纤维”。

---

## 2. 二、隐藏纤维不是抽象参数，而是一个运输图上的环流

### 定义 1：AURIC 局部运输图

把一个合法三元组：

$$
(a,b,c)
$$

看成从左边界二元状态 $(a,b)$ 到右边界二元状态 $(b,c)$ 的一条有向边。

左、右边界状态都取：

$$
\mathcal S_2=\{00,10,01\}.
$$

五个合法三元组对应五条边：

| 三元组 | 左边界 | 右边界 |
|---|---|---|
| $000$ | $00$ | $00$ |
| $100$ | $10$ | $00$ |
| $010$ | $01$ | $10$ |
| $001$ | $00$ | $01$ |
| $101$ | $10$ | $01$ |

因此 AURIC 局部律可以看成这个二部图上的边流：

$$
q=(q_{000},q_{100},q_{010},q_{001},q_{101}).
$$

在五态概率记号中：

$$
q_{000}=p_0,
\qquad
q_{100}=p_1,
\qquad
q_{010}=p_2,
\qquad
q_{001}=p_3,
\qquad
q_{101}=p_{13}.
$$

左边界边缘由 $(X,Z)$ 决定：

$$
\ell=(1-X-Z,\;X,\;Z).
$$

右边界边缘由 $(Y,Z)$ 决定：

$$
r=(1-Y-Z,\;Z,\;Y).
$$

所以：

- $(X,Y,Z)$ 是运输流的左右边界；
- $p$ 是运输图内部的边流；
- $\kappa$ 是内部环路流强度。

---

### theorem 2.1: 定理 1：隐藏纤维维数等于运输图的环路数

设一个有限二部支持图有：

- $E$ 条边；
- $V$ 个顶点；
- $c$ 个连通分支。

固定所有左右节点边缘后，运输流的线性自由度维数为：

$$
\boxed{
g=E-V+c.
}
$$

这个 $g$ 就是图的 cyclomatic number，也就是独立环路数。

#### 证明

给每条边规定从左节点指向右节点的方向。边流向节点边缘的线性映射由有向关联矩阵：

$$
A:\mathbb R^E\to\mathbb R^V.
$$

两个流 $q,q'$ 具有相同左右边界，当且仅当：

$$
A(q-q')=0.
$$

因此同一边界下的差异空间就是：

$$
\ker A.
$$

对一个有 $c$ 个连通分支的图，有向关联矩阵的秩为：

$$
\operatorname{rank}(A)=V-c.
$$

由秩—零度定理：

$$
\dim\ker A=
E-(V-c)=
E-V+c.
$$

正性约束只会把这个线性空间截成一个多面体，不会增加维数。

证毕。

---

### 应用于 AURIC 五态

AURIC 运输图有：

$$
E=5,
\qquad
V=6,
\qquad
c=2.
$$

所以：

$$
g=5-6+2=1.
$$

这正好解释了为什么三维金字塔投影的隐藏自由度只有一维：

$$
\boxed{
\dim(\text{隐藏纤维})=1.
}
$$

这个一维方向就是：

$$
h=(1,-1,0,-1,1).
$$

即：

$$
(p_0,p_1,p_2,p_3,p_{13})
\mapsto
(p_0,p_1,p_2,p_3,p_{13})
+t(1,-1,0,-1,1).
$$

在三元组边流语言中，这表示：

$$
000-100-001+101.
$$

它是一个零边界环流：

- 对每个左边界节点，流入流出变化相抵；
- 对每个右边界节点，流入流出变化也相抵；
- 但内部边流发生了变化。

这就是：

$$
\nu_0+\nu_{13}=
\nu_1+\nu_3
$$

的流图版本。

---

### 重要结论：AURIC 的“体”是一个环流，而不是额外的坐标轴

因此，$\kappa$ 不应被理解成一个与 $X,Y,Z$ 对称的第四个普通坐标。

更准确地说：

- $X,Y,Z$ 是边界可见的节点边缘；
- $\kappa$ 是内部运输环路上的流量；
- $\kappa$ 不改变边界；
- $\kappa$ 只改变内部如何实现相同边界。

这就是“边界相同、内部不同”的严格数学形式。

---

## 3. 三、$\kappa$ 是 $2\times2$ 运输方块上的 Markov 基元

在中间原子为空的条件 $z=0$ 下，只剩下四个端点模式：

$$
F[\mathrm{null}],\quad F[1],\quad F[3],\quad F[1,3].
$$

对应的二维联合表为：

$$
Q=
\begin{pmatrix}
p_0&p_3\\
p_1&p_{13}
\end{pmatrix}.
$$

行边缘为：

$$
(r-X,X),
$$

列边缘为：

$$
(r-Y,Y),
$$

其中：

$$
r=1-Z.
$$

保持行列边缘不变的标准 $2\times2$ 运输变形是：

$$
Q
\mapsto
Q+t
\begin{pmatrix}
1&-1\\
-1&1
\end{pmatrix}.
$$

这正是：

$$
(p_0,p_1,p_3,p_{13})
\mapsto
(p_0,p_1,p_3,p_{13})
+t(1,-1,-1,1).
$$

所以 AURIC 中的隐藏纤维就是代数统计中的 square move，也就是 $2\times2$ 列联表的唯一 Markov 基元。

---

### theorem 3.1: 定理 2：独立截面是唯一的最大熵截面

设：

$$
r>0.
$$

在固定 $(X,Y,Z)$ 的所有端点联合分布中，唯一满足：

$$
\Delta=0
$$

的分布为：

$$
\boxed{
\kappa_0=\frac{XY}{r}.
}
$$

它同时是条件熵最大的分布。

#### 证明

归一化底面联合表：

$$
\widetilde Q=\frac{Q}{r}.
$$

它的行边缘和列边缘固定。设其行边缘为 $u$，列边缘为 $v$。信息论恒等式为：

$$
D_{\mathrm{KL}}(\widetilde Q\Vert u\otimes v)=
H(u)+H(v)-H(\widetilde Q).
$$

因为 KL 散度非负：

$$
H(\widetilde Q)
\le
H(u)+H(v).
$$

等号当且仅当：

$$
\widetilde Q=u\otimes v.
$$

这就是条件独立分布。

其共同占用概率为：

$$
\frac{\kappa}{r}=
\frac{X}{r}\frac{Y}{r}.
$$

因此：

$$
\kappa=\frac{XY}{r}.
$$

同时：

$$
\Delta=r\kappa-XY=0.
$$

证毕。

---

### 解释

$\kappa_0$ 可以看作一个“独立规范”或“最大熵规范”：

$$
\kappa=\kappa_0+\xi.
$$

其中：

$$
\xi=\kappa-\frac{XY}{r}.
$$

于是：

$$
\Delta=r\xi.
$$

因此：

- $\xi=0$：选择最大熵、条件独立的内部实现；
- $\xi>0$：端点共同出现超过独立基线；
- $\xi<0$：端点共同出现低于独立基线。

但这里的“规范”只是数学选择，不代表真实来源一定条件独立。

---

## 4. 四、Transfer matrix 的秩：隐藏相关何时能被未来恢复

将边界状态顺序固定为：

$$
(00,10,01).
$$

由三元组概率构造 transfer matrix：

$$
T(\kappa)=
\begin{pmatrix}
p_0&0&p_3\\
p_1&0&p_{13}\\
0&p_2&0
\end{pmatrix}.
$$

其中：

- 第 $i$ 行是左边界状态；
- 第 $j$ 列是右边界状态；
- 每个非零元素是一条局部合法转移的质量。

将 $\kappa$ 的变化写成矩阵变化：

$$
T(\kappa)=T(0)+\kappa H,
$$

其中：

$$
H=
\begin{pmatrix}
1&0&-1\\
-1&0&1\\
0&0&0
\end{pmatrix}.
$$

它可以写成秩一形式：

$$
H=uv^{\mathsf T},
$$

其中：

$$
u=
\begin{pmatrix}
1\\-1\\0
\end{pmatrix},
\qquad
v=
\begin{pmatrix}
1\\0\\-1
\end{pmatrix}.
$$

并且：

$$
H\mathbf 1=0,
\qquad
\mathbf 1^{\mathsf T}H=0.
$$

这说明改变 $\kappa$ 不改变左右边界总流。

---

### theorem 4.1: 定理 3：transfer determinant 由 $\Delta$ 完全控制

$$
\boxed{
\det T(\kappa)=
-Z\Delta.
}
$$

#### 证明

直接展开：

$$
\begin{aligned}
\det T
&=
p_0(0\cdot0-p_{13}p_2)
+
p_3(p_1p_2-0)\\
&=
-p_0p_{13}p_2+p_1p_3p_2\\
&=
-p_2(p_0p_{13}-p_1p_3).
\end{aligned}
$$

由于：

$$
p_2=Z,
\qquad
p_0p_{13}-p_1p_3=\Delta,
$$

所以：

$$
\det T=-Z\Delta.
$$

证毕。

---

### 推论：最大熵局部填充恰好导致 transfer rank collapse

当：

$$
Z>0,
$$

有：

$$
T\text{ 可逆}
\iff
\Delta\neq0.
$$

而最大熵截面满足：

$$
\Delta=0.
$$

因此：

$$
\boxed{
\text{最大熵局部填充}
\Longrightarrow
\text{transfer matrix 降秩}.
}
$$

这揭示了一个非常深的关系：

> 局部最大熵意味着端点相关被消除；端点相关被消除以后，局部 continuation 的一个方向也丢失了。

相反：

$$
\Delta\neq0
$$

时，transfer matrix 在线性代数意义下恢复可逆性。

必须加一个限制：

- $T^{-1}$ 存在，不代表 $T^{-1}$ 仍然是概率矩阵；
- 这里的“可逆”只是线性 transfer 的可逆；
- 它不是物理时间的可逆，也不是随机过程的可逆。

因此，可以把 $\Delta$ 理解为：

$$
\boxed{
\text{局部关联}
\longleftrightarrow
\text{未来延拓中的可恢复方向}.
}
$$

---

## 5. 五、哪些观测能看见 $\kappa$

### theorem 5.1: 定理 4：一阶金字塔可观测量的完全判据

设 $f$ 是五个模式上的任意实函数，记：

$$
f_0=f(F[\mathrm{null}]),
$$

$$
f_1=f(F[1]),
\qquad
f_2=f(F[2]),
\qquad
f_3=f(F[3]),
\qquad
f_{13}=f(F[1,3]).
$$

定义四点差分：

$$
J_f=f_{13}-f_1-f_3+f_0.
$$

则：

$$
\boxed{
\mathbb E_p[f]=
f_0
+(f_1-f_0)X
+(f_3-f_0)Y
+(f_2-f_0)Z
+J_f\kappa.
}
$$

因此：

$$
\boxed{
\mathbb E_p[f]\text{ 仅由 }(X,Y,Z)\text{ 决定}
\iff
J_f=0.
}
$$

#### 证明

直接将：

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
p_{13}=\kappa
$$

代入：

$$
\mathbb E_p[f]=
p_0f_0+p_1f_1+p_2f_2+p_3f_3+p_{13}f_{13}.
$$

整理 $\kappa$ 项即可。

如果 $J_f=0$，$\kappa$ 消失，故一阶坐标足够。

如果 $J_f\neq0$，只要纤维宽度 $w_\kappa>0$，改变 $\kappa$ 就改变期望，所以一阶坐标不足。

证毕。

---

### 5.1 FIB 加法权重天然看不见 $\kappa$

定义原子加法权重：

$$
S=2x+3z+5y.
$$

其五个模式值是：

$$
0,\quad2,\quad3,\quad5,\quad7.
$$

因为：

$$
0+7=2+5,
$$

所以：

$$
J_S=7-2-5+0=0.
$$

因此：

$$
\boxed{
\mathbb E[S]=2X+3Z+5Y.
}
$$

这说明 FIB 的加法读出天然只看见金字塔的一阶位置，而看不见端点联合填充。

但是二阶加法读出会看到 $\kappa$。

由于：

$$
x^2=x,
\qquad
y^2=y,
\qquad
z^2=z,
\qquad
xz=yz=0,
$$

有：

$$
S^2=
4x+9z+25y+20xy.
$$

于是：

$$
\boxed{
\mathbb E[S^2]=
4X+9Z+25Y+20\kappa.
}
$$

所以：

- 平均 FIB 数值看不见 $\kappa$；
- FIB 数值的方差能看见 $\kappa$；
- $\kappa$ 是平均填充不变、波动结构改变的方向。

这与先前的 $\Delta$ 完全一致：$\Delta$ 是中心化后的端点联合信息。

---

### 5.2 一个最小的隐藏关系读口

定义状态函数：

$$
\chi=z+xy.
$$

五个模式上：

| 模式 | $\chi$ |
|---|---:|
| $F[\mathrm{null}]$ | $0$ |
| $F[1]$ | $0$ |
| $F[2]$ | $1$ |
| $F[3]$ | $0$ |
| $F[1,3]$ | $1$ |

其期望为：

$$
\mathsf W=
\mathbb E[\chi]=
Z+\kappa.
$$

因此：

$$
\boxed{
\kappa=\mathsf W-Z.
}
$$

于是给定：

$$
(X,Y,Z,\mathsf W)
$$

就能唯一恢复完整五态概率律：

$$
p_0=1-X-Y-Z+\mathsf W-Z,
$$

$$
p_1=X-\mathsf W+Z,
$$

$$
p_2=Z,
$$

$$
p_3=Y-\mathsf W+Z,
$$

$$
p_{13}=\mathsf W-Z.
$$

这里的关键不是 $\chi$ 这个名字，而是：

> 三个边界均值加一个联合敏感读口，恰好补上运输图唯一的环流自由度。

这与项目当前动态文档中提出的：

$$
\chi=z+xy,
\qquad
\mathbb E[\chi]=Z+\kappa
$$

相吻合。但必须区分：

- $\kappa$ 是单个局部窗口的静态联合坐标；
- 动态 future quotient 中的 phase、$A$、$B$ 是历史计数与未来律状态；
- $(X,Y,Z,\mathsf W)$ 能恢复一个局部概率律，不等于能恢复完整历史。

---

## 6. 六、开放路径：所有局部 $\kappa_i$ 都可以被缝合

设有 $L$ 个连续窗口，每个窗口有局部概率律：

$$
q_i(a,b,c),
\qquad
1\le i\le L.
$$

定义窗口 $i$ 的右边界：

$$
\mu_i(b,c)=
\sum_a q_i(a,b,c).
$$

定义窗口 $i+1$ 的左边界：

$$
\mu_i'(b,c)=
\sum_d q_{i+1}(b,c,d).
$$

局部缝合条件为：

$$
\mu_i(b,c)=\mu_i'(b,c).
$$

在 AURIC 坐标中，这等价于：

$$
Z_i=X_{i+1},
\qquad
Y_i=Z_{i+1}.
$$

定义路径基空间：

$$
\mathcal B_L=
\left\{
((X_i,Y_i,Z_i))_{i=1}^L:
Z_i=X_{i+1},\;
Y_i=Z_{i+1}
\right\}.
$$

每一个局部窗口还拥有自己的区间纤维：

$$
\kappa_i\in I_i=
\left[
\max(0,X_i+Y_i+Z_i-1),
\;
\min(X_i,Y_i)
\right].
$$

---

### theorem 6.1: 定理 5：开放路径的纤维化延拓

对于一条开放路径，只要基空间边界条件相容，则任意选择：

$$
\kappa_i\in I_i
$$

都可以构造一个全局合法概率分布，使其三元窗口边缘等于给定的 $q_i$。

#### 证明

从第一个窗口 $q_1$ 开始采样。

若当前公共边界为 $(b,c)$，定义：

$$
K_i(d\mid b,c)=
\frac{q_{i+1}(b,c,d)}
{\mu_i(b,c)}
$$

当：

$$
\mu_i(b,c)>0.
$$

当 $\mu_i(b,c)=0$ 时，该状态不会被访问，转移可以任意定义。

由边缘一致性：

$$
\sum_d K_i(d\mid b,c)=1.
$$

因此可以递归生成全局词：

$$
x_1,x_2,\ldots,x_{L+2}.
$$

每个局部三元组都属于：

$$
\{000,100,010,001,101\},
$$

所以不会出现相邻的 $11$。

归纳地，假设窗口 $i$ 的边缘为 $q_i$，则下一窗口的边缘为：

$$
\begin{aligned}
\Pr(x_i=b,x_{i+1}=c,x_{i+2}=d)
&=
\mu_i(b,c)K_i(d\mid b,c)\\
&=
q_{i+1}(b,c,d).
\end{aligned}
$$

因此所有窗口边缘都被实现。

证毕。

---

### 这一定理的几何含义

开放路径的总空间可以写成：

$$
\mathcal E_L
\longrightarrow
\mathcal B_L,
$$

其典型纤维为：

$$
\prod_{i=1}^{L} I_i.
$$

所以开放路径上：

- 横向坐标控制边界接缝；
- 纵向坐标 $\kappa_i$ 控制每个局部运输环路；
- 没有额外的全局拓扑障碍；
- 所有局部隐藏关系都可以沿树状结构独立选择后再缝合。

这正是项目 README 中树扩展定理在 AURIC 五态窗口上的具体化。

---

## 7. 七、闭环：局部相容不再足够

把路径首尾连接成周期环后，局部边缘一致仍然只是必要条件。

定义全局环路耦合多面体：

$$
\Gamma_L(q_1,\ldots,q_L)
$$

为所有满足以下条件的非负分布 $\gamma$ 的集合：

1. $\gamma$ 支持在合法周期词上；
2. 每个局部三元窗口边缘等于 $q_i$；
3. 最后一窗口和第一窗口也满足周期接缝。

于是：

$$
\Gamma_L\neq\varnothing
$$

才等价于存在全局周期延拓。

---

### theorem 7.1: 定理 6：环路闭合的分层判据

对于周期窗口系统，必须分两层检查：

### 第一层：水平边界可行性

基础占用率必须属于全局独立集边缘多面体：

$$
(X_1,\ldots,X_n)
\in
\operatorname{STAB}(C_n).
$$

如果不属于，则无论如何选择 $\kappa_i$，都不能实现全局分布。

### 第二层：垂直联合闭合

即使所有一阶占用率都属于全局边缘多面体，仍需检查：

$$
\Gamma_L(q_1,\ldots,q_L)\neq\varnothing.
$$

#### 证明

设 $G_n$ 是所有合法周期硬词的集合。任意全局概率律都是这些硬词指示向量的凸组合，因此其一阶边缘必属于：

$$
\operatorname{STAB}(C_n).
$$

所以如果基础点不在稳定集凸包中，则不存在任何全局分布。

反过来，如果一阶点属于稳定集凸包，则它可以由周期独立集的混合得到，但这只保证存在某个全局分布，不保证给定的局部 $\kappa_i$ 正好与该分布一致。

因此：

- $(X_i,Y_i,Z_i)$ 检查水平投影；
- $\kappa_i$ 和 $\Gamma_L$ 检查内部联合结构。

证毕。

---

### 7.1 C5 奇环反例的 transfer 版本

令每个窗口：

$$
q_i=
\frac12\delta_{101}
+
\frac12\delta_{010}.
$$

其 pair-state transfer 只在 $10$ 与 $01$ 之间交换：

$$
T_i=
\frac12
\begin{pmatrix}
0&0&0\\
0&0&1\\
0&1&0
\end{pmatrix}.
$$

限制在 $\{10,01\}$ 上，它就是：

$$
\frac12
\begin{pmatrix}
0&1\\
1&0
\end{pmatrix}.
$$

绕五次以后仍然是交换矩阵，所以：

$$
\operatorname{tr}(T_5T_4T_3T_2T_1)=0.
$$

因此不存在闭合的硬轨迹，也不存在具有这些局部窗口边缘的全局 C5 分布。

这与独立集数界一致：

$$
\mathbb E[\text{总占用}]=
5\cdot\frac12=
\frac52,
$$

但：

$$
\alpha(C_5)=2.
$$

所以：

$$
\frac52>2.
$$

这里必须谨慎：

- 若 transfer product 的迹为零，则没有任何闭合支持轨迹，这是强有力的不可能证书；
- 迹为正只能说明存在一个闭合支持轨迹，未必自动保证给定全部边缘质量的 $\Gamma_L$ 非空。

因此，$\operatorname{tr}$ 是闭合支持的快速证书，不是所有概率边缘约束的完整替代。

---

## 8. 八、几何软到刚与 AURIC 纤维的精确类比

`soft-to-rigid` 中，形状族为：

$$
S_{\gamma,\tau}=
\gamma\left[(1-\tau)P\oplus\tau\rho D\right].
$$

当 $\tau$ 减小时，形状变大，冲突边增加，合法独立集族收缩。

AURIC 中，固定 $(X,Y,Z)$ 后：

$$
\kappa\in[\kappa_-,\kappa_+]
$$

改变的是内部运输，而不是外部边界。

因此两者的共同结构是：

$$
\boxed{
\text{内部变形}
\quad
\text{不改变某类一阶边界}
\quad
\text{但改变二阶或延拓性质}.
}
$$

具体对应如下：

| 几何软到刚 | AURIC FIB ATOM |
|---|---|
| $\tau$ 改变形状内部几何 | $\kappa$ 改变局部内部运输 |
| 墙面约束是外部边界 | $(X,Y,Z)$ 是边界边缘 |
| 重叠边构成冲突图 | 三元组边构成运输图 |
| 形状膨胀增加冲突边 | $\kappa$ 沿零边界环流变化 |
| 合法独立集是刚性填充 | 全局硬词是刚性填充 |
| 局部数值残差不保证全局可行 | 局部边缘一致不保证环路闭合 |

但不能把：

$$
\tau=\kappa
$$

或：

$$
\tau=Z
$$

作为数学等式。它们属于两个不同模型中的参数，只是在“边界不可见的内部自由度”这一结构层面相似。

---

## 9. 九、与当前动态 future quotient 的关系

当前参考文档进一步把静态隐藏坐标接到动态历史上。它提出的一个重要区分是：

- 静态窗口律的隐藏量是 $\kappa$；
- 动态未来律的状态还需要 phase、$A$、$B$ 等历史计数；
- future law 的最小摘要不一定是一个有限状态，而可能是无界计数的有限维坐标。

可以把动态状态写成：

$$
\sigma(h)=
\bigl(a(h),A_h,B_h\bigr).
$$

如果隐藏深度为 $K$，某段历史的似然比例具有形式：

$$
\mu(k)\,r_k^{A_h}s_k^{B_h}.
$$

两个深度 $i,j$ 的后验比为：

$$
\frac{\nu_h(i)}{\nu_h(j)}=
\frac{\mu(i)}{\mu(j)}
\left(\frac{r_i}{r_j}\right)^{A_h}
\left(\frac{s_i}{s_j}\right)^{B_h}.
$$

---

### theorem 9.1: 定理 7：动态未来律的无穷状态障碍

假设：

1. 先验至少支持两个不同隐藏深度；
2. 不同深度的 $(r_k,s_k)$ 具有乘法可识别性；
3. 存在无限多个具有相同 phase、但 $(A_h,B_h)$ 不同的合法历史；
4. 完整 future law 能区分不同后验。

则 future-law 等价类是无限多个，因此不存在有限状态摘要精确表示全部未来律。

#### 证明

若两段历史 $h,h'$ 具有不同计数，则至少存在一对深度 $i,j$，使：

$$
\frac{\nu_h(i)}{\nu_h(j)}
\neq
\frac{\nu_{h'}(i)}{\nu_{h'}(j)}.
$$

所以：

$$
\nu_h\neq\nu_{h'}.
$$

由假设 4，后验不同会导致某个完整未来事件的概率不同，因此：

$$
\mathscr L_h\neq\mathscr L_{h'}.
$$

由于存在无限多个不同的 $(A_h,B_h)$，就存在无限多个不同的 future laws。

如果有限状态摘要存在，则由鸽巢原理，两段不同历史必须落入同一状态；这会要求它们具有相同 future law，产生矛盾。

证毕。

---

### 静态 $\kappa$ 与动态 $(A,B)$ 的关系

因此，完整的观察者状态可能具有分层形式：

$$
\boxed{
\text{局部律}=
(X,Y,Z,\kappa)
}
$$

而动态未来状态则近似为：

$$
\boxed{
\text{动态律}=
(X,Y,Z,\kappa,\mathrm{phase},A,B,\mathrm{boundary\ domain}).
}
$$

但不能机械地把这些坐标全部拼接为“最小状态”。最小性取决于目标：

- 如果目标只预测平均加法权重，$\kappa$ 可以丢弃；
- 如果目标预测 $S^2$，$\kappa$ 必须保留；
- 如果目标预测局部 transfer 的逆向恢复，$\Delta$ 必须保留；
- 如果目标预测动态 future law，phase、$A$、$B$ 可能也必须保留；
- 如果处于 pending 或 delivered 边界，允许的未来操作集合本身发生变化。

所以：

$$
\boxed{
\text{预测充分性}
\neq
\text{状态可维护性}
\neq
\text{历史可恢复性}.
}
$$

这也是当前项目强调 boundary domain、pending、delivered、return compatibility 的原因。

---

## 10. 十、最新项目进展如何改变 AURIC 的研究方向

当前 `dev` 最新合并的 compatible-flow 工作，核心不是再增加一个静态公式，而是解决：

> 一组相容的、可能是无限或非原子分布的未来律，能否被有限共同生成器近似或实现？

这与 AURIC 的新结构有直接对应：

| 项目最新方向 | AURIC 对应结构 |
|---|---|
| complete-law flow | 局部窗口之间的边流或概率流 |
| common marginals | 相邻窗口的共享 separator 边缘 |
| finite common generator | 有限状态 transfer / 有限兼容图 |
| barycentric approximation | 金字塔内部点的凸分解 |
| residual compatibility | $\kappa$、$\Delta$ 与后续 continuation 的相容性 |
| finite atomicity | 有限个硬填充或有限个局部律原子 |
| exact attainment vs tolerance | 精确闭合与近似闭合的区别 |

这说明项目的研究重心正在从：

$$
\text{“一个点代表什么？”}
$$

推进到：

$$
\text{“一族局部律能否由共同流和有限装置同时实现？”}
$$

这正是 AURIC 金字塔下一阶段最值得形式化的方向。

---

## 11. 十一、一个更强的统一定理

前面的结果可以压缩为下面的“边界—纤维—闭合定理”。

### theorem 11.1: 定理 8：AURIC 边界—纤维—闭合分层定理

对任意有限 AURIC 窗口网络，存在三层判据：

### 第一层：局部边界合法性

每个窗口的边界坐标必须属于其局部金字塔：

$$
(X_i,Y_i,Z_i)\in\mathcal P.
$$

### 第二层：内部运输纤维

在固定边界后，内部概率律的自由度由支持运输图的环路数决定：

$$
\dim\mathcal F_i=
E_i-V_i+c_i.
$$

对三原子 AURIC 窗口：

$$
\dim\mathcal F_i=1,
\qquad
\mathcal F_i\cong[\kappa_{i,-},\kappa_{i,+}].
$$

### 第三层：全局闭合

- 若窗口覆盖的超图是树或开放路径，则 separator 边缘一致足以全局延拓；
- 若窗口覆盖形成环，则还必须存在全局 loop-coupling $\Gamma$；
- 奇环可能在第一阶投影上已经失败；
- 即使第一阶投影成功，$\kappa_i$ 仍可能在第二层闭合失败。

#### 证明

第一层来自局部合法模式的凸包表示。

第二层由运输图边缘映射的核维数定理给出：

$$
\dim\ker\partial=E-V+c.
$$

第三层在开放路径上由 Markov 缝合构造；在环路上，局部律必须来自某个周期全局分布，因此必须属于 loop-coupling 多面体。若其支持 transfer product 没有闭合轨迹，则该多面体为空。

证毕。

---

## 12. 十二、当前最重要的新洞察

### 1. $\kappa$ 是局部“体”自由度

$(X,Y,Z)$ 是边界。

$\kappa$ 是体内环路流。

因此：

$$
\text{AURIC 金字塔}
\neq
\text{全部信息}.
$$

它只是完整五态单纯形沿一个环流方向的投影。

---

### 2. $\Delta$ 是联合曲率，不是第四个普通坐标

$$
\Delta=(1-Z)\kappa-XY.
$$

它不表示新的原子，而表示实际内部运输偏离独立补全的程度。

---

### 3. 最大熵与 transfer 降秩是同一件事的两种语言

$$
\Delta=0
$$

同时意味着：

- 端点条件独立；
- 条件熵最大；
- $\kappa=\frac{XY}{1-Z}$；
- transfer matrix 降秩；
- 一个 continuation 方向不可逆恢复。

所以“最大熵”在这里不是单纯的统计偏好，而是一个结构退化点。

---

### 4. 基础加法无法发现隐藏关系

$$
0+7=2+5
$$

导致：

$$
J_S=0.
$$

因此平均 FIB 数值完全看不见 $\kappa$。

要看见隐藏结构，必须使用：

- 二阶矩；
- 联合事件；
- $\chi=z+xy$；
- $\Delta$；
- transfer rank；
- 或实际共享接缝。

---

### 5. 先检查水平，再检查垂直

这是一条很重要的工程化原则：

### 水平检查

先检查基础占用率是否属于全局稳定集多面体：

$$
x\in\operatorname{STAB}(G).
$$

如果失败，任何 $\kappa$ 都无法修复。

### 垂直检查

如果水平可行，再检查：

- 每个局部纤维的 $\kappa_i$；
- $\Delta_i$；
- transfer product；
- loop-coupling polytope；
- phase 与 future-domain 的兼容性。

因此：

$$
\boxed{
\text{先水平可行，再垂直闭合。}
}
$$

---

### 6. 树扩展与环路障碍是同一理论的两面

开放路径没有一阶拓扑环，因此局部运输环流可以独立调节并通过 Markov 方式缝合。

闭环具有非平凡的一阶拓扑，局部相位可能绕一圈后翻转。

所以：

$$
\text{树状结构}
\Rightarrow
\text{局部一致通常可延拓},
$$

$$
\text{环状结构}
\Rightarrow
\text{必须额外检查 holonomy}.
$$

这不是比喻，而是运输图的核、transfer product 和周期边缘多面体共同给出的定理链。

---

## 13. 十三、下一步应当在项目中正式冻结的对象

最值得进入 Lean 或至少进入可检查理论源的不是更多隐喻，而是以下六个接口：

### 接口 A：运输图接口

定义：

$$
\mathcal B_{\mathrm{AURIC}}
$$

及其五条合法边，证明：

$$
\dim\ker\partial=1.
$$

### 接口 B：纤维接口

定义：

$$
I(X,Y,Z)=
[\kappa_-,\kappa_+].
$$

证明其端点、宽度和四个退化面。

### 接口 C：独立规范接口

定义：

$$
\kappa_0=\frac{XY}{1-Z}.
$$

证明：

$$
\Delta=0
\iff
\kappa=\kappa_0
\iff
\text{条件独立}
\iff
\text{条件熵最大}.
$$

### 接口 D：transfer 接口

定义：

$$
T(\kappa)=
\begin{pmatrix}
p_0&0&p_3\\
p_1&0&p_{13}\\
0&p_2&0
\end{pmatrix}.
$$

证明：

$$
\det T=-Z\Delta.
$$

### 接口 E：开放路径接口

证明：

$$
\text{separator marginals 一致}
\Longrightarrow
\text{存在全局路径律}.
$$

### 接口 F：周期闭合接口

定义：

$$
\Gamma_L(q_1,\ldots,q_L)
$$

并输出至少三种证书：

1. 基础稳定集不等式失败；
2. transfer product 无闭合支持；
3. loop-coupling polytope 为空。

这样，AURIC FIB ATOM 金字塔就从一个几何图形正式提升为：

$$
\boxed{
\text{局部运输代数}
+
\text{概率纤维}
+
\text{动态未来商}
+
\text{全局闭合证书}.
}
$$

这也是当前项目从“局部理论文件”向“共同流、有限生成器、边界兼容和可复用证明”的最新推进方向。

## 追加锚（本行以下为增补区）
