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

## 14. 原周期闭合的来源域与完整局部坐标

**定义 14.1（固定标号环上的五模式与两种可行集）。** 固定整数 $n\ge5$，
位置属于 $\mathbb Z_n=\mathbb Z/n\mathbb Z$。三位窗的印刷顺序始终是
$(U_i,U_{i+1},U_{i+2})$，合法模式按

$$
\Sigma=(000,100,010,001,101)
\tag{14.1}
$$

排列，分别对应 $F[\mathrm{null}],F[1],F[2],F[3],F[1,3]$。
这里的 $1,2,3$ 是窗口内的相对位置；原 FIB 输出名称分别为
$\mathrm{null},[2],[3],[5],[2,5]$，数值名称不是位置标号。
给每个 $i$ 一份概率律 $p_i:\Sigma\to[0,1]$，在其余三位字上延为零。
任意这类概率族组成

$$
\mathscr P_n=\prod_{i\in\mathbb Z_n}\operatorname{Prob}(\Sigma).
$$

完整重叠相容性指对每个 $i$ 和每个 $(b,c)\in\{0,1\}^2$，

$$
\sum_{a\in\{0,1\}}p_i(abc)
=\sum_{d\in\{0,1\}}p_{i+1}(bcd).
\tag{14.2}
$$

$bc=11$ 时两边都是零；另外三个等式匹配完整二位律。
满足 (14.2) 的族组成局部相容多面体 $\mathscr L_n$。
真实原周期来源的样本空间是

$$
B_n^{\mathrm{cyc}}
=\{u\in\{0,1\}^{\mathbb Z_n}:u_iu_{i+1}=0\text{ 对所有 }i\}.
\tag{14.3}
$$

写 $v(u)_{i,\sigma}=\mathbf1\{(u_i,u_{i+1},u_{i+2})=\sigma\}$，定义

$$
\mathscr C_n=\operatorname{conv}\{v(u):u\in B_n^{\mathrm{cyc}}\}.
\tag{14.4}
$$

等价地，$p\in\mathscr C_n$ 指存在同一概率律 $P$ 于 (14.3)，逐位置实现
全部 $p_i$。允许任意实概率，不预设旋转不变、平稳 Markov 结构或最小周期。
“原周期”只固定来源有 $n$ 个标号位置，字的最小周期可以整除 $n$。
全局边缘当然满足 (14.2)，所以 $\mathscr C_n\subseteq\mathscr L_n$。

本卷 §7 的全局耦合对象在这里明确写成

$$
\Gamma_n(p)=\left\{(P(u))_{u\in B_n^{\mathrm{cyc}}}:
P(u)\ge0,\ \sum_uP(u)=1,\
\sum_uv(u)_{i,\sigma}P(u)=p_i(\sigma)\quad\forall i,\sigma\right\}.
\tag{14.5}
$$

因此 $\Gamma_n(p)\ne\varnothing$ 与 $p\in\mathscr C_n$ 是同一个问题。
本节以后的小写 $q_i$ 专指一个位点的占据率，不沿用 §7 将整份窗口律
记成 $q_i$ 的记号。

**命题 14.2（不预设全局来源的坐标及其精确仿射维数）。** 对
$p\in\mathscr L_n$，直接从数据定义

$$
q_i=p_i(100)+p_i(101),\qquad \kappa_i=p_i(101).
\tag{14.6}
$$

完整重叠等式保证

$$
q_i=p_{i-1}(010)=p_{i-2}(001)+p_{i-2}(101).
\tag{14.7}
$$

于是全部局部律与 $(q_0,\ldots,q_{n-1};\kappa_0,\ldots,\kappa_{n-1})$
之间存在仿射逆

$$
p_i=\left(1-q_i-q_{i+1}-q_{i+2}+\kappa_i,
q_i-\kappa_i,q_{i+1},q_{i+2}-\kappa_i,\kappa_i\right).
\tag{14.8}
$$

特别地，$\mathscr L_n$ 和 $\mathscr C_n$ 的仿射维数都恰为 $2n$。

证明。对相邻窗口的公共二位边缘再取位点 $i$ 的单点边缘，窗口 $i$ 的
第一位与窗口 $i-1$ 的第二位相同。后者在合法支持上只有 $010$ 能为一，
故给 (14.7) 的第一个等号。再将窗口 $i-1$ 的第二位与窗口 $i-2$ 的
第三位匹配，给第二个等号。此时还没有假定 $P$ 存在。
$p_i(101)=\kappa_i$ 与第一、第三位边缘分别给第二、第四坐标；
中位边缘给第三坐标；概率和一给第一坐标，得到 (14.8)。

反向，任意 $(q,\kappa)$ 使 (14.8) 的五项非负时，它们自动和一。
第 $i$ 窗的前两位律按 $00,01,10$ 为

$$
(1-q_i-q_{i+1},q_{i+1},q_i),
$$

后两位律为 $(1-q_{i+1}-q_{i+2},q_{i+2},q_{i+1})$，正等于下一窗的
前两位律。这证明 (14.8) 在非负域上精确参数化 $\mathscr L_n$，
并给出维数至多 $2n$。只有在 $P$ 存在时才进一步可以把它们写成
$q_i=P(U_i=1)$、$\kappa_i=P(U_i=1,U_{i+2}=1)$。

为证下界，在 $B_n^{\mathrm{cyc}}$ 中取全零字、$n$ 个单占位字，
以及 $n$ 个仅在 $i,i+2$ 占位的双占位字。$n\ge5$ 保证这些双占位字合法，
且无序对 $\{i,i+2\}$ 彼此不同：反向重合会要求 $n\mid4$。
单占位字的坐标为 $(e_i,0)$；双占位字的坐标为 $(e_i+e_{i+2},e_i)$。
在以全零点为原点的任一线性关系中，先读 $\kappa$ 坐标就使全部双占位
系数为零，再读 $q$ 坐标使全部单占位系数为零。
这 $2n+1$ 个点仿射独立且都在 $\mathscr C_n$，所以两者维数均为 $2n$。
坐标完备并不将局部非负性升级为全局闭合性。证毕。

**数学引文与参数对应 14.3。** 本卷 §§1、5、7 供应单窗五态纤维、四角读出
和指定边缘的 $\Gamma$ 问题。
[《接缝、周期与算术边界重构》§§21–22](AURIC_FIB_SEAMS_CYCLES_ARITHMETIC_BOUNDARY_RECONSTRUCTION.md)
供应位置依赖的完整重叠合同、三态分层流及延长周期的实现。
其 §§23–26 供应齐次纤维、间隙计数与五环固定均值投影，§27 区分路径权重迹
和指定边缘来源。在当前第 $i$ 窗，原有字典精确为

$$
(X,Y,Z,\kappa)=(q_i,q_{i+2},q_{i+1},\kappa_i),
\qquad (x,z,y)=(u_i,u_{i+1},u_{i+2}).
\tag{14.9}
$$

延长为 $\ell n$ 的来源与 (14.3) 不同；后面的证书和修补始终回到 (14.3)。

## 15. 四角差进入整圈测试的联合占位项

**定义 15.1（位置依赖的测试菜单）。** 给每个窗口实函数
$f_i:\Sigma\to\mathbb R$，定义确定字分数和局部数据的线性分数

$$
F_f(u)=\sum_{i\in\mathbb Z_n}f_i(u_i,u_{i+1},u_{i+2}),\qquad
\langle f,p\rangle=\sum_{i\in\mathbb Z_n}\sum_{\sigma\in\Sigma}
f_i(\sigma)p_i(\sigma).
\tag{15.1}
$$

**定理 15.2（四角读口的整圈展开与退化纤维边界）。** 令

$$
\begin{aligned}
a_i&=f_i(100)-f_i(000),& b_i&=f_i(010)-f_i(000),\\
c_i&=f_i(001)-f_i(000),&
J_i&=f_i(000)-f_i(100)-f_i(001)+f_i(101),\\
C_f&=\sum_i f_i(000),&h_i&=a_i+b_{i-1}+c_{i-2}.
\end{aligned}
\tag{15.2}
$$

则对任意 $u\in B_n^{\mathrm{cyc}}$ 和任意 $p\in\mathscr L_n$，分别有

$$
F_f(u)=C_f+\sum_i h_i u_i+\sum_iJ_i u_iu_{i+2},
\qquad
\langle f,p\rangle=C_f+\sum_i h_iq_i+\sum_iJ_i\kappa_i.
\tag{15.3}
$$

证明。在合法的五种 $(x,z,y)$ 上，

$$
f_i(x,z,y)=f_i(000)+a_ix+b_iz+c_iy+J_i xy.
\tag{15.4}
$$

在 $000$ 上右边是常数项；在 $100,010,001$ 上依次为常数加 $a_i,b_i,c_i$；
在 $101$ 上为 $f_i(000)+a_i+c_i+J_i=f_i(101)$。
这逐项证明 (15.4)，没有对非法模式作多项式延拓的要求。
代入 $x=u_i,z=u_{i+1},y=u_{i+2}$ 并求和。
循环重编号 $j=i+1$ 和 $j=i+2$ 分别给

$$
\sum_i b_i u_{i+1}=\sum_j b_{j-1}u_j,\qquad
\sum_i c_i u_{i+2}=\sum_j c_{j-2}u_j,
$$

与第一位项合并即得确定字式。
对各自的窗口律求 (15.4) 的期望，(14.6)–(14.8) 给
$f_i(000)+a_iq_i+b_iq_{i+1}+c_iq_{i+2}+J_i\kappa_i$；
使用相同的循环重编号得到局部数据式。它不以存在全局 $P$ 为前提。

固定一个非空的局部一阶纤维 $(q_i,q_{i+1},q_{i+2})$ 时，非负性给

$$
\kappa_i\in I_i=
[\max(0,q_i+q_{i+1}+q_{i+2}-1),\min(q_i,q_{i+2})],
\qquad w_i=|I_i|.
\tag{15.5}
$$

沿这条局部纤维的期望变化是 $J_i(\kappa_i'-\kappa_i)$，故期望在整个
$I_i$ 上不变当且仅当 $J_iw_i=0$；其全幅变化为 $|J_i|w_i$。
$J_i=0$ 总使该测试不读取隐藏坐标；$J_i\ne0$ 在零宽纤维上仍无变化。
此外，$I_i$ 是局部可行区间，不保证整圈闭合约束下能独立改变某一个
$\kappa_i$。公式 (15.3) 只确定其作为整圈二步联合项的系数。
$F_f$ 是无单位预设的数学分数；物理能量的解释还需要实现和单位的额外映射。
证毕。

## 16. 保留同一起始接缝的正证书

**定义 16.1（三态接缝与锚定分层流）。** 合法二位状态是
$\mathcal S=(00,01,10)$，五条有向边及其三位字如下。

| 模式 $\sigma$ | 起状态 $s$ | 终状态 $t$ |
| --- | --- | --- |
| $000$ | $00$ | $00$ |
| $100$ | $10$ | $00$ |
| $010$ | $01$ | $10$ |
| $001$ | $00$ | $01$ |
| $101$ | $10$ | $01$ |

记这五条边的集合为 $E$，$\sigma(s,t)$ 表示唯一对应的模式。
在第零层切开环，层号为 $0,1,\ldots,n$，每条第 $i$ 层边从 $(i,s)$ 指向
$(i+1,t)$。对每个锚 $a\in\mathcal S$ 引入

$$
z_i^a(s,t)\ge0\qquad(0\le i<n,\ (s,t)\in E),
\tag{16.1}
$$

其余状态对约定流为零。约束为

$$
\sum_{r\in\mathcal S}z_{i-1}^a(r,s)
=\sum_{t\in\mathcal S}z_i^a(s,t)
\quad(1\le i<n,\ s\in\mathcal S,\ a\in\mathcal S),
\tag{16.2}
$$

$$
z_0^a(s,t)=0\ (s\ne a),\qquad
z_{n-1}^a(s,t)=0\ (t\ne a),
\tag{16.3}
$$

$$
\sum_{a\in\mathcal S}z_i^a(s,t)=p_i(\sigma(s,t))
\quad(0\le i<n,\ (s,t)\in E).
\tag{16.4}
$$

共有至多 $3\cdot5n=15n$ 个非负变量。两个端点使用同一个 $a$；
只要求合并锚后的起终分布相同是另一个较弱条件。

**定理 16.2（原周期实现与锚定流充要等价）。** 对任意
$p\in\mathscr P_n$，

$$
p\in\mathscr C_n\quad\Longleftrightarrow\quad
\text{存在满足 (16.1)–(16.4) 的流}.
\tag{16.5}
$$

证明。若存在 $P$，令 $S_i=(U_i,U_{i+1})$，索引按模 $n$，故 $S_n=S_0$。
定义

$$
z_i^a(s,t)=P(S_0=a,S_i=s,S_{i+1}=t).
\tag{16.6}
$$

不合法边的概率为零。对前后状态求和都得到 $P(S_0=a,S_i=s)$，给内部守恒；
$S_n=S_0$ 给相同锚的端点条件；对 $a$ 求和给指定三位边缘。

反向固定 $a$。这是层号严格上升的有限有向无环图。
若某条边仍有正流，从它的起点向前追溯：任何非零层的正流出顶点都由
(16.2) 有正流入，故有限步到达第零层。端点约束使其必为 $(0,a)$。
向后延伸时，任意非末层的正流入顶点也有正流出，所以最终到达 $(n,a)$。
这样得到恰有 $n$ 条边的正流路径。减去路径上边流的最小值
$\beta>0$ 乘路径指示，剩余流非负、内部仍守恒、端点条件仍成立，
并至少少一条正边。重复至无正边，至多作初始正边数那么多次。
这是一份有限路径分解，不需要流为有理数，也没有剩余环可滞留在内部。

对每个 $a$，记分解权重为 $\beta_{a,r}$。它们之和等于第零层该锚的流量
$\lambda_a=\sum_tz_0^a(a,t)$；内部守恒又使每层总量都是 $\lambda_a$。
由 (16.4) 和 $p_0$ 归一化，

$$
\sum_{a,r}\beta_{a,r}=\sum_a\lambda_a
=\sum_{(s,t)\in E}p_0(\sigma(s,t))=1.
\tag{16.7}
$$

一条路径的状态写成 $s_i=(b_i,b_{i+1})$，$0\le i\le n$。
合法边强迫相邻状态的共享位相同；末状态与初状态都为 $a$，所以
$b_n=b_0,b_{n+1}=b_1$。令 $u_i=b_i$，$0\le i<n$。
每个状态都没有 $11$，包括跨末端的 $(b_{n-1},b_n)$，故
$u\in B_n^{\mathrm{cyc}}$。第 $i$ 条边恰对应 $u_iu_{i+1}u_{i+2}$，
最后两窗也由上述两条闭合等式恢复。
以 (16.7) 的权重混合这些字，逐边恢复各锚流，再由 (16.4) 恢复每个 $p_i$。
所以得到同一原长度来源。证毕。

**推论 16.3（至多 $2n+1$ 份确定字的正证书）。** 若 $p\in\mathscr C_n$，
存在 $m\le2n+1$、$u^{(r)}\in B_n^{\mathrm{cyc}}$ 和
$\lambda_r\ge0,\sum_r\lambda_r=1$，使

$$
p_i(\sigma)=\sum_{r=1}^m\lambda_r
\mathbf1\{(u_i^{(r)},u_{i+1}^{(r)},u_{i+2}^{(r)})=\sigma\}.
\tag{16.8}
$$

证明。先取 (14.4) 或定理 16.2 给出的有限表示，去掉零权重。
若点数 $m>2n+1$，由命题 14.2，存在不全为零的实系数 $c_r$ 满足

$$
\sum_rc_r=0,\qquad\sum_rc_r(q^{(r)},\kappa^{(r)})=0.
$$

系数有正有负。令 $t=\min_{c_r>0}\lambda_r/c_r>0$，
改权重为 $\lambda_r'=\lambda_r-tc_r$。所有新权重非负、总和仍为一、
坐标不变，且至少一项为零。由仿射逆 (14.8) 全部窗口数据也不变。
删去零项并重复，有限次后得到 (16.8)。这是 Carathéodory 仿射相关消元在
本坐标域中的应用。

该结论保证存在小支持来源，不识别产生数据的原始 $P$，也不保证固定份数
的等权样本能表示这些实权重。锚定标签是正证书的数学表示，不是原生观察者
必须具有三态记忆的下界。证毕。

## 17. 最大—加法反证书与全部有界测试

**定义 17.1（按时间顺序的最大—加法矩阵）。** 在
$\mathbb R\cup\{-\infty\}$ 上，$x\oplus y=\max(x,y)$、$x\otimes y=x+y$，
并约定 $-\infty+x=-\infty$。矩阵乘法为

$$
(A\otimes B)_{st}=\max_{r\in\mathcal S}(A_{sr}+B_{rt}).
$$

单位矩阵的对角元是零，其余为 $-\infty$。按状态顺序 $(00,01,10)$ 定义

$$
T_i(f)=\begin{pmatrix}
f_i(000)&f_i(001)&-\infty\\
-\infty&-\infty&f_i(010)\\
f_i(100)&f_i(101)&-\infty
\end{pmatrix},\qquad
M_f=T_0(f)\otimes\cdots\otimes T_{n-1}(f).
\tag{17.1}
$$

行是出发状态、列是到达状态；乘积先走第零窗，再依次走到第 $n-1$ 窗，
一般不能交换因子。最大—加法迹定义为
$\operatorname{tr}_{\max}M=\max_sM_{ss}$，并非对角元的普通和。

**定理 17.2（原长度准确测试上界）。** 对任意实测试菜单，

$$
H_n(f):=\max_{u\in B_n^{\mathrm{cyc}}}F_f(u)
=\operatorname{tr}_{\max}M_f.
\tag{17.2}
$$

证明。对因子数归纳，$(T_0\otimes\cdots\otimes T_{j-1})_{st}$ 等于
所有从第零层 $s$ 到第 $j$ 层 $t$ 的合法路径的最大分数；无路径时为
$-\infty$。归纳步正是对最后一个中间状态取最大，再加最后一条边的分数。
取 $j=n,t=s$，路径恰满足相同起终状态。定理 16.2 中的重叠恢复过程给
它与一个标号 $n$ 位合法字的一一对应，反向由字逐窗取状态得到唯一路径。
因此对所有对角元取最大恰枚举原长度字的最优分数。全零字总合法，故最大值
有限且达到。

对一个已经给定的 $f$，固定大小的 $3\times3$ 递推用 $O(n)$ 次实数加法和
比较就计算 (17.2)。这是算术操作计数，不是任意实数的有限编码保证，
也不是证书发现、所有面的枚举或实际测量取得的复杂度界。证毕。

**定理 17.3（全部有界测试的充要反证书判据）。** 对任意
$p\in\mathscr P_n$，包括尚不满足局部相容性的概率族，

$$
p\in\mathscr C_n\quad\Longleftrightarrow\quad
\langle f,p\rangle\le H_n(f)
\quad\text{对所有 }f=(f_i)_{i\in\mathbb Z_n},\quad 0\le f_i(\sigma)\le1.
\tag{17.3}
$$

证明。若 $p$ 由 $P$ 实现，线性性给
$\langle f,p\rangle=\sum_uP(u)F_f(u)\le H_n(f)$。
反向，$\mathscr C_n$ 是有限个向量的凸包，非空且紧凸。
若 $p\notin\mathscr C_n$，有限维严格分离给某个实向量 $g$，满足

$$
\langle g,p\rangle>\max_{r\in\mathscr C_n}\langle g,r\rangle=H_n(g).
\tag{17.4}
$$

这里严格分离也可直接由最近欧氏点得到：取紧集上的最近点 $r_0$，
令 $g=p-r_0\ne0$。对每个 $r\in\mathscr C_n$，线段
$r_0+t(r-r_0)$ 留在凸集中，最短距离在 $t=0$ 的右导数非负，故
$\langle g,r-r_0\rangle\le0$。于是
$\langle g,p\rangle-\sup_r\langle g,r\rangle\ge\|g\|^2>0$。

对每窗置 $m_i=\min_\sigma g_i(\sigma)$，并取共同正数

$$
R=\max_{i,\sigma}(g_i(\sigma)-m_i).
$$

若 $R=0$，各窗口测试均为常数，在每份归一化概率族上的总分都是
$\sum_im_i$，与 (17.4) 矛盾。因此 $R>0$，可定义
$f_i(\sigma)=(g_i(\sigma)-m_i)/R\in[0,1]$。
所有窗口在 $p$、$r$ 和确定字上的质量都是一，故逐窗平移都扣去同一总数
$\sum_im_i$；再除以同一个 $R$，有

$$
\langle f,p\rangle-H_n(f)
=\frac{\langle g,p\rangle-H_n(g)}R>0.
$$

这与全部有界测试不等式矛盾，得充分性。不能将共同缩放擅自替换为
各窗口不同缩放，因为那会改变各窗对分离差的相对权重。证毕。

**定义 17.4（可核验的负证书及其范围）。** 一份负证书是
$f\in[0,1]^{5n}$、由 (17.2) 确定的 $H_n(f)$，以及严格正的
$\langle f,p\rangle-H_n(f)$。这指出哪一个局部线性组合超出了所有原长度
共同来源的上界。检查给定的 $f$，寻找这样的 $f$，列出边缘多面体的全部面，
给输入实数编码并控制位复杂度，以及实际取得 $p_i$，是不同任务。
定理 17.3 的量词是所有有界测试，不将任意一项测试的通过认作充分。

## 18. 局部松弛的准确一圈、两圈与三圈公式

**定理 18.1（分层环流的归一化与局部测试上界）。** 对
$H_n^{\mathrm{loc}}(f)=\max_{p\in\mathscr L_n}\langle f,p\rangle$，有

$$
H_n^{\mathrm{loc}}(f)=\max\left\{
\operatorname{tr}_{\max}M_f,
\frac{\operatorname{tr}_{\max}M_f^{\otimes2}}2,
\frac{\operatorname{tr}_{\max}M_f^{\otimes3}}3\right\}.
\tag{18.1}
$$

证明。将层号重新按模 $n$ 连接，得到顶点 $(i,s)\in\mathbb Z_n\times\mathcal S$
的图 $\mathcal G_n$。边 $(i,ab)\to(i+1,bc)$ 的流为 $p_i(abc)$。
在顶点 $(i,s)$ 流入等于流出正是 (14.2) 的移位；每层边流总和是一。
所以 $\mathscr L_n$ 恰由这类非负守恒流组成，且是非空紧多面体，线性最大值达到。

对任一非零剩余守恒流，从正边开始沿正边前进；正流入保证正流出。
有限顶点必重复，首次重复之间给简单有向圈 $\gamma$。
扣除圈上最小边流 $\alpha_\gamma>0$ 乘圈指示，仍非负且守恒，并至少删除
一条正边。有限重复得到

$$
p=\sum_\gamma\alpha_\gamma\mathbf1_\gamma.
\tag{18.2}
$$

每一步层号增加一，圈长必是 $m_\gamma n$。简单圈在每层不能重复同一状态，
每层只有三状态，所以 $m_\gamma\in\{1,2,3\}$，且该圈恰在每层访问
$m_\gamma$ 次。对任一层求边流和给

$$
\sum_\gamma m_\gamma\alpha_\gamma=1,\qquad
p^\gamma=\frac{\mathbf1_\gamma}{m_\gamma}\in\mathscr L_n,
\qquad\lambda_\gamma=m_\gamma\alpha_\gamma,
\qquad p=\sum_\gamma\lambda_\gamma p^\gamma.
\tag{18.3}
$$

因此凸混合权重是 $m_\gamma\alpha_\gamma$，不是 $\alpha_\gamma$。
从该圈在第零层的任一访问开始，按状态重叠读出一个长度 $m_\gamma n$
的合法周期字。它的总测试分数使用 $f_i$ 每 $n$ 步重复，故不超过
$\operatorname{tr}_{\max}M_f^{\otimes m_\gamma}$。
归一化圈流的分数等于该总分除以 $m_\gamma$，再用 (18.3) 混合，
得到 (18.1) 的“至多”方向。

反向不要求路径简单。任意长度 $mn$、$m\ge1$ 的闭走法，每层恰出现
$m$ 次。将各条边的经过次数除以 $m$，每层总量为一；闭走法在每个顶点
流入次数与流出次数相同，故给一个 $\mathscr L_n$ 中的族，分数恰为
总分除以 $m$。特别对 $m=1,2,3$，选取达到
$\operatorname{tr}_{\max}M_f^{\otimes m}$ 的闭走法，三个右侧候选各自
都不超过 $H_n^{\mathrm{loc}}(f)$。与前向合并即得等式。
这一反向构造也说明任意多圈闭走法的平均分都不超过 (18.1)，
即使它含重复顶点。证毕。

**数学引文与范围 18.2。** 守恒流按简单圈扣除的经典方法见
Goldstein–Kuna–Lebowitz–Speer，*Translation invariant extensions of finite
volume measures*，[arXiv:1508.04448v2，§4.1 Theorem 6](https://arxiv.org/pdf/1508.04448v2)。
其中 $X_k$ 是 $k+1$ 位二进制块，de Bruijn 图有 $2^k$ 个状态，讨论单个
局部平移一致律；§4.2 Theorem 8 给其通用环长
$\operatorname{lcm}\{1,\ldots,2^k\}$，$k=2$ 为 $12$。
这里有 no11 限制和指定位置层，简单圈的每层访问数至多三由 (18.2)–(18.3)
另行推导，不能把该文的通用长度结论直接当作原 $n$ 位实现。

Karp 的原报告 *A Characterization of the Minimum Cycle Mean in a Digraph*，
[UCB/ERL M77/47，Theorem 1](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1977/Archive/ERL-m-77-47.pdf)，
对强连通有向图、实边权 $w$，令 $N$ 为顶点数、$D_k(v)$ 为从固定起点到
$v$ 的恰长 $k$ 路径的最小权，证明最小平均圈权为

$$
\mu_{\min}=\min_{v:D_N(v)<\infty}\ 
\max_{0\le k<N}\frac{D_N(v)-D_k(v)}{N-k}.
\tag{18.4}
$$

不可达 $D_k(v)=+\infty$ 的相应比值按 $-\infty$ 处理；
一般图按含圈的强连通分量处理。最大平均圈由边权取负得到。
该报告给 $O(N|E|)$ 次算术操作的递推算法，不是概率转移矩阵的普通乘法。
本图的 $H_n^{\mathrm{loc}}$ 是每基础圈的分数，等于每条边最大平均权的
$n$ 倍；(18.1) 还利用三状态和分层结构得到了更具体的短公式。
这些是经典最大平均圈方法的应用，原长度的 $H_n$ 则只允许恰走 $n$ 步闭合。
若某一个 $f$ 恰有 $H_n^{\mathrm{loc}}(f)=H_n(f)$，只说明该方向的支撑值相同；
例如零测试总相等，它不证明任意指定 $p$ 属于 $\mathscr C_n$。

## 19. 不固定任何均值的闭合距离与精确对偶

**定义 19.1（平均总变差闭合距离）。** 对任意 $p\in\mathscr P_n$，定义

$$
\operatorname{TV}(a,b)=\frac12\sum_{\sigma\in\Sigma}|a(\sigma)-b(\sigma)|,
\qquad d_n(p,r)=\frac1n\sum_i\operatorname{TV}(p_i,r_i),
\qquad
\Delta_n(p)=\min_{r\in\mathscr C_n}d_n(p,r).
\tag{19.1}
$$

输入 $p$ 可以局部不相容。修补的可行域是全部 $\mathscr C_n$，允许改变
每个局部概率，因而允许改变所有 $q_i$ 和 $\kappa_i$；局部不相容输入也不必
先赋予跨窗统一的 $q_i$。若另要求保持某些均值，得到的是不同的受限问题。
$\mathscr C_n$ 是非空紧凸集，$d_n(p,\cdot)$ 连续，故这里最小值存在。
同时 $\Delta_n(p)=0$ 当且仅当 $p\in\mathscr C_n$。

**定理 19.2（最小修补量等于最大归一化违例）。** 对每个
$p\in\mathscr P_n$，有达到的最大值

$$
\boxed{\displaystyle
\Delta_n(p)=\frac1n\max_{f\in[0,1]^{5n}}
\bigl[\langle f,p\rangle-H_n(f)\bigr].}
\tag{19.2}
$$

证明。先在一个有限窗口上令 $d_\sigma=p_i(\sigma)-r_i(\sigma)$。
两份律都归一化，所以 $\sum_\sigma d_\sigma=0$，正部分总质量与负部分
绝对值相同，均为 $\frac12\sum_\sigma|d_\sigma|$。
在 $d_\sigma>0$ 处取 $f_i(\sigma)=1$、在负处取零，正好达到

$$
\operatorname{TV}(p_i,r_i)
=\max_{0\le f_i\le1}\sum_\sigma f_i(\sigma)
\bigl(p_i(\sigma)-r_i(\sigma)\bigr).
\tag{19.3}
$$

任意其余 $f_i\in[0,1]^5$ 的分数都不超过正部分质量。
各窗的测试可以独立选择，故

$$
n\,d_n(p,r)=\max_{f\in K}\Phi(f,r),
\qquad K=[0,1]^{5n},\qquad \Phi(f,r)=\langle f,p-r\rangle.
\tag{19.4}
$$

应用 Sion 的 *On General Minimax Theorems*，
[Pacific Journal of Mathematics 8(1), 171–176，Theorem 3.4](https://msp.org/pjm/1958/8-1/pjm-v8-n1-p14-s.pdf)。
原定理对最大化变量要求准凹、上半连续，对最小化变量要求准凸、下半连续，
并以非空紧凸域保证 $\sup\inf=\inf\sup$。
在这里最大化域 $K$ 和最小化域 $\mathscr C_n$ 都是有限维欧氏空间的
非空紧凸集；$\Phi$ 联合连续，固定 $r$ 后对 $f$ 线性，固定 $f$ 后对
$r$ 仿射，因而分别凹与凸，尤其满足相应准凹、准凸和半连续要求。
严格地说固定 $p$ 后 $\Phi(f,r)=\langle f,p\rangle-\langle f,r\rangle$
是双仿射函数；在增广变量 $(1,r)$ 中它是连续双线性函数。
两种表述都给出所需的逐变量条件，无须将紧性或连续性省略。

由此可以交换 (19.4) 中的最小、最大：

$$
\begin{aligned}
n\Delta_n(p)
&=\min_{r\in\mathscr C_n}\max_{f\in K}\Phi(f,r)\\
&=\max_{f\in K}\min_{r\in\mathscr C_n}\Phi(f,r)\\
&=\max_{f\in K}\left[\langle f,p\rangle
-\max_{r\in\mathscr C_n}\langle f,r\rangle\right]\\
&=\max_{f\in K}[\langle f,p\rangle-H_n(f)].
\end{aligned}
\tag{19.5}
$$

最后一步是有限凸包 (14.4) 上线性函数在某个确定字达到最大。
最小端的达到已由定义 19.1 说明；最大端也真正达到，因为
$H_n(f)$ 是有限个线性函数 $F_f(u)$ 的最大值，连续，
故方括号内函数在紧立方体 $K$ 上达到最大。$f=0$ 给零，所以对偶值非负。
全程只用了各窗的概率归一化，没有使用 (14.2)。证毕。

**推论 19.3（相等的原始、对偶证书证明全局最优）。** 若一份实际原长度来源
给出 $r\in\mathscr C_n$，且某个 $f\in[0,1]^{5n}$ 满足

$$
d_n(p,r)=\frac{\langle f,p\rangle-H_n(f)}n,
\tag{19.6}
$$

则 $r$ 是不加均值约束的最近点，$f$ 是达到最大违例的测试。
证明。可行修补给 $\Delta_n(p)\le d_n(p,r)$，定理 19.2 给反向下界为
(19.6) 的右边；两边相等即迫使所有不等式取等号。
这只证明最优值和所给点的最优性，不推断最近点或全局来源唯一。证毕。

## 20. 全正五环的无约束最优修补与三种圈数

**命题 20.1（长零间隙测试的全部长度最优值）。** 对长度 $L\ge5$ 的合法环字，
在每个窗口使用同一测试

$$
f(100)=f(001)=1,\qquad f(000)=f(010)=f(101)=0.
\tag{20.1}
$$

则

$$
H_L(f)=2\lfloor L/3\rfloor.
\tag{20.2}
$$

证明。若字为全零，分数为零。若有 $K>0$ 个一，依次记两个一之间的
零间隙长为 $g_1,\ldots,g_K\ge1$。一个长至少二的间隙在左端恰贡献一次
$100$、右端恰贡献一次 $001$，其余内部窗不计分；长一的间隙没有这两个
模式。故若长间隙数为 $B$，分数为 $2B$。每个这样的间隙连同它前面的一
至少占三个位点，不同间隙所占段互不重叠，所以 $3B\le L$，即上界
$2\lfloor L/3\rfloor$。
写 $L=3h+r$，$r\in\{0,1,2\}$，取字 $(100)^h0^r$。
$L\ge5$ 保证 $h\ge1$；其中 $h-1$ 个零间隙长二，剩下一个长 $2+r$，
包括跨切口间隙都非空，故合法且 $B=h$，达到上界。证毕。

**定理 20.2（全正五环的无均值限制距离）。** 在 $n=5$，各窗取

$$
p_i=p=\frac1{44}(3,13,14,13,1).
\tag{20.3}
$$

这是严格正的局部相容族，且

$$
\Delta_5(p)=\frac{21}{110}.
\tag{20.4}
$$

一个达到它的来源是以总权 $9/22$ 取 $10000$ 的均匀标号旋转律，
以总权 $13/22$ 取 $10100$ 的均匀标号旋转律。

证明。五个分子均正且总和 $44$。前两位边缘按 $00,01,10$ 为
$(p_{000}+p_{001},p_{010},p_{100}+p_{101})=(16,14,14)/44$，
后两位为 $(p_{000}+p_{100},p_{001}+p_{101},p_{010})$，也是同一向量。
故完整重叠相容，且各位 $q_i=14/44=7/22$，$\kappa_i=1/44$。

对 (20.1)，命题 20.1 给 $H_5=2$，例如 $10000$ 达到。
但给定数据的分数为

$$
\langle f,p\rangle=5\frac{13+13}{44}=\frac{65}{22},\qquad
\langle f,p\rangle-H_5=\frac{21}{22}>0.
\tag{20.5}
$$

所以 $p\notin\mathscr C_5$，且 (19.2) 给
$\Delta_5(p)\ge(21/22)/5=21/110$。这个下界针对整个 $\mathscr C_5$，
不要求候选修补齐次或保持任何均值。

再构造上界。单占位字 $10000$ 的五窗计数为 $(2,1,1,1,0)$；
双占位字 $10100$ 的计数为 $(0,1,2,1,1)$。
在五个标号旋转中均匀抽取时，每个固定窗口恰有计数除以五的律。
两个总权相加为一，所以所述混合是实际五位来源，其每窗边缘为

$$
p_*=\frac9{22}\frac{(2,1,1,1,0)}5
+\frac{13}{22}\frac{(0,1,2,1,1)}5
=\frac1{110}(18,22,35,22,13).
\tag{20.6}
$$

统一分母 $220$ 后，

$$
p=\frac1{220}(15,65,70,65,5),\qquad
p_*=\frac1{220}(36,44,70,44,26),\qquad
p_*-p=\frac1{220}(21,-21,0,-21,21).
\tag{20.7}
$$

因此每窗 $\operatorname{TV}(p,p_*)=\frac12\cdot84/220=21/110$，
平均值也相同。由推论 19.3，上下界相等，得 (20.4)。
此 $p_*$ 恰保留 $q_i=7/22$，而 $\kappa_i$ 改为 $13/110$。
供应卷定理 26.2 的固定三均值问题已有同一个候选和数值；
(20.5) 额外排除了所有不固定均值、甚至位置依赖的修补能更近的可能。
无约束最优性并不将受限问题中的唯一性自动推广到无约束域。证毕。

**命题 20.3（同一测试的重复圈数与普通支持迹）。** 在 (20.1) 下，

| 来源长度 | 准确总分 $H_L$ | 按五位基础圈归一化 |
| ---: | ---: | ---: |
| $5$ | $2$ | $2$ |
| $10$ | $6$ | $3$ |
| $15$ | $10$ | $10/3$ |

因此以五位为基础的局部最大值是 $H_5^{\mathrm{loc}}(f)=10/3$，
严格大于原五位上界 $2$。此外，把 (20.3) 的概率直接作为普通边权得到
的矩阵 $A$ 满足 $\operatorname{tr}(A^5)\ge(3/44)^5>0$，仍不能实现 (20.3)。

证明。前三个值分别是 (20.2) 在 $L=5,10,15$ 的值。
达到字可分别取 $10000,(100)^30,(100)^5$；上界均由长间隙计数证明。
由于每个位置使用相同 $f$，重复五位测试与这三个长度的同质测试相同，
所以 $\operatorname{tr}_{\max}M_f^{\otimes m}=H_{5m}$，$m=1,2,3$。
定理 18.1 给局部最大值 $10/3$。它也直接由局部律
$(0,1,1,1,0)/3$ 取得：每窗分数 $2/3$，五窗总分 $10/3$，
这份局部律没有因此变成一个五位来源。

对最后的断言，普通矩阵按定义 16.1 的五条边赋权 $p(\sigma)$，
非法边为零。全零的闭合状态路径给普通迹和中的一项 $(3/44)^5$；
所有其余项非负，故迹严格正。而 (20.5) 已严格排除指定边缘实现。
这把 §7 的“存在闭合支持”与“满足全部指定边缘”区分成了同一全正数据上的
具体反例。证毕。

## 21. 保留层标签的原环长随机切口修补

**定理 21.1（每个窗口同时至多 $2/n$ 的修补）。** 对任意
$p\in\mathscr L_n$，存在同一份 $n$ 位合法来源，其边缘
$\widetilde p\in\mathscr C_n$ 满足

$$
\operatorname{TV}(p_i,\widetilde p_i)\le\frac2n
\qquad\text{对每个 }i\in\mathbb Z_n.
\tag{21.1}
$$

证明。使用 (18.2)–(18.3) 的同一归一化，写
$p=\sum_\gamma\lambda_\gamma p^\gamma$，
$p^\gamma=\mathbf1_\gamma/m_\gamma$，
$\lambda_\gamma=m_\gamma\alpha_\gamma$，
$m_\gamma\in\{1,2,3\}$，$\sum_\gamma\lambda_\gamma=1$。
先在一个成分上构造，最后按这些权重混合。

固定简单圈 $\gamma$，记 $m=m_\gamma$。
从第零层的某次出现开始读其合法字 $u$，长度 $mn$，并按 $mn$ 周期延为
整数下标序列。位置 $a$ 的基础层标签是 $a\bmod n$。
第 $i$ 层的 $m$ 次出现对应 $i+rn$，$r\in\mathbb Z_m$，所以其窗口律为

$$
p_i^\gamma(\sigma)=\frac1m\sum_{r=0}^{m-1}
\mathbf1\{(u_{i+rn},u_{i+1+rn},u_{i+2+rn})=\sigma\}.
\tag{21.2}
$$

这不是对全部 $mn$ 个位置作任意旋转平均：抽样相位必须留在同一基础层。
为修补，独立均匀选 $j\in\mathbb Z_n$ 和 $r\in\mathbb Z_m$。
先取连续 $n$ 位并保留原层号，定义

$$
V^{j,r}_{j+t\bmod n}=u_{j+rn+t\bmod mn}\quad(0\le t<n),
\qquad V^{j,r}_j:=0.
\tag{21.3}
$$

最后的赋值覆盖切口位。$j$ 可取任一整数代表元；换成 $j+an$ 只把均匀相位
$r$ 平移为 $r+a\bmod m$，故条件分布不变。
除跨切口的边外，截取段相邻位来自原字，相邻乘积为零。
切口位变零后，$j-1$ 与 $j$、$j$ 与 $j+1$ 的相邻乘积也为零，包括从截取
末位接回首位的一条边。因此每个 $V^{j,r}$ 都属于 $B_n^{\mathrm{cyc}}$。
它们的均匀混合定义一个来源 $P^\gamma$，记其边缘为 $\widetilde p_i^\gamma$。

固定窗口标签 $i$，令 $R_i^j$ 表示在切口 $j$ 下仅对相位 $r$ 平均的三位律。
对原成分记

$$
x=q_i^\gamma=\frac1m\sum_ru_{i+rn},\qquad
y=q_{i+2}^\gamma=\frac1m\sum_ru_{i+2+rn}.
\tag{21.4}
$$

下面精确区分全部切口。

若 $j\notin\{i,i+1,i+2\}$，令 $t\in\{0,\ldots,n-1\}$ 满足
$j+t\equiv i\pmod n$。此时 $1\le t\le n-3$，三个位置在截取段内连续且
没有任何一个被置零。存在整数 $a$ 使 $j+t=i+an$，故三位为

$$
(u_{i+(r+a)n},u_{i+1+(r+a)n},u_{i+2+(r+a)n}).
$$

$r\mapsto r+a\bmod m$ 是层出现次数的双射；因相位均匀，
$R_i^j=p_i^\gamma$。这是律相同，不要求同一个未重编号相位的三位逐样本相同。

若 $j=i$，由 (21.3) 直接得到

$$
(V_i,V_{i+1},V_{i+2})=(0,u_{i+1+rn},u_{i+2+rn}).
\tag{21.5}
$$

所以 $R_i^i$ 是原窗口律只把左端抹零的推前。
这个映射只将 $100\mapsto000$、$101\mapsto001$，其余模式不变。
离开两个左端为一的模式的质量恰是 $x$，并全部进入互不相交的左端为零的
模式；总 $\ell^1$ 变化为 $2x$，所以
$\operatorname{TV}(p_i^\gamma,R_i^i)=x$。

若 $j=i+2$，允许把 $j$ 提升为这个整数代表元，窗口前两位在截取段末尾。
代入 $t=n-2,n-1,0$ 给

$$
(V_i,V_{i+1},V_{i+2})
=(u_{i+(r+1)n},u_{i+1+(r+1)n},0).
\tag{21.6}
$$

$r\mapsto r+1\bmod m$ 保持均匀相位，故这正是原窗口律只把右端抹零的
推前。它只将 $001\mapsto000$、$101\mapsto100$，离开与进入的模式集合
不相交，移动总质量 $y$，所以
$\operatorname{TV}(p_i^\gamma,R_i^{i+2})=y$。
相位平移解释了跨切口的右端情形，不能在固定 $r$ 下直接把它写成原窗口。

若 $j=i+1$，代入 $t=n-1,0,1$ 给

$$
(V_i,V_{i+1},V_{i+2})
=(u_{i+(r+1)n},0,u_{i+2+rn}).
\tag{21.7}
$$

记其律为 $c_i=R_i^{i+1}$。中位总为零，左、右端边缘分别仍为 $x,y$，
因为对左端的 $r+1$ 仍遍历全部相位，而右端本来如此。
但两个端点来自不同相位，(21.7) 的联合配对可以不同于 (21.2)，
所以不把 $c_i$ 当作原窗口简单抹去中位的律。

对任意边缘为 $x,y$ 的两个指示变量，容斥给同时为一的概率至少为
$x+y-1$，并且概率非负。因此原窗口和中位切口窗口都满足

$$
p_i^\gamma(101)\ge a,\qquad c_i(101)\ge a,\qquad
a=\max(0,x+y-1).
\tag{21.8}
$$

在原窗口中，两端同时为一时 no11 支持迫使中位为零；
在 $c_i$ 中中位按构造已为零。这说明容斥下界确是同一个 $101$ 原子的
共有质量，而非只在不同事件上得到相同数值。
对两个概率向量 $b,d$，恒等式

$$
\operatorname{TV}(b,d)=1-\sum_{\sigma\in\Sigma}\min(b(\sigma),d(\sigma))
$$

由 $|b-d|=b+d-2\min(b,d)$ 求和即得。
所以 $\operatorname{TV}(p_i^\gamma,c_i)\le1-a$。

对 $j$ 的均匀混合给

$$
\widetilde p_i^\gamma
=\frac{n-3}{n}p_i^\gamma+\frac1n(R_i^i+c_i+R_i^{i+2}).
\tag{21.9}
$$

三角不等式或 TV 的凸性于是给

$$
\begin{aligned}
\operatorname{TV}(p_i^\gamma,\widetilde p_i^\gamma)
&\le\frac{x+y+1-\max(0,x+y-1)}n\\
&\le\frac2n.
\end{aligned}
\tag{21.10}
$$

最后一步分为 $x+y\le1$ 时分子 $x+y+1\le2$，以及 $x+y\ge1$ 时分子
恰为二。全部 $i$ 用的是同一来源 $P^\gamma$，没有逐窗分别选择来源。

最终取 $P=\sum_\gamma\lambda_\gamma P^\gamma$，仍是原 $n$ 位合法字上的
概率律，边缘为 $\widetilde p_i=\sum_\gamma\lambda_\gamma\widetilde p_i^\gamma$。
使用同一归一化权重和 TV 凸性，

$$
\operatorname{TV}(p_i,\widetilde p_i)
\le\sum_\gamma\lambda_\gamma
\operatorname{TV}(p_i^\gamma,\widetilde p_i^\gamma)
\le\frac2n\sum_\gamma\lambda_\gamma=\frac2n.
$$

这完成同时逐窗的结论。$101$ 的共有质量把三个受影响切口的粗界 $3/n$
改进为 $2/n$；没有隐藏地假定中位切口保留联合律。
(21.3) 是概率来源空间上的数学操作，把切口位置零不自动给原生执行者
提供免费 reset、控制权限或物理实现。证毕。

## 22. 奇数环的准确最坏距离与达到来源

**定理 22.1（所有奇数环的常数二锐性）。** 对每个奇数
$n=2k+1\ge5$，

$$
\max_{p\in\mathscr L_n}\Delta_n(p)=\frac2n.
\tag{22.1}
$$

局部严格交替律

$$
p_i^{\mathrm{alt}}=\frac12(0,0,1,0,1)
\tag{22.2}
$$

达到这个最大距离；字 $(10)^k0$ 的均匀标号旋转律给它的一个最近来源。

证明。对 (22.2)，前两位与后两位的律都为
$(0,1/2,1/2)$（按 $00,01,10$ 顺序），所以完整二位重叠相容。
取每窗测试

$$
g(010)=g(101)=1,\qquad g(000)=g(100)=g(001)=0.
\tag{22.3}
$$

该局部数据每窗分数一，故 $\langle g,p^{\mathrm{alt}}\rangle=n$。
对确定合法字，若无占位，即字 $0^n$，分数为零；它是长度 $n$ 的全零字，
不是长度零的字。若有 $K>0$ 个一，记长至少二的零间隙数为 $B$。
每个一作为中位恰给一个 $010$；每个长一的零间隙恰给一个 $101$，所以

$$
N_{010}=K,\qquad N_{101}=K-B,\qquad F_g(u)=2K-B.
\tag{22.4}
$$

每个一后至少一个零，故 $2K\le n$，即 $K\le k$。
若 $B=0$，所有间隙长一，得到 $n=2K$ 为偶数，矛盾。因此非全零情形
$B\ge1$，从而 $F_g(u)\le2k-1=n-2$。
全零分数零也不超过 $n-2$。字 $(10)^k0$ 有 $K=k$，一段长二零间隙和
$k-1$ 段长一零间隙，故 $B=1$，达到上界。因此

$$
H_n(g)=n-2,\qquad
\Delta_n(p^{\mathrm{alt}})\ge\frac{n-(n-2)}n=\frac2n.
\tag{22.5}
$$

再计算达到修补。$(10)^k0$ 中没有长三零段，所以 $N_{000}=0$；
唯一长二间隙给 $N_{100}=N_{001}=1$；由 (22.4) 得
$N_{010}=k,N_{101}=k-1$。五个计数之和为 $2k+1=n$。
均匀选择 $n$ 个标号旋转后，每个固定窗口的律为

$$
\widetilde p=\left(0,\frac1n,\frac kn,\frac1n,\frac{k-1}{n}\right).
\tag{22.6}
$$

它与 (22.2) 的绝对坐标差依次为
$0,1/n,1/(2n),1/n,3/(2n)$，故

$$
\operatorname{TV}(p_i^{\mathrm{alt}},\widetilde p)
=\frac12\left(\frac1n+\frac1{2n}+\frac1n+\frac3{2n}\right)=\frac2n.
\tag{22.7}
$$

这对每一窗口都相同，给 (22.5) 的上界并证明达到。
对任意 $p\in\mathscr L_n$，定理 21.1 已给每窗同时 $2/n$，因而平均距离
$\Delta_n(p)\le2/n$。与 (22.2) 的达到例合并得 (22.1)。证毕。

**推论 22.2（逐窗上界与平均下界的量词）。** 定理 21.1 对每个 $n\ge5$
都给一个来源同时控制每窗；定理 22.1 在每个奇数 $n$ 给一份局部族，使
所有来源的平均误差至少 $2/n$，因而不能用更小常数统一控制每窗。
这不是说对每个候选来源的每个窗口误差都至少 $2/n$。
偶数环仍有定理 21.1 的上界，但 (22.2) 可由交替字实现，不能用于证明
偶数环的锐性，(22.1) 不对偶数 $n$ 作等号主张。
对任意大的奇数环，(22.5) 的严格违例仍在，而归一化分离量 $2/n$ 趋零；
因此以固定局部 TV 精度判断时，这族精确不可实现数据与真实来源的距离趋零。
证明。前两句分别是 (21.1)、(22.5) 和平均值不超过最大值。
偶数 $n$ 的交替字两相位均匀混合恰给 (22.2)；最后一句由
(22.5)–(22.7) 的精确值及 $2/n\to0$ 得到。证毕。

## 23. 任意估计窗口律的稳健违例与距离稳定性

**定理 23.1（带 TV 误差余量的严格反证书）。** 设
$p,\widehat p\in\mathscr P_n$，并有另行建立的误差界

$$
\operatorname{TV}(\widehat p_i,p_i)\le\varepsilon_i,\qquad
\overline\varepsilon=\frac1n\sum_i\varepsilon_i.
\tag{23.1}
$$

两份族均不必先局部相容。则对任意 $f\in[0,1]^{5n}$，

$$
\left|\frac1n\langle f,\widehat p-p\rangle\right|
\le\overline\varepsilon,
\tag{23.2}
$$

从而

$$
\frac{\langle f,\widehat p\rangle-H_n(f)}n>
\overline\varepsilon\quad\Longrightarrow\quad p\notin\mathscr C_n.
\tag{23.3}
$$

证明。对单窗，(19.3) 给
$\langle f_i,\widehat p_i-p_i\rangle\le\operatorname{TV}(\widehat p_i,p_i)$。
交换两份律也给相反数的同一上界，故绝对值至多 $\varepsilon_i$。
求和并用三角不等式得到 (23.2)。因此

$$
\frac{\langle f,p\rangle-H_n(f)}n
\ge\frac{\langle f,\widehat p\rangle-H_n(f)}n-\overline\varepsilon>0.
$$

定理 17.3 即排除 $p\in\mathscr C_n$。严格大于不能改为大于等于，
因为零余量可以落在支撑超平面上。
若 (23.1) 只在某个已证明概率至少为 $1-\eta$ 的事件上成立，
上述排除结论就在同一事件上成立；这份事件概率须来自取得模型，
不由代数测试自行生成。证毕。

**定理 23.2（闭合距离对平均 TV 是一 Lipschitz）。** 对任意
$p,\widehat p\in\mathscr P_n$，

$$
|\Delta_n(\widehat p)-\Delta_n(p)|
\le d_n(\widehat p,p)
\le\overline\varepsilon
\quad\text{若 (23.1) 成立}.
\tag{23.4}
$$

证明。任取 $r\in\mathscr C_n$，逐窗 TV 三角不等式给
$d_n(\widehat p,r)\le d_n(\widehat p,p)+d_n(p,r)$。
对 $r$ 取最小值得
$\Delta_n(\widehat p)\le d_n(\widehat p,p)+\Delta_n(p)$。
交换 $p,\widehat p$ 得反向差的同一界，合并即得第一式。
对 (23.1) 求平均得第二式。
所以即使估计族因误差而违反重叠等式，也能直接代入距离和测试定理，
无须先将其投影到 $\mathscr L_n$。证毕。

**定义与适用边界 23.3（读数、共同来源和操作的独立前提）。**
符号 $p_i$ 表示概率模型，(23.1) 表示另行建立的取得精度。
一个真实测量协议若要应用 (23.3)，还须说明各窗口数据对应哪一份实际来源，
能否在同一来源条件下重复采样、样本如何产生、误差事件如何成立。
这些条件与计算给定测试的数学上界不同。有限样本不会自动给任意实概率的
精确值，小支持来源也不自动赋予任何采样或控制权限。
同理，(21.3) 的置零构造与其代价不包含原生操作可行性或资源最优性的断言。

## 24. 齐次整除供应不能替代带标号的闭合检验

**命题 24.1（六位异质族仍可局部相容而不闭合）。** 在 $n=6$，置

$$
q_i=\begin{cases}1/2,&i\text{ 为偶数},\\0,&i\text{ 为奇数},\end{cases}
\qquad\kappa_i=0\quad\text{对所有 }i.
\tag{24.1}
$$

由 (14.8) 得

$$
p_i=\begin{cases}
(0,1/2,0,1/2,0),&i\text{ 为偶数},\\
(1/2,0,1/2,0,0),&i\text{ 为奇数}.
\end{cases}
\tag{24.2}
$$

这份族在 $\mathscr L_6\setminus\mathscr C_6$。

证明。两类五项都非负且和一，按 (14.8) 的逆向论证，它们完整重叠相容。
若有全局来源，三个位点 $0,2,4$ 的占据事件边缘概率各为 $1/2$。
由于 $\kappa_0=\kappa_2=\kappa_4=0$，任意两个事件同时发生的概率为零。
有限个零概率事件的并仍为零，所以几乎处处三个偶数位至多一个为一，
得到 $U_0+U_2+U_4\le1$ 几乎处处。但其期望为 $3/2>1$，矛盾。
这直接排除共同六位来源。

供应卷 §25 的 $6\mid n$ 全可实现结论要求所有窗口使用同一个齐次律。
(24.2) 保留位置依赖，所以没有满足那个前提。该反例只区分齐次与异质
量词，不计算偶数环的最坏 TV 距离。证毕。

## 25. 正反证书、修补与已有方法的精确对应

**定理 25.1（固定来源域中的闭合等价与定量边界）。** 对
$n\ge5,p\in\mathscr P_n$，以下条件等价：

$$
\Gamma_n(p)\ne\varnothing
\quad\Longleftrightarrow\quad
p\in\mathscr C_n
\quad\Longleftrightarrow\quad
\text{存在 (16.1)–(16.4) 的同锚非负流}
\quad\Longleftrightarrow\quad
\langle f,p\rangle\le H_n(f)\ \forall f\in[0,1]^{5n}.
\tag{25.1}
$$

同时，$\Delta_n(p)$ 等于 (19.2) 的最大归一化违例；若进一步
$p\in\mathscr L_n$，存在一个原长度来源同时满足每窗 $2/n$ 的修补界；
对奇数 $n$，$\mathscr L_n$ 上的最大平均修补量恰为 $2/n$。
四角系数 $J_i$ 通过 (15.3) 将隐藏联合坐标接入这些全局测试。

证明。前两项由 (14.4)–(14.5) 同义；同锚流等价由定理 16.2 的两向路径
恢复给出；全部测试等价由定理 17.3 的严格分离给出。
定理 19.2 适用于所有概率族，定理 21.1 在局部相容前提下给出实际逐窗
修补来源，定理 22.1 给奇数域的平均下界与达到例。
公式 (15.3) 在可实现与仅局部相容两种情形都已直接推导，因此没有在
测试输入中偷用待判定的全局来源。证毕。

**数学引文与归属 25.2。** 各项已有供应在上述推导中的作用如下。

| 来源 | 已有结果的范围 | 本文使用的对应 |
| --- | --- | --- |
| 本卷 §§1、5、7 及接口 F | 五态反解、四角读出、指定三元边缘的耦合问题 | $(X,Y,Z,\kappa)=(q_i,q_{i+2},q_{i+1},\kappa_i)$，$\Gamma_n(p)$ 保持原标号来源 |
| [接缝供应卷 §§21–22](AURIC_FIB_SEAMS_CYCLES_ARITHMETIC_BOUNDARY_RECONSTRUCTION.md) | 位置分层守恒流、长度 $mn$ 的简单圈及周期提升 | (18.3) 保留 $m\alpha$ 的混合权重；(16.5) 要求原长度同锚，(21.3) 将每个成分修回原 $n$ 位 |
| 同卷 §§23–26 | 齐次纤维、间隙计数和固定均值五环 TV 投影 | (20.5) 以覆盖所有来源的测试把同一候选提升为不固定均值的最优修补；(24.2) 区分齐次量词 |
| 同卷 §27 | 普通路径权重迹、给定边缘与乘积来源的区别 | (17.1) 使用最大—加法评分，(20.3) 的全正律显示普通支持迹不足 |
| [Goldstein–Kuna–Lebowitz–Speer，arXiv:1508.04448v2，Theorems 6、8](https://arxiv.org/pdf/1508.04448v2) | 单个局部平移一致块律的 de Bruijn 圈分解和通用环长 | 使用经典扣除正流方法；保留 no11 的三状态、位置层和原长度合同 |
| [Karp，UCB/ERL M77/47，Theorem 1](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1977/Archive/ERL-m-77-47.pdf) | 强连通图的最小平均圈公式，取负权得最大版本 | 局部目标按基础圈计分，是每边最大平均权的 $n$ 倍；三圈上限另由简单分层圈证明 |
| [Sion，On General Minimax Theorems，Theorem 3.4](https://msp.org/pjm/1958/8-1/pjm-v8-n1-p14-s.pdf) | 紧凸域、准凹准凸及相应上下半连续条件下的极小极大等式 | $K=[0,1]^{5n}$ 与 $\mathscr C_n$，连续双仿射配对满足全部条件，最大值另由连续性达到 |

流分解、有限凸分离、Carathéodory 消元、动态规划、最大平均圈和极小极大
等式均是已有工具。这里的具体推导是这些工具在带标号五模式、指定原周期
和隐藏坐标上的组合，不把一般方法、坐标运输或综合表达列为全球新颖性。
这些结论的证明对象是明确给出的有限概率空间；物理解释、原生控制、
实际取得、证书发现和位复杂度各需其自身的对象与假设。

## 追加锚（本行以下为增补区）


## 26. 固定标号原环上的最坏平均闭合缺陷

**定义与供应 26.1（同一个来源域与五模式坐标）。** 固定整数 $n\ge5$，
所有位置属于 $\mathbb Z_n$，第 $i$ 个三位窗口读取
$(U_i,U_{i+1},U_{i+2})$。沿用本卷定义 14.1 的模式顺序

$$
\Sigma=(000,100,010,001,101)
\longleftrightarrow
(F[\mathrm{null}],F[1],F[2],F[3],F[1,3]).
\tag{26.1}
$$

每窗给定非负且和一的向量 $p_i$，在非法模式上延为零。局部可行集是

$$
\mathscr L_n=\left\{p\in\operatorname{Prob}(\Sigma)^n:
\sum_{a\in\{0,1\}}p_i(abc)
=\sum_{d\in\{0,1\}}p_{i+1}(bcd)
\quad\forall i,b,c\right\}.
\tag{26.2}
$$

这里匹配完整二位重叠边缘，包括恒为零的 $11$ 项。真实来源域仍然是

$$
B_n^{\mathrm{cyc}}
=\{u\in\{0,1\}^{\mathbb Z_n}:u_iu_{i+1}=0\quad\forall i\},
\qquad
\mathscr C_n=\left\{p:
\exists P\in\operatorname{Prob}(B_n^{\mathrm{cyc}}),\
p_i(\sigma)=\sum_uP(u)\mathbf1\{(u_i,u_{i+1},u_{i+2})=\sigma\}
\right\}.
\tag{26.3}
$$

同一份 $P$ 必须同时给出全部窗口，故 $\mathscr C_n\subseteq\mathscr L_n$。
没有附加旋转不变性、Markov 性、有理权重或“最小周期恰为 $n$”条件；
字的最小周期可以整除 $n$。特别是 $0^n$ 始终属于来源域。
延长成 $2n$、$3n$ 或 $6n$ 位的来源只可作为分解材料，不能替代 (26.3)。

直接由局部数据定义

$$
q_i=p_i(100)+p_i(101),\qquad \kappa_i=p_i(101).
\tag{26.4}
$$

本卷命题 14.2 给出完整重叠下的反解

$$
p_i=(1-q_i-q_{i+1}-q_{i+2}+\kappa_i,
q_i-\kappa_i,q_{i+1},q_{i+2}-\kappa_i,\kappa_i).
\tag{26.5}
$$

这一步无需假设共同来源存在。原有金字塔的坐标次序是左、右、中，
而印刷位序是左、中、右，所以本卷 §§1、14 的参数对应严格为

$$
(x,z,y)=(U_i,U_{i+1},U_{i+2}),\qquad
(X_i,Y_i,Z_i,\kappa_i)=(q_i,q_{i+2},q_{i+1},\kappa_i).
\tag{26.6}
$$

$F[1],F[2],F[3]$ 的数值输出名分别是 $[2],[3],[5]$，不把它们当作环位置。
局部隐藏纤维的区间为
$\max(0,q_i+q_{i+1}+q_{i+2}-1)\le\kappa_i\le\min(q_i,q_{i+2})$；
这只保证 (26.5) 非负，尚不保证 (26.3)。

**定义与推导 26.2（平均距离、连续性与达到）。** 使用定义 19.1 的同一距离

$$
\operatorname{TV}(a,b)=\frac12\sum_{\sigma\in\Sigma}|a(\sigma)-b(\sigma)|,
\qquad d_n(p,r)=\frac1n\sum_{i\in\mathbb Z_n}\operatorname{TV}(p_i,r_i),
\qquad \Delta_n(p)=\min_{r\in\mathscr C_n}d_n(p,r),
\tag{26.7}
$$

并定义最坏平均闭合缺陷

$$
\mathfrak E_n=\max_{p\in\mathscr L_n}\Delta_n(p).
\tag{26.8}
$$

修补域是整个 $\mathscr C_n$，允许改变 $q_i$ 和 $\kappa_i$；固定均值后的
最近点问题是另一个问题。$d_n$ 是有限概率向量族上的度量。
$\mathscr L_n$ 是有限个闭线性条件与有限单纯形乘积的交，非空、紧且凸。
$\mathscr C_n$ 是有限集合 $\{v(u):u\in B_n^{\mathrm{cyc}}\}$ 的凸包，
也非空、紧且凸，其中 $v(u)$ 是确定字的全部窗口指示向量。
因此对每个 $p$，连续函数 $d_n(p,\cdot)$ 在 $\mathscr C_n$ 上达到最小值。

在取 (26.8) 的最大值之前还须验证 $\Delta_n$ 连续。
对任意 $p,p'$ 和任意 $r\in\mathscr C_n$，TV 三角不等式给
$d_n(p,r)\le d_n(p,p')+d_n(p',r)$。对 $r$ 取最小，再交换 $p,p'$，得到

$$
|\Delta_n(p)-\Delta_n(p')|\le d_n(p,p').
\tag{26.9}
$$

这正是本卷定理 23.2 的一 Lipschitz 性，故 $\Delta_n$ 在紧集
$\mathscr L_n$ 上连续并达到最大。最近点的达到也说明
$\Delta_n(p)=0$ 当且仅当 $p\in\mathscr C_n$。
下面要计算的正是这个保持原标号来源域的最大值。

## 27. 归一化分层简单圈与真实来源的凸混合

**供应及推导 27.1（从守恒流到三种圈长）。** 沿用定义 16.1 和定理 18.1，
接缝状态按 $\mathcal S=(00,01,10)$ 排列，完整边字典如下。

| 模式 | 名称 | 起状态 | 终状态 |
| --- | --- | --- | --- |
| $000$ | $F[\mathrm{null}]$ | $00$ | $00$ |
| $100$ | $F[1]$ | $10$ | $00$ |
| $010$ | $F[2]$ | $01$ | $10$ |
| $001$ | $F[3]$ | $00$ | $01$ |
| $101$ | $F[1,3]$ | $10$ | $01$ |

将每个接缝加上原位置标签，得到 $3n$ 个顶点 $(i,s)$，边
$(i,ab)\to(i+1,bc)$ 的质量为 $p_i(abc)$。
顶点 $(i,bc)$ 的入流是 $\sum_a p_{i-1}(abc)$，出流是
$\sum_dp_i(bcd)$。所以 (26.2) 正是逐顶点守恒；归一化则是每层边质量一。

本卷 §2 的单窗二部运输图把左、右状态视作不同顶点，固定的是其两端边缘；
它的四角方向是有符号的零边界差流。此处先把相邻窗口的共同接缝识别，
再要求非负守恒流，因此不是把那个有符号 incidence 核向量当作一份概率来源。
整张分层图的边质量总和为 $n$，也不是全图总质量一。
这些区别决定以下归一化因子。

为完整消费本卷 (18.2)–(18.3) 及
[接缝供应卷定理 21.4、22.2](AURIC_FIB_SEAMS_CYCLES_ARITHMETIC_BOUNDARY_RECONSTRUCTION.md)，
给出分解步骤。非零非负守恒流中，从一条正边开始沿正边前进；到达顶点
有正入流，故必有正出流。有限顶点集使路径重复，首次重复之间是简单有向圈。
从圈上每条边扣去其当前最小质量 $\alpha>0$，所得流仍非负、守恒，
并至少少一条正边。有限次后得到

$$
p=\sum_{\gamma}\alpha_\gamma\mathbf1_\gamma,
\qquad \alpha_\gamma>0.
\tag{27.1}
$$

每走一条边层号增加一，因此简单圈长度是 $m_\gamma n$。
它在每层出现 $m_\gamma$ 次，而每层只有三个顶点，简单性给
$m_\gamma\in\{1,2,3\}$。对任何一层求边质量和，得

$$
\sum_\gamma m_\gamma\alpha_\gamma=1,
\qquad p^\gamma=\frac{\mathbf1_\gamma}{m_\gamma},
\qquad \lambda_\gamma=m_\gamma\alpha_\gamma,
\qquad p=\sum_\gamma\lambda_\gamma p^\gamma.
\tag{27.2}
$$

每个 $p^\gamma$ 在每层分别有一、二、三条边，各边质量分别为
$1,1/2,1/3$。因此概率混合权是 $m_\gamma\alpha_\gamma$，
不是原始扣流系数 $\alpha_\gamma$；也不是把圈边统一除以圈长
$m_\gamma n$ 后直接当作每窗概率。

按重叠状态读出圈的周期字 $w$，长度 $m_\gamma n$，使第 $a$ 个位置
的原层号为 $a\bmod n$。同层相位均匀取样给

$$
p_i^\gamma(\sigma)=\frac1{m_\gamma}
\sum_{h=0}^{m_\gamma-1}
\mathbf1\{(w_{i+hn},w_{i+1+hn},w_{i+2+hn})=\sigma\}.
\tag{27.3}
$$

$w$ 的下标按 $m_\gamma n$ 取模；不能将这一同层平均换成任意旋转平均。
若 $m_\gamma=1$，$w$ 本身就在 $B_n^{\mathrm{cyc}}$ 中，故修补量为零。

对于每个成分，只要构造一份实际 $n$ 位来源 $P^\gamma$，其窗口族为
$\widetilde p^\gamma$，就可在相同来源域取
$P=\sum_\gamma\lambda_\gamma P^\gamma$。边缘是相同权重的混合，逐坐标三角不等式给

$$
\begin{aligned}
\operatorname{TV}\!\left(\sum_\gamma\lambda_\gamma p_i^\gamma,
\sum_\gamma\lambda_\gamma\widetilde p_i^\gamma\right)
&\le\sum_\gamma\lambda_\gamma
\operatorname{TV}(p_i^\gamma,\widetilde p_i^\gamma),\\
\Delta_n(p)&\le
\sum_\gamma\lambda_\gamma\frac1n\sum_i
\operatorname{TV}(p_i^\gamma,\widetilde p_i^\gamma).
\end{aligned}
\tag{27.4}
$$

所以修补这三类成分足以控制任意局部相容数据，且混合确实由同一份真实
来源实现。相同论证也给 $\Delta_n$ 的凸性：为各成分选择达到的最近来源
再混合即可。它没有要求原流的分解唯一，也没有把某次分解出现长圈视为
原流不可实现的充要判据。

这里使用的是经典非负守恒流圈分解。Goldstein–Kuna–Lebowitz–Speer，
*Translation invariant extensions of finite volume measures*，
[arXiv:1508.04448v2，§4.1 Theorem 6](https://arxiv.org/pdf/1508.04448v2)，
将单个局部平移一致二进制块律与 de Bruijn 图守恒流对应，并证明简单圈的
归一化律给其极点与凸组合。该文的 $X_k$ 是 $k+1$ 位块，$G_k$ 有 $2^k$
个状态；其全图概率归一化与 (27.2) 的每层归一化不同。
§4.2 Theorem 8 的通用环长为 $\operatorname{lcm}\{1,\ldots,2^k\}$，
$k=2$ 时为 $12$。本题保留 no11 的三状态及位置层，且固定原长度 $n$，
不以那个通用长度或接缝供应卷的六重提升替代原长度修补。

## 28. 两圈成分的准确分类与保相位切口

**定理 28.1（普通两圈准确为 $1/n$，交替例外准确为 $2/n$）。**
设 $p=p^\gamma$ 是分层图中一条长度 $2n$ 的简单圈的归一化流。
若 $p$ 不是每窗都等于 $\frac12(0,0,1,0,1)$ 的严格交替律，则

$$
\Delta_n(p)=\frac1n.
\tag{28.1}
$$

严格交替例外只在奇数 $n$ 上形成这样的简单两圈，其准确距离是 $2/n$。

证明。按 (27.3) 恢复合法 $2n$ 周期字 $w$。同一层的两次接缝
$(w_j,w_{j+1})$ 和 $(w_{j+n},w_{j+n+1})$ 必须不同，否则重复了分层顶点。
先设某个 $j$ 有 $w_j=w_{j+n}$。它们不能同为一：no11 会使两次接缝
都为 $10$，违反简单性。故必有一个同层双零

$$
w_j=w_{j+n}=0.
\tag{28.2}
$$

保留原标签，明确定义两份 $n$ 位字

$$
v^{(h)}_{j+t\bmod n}=w_{j+hn+t\bmod 2n},
\qquad h\in\{0,1\},\quad 0\le t<n.
\tag{28.3}
$$

这里 $j$ 是原环的切口位置，不把截得的片段重新安放到标签零。
每段内部相邻位来自合法原字，首位是零，因此末位接回首位仍满足 no11；
两字确属 $B_n^{\mathrm{cyc}}$。取它们的等权来源
$\frac12\delta_{v^{(0)}}+\frac12\delta_{v^{(1)}}$。

不包含切口的窗口仍在某个原片段内连续，必要的相位平移
$h\mapsto h+1\bmod2$ 不改变均匀相位律。切口为左端或右端的窗口，
共同零位也没有改变；右端情形只需对原相位作同样重编号。
因此唯一可能改变的是原标签 $i=j-1$ 的中位切口窗口。
令

$$
a_h=w_{j-1+hn},\qquad b_h=w_{j+1+hn}.
$$

在层 $j-1$，两次接缝为 $(a_0,0),(a_1,0)$，简单性迫使 $a_0\ne a_1$；
在层 $j$，两次接缝为 $(0,b_0),(0,b_1)$，同理 $b_0\ne b_1$。
原中位窗口及修补后窗口分别是等权的

$$
(a_h,0,b_h),\qquad(a_{h+1},0,b_h),\qquad h\bmod2.
\tag{28.4}
$$

两个二元端点的边缘都为 $1/2$。原配对若是同现，则两个模式为
$000,101$；若是反现，则为 $100,001$。交换左端相位恰将这两种配对互换。
两个支持集合互不相交，所以这一个窗口的 TV 恰为一，其余为零，给
$\Delta_n(p)\le1/n$。

为证反向，令 $f_i(\sigma)$ 在原圈第 $i$ 层的两条支持边上为一，其余为零。
局部总分为 $\langle f,p\rangle=n$。若某个 $n$ 位合法字每窗都得一分，
它就在原圈支持内给出长度恰为 $n$ 的闭走法。但一条简单 $2n$ 有向圈中，
每个支持顶点只有唯一后继，回到原顶点的正步数必须是 $2n$ 的倍数。
不存在这样的 $n$ 步闭走法。故任一真实字至少失去一分，
$F_f(u)\le n-1$，混合后的来源也满足这个界。

对任意两份概率律 $a,b$ 和 $0\le f\le1$，令 $d=a-b$；
$\sum d=0$，所以 $\sum f d\le\sum_{d>0}d=\operatorname{TV}(a,b)$。
逐窗相加后，对所有 $\widetilde p\in\mathscr C_n$ 有

$$
1\le\langle f,p\rangle-\langle f,\widetilde p\rangle
\le\sum_i\operatorname{TV}(p_i,\widetilde p_i).
\tag{28.5}
$$

于是 $\Delta_n(p)\ge1/n$，得准确等式。事实上 (28.3) 的两字仅在
$j-1$ 窗失分，各自得 $n-1$ 分，所以该测试的真实上界也准确为 $n-1$。

剩余情形是每个同层位置都相反，即
$w_{j+n}=1-w_j$ 对所有 $j$ 成立。平移后的 $w$ 仍是合法字，故 $w$ 和
它的补码都不含 $11$。补码不含 $11$ 等价于 $w$ 不含 $00$，所以 $w$
必须严格交替。移动 $n$ 位翻转位值要求 $n$ 为奇数。
相位均匀给每窗的 $010,101$ 各一半。反向在奇数 $n$，严格交替字的
两次同层接缝分别为 $01,10$，确无重复，形成简单 $2n$ 圈。
本卷定理 22.1 给其准确值 $2/n$；为完整用于奇偶主定理，§30.1 将保留
其全零分支、计数下界和实际旋转修补的全部推导。证毕。

**命题 28.2（五环切口的原标签实例）。** 在 $n=5$，取

$$
w=0000010101,\qquad j=1.
$$

其每层两次接缝不同，故是简单两圈；(28.3) 给

$$
v^{(0)}=10000,\qquad v^{(1)}=00101.
\tag{28.6}
$$

下面每一格列两次等权抽样所得模式，次序本身不影响概率律。

| 原窗口标签 $i$ | 原两圈的模式 | 两个修补字的模式 |
| ---: | --- | --- |
| $0$ | $000,101$ | $100,001$ |
| $1$ | $000,010$ | $000,010$ |
| $2$ | $000,101$ | $000,101$ |
| $3$ | $001,010$ | $001,010$ |
| $4$ | $010,100$ | $010,100$ |

证明。逐层接缝分别为
$(00,10),(00,01),(00,10),(00,01),(01,10)$，每对不同，且原字无相邻一。
从 $j=1$ 读出的片段为 $00001$ 和 $01010$，但这些位依次放在
原标签 $1,2,3,4,0$，于是给 (28.6)。逐窗读取即得表，TV 仅在标签零为一。
若将片段重新放在标签 $0,1,2,3,4$，便旋转了所要匹配的数据，不能据此
计算原来带标号族的误差。证毕。

## 29. 三圈成分的两种转移与原长度修补

**定理 29.1（三圈局部转移及总误差 $4/3$ 的上界）。**
若 $p$ 是一条简单 $3n$ 圈的归一化流，则每层窗口律只能是

$$
p^A=\frac13(1,0,1,0,1),\qquad
p^B=\frac13(0,1,1,1,0),
\tag{29.1}
$$

并存在实际 $n$ 位来源 $\widetilde p\in\mathscr C_n$ 使

$$
\sum_i\operatorname{TV}(p_i,\widetilde p_i)\le\frac43,
\qquad \Delta_n(p)\le\frac4{3n}.
\tag{29.2}
$$

证明。简单圈在每层必须访问全部三个状态各一次，每层的出边与下一层的
入边因而形成置换。状态 $01$ 只有后继 $10$；其余两个状态 $00,10$
必须分别映到 $00,01$，恰有以下两种可能：

$$
\begin{aligned}
A &:00\mapsto00,\quad01\mapsto10,\quad10\mapsto01,\\
B &:00\mapsto01,\quad01\mapsto10,\quad10\mapsto00.
\end{aligned}
\tag{29.3}
$$

按 $(00,01,10)$ 的行出发、列到达约定，它们的矩阵为

$$
A=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix},\qquad
B=\begin{pmatrix}0&1&0\\0&0&1\\1&0&0\end{pmatrix}.
\tag{29.4}
$$

每层每条所用边质量 $1/3$，逐边字典立即给 (29.1)。质量矩阵是
$A/3$、$B/3$，条件转移矩阵才是 $A$、$B$，两者不混用。
这些置换及局部律由
[接缝供应卷定理 22.3、命题 23.2](AURIC_FIB_SEAMS_CYCLES_ARITHMETIC_BOUNDARY_RECONSTRUCTION.md)
供应；其纤维参数 $s=3\kappa$ 分别为 $1,0$。
本卷 §4 的较早状态序为 $(00,10,01)$。若 $T_{\rm old}$ 是该次序的质量矩阵，
则本节矩阵是

$$
T_{\rm new}=J T_{\rm old}J^{\mathsf T},\qquad
J=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix}.
\tag{29.5}
$$

这只重排状态坐标，不改变边方向和原位置标签。

两种律的前后接缝边缘均为 $(1/3,1/3,1/3)$，并且

$$
X=Y=Z=\frac13,\qquad \kappa_A=\frac13,\quad\kappa_B=0,
\qquad p^A-p^B=\frac13(1,-1,0,-1,1).
\tag{29.6}
$$

因此它们的差恰沿本卷 §2 的四角隐藏方向，保留所有三均值与完整二位边缘。

以上是从一个给定简单 $3n$ 圈得到 A/B 形式的必要分类。
任意 A/B 排列虽然都局部相容，却未必形成单独的简单 $3n$ 圈。
若第 $i$ 层为 $R_i\in\{A,B\}$，按先 $R_0$ 后 $R_1$ 的作用次序置
$\pi=R_{n-1}\circ\cdots\circ R_0$。一个初态在 $\pi$ 下的长度 $\ell$
轨道，对应分层图的一条简单 $\ell n$ 圈，因为各层转移为双射。
故 $\pi$ 为恒等时是三个 $n$ 圈，为换位时是一个 $n$ 圈加一个 $2n$ 圈，
为三循环时才是一个 $3n$ 圈。特别地，偶数 $n$ 的全 A 排列有
$A^n=I$，并非简单三圈。

先处理至少一层为 A 的情形。选该层为 $i$，令其原中位标签为 $j=i+1$。
由 (27.3) 取对应的 $3n$ 周期字 $w$。使用本卷 (21.3) 的同一保标签构造，
但固定这个切口，定义三个实际 $n$ 位字

$$
v^{(h)}_{j+t\bmod n}=
\begin{cases}
0,&t=0,\\
w_{j+hn+t\bmod3n},&1\le t<n,
\end{cases}
\qquad h=0,1,2.
\tag{29.7}
$$

内部边来自原合法字，首位抹为零后首尾闭合合法，相邻两边也合法。
所以等权选择三个字给一份 $B_n^{\mathrm{cyc}}$ 上的概率律。

只有原标签 $j-2,j-1,j$ 的三个窗口可能改变。
其他窗口在某一截取段内连续；对 $h$ 的循环平移保持均匀相位，故其律不变。
在标签 $j$，新模式为 $(0,w_{j+1+hn},w_{j+2+hn})$，是原窗口左端抹零。
原左端为一的总质量恰 $1/3$；这份质量全部从左端为一的模式移入左端
为零的模式，二者不交，故此窗 TV 准确为 $1/3$。
在标签 $j-2$，新模式为

$$
(w_{j-2+(h+1)n},w_{j-1+(h+1)n},0).
\tag{29.8}
$$

对 $h+1$ 重编号后，是原窗口右端抹零。同理，移动的质量恰为 $1/3$，
此窗 TV 也准确为 $1/3$。

中位切口窗位于原标签 $j-1=i$，其新模式为

$$
(w_{j-1+(h+1)n},0,w_{j+1+hn}).
\tag{29.9}
$$

左右端来自相邻两段的不同相位，不能把它写成原窗口单纯抹去中位。
两端各自的边缘仍为 $1/3$。令 $t$ 是新窗口两端同时为一的概率，则
$0\le t\le1/3$，归一化与两端边缘迫使新律为

$$
c(t)=\left(\frac13+t,\frac13-t,0,\frac13-t,t\right).
\tag{29.10}
$$

原律是 $p^A$，五项差的绝对值依次为
$t,1/3-t,1/3,1/3-t,1/3-t$，故

$$
\operatorname{TV}(p^A,c(t))=\frac23-t,
\qquad
\sum_i\operatorname{TV}(p_i,\widetilde p_i)
=\frac13+\left(\frac23-t\right)+\frac13
=\frac43-t\le\frac43.
\tag{29.11}
$$

现在处理全 B 的简单三圈。其一圈返回置换是 $B^n$，所以简单三圈要求
$3\nmid n$；若 $3\mid n$，返回为恒等，图分为三个 $n$ 圈。
全 B 的窗口在 $100,010,001$ 上各为 $1/3$。
这些模式每三个连续位恰有一个一，沿合法重叠相减得到 $w_{a+3}=w_a$，
即原长圈是三周期的均匀相位来源。

若 $n=3a+1$，取实际 $n$ 位字

$$
z=(100)^a0.
\tag{29.12}
$$

它有 $a$ 个一；其 $a-1$ 个零间隙长二，剩下一段长三，包括跨切口的间隙。
故合法。每个一给一个 $010$，每个长间隙的两端各给一次 $100,001$，
唯一长三间隙内部给一次 $000$，没有长一间隙产生 $101$。
于是完整五模式次数为 $(1,a,a,a,0)$。均匀抽取 $n$ 个标号旋转，
每个固定窗口的律为这个向量除以 $n$，与 $p^B$ 的差为

$$
\left(\frac1n,-\frac1{3n},-\frac1{3n},-\frac1{3n},0\right),
\quad \operatorname{TV}=\frac1n\le\frac4{3n}.
\tag{29.13}
$$

若 $n=3a+2$，改取

$$
z=(100)^a10.
\tag{29.14}
$$

它有 $a+1$ 个一，$a$ 个长二零间隙及一个长一零间隙，跨末端的间隙也非空，
故合法。没有 $000$；长二间隙给 $N_{100}=N_{001}=a$，
每个一给 $N_{010}=a+1$，唯一长一间隙给 $N_{101}=1$。
完整次数是 $(0,a,a+1,a,1)$，总数为 $3a+2=n$。
均匀标号旋转后的逐窗律与 $p^B$ 的差为

$$
\left(0,-\frac2{3n},\frac1{3n},-\frac2{3n},\frac1n\right),
\quad \operatorname{TV}=\frac4{3n}.
\tag{29.15}
$$

这两种旋转平均合法，是因为目标全 B 律本来就与位置无关；它们仍然只使用
原 $n$ 位字。上述计数也与接缝供应卷 §24 的零间隙公式一致。
两种情形均给 (29.2)，完成证明。

本定理只给三圈成分的统一上界，并不分类每一个三圈成分的准确距离。
例如全 B 且 $n\equiv1\pmod3$ 已有更小的 $1/n$ 修补；
(29.15) 的等号是所列修补的 TV 值，不能单独推出它对所有来源最优。

## 30. 奇数交替成分的准确上下界

**供应与证明 30.1（交替例外的完整计数证书）。** 本卷定理 22.1 已给
奇数环的交替达到例；在定理 28.1 的两圈分类中使用的是同一结果。
为明确闭合距离的来源域与空占位分支，设 $n=2a+1\ge5$，并取

$$
p_i^{\mathrm{alt}}=\frac12(0,0,1,0,1),\qquad
f(010)=f(101)=1,\quad f(000)=f(100)=f(001)=0.
\tag{30.1}
$$

前后接缝律都为 $(0,1/2,1/2)$，故 $p^{\mathrm{alt}}\in\mathscr L_n$，
其测试总分为 $n$。

任取 $u\in B_n^{\mathrm{cyc}}$。若占位集合为空，则 $u=0^n$，全部窗口
为 $000$，分数为零。这里是长度 $n$ 的全零字；长度零的空字不在来源域内。
若有 $K>0$ 个一，沿环列出它们之间的 $K$ 段零间隙，每段长至少一。
令 $B$ 是长度至少二的零间隙数；它在本节是一个整数，不是置换 B。
每个一作为中位恰贡献一次 $010$，长一间隙恰贡献一次 $101$，所以

$$
N_{010}=K,\qquad N_{101}=K-B,
\qquad F_f(u)=2K-B.
\tag{30.2}
$$

每个一后至少一个零给 $2K\le n$，从而 $K\le a$。
若 $B=0$，全部间隙长一，必有 $n=2K$ 为偶数，与当前假设冲突。
因此 $B\ge1$，$F_f(u)\le2a-1=n-2$。全零字的分数零也不超过这个界。
实际字

$$
z=(10)^a0
\tag{30.3}
$$

有 $K=a$，恰一个长二间隙、其余 $a-1$ 个间隙长一，故达到 $n-2$。
于是确定字和它们的任意混合都具有准确最优分数

$$
H_n(f)=n-2.
\tag{30.4}
$$

有界测试的 TV 估计 (28.5) 因而给所有真实修补的下界

$$
\sum_i\operatorname{TV}(p_i^{\mathrm{alt}},\widetilde p_i)
\ge n-(n-2)=2.
\tag{30.5}
$$

反向使用 (30.3) 的均匀标号旋转律。字中没有三个连续零，故 $N_{000}=0$；
唯一长二间隙给 $N_{100}=N_{001}=1$；(30.2) 给
$N_{010}=a,N_{101}=a-1$。因此五模式次数和每窗律分别为

$$
(0,1,a,1,a-1),\qquad
\widetilde p_i=\left(0,\frac1n,\frac an,\frac1n,\frac{a-1}{n}\right).
\tag{30.6}
$$

旋转平均的理由是：对一个固定窗口，$n$ 个标号旋转使它依次读遍原字的
所有 $n$ 个窗口。即使某个字有短周期，仍按旋转抽样次数计概率。
这个来源的每窗绝对差为

$$
\left(0,\frac1n,\frac1{2n},\frac1n,\frac3{2n}\right),
$$

故 TV 为这些数之和的一半，即 $2/n$。与 (30.5) 合并，得到

$$
\Delta_n(p^{\mathrm{alt}})=\frac2n.
\tag{30.7}
$$

这完成两圈分类中交替例外的上下界，而非仅以圈长作猜测。
例如 $n=5$ 时字 $10100$ 的均匀旋转律为 $(0,1,2,1,1)/5$，
距交替律恰为 $2/5$；它的测试分数为 $3$，局部交替分数为 $5$。
偶数 $n$ 则可直接等权取 $(10)^{n/2},(01)^{n/2}$ 实现交替律，
故这一例外不能用于偶数下界。

## 31. 偶数极值：两处隐藏坐标变化与三字最优来源

**定理 31.1（均值全为 $1/3$ 的偶数达到例）。** 对每个偶数 $n\ge6$，取

$$
p_i^*=\begin{cases}
p^A,&0\le i\le n-3,\\
p^B,&i=n-2,n-1.
\end{cases}
\tag{31.1}
$$

则 $p^*\in\mathscr L_n$，各窗的完整前后接缝边缘都是三态均匀律，
$X_i=Y_i=Z_i=1/3$，且

$$
\Delta_n(p^*)=\frac4{3n}.
\tag{31.2}
$$

证明。由 (29.1) 逐项计算，A 的前接缝律为
$(p_{000}+p_{001},p_{010},p_{100}+p_{101})=(1,1,1)/3$，
后接缝律为 $(p_{000}+p_{100},p_{001}+p_{101},p_{010})$，也是同一向量；
B 同样如此。因此每个相邻窗口的完整重叠匹配。
每种律的三个单点均值也各为 $1/3$。

这里确实只改变两处隐藏坐标即可从真实来源离开 $\mathscr C_n$。
先给全 A 的真实基准：等权选择

$$
0^n,\qquad (10)^{n/2},\qquad (01)^{n/2}.
\tag{31.3}
$$

三个字在每个窗口恰给 $000,010,101$ 各一次，所以全部边缘为 $p^A$。
由 (26.5)，保持全部 $q_i=1/3$，只将
$\kappa_{n-2},\kappa_{n-1}$ 从 $1/3$ 降至零，就得到 (31.1)。
其余 $\kappa_i$ 完全不动；每个局部隐藏区间是 $[0,1/3]$，两个端点单独都合法。
在分层置换描述中，(31.1) 的返回为
$B\circ B\circ A^{n-2}=B^2$，所以这一特定排列也确实是简单三圈。
这与任意 A/B 排列都形成三圈的错误逆命题不同。

定义有界测试菜单

$$
f_i(abc)=\begin{cases}
\mathbf1\{a=c\},&0\le i\le n-3,\\
\mathbf1\{a\ne c\},&i=n-2,n-1.
\end{cases}
\tag{31.4}
$$

在 A 窗口三种模式的端点全部相同，故局部贡献一；在 B 窗口，
$100,001$ 的端点不同而 $010$ 的端点相同，贡献 $2/3$。
所以

$$
\langle f,p^*\rangle=(n-2)+\frac43=n-\frac23.
\tag{31.5}
$$

对任意确定字，步长二将位置分成两个环

$$
0\to2\to\cdots\to n-2\to0,
\qquad
1\to3\to\cdots\to n-1\to1.
\tag{31.6}
$$

每个环只有最后一条边要求两端不同，其余要求相同。沿环取异或，
每个顶点值出现两次，所以实际端点差的异或为零；测试期望的差向量却有
恰一个一，异或为一。因此每个环至少违反一条要求。
这在所有二元字上成立，尤其在 no11 合法字上成立，给
$F_f(u)\le n-2$。全零字在全部 A 位得分，在两个 B 位失分，准确取得 $n-2$。
故

$$
H_n(f)=n-2,
\qquad
\langle f,p^*\rangle-H_n(f)=\frac43.
\tag{31.7}
$$

由有界测试与 TV 的关系，任意真实来源都满足
$\Delta_n(p^*)\ge4/(3n)$。
下面的三份字给出相等的上界，不需要只由统一上界推知存在。

以相同概率 $1/3$ 选择

$$
\begin{aligned}
v^{(0)}&=1\,0^{n-1},\\
v^{(1)}&=00(10)^{n/2-1},\\
v^{(2)}&=00(01)^{n/2-1}.
\end{aligned}
\tag{31.8}
$$

第一字只有一个一，合法；后二字在标签 $0,1$ 都为零，其余位置严格交替。
内部无 $11$，末位接回标签零时也合法，故三字均在原 $B_n^{\mathrm{cyc}}$ 中。
以下列出所有位置的完整修补边缘 $\widetilde p_i$；五坐标仍按 (26.1)。

| 窗口标签 | 原律 $p_i^*$ | 三字混合的 $\widetilde p_i$ | $\widetilde p_i-p_i^*$ | TV |
| --- | --- | --- | --- | --- |
| $0$ | $(1,0,1,0,1)/3$ | $(1,1,0,1,0)/3$ | $(0,1,-1,1,-1)/3$ | $2/3$ |
| $1$ | $(1,0,1,0,1)/3$ | $(1,0,1,1,0)/3$ | $(0,0,0,1,-1)/3$ | $1/3$ |
| $2\le i\le n-3$ | $p^A$ | $p^A$ | $0$ | $0$ |
| $n-2$ | $p^B$ | $p^B$ | $0$ | $0$ |
| $n-1$ | $(0,1,1,1,0)/3$ | $(1,1,1,0,0)/3$ | $(1,0,0,-1,0)/3$ | $1/3$ |

逐行的模式来源如下：标签零的三字窗口分别为 $100,001,000$；
标签一分别为 $000,010,001$。对 $2\le i\le n-3$，第一字给 $000$，
后二字给 $010,101$，次序随 $i$ 奇偶交换。标签 $n-2$ 的三个窗口分别为
$001,100,010$；标签 $n-1$ 分别为 $010,000,100$。
这证明表中全部边缘，而非只核对单点均值。
因此

$$
d_n(p^*,\widetilde p)=\frac1n\left(\frac23+\frac13+\frac13\right)
=\frac4{3n}.
\tag{31.9}
$$

与 (31.7) 的下界相等，得到 (31.2) 和三字来源的最优性。证毕。

**命题 31.2（六位达到例的完整字证书）。** $n=6$ 时，(31.8) 为

$$
100000,\qquad001010,\qquad000101.
\tag{31.10}
$$

原局部族在窗口 $0,1,2,3$ 取 A，在窗口 $4,5$ 取 B。三字的逐窗模式如下。

| 标签 $i$ | $100000$ 的窗口 | $001010$ 的窗口 | $000101$ 的窗口 | 原律与混合律的 TV |
| ---: | --- | --- | --- | ---: |
| $0$ | $100$ | $001$ | $000$ | $2/3$ |
| $1$ | $000$ | $010$ | $001$ | $1/3$ |
| $2$ | $000$ | $101$ | $010$ | $0$ |
| $3$ | $000$ | $010$ | $101$ | $0$ |
| $4$ | $001$ | $100$ | $010$ | $0$ |
| $5$ | $010$ | $000$ | $100$ | $1/3$ |

证明。循环读取这三份明确的六位字得到表，每列权为 $1/3$。
其平均距离为 $2/9$。对应测试的局部分数为 $16/3$，真实上界为 $4$，
差为 $4/3$，除以六也给 $2/9$。故正来源与测试下界准确吻合。证毕。

## 32. 最坏闭合缺陷的精确奇偶定律

**定理 32.1（原环长平均 TV 的准确常数）。** 对全部 $n\ge5$，

$$
\boxed{
\mathfrak E_n=
\begin{cases}
\dfrac2n,&n\text{ 为奇数},\\[2mm]
\dfrac4{3n},&n\text{ 为偶数}.
\end{cases}}
\tag{32.1}
$$

证明。任意 $p\in\mathscr L_n$ 按 (27.2) 分成归一化简单圈，并使用相同
概率权重混合各自的原长度修补。单圈本身真实，代价零。
定理 28.1 与 §30.1 给两圈代价：普通类型准确为 $1/n$，
严格交替类型仅在奇数 $n$ 出现，准确为 $2/n$。
定理 29.1 给三圈代价至多 $4/(3n)$。

若 $n$ 为奇数，这些成分的修补量都不超过 $2/n$；若 $n$ 为偶数，
交替两圈例外不可能出现，全部成分的修补量都不超过 $4/(3n)$。
由 (27.4) 的 TV 凸性及 $\sum_\gamma\lambda_\gamma=1$，分别得到
对任意 $p$ 的两个统一平均上界。
奇数下界由 (30.7) 的局部交替律达到，偶数下界由定理 31.1 的 A/B 族达到。
两端相等，证明 (32.1)。

构造均在同一个 $B_n^{\mathrm{cyc}}$ 上定义；先按 $\lambda_\gamma$
选择成分，再按该成分明确给出的字分布选择真实字，就实现上界。
用到长圈只为描述局部守恒流，没有在修补时改变来源域。证毕。

**推论 32.2（八个环长的准确值与量词范围）。** 公式 (32.1) 给出

| $n$ | 准确最坏平均修补量 $\mathfrak E_n$ | 达到族 |
| ---: | ---: | --- |
| $5$ | $2/5$ | 严格交替局部律 |
| $6$ | $2/9$ | (31.1) 的 A/B 族 |
| $7$ | $2/7$ | 严格交替局部律 |
| $8$ | $1/6$ | (31.1) 的 A/B 族 |
| $9$ | $2/9$ | 严格交替局部律 |
| $10$ | $2/15$ | (31.1) 的 A/B 族 |
| $11$ | $2/11$ | 严格交替局部律 |
| $12$ | $1/9$ | (31.1) 的 A/B 族 |

证明。逐个代入奇偶公式，达到族已由 §§30–31 给出。
表是任意长度定理的八个实例；有限个数值本身不能证明无界长度结论。

偶数界 $4/(3n)$ 的量词是：对每份局部族，存在同一真实来源使所有窗口的
TV 的平均值至多此数。它不是每个窗口都分别至多此数的断言。
例如 (31.8) 的最优修补在一个窗口的 TV 为 $2/3$，仍准确达到平均最优值。
本卷定理 21.1 的另一个随机切口构造继续给每窗同时 $2/n$；
这里没有把那个逐窗结论的常数直接替换为 $4/3$。
同样，定理 29.1 是三圈的上界，不是所有三圈的距离等式。
证毕。

## 33. 四角隐藏坐标的步长二障碍与不充分性

**定义及应用 33.1（直接从局部律读出的端点分歧）。** 对
$p\in\mathscr L_n$，定义标量

$$
r_i=p_i(100)+p_i(001).
\tag{33.1}
$$

它是第 $i$ 个局部窗口的端点不同的概率，不先写成尚未存在的全局 $P$
上的事件。由 (26.5) 立即得到

$$
r_i=q_i+q_{i+2}-2\kappa_i.
\tag{33.2}
$$

本节 $r_i$ 只表示这个标量，不是 §2 的右接缝边缘向量，也不是底部
全零质量 $p_i(000)$。只有在已经给出共同来源时，才可另写
$r_i=P(U_i\ne U_{i+2})$。

**命题 33.2（保持所有均值时的闭环隐藏障碍）。** 设 $C$ 是步长二图
$i\to i+2$ 的任意一个环，以起点标签标识其边。若 $p\in\mathscr C_n$，
则每个奇数大小的边集合 $S\subseteq C$ 都满足

$$
\sum_{i\in S}r_i-\sum_{i\in C\setminus S}r_i\le |S|-1.
\tag{33.3}
$$

偶数族 (31.1) 在每个步长二环上都违反其中一条不等式，尽管所有均值
与每个局部隐藏区间都保持合法；但全部 (33.3) 一起仍不足以刻画
$\mathscr C_n$。

证明。先消费二元环的经典奇偶不等式。对于一个实际确定字，置
$z_i=u_i\oplus u_{i+2}\in\{0,1\}$。沿 $C$ 每个位值恰出现两次，所以

$$
\bigoplus_{i\in C}z_i=0.
\tag{33.4}
$$

奇数集合 $S$ 的指示向量的异或为一，因此实际 $z$ 不可能恰在 $S$ 上
全为一、在其补集上全为零，至少有一个要求失败。于是

$$
\sum_{i\in S}z_i+\sum_{i\in C\setminus S}(1-z_i)\le |C|-1.
$$

移项得 $\sum_{i\in S}z_i-\sum_{i\in C\setminus S}z_i\le|S|-1$。
如果存在实现 $p$ 的同一来源 $P$，对这个逐字成立的不等式取期望，
(33.1) 正是各项期望，得到 (33.3)。此处期望只在必要性证明中使用，
没有把共同来源偷放进局部数据的定义。

这个中间步骤是已有的二元环不等式，不作新一般定理的归属主张。
Araújo、Quintino、Budroni、Terra Cunha、Cabello，
*All noncontextuality inequalities for the n-cycle scenario*，
[arXiv:1206.3212v3，Theorem 1，式 (4)](https://arxiv.org/pdf/1206.3212v3)，
对 $m\ge3$ 个二值符号及相邻对关联给
$\sum_{j=0}^{m-1}\gamma_j\langle X_jX_{j+1}\rangle\le m-2$，
其中 $\gamma_j\in\{-1,1\}$ 且负号数为奇数。
精确对应为：将 $C$ 依次列为 $i_0,i_1,\ldots,i_{m-1}$，
$i_{j+1}=i_j+2$，取 $X_j=(-1)^{U_{i_j}}$；
相邻符号乘积的局部期望是

$$
E_i=1-2r_i.
\tag{33.5}
$$

在 $S$ 上选 $\gamma_i=-1$，其余选 $+1$，则

$$
\sum_{i\in C}\gamma_i E_i
=|C|-2|S|+2\left(\sum_{i\in S}r_i-\sum_{i\in C\setminus S}r_i\right).
\tag{33.6}
$$

其上界 $|C|-2$ 正好等价于 (33.3)。该文的二元相邻对场景与这里完整
no11 三位边缘的可实现问题不是同一个多面体，不能移植其完整面刻画结论。
上面的 XOR 证明直接承担当前模型中所需的必要性。

现在代入 (31.1)，有

$$
q_i=\frac13,\qquad
\kappa_i=\begin{cases}1/3,&0\le i\le n-3,\\0,&i=n-2,n-1,\end{cases}
\qquad
r_i=\begin{cases}0,&0\le i\le n-3,\\2/3,&i=n-2,n-1.\end{cases}
\tag{33.7}
$$

在偶位置环选 $S=\{n-2\}$，在奇位置环选 $S=\{n-1\}$，两次左侧都为
$2/3$，右侧都为零，故各自违反一条必要条件。
由 (31.3) 的全 A 来源到 (31.1)，全部单点均值和完整二位边缘都没变，
只是两处 $\kappa$ 沿同一四角方向发生变化。这把单窗的隐藏自由度
接到了整圈共同实现必须满足的关系，而不是给一个局部概率分量换名称。

最后给出必要条件的不充分性。对奇数 $n$ 的交替局部律 (30.1)，
有 $q_i=\kappa_i=1/2$，所以 $r_i=0$。每条 (33.3) 的左侧为零，
右侧 $|S|-1\ge0$，全部通过。但 (30.5) 证明它到 $\mathscr C_n$ 的距离
为正，不能实现。这是当前完整三位问题中直接的反例，故不能将
“全部步长二奇偶测试通过”提升为共同来源存在的充分条件。证毕。

**命题 33.3（全正五环也能通过全部奇偶测试而不可实现）。** 在 $n=5$，
各窗取

$$
p_i=p=\frac1{220}(6,4,105,4,101).
\tag{33.8}
$$

它全正、完整重叠相容，满足全部 (33.3)，但不属于 $\mathscr C_5$。

证明。五个分子均正且和为 $220$。前后接缝边缘都为
$(10,105,105)/220$，故相容。由局部读数

$$
q_i=\frac{105}{220}=\frac{21}{44},\qquad
\kappa_i=\frac{101}{220},\qquad r_i=\frac8{220}=\frac2{55}.
\tag{33.9}
$$

步长二图是一条五环。若 $|S|=s\in\{1,3,5\}$，(33.3) 左侧分别为
$(2s-5)\,2/55$，即 $-6/55,2/55,2/11$，分别不超过右侧 $0,2,4$。
这穷尽了所有奇数大小子集的情形。
另一方面，每个合法五位字的一都需一个相邻零，故占位数至多二。
任何共同来源都应满足 $\sum_iq_i\le2$，而给定数据为
$5\cdot21/44=105/44>2$，矛盾。这个反例全部模式概率严格为正，
不能将其闭合失败归因于某个模式恰为零。证毕。

## 34. 有界测试的准确松弛代价与全正边界

**定理 34.1（最大测试虚增量的奇偶常数）。** 对任意
$f=(f_i)\in[0,1]^{5n}$，沿用本卷 §§15、17–18 的定义

$$
\langle f,p\rangle=\sum_i\sum_{\sigma\in\Sigma}f_i(\sigma)p_i(\sigma),
\qquad
H_n(f)=\max_{p\in\mathscr C_n}\langle f,p\rangle
=\max_{u\in B_n^{\mathrm{cyc}}}\sum_i f_i(u_i,u_{i+1},u_{i+2}),
$$

$$
H_n^{\mathrm{loc}}(f)=\max_{p\in\mathscr L_n}\langle f,p\rangle.
\tag{34.1}
$$

这些最大值由有限维紧性达到，且

$$
\boxed{
\max_{f\in[0,1]^{5n}}\bigl[H_n^{\mathrm{loc}}(f)-H_n(f)\bigr]
=n\mathfrak E_n
=\begin{cases}2,&n\text{ 为奇数},\\4/3,&n\text{ 为偶数}.
\end{cases}}
\tag{34.2}
$$

证明。给定任意局部族 $p$，定理 32.1 的构造产生同一真实修补
$\widetilde p$，满足 $\sum_i\operatorname{TV}(p_i,\widetilde p_i)\le n\mathfrak E_n$。
因此对任意有界测试

$$
\langle f,p\rangle
\le\langle f,\widetilde p\rangle+
\sum_i\operatorname{TV}(p_i,\widetilde p_i)
\le H_n(f)+n\mathfrak E_n.
\tag{34.3}
$$

先对 $p$ 取最大，再对 $f$ 取上确界，得到 (34.2) 的上界。
奇数时 (30.1) 的测试在交替局部律上得 $n$；因每窗至多一分，
$H_n^{\mathrm{loc}}(f)=n$，而 (30.4) 给 $H_n(f)=n-2$，差准确为二。
偶数时 (31.4) 的测试在 (31.1) 上得 $n-2/3$，真实最大为 $n-2$。
由 (34.3) 它的局部最大又不能大于 $(n-2)+4/3=n-2/3$，
所以其差准确为 $4/3$。两个显式测试都在允许的闭立方体内，故所写的是
达到的最大值，不只是上确界。证毕。

本卷定理 19.2 已给更强的逐输入精确对偶
$n\Delta_n(p)=\max_f[\langle f,p\rangle-H_n(f)]$；
(34.2) 是计算完最坏修补量后的具体松弛常数，(34.3) 的证明本身只需
有界测试估计和实际修补。它没有另行发明一般 TV 对偶或极小极大原理。
总测试虚增量不随 $n$ 增长，平均误差则在除以窗口数后呈 $1/n$。

**定理 34.2（全正局部族的严格界与同一上确界）。** 对每个 $n\ge5$，
存在全部 $p_i(\sigma)>0$ 的局部相容而不可实现族。
每个全正 $p\in\mathscr L_n$ 都有

$$
\Delta_n(p)<\mathfrak E_n,
\qquad
\sup_{\substack{p\in\mathscr L_n\\p_i(\sigma)>0\ \forall i,\sigma}}
\Delta_n(p)=\mathfrak E_n.
\tag{34.4}
$$

证明。对 $B_n^{\mathrm{cyc}}$ 中的全部合法字均匀取样，记其窗口族为 $u$。
为避免同确定字记号混淆，本证明 $u$ 指这个概率族。
每个局部合法模式都能延成原长度合法字：将该模式安放在原标签
$i,i+1,i+2$，其余位置全部置零即可。对 $000$ 得全零字，对
$100,010,001$ 得相应的单占位字，对 $101$ 得两位相隔二的双占位字。
$n\ge5$ 保证最后一种在另一个环向距离上也不相邻，故所有延拓均合法。
因此均匀来源赋给这些字正概率，$u_i(\sigma)>0$ 对每个坐标都成立，
并且 $u\in\mathscr C_n$。

现在设 $p$ 全正，定义

$$
\lambda=\min_{i,\sigma}\frac{p_i(\sigma)}{u_i(\sigma)}.
\tag{34.5}
$$

有限个正比值的最小值为正。由 $p_i\ge\lambda u_i$ 逐窗求和，
$1\ge\lambda$，故 $0<\lambda\le1$。
若 $\lambda=1$，则每个坐标 $p_i(\sigma)\ge u_i(\sigma)$；
同一窗口的总和又相等，迫使逐坐标相等，即 $p=u$，从而
$\Delta_n(p)=0<\mathfrak E_n$。

若 $0<\lambda<1$，定义残余族

$$
v_i(\sigma)=\frac{p_i(\sigma)-\lambda u_i(\sigma)}{1-\lambda},
\qquad p=\lambda u+(1-\lambda)v.
\tag{34.6}
$$

最小比值定义保证每项非负，归一化给每窗质量一。
$p$ 与 $u$ 的完整重叠等式相减并除以 $1-\lambda$，给 $v$ 的全部重叠等式，
所以 $v\in\mathscr L_n$。为 $v$ 取定理 32.1 的真实修补 $\widetilde v$，
再以相同权重混合 $u$ 的真实来源与 $\widetilde v$ 的来源。
所得 $\widetilde p=\lambda u+(1-\lambda)\widetilde v$ 属于 $\mathscr C_n$，且

$$
\Delta_n(p)\le d_n(p,\widetilde p)
=(1-\lambda)d_n(v,\widetilde v)
\le(1-\lambda)\mathfrak E_n<\mathfrak E_n.
\tag{34.7}
$$

最后选取 §§30–31 的相应极值族 $p^*$，对 $0<\varepsilon<1$ 置

$$
p_\varepsilon=(1-\varepsilon)p^*+\varepsilon u.
\tag{34.8}
$$

这个族局部相容且每个坐标严格正。TV 齐次性与两概率律的 TV 至多一给

$$
d_n(p_\varepsilon,p^*)=\varepsilon d_n(u,p^*)\le\varepsilon.
$$

先前已证明的一 Lipschitz 性 (26.9) 因而给

$$
\Delta_n(p_\varepsilon)\ge\Delta_n(p^*)-\varepsilon
=\mathfrak E_n-\varepsilon.
\tag{34.9}
$$

取 $0<\varepsilon<\mathfrak E_n$ 就得到严格正距离，所以这种全正族
确实不可实现。令 $\varepsilon\downarrow0$，又使距离任意接近
$\mathfrak E_n$；结合 (34.7) 的严格界得到 (34.4)。
最大缺陷在非全正边界达到，但闭合失败并不限于零概率模式。
这是凸混合与距离连续性的结论，不是零事件解释。证毕。

**数学引文及适用范围 34.3（本结果实际消费的供应）。**
本组推导在同一带标号 no11 五模式来源域中组合既有结果，主要对应如下。

| 数学供应 | 代入与保留的条件 | 在本组推导中的用途 |
| --- | --- | --- |
| 本卷 §1、命题 14.2、定理 15.2 | $(X,Y,Z)=(q_i,q_{i+2},q_{i+1})$，$(x,z,y)=(U_i,U_{i+1},U_{i+2})$；$\kappa_i=p_i(101)$ | 完整局部反解、四角方向及直接从数据定义的 $r_i$ |
| 本卷定理 16.2、17.2–17.3、19.2 | 保留 $B_n^{\mathrm{cyc}}$、同一 $P$ 与全部原标签；$f_i\in[0,1]$ | 实际字来源与测试分离的既有意义；支持指标和奇偶测试只消费其中的必要估计 |
| 本卷定理 18.1、式 (18.2)–(18.3) | 供应 $m_\gamma$ 就是 (27.2) 的绕圈数；$\lambda_\gamma=m_\gamma\alpha_\gamma$ | 局部流拆为一、二、三圈，再按概率权重混合原长度修补 |
| 本卷定理 21.1、式 (21.3)、(21.7) | 原层标签 $j+t\bmod n$、长字相位 $j+hn+t$；中位端点分别来自 $h+1,h$ | 普通两圈切双零与三圈 A 中位切口的精细代价；不改变原有逐窗 $2/n$ 的量词 |
| 本卷定理 22.1、23.2 | 奇数 $n=2a+1$；$d_n$ 与 $\Delta_n$ 保持同一来源域 | 继承交替精确值及其实际旋转来源；连续性用于最坏值达到和全正逼近 |
| [接缝供应卷 §§21–22](AURIC_FIB_SEAMS_CYCLES_ARITHMETIC_BOUNDARY_RECONSTRUCTION.md) | 层标签、边字典不变；其 $q_\nu$ 是本组 $m_\gamma$，不是位点均值 $q_i$ | 经典圈分解在位置依赖模型中的归一化；提升域 $B_{6n}^{\mathrm{cyc}}$ 仍与当前修补域不同 |
| 同卷定理 22.3、命题 23.2、§24、推论 25.2 | A/B 作用次序相同，$s=3\kappa$；计数 $B=N_{100}=N_{001}$、$D=N_{101}$ | A/B 置换及密度 $1/3$ 纤维、零间隙次数、全 A 的偶数原长度来源 |
| Goldstein–Kuna–Lebowitz–Speer，Theorems 6、8 | $k=2$ 对应三位块，但当前加 no11 和位置层；全图与逐层质量分别归一化 | 有限正流扣圈的经典方法；不把通用环长结论当作原长度实现 |
| Araújo 等，Theorem 1、式 (4) | 每条步长二环有 $m=n/\gcd(n,2)\ge3$ 个顶点，$E_i=1-2r_i$，负号集为奇数 $S$ | (33.3) 的经典二元环先例；不运输其场景的面完备性到完整三位边缘域 |

本卷 §2 的四角零边界方向、本卷 §21 的保标签切口耦合、§22 的奇数锐性，
以及上述经典流分解和奇偶不等式，均是被使用的既有数学供应。
这里承担具体结论的是两圈的准确分类、三圈的明确原长度修补、偶数 A/B
达到族及其三字证书，以及它们对最坏平均缺陷、测试松弛和全正边界的推导。
这些具体推导不将一般方法、换坐标或继承的奇数结果另列为独立发明，
也不提出未经文献比较的全球新颖性断言。

所有结论的量词都针对 (26.1)–(26.3) 的有限经典概率模型、完整二位重叠、
指定原标号环和不固定均值的平均 TV 距离。切口置零、任意实概率混合、
旋转取样及三字制备是来源存在性的数学构造；它们不自动给原生控制、
实际测量取得或物理制备提供操作权限与成本界。
$\mathfrak E_n$ 不是物理能量、运行时间、记忆位数或 Atiyah–Singer 指标。
仅给单点读数、改用别的支持、增加保持均值条件、更换窗口大小或允许改换
环长，都改变了这里证明的任务，不能无条件沿用这些准确常数。

## 追加锚（本行以下为增补区）
