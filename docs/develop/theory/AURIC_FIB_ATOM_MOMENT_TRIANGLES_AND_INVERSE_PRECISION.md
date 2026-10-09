# Auric FIB-ATOM：关系三角形与反演精度

## 从共同来源，到面积、正反方向与可取得的边界

## 来源、记号与参考边界

**参考输入与 open 边界。** 本卷完整收录用户提供的数学论述。新增候选数学均为 open；正文的“证明”“推得”“本篇证明”等是供稿者的普通数学论证用语，不构成仓库形式化认证。只有经 Lean kernel 验证的声明、证明项及其 axiom 闭包承载本库的数学真值，理论散文与消化状态不承载该真值。本卷不新增 Lean，也不重现实验。

**来源与版本。** 作者类型为 mixed（用户供稿交付），原作者及原模型未知；接收时点为 2026-10-10。来源标识为 `moment-triangle-source`；原始供稿字节的 SHA-256 为 `c8756f7eaa5b16013f0ba1fa64692d6123092408a133fcee001b63b76a0c7c8b`。供稿的项目快照 `05725d4` 固定为完整修订 `05725d4098ad0009f95b36924b32ea6d34479617`；正文的“本次”“本轮”“最新”及原始核验自述均归属于该供稿。

**空模式与位置字典。** 本卷使用获准记号 $\mathsf F[\mathrm{null}]$（`F[null]`），它与供稿中的 $\mathsf F[\varnothing]$ 表示同一个空选择。五模式仍是 `F[null]`、`F[1]`、`F[2]`、`F[3]`、`F[1,3]`；$x$ 为位置 1（左端），$y$ 为位置 3（右端），$z$ 为位置 2（中间）。这是空模式别名与指标字典，不作物理识别，也不推断接缝方向。

**项目引用范围。** 正文的“项目§22”“项目§23”“项目§24”均指同一快照的 [RECURSIVE_RELATIONAL_OBSERVATION_FUTURE_RESPONSE_SUFFICIENCY](https://github.com/the-omega-institute/trureturing/blob/05725d4098ad0009f95b36924b32ea6d34479617/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FUTURE_RESPONSE_SUFFICIENCY.md)，分别为固定先验实际后验像上的两项律窗口、窗口表示与原合法续接交换、一个固定全支持先验下的实际反演不稳定性。`#14860` 的 `complete_original_recovery` 可在 [FourthSegmentLawRecovery.lean:901](https://github.com/the-omega-institute/trureturing/blob/05725d4098ad0009f95b36924b32ea6d34479617/D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentLawRecovery.lean#L901) 作源码检查；此处只给出来源定位，没有重新编译或核验其当前公理闭包，也不以它认证本卷定理 1 的两矩恢复。`#14880` 的十五相位费用属于另一个来源合同 [KBONACCI_SELF_CALIBRATING_BOUNDARIES，定理 25.3](https://github.com/the-omega-institute/trureturing/blob/05725d4098ad0009f95b36924b32ea6d34479617/docs/develop/theory/KBONACCI_SELF_CALIBRATING_BOUNDARIES.md)；其六块、四十八位结论不得转移为 FIB 恢复费用。

**文献范围。** [arXiv:2008.12698，Ten Lectures on the Moment Problem](https://arxiv.org/abs/2008.12698) 是矩问题与正性背景；[Berkeley 技术报告 649，Graphical models, exponential families, and variational inference](https://statistics.berkeley.edu/tech-reports/649) 是指数族、协方差与参数导数的背景。两项背景引用为 `literature-attested`，只承担对应背景，不认证本卷的 FIB 面积、雅可比双边界或原生长度律常数。供稿中的自行推导表述保留为来源论证，不作为本稿的原创性或新颖性认证。

**不可取得的附件与核验自述。** 供稿所称“量子续篇”“附件”和“粘贴的文本 (1)”未随本来源取得，其措辞作为来源引用原样保留，未据此验证物理记录实现。原始 `sandbox:/mnt/data/fib_moment_triangle_inverse_checks.py` 与 `sandbox:/mnt/data/fib_moment_triangle_inverse_checks.json` 定位也不可取得；文末所称 40、60、60、50、80、40 组检查及 100 位精度只是供稿者报告，未独立复现，不作为本卷的核验结果。固定先验与任意混合、实际整数历史与连续参数分析、概率律恢复与本次隐藏深度、来源合同的取得费用与坐标维数、局部行列式与各方向稳定性均按原文的范围区分。

## 导言

**最新进展让我们可以继续追问一个更细的问题：边界能够“唯一恢复”内部，是否意味着它能够“稳定恢复”内部？**

答案并不相同。这一轮可以把差别精确地连接到三角形面积：

> **三个候选来源在观察坐标中围成的三角形越瘦，区分其混合比例就越依赖精度。Fibonacci 递归不只决定原子数量怎样增长，还能精确决定这种关系三角形怎样缩小。**

本轮将推得：

```math
\boxed{
\mathcal A_n
=
\frac{1}{
2\bigl(F_{n+3}F_{n+4}F_{n+5}\bigr)^2
}.
}
```

这是三个连续候选深度在一阶、二阶读数平面中形成的三角形面积。它始终非零，所以精确区分仍然可能；但它迅速趋于零，所以不能把精确反演当成固定精度下的免费恢复。

本次冻结读取的 `dev` 为 `05725d4`。其中，**#14860** 已提供 Lean 声明 `complete_original_recovery`，把原第四段的完整剩余付费长度律、活动相位与深度后验、完整允许残余转录律连接为等价对象；它恢复的是概率律，不是本次隐藏深度或尚未发生的未来。**#14880** 则在另一份 KBonacci 读者合同中，将十五相位任务的自适应与共同预设费用都确定为六个完整块。两者分别约束“表示是否充分”与“实际取得需要多少操作”，不能混成一项结论。

下面先沿第一条进展研究关系几何，再回到金字塔、记录与取得成本。**新增的面积—反演公式由本篇证明；不把它们冒充已经完成仓库形式化的声明。**


---

## 一、先固定：来源自由度与模型自由度不是一回事

沿用五模式：

```math
\Sigma=
\left\{
\mathsf F[\mathrm{null}],
\mathsf F[1],
\mathsf F[2],
\mathsf F[3],
\mathsf F[1,3]
\right\}.
```

低端、高端、中间占位为 $x,y,z$，满足：

```math
xz=yz=0.
```

令：

```math
X=\mathbb E[x],\qquad
Y=\mathbb E[y],\qquad
Z=\mathbb E[z],\qquad
\kappa=\mathbb E[xy].
```

完整概率恢复为：

```math
\boxed{
\begin{aligned}
p_0&=1-X-Y-Z+\kappa,\\
p_1&=X-\kappa,\\
p_2&=Z,\\
p_3&=Y-\kappa,\\
p_{13}&=\kappa.
\end{aligned}
}
```

因此，一般五模式律不能由三个金字塔均值唯一决定。项目的观察更新卷也明确指出：读取 $x$ 后，要预测另一端 $y$，会重新用到 $\kappa$。

但如果额外验证来源属于：

```math
p\propto(1,a,b,c,ac),
```

那么：

```math
p_0p_{13}=p_1p_3,
```

从而：

```math
\boxed{\kappa=\frac{XY}{1-Z}.}
```

**这不是三个均值凭空增加了信息，而是生成规则排除了其他相容来源。**

最新的第四段恢复结果也体现了同一种区别：

```math
\boxed{
\text{任意深度混合}
\quad\ne\quad
\text{固定先验经过实际历史产生的后验族}.
}
```

后者受到额外的同源约束，因而可能由少量精确坐标唯一表示。

---

## 二、最新项目中的两个精确概率，为什么能表示整个后验？

### 定义1　同一个隐藏深度与实际历史后验

项目固定：

```math
r_k=\frac{F_{k+1}}{F_{k+3}},
\qquad k\ge1,
```

并在一次运行中使用同一个隐藏深度 $K$。

实际取得 $A$ 次 $\alpha$、$B$ 次 $\beta$ 后，安装先验 $\mu$ 更新为：

```math
\boxed{
\nu_{A,B}(k)
=
\frac{\mu(k)r_k^A(1-r_k)^B}
{\sum_j\mu(j)r_j^A(1-r_j)^B}.
}
```

这里 $A,B$ 包含已经实际读取的拒绝、返回与部分解析，不是只数最后被接受的标记。

定义：

```math
m_j=\mathbb E_\nu[r^j].
```

项目第四段有两个活动控制相位。其剩余付费长度律的前两项分别是：

```math
\boxed{
\begin{array}{c|cc}
\text{活动相位}&D(1)&D(2)\\ \hline
p&m_1&1-2m_1+m_2\\
\beta&1-m_1&m_2
\end{array}
}
```

第一项的区间分别为：

```math
[1/3,2/5],
\qquad
[3/5,2/3],
```

所以可以识别相位，再恢复 $m_1,m_2$。这些公式和完整长度律恢复，来自项目的既定来源与原停止协议。

### theorem 1: 固定安装先验后，一阶、二阶矩唯一确定该后验族

Claim status: open（参考候选，未经本稿的 Lean kernel 核验）。

若：

```math
\nu=\nu_{A,B},
\qquad
\nu'=\nu_{A',B'},
```

来自**同一个**安装先验，并满足：

```math
\mathbb E_\nu[r]=\mathbb E_{\nu'}[r],
\qquad
\mathbb E_\nu[r^2]=\mathbb E_{\nu'}[r^2],
```

则：

```math
\boxed{\nu=\nu'.}
```

这是项目§22的普通数学结论；这里展开它的关键证明，不把它与 #14860 已形式化的“完整长度律恢复”混为同一声明。

#### 证明

两后验之比为：

```math
\frac{\nu(k)}{\nu'(k)}
=
e^{g(r_k)},
```

其中：

```math
g(r)=c+(A-A')\log r+(B-B')\log(1-r).
```

其导数：

```math
g'(r)=
\frac{(A-A')-[(A-A')+(B-B')]r}{r(1-r)}
```

至多有一个零点。因此，除非 $g$ 恒为零，否则 $g$ 至多改变符号两次。

选一个次数不超过二的多项式 $P(r)$，使它在 $g(r)\ne0$ 的位置与 $g(r)$ 同号。

于是：

```math
P(r_k)\bigl(\nu(k)-\nu'(k)\bigr)\ge0.
```

若两个后验不同，至少一项严格为正；但零、一、二阶矩相等，又要求：

```math
\sum_kP(r_k)\bigl(\nu(k)-\nu'(k)\bigr)=0,
```

矛盾。可数求和绝对收敛，因为全部 $r_k$ 位于一个紧区间内。证毕。

**所以，两个精确概率可以在这份受限实际后验族上具有很强的辨识力。**

但它们不是“两次随机结果”，也不是两个固定长度的数字寄存器。精确实数表示、有限样本估计、实际取得费用，仍是不同任务。

---

## 三、把一个读数提升为一条曲线，三角形会自然出现

### 定义2　一阶—二阶关系曲线

对一个候选响应率 $r$，定义：

```math
\boxed{\gamma(r)=(r,r^2).}
```

对混合来源 $\nu$，其读数就是这些点的重心：

```math
\boxed{
(m_1,m_2)=\sum_k\nu(k)\gamma(r_k).
}
```

这给出一张不需要先指定三角形的几何：候选来源先落在抛物线上，三种候选来源再形成三角形。

同时：

```math
\boxed{
m_2-m_1^2=\operatorname{Var}_\nu(r)\ge0.
}
```

这项二阶余量还具有直接的同源含义。若两次读取使用同一个隐藏深度：

```math
\Pr(\alpha\alpha)=m_2.
```

若错误地在每次读取前独立重抽深度，则会得到：

```math
\Pr(\alpha\alpha)=m_1^2.
```

**两者相差的，正是共同来源留下的方差。**

### theorem 2: 三种不同响应率形成的面积，等于三个差异的乘积

Claim status: open（参考候选，未经本稿的 Lean kernel 核验）。

取：

```math
a<b<c.
```

在标准 $(r,r^2)$ 坐标尺下，三个点的三角形面积为：

```math
\boxed{
\mathcal A(a,b,c)
=
\frac12(b-a)(c-a)(c-b).
}
```

#### 证明

两条差向量为：

```math
(b-a,b^2-a^2),
\qquad
(c-a,c^2-a^2).
```

它们的行列式为：

```math
(b-a)(c-a)\bigl[(c+a)-(b+a)\bigr],
```

即：

```math
(b-a)(c-a)(c-b).
```

除以二得到面积。证毕。

**这三项差异不是独立的装饰：任意两种候选靠近，整个关系三角形都会变瘦。**

### theorem 3: 已知三种响应率时，一阶、二阶矩恢复全部混合权重

Claim status: open（参考候选，未经本稿的 Lean kernel 核验）。

设来源只支持不同的 $r_1,r_2,r_3$，概率为 $p_i$。

对 $\{i,j,\ell\}=\{1,2,3\}$：

```math
\boxed{
p_i=
\frac{
m_2-(r_j+r_\ell)m_1+r_jr_\ell
}{
(r_i-r_j)(r_i-r_\ell)
}.
}
```

#### 证明

对多项式：

```math
(r-r_j)(r-r_\ell)
```

求期望。它在另外两个候选率上为零，只留下：

```math
p_i(r_i-r_j)(r_i-r_\ell).
```

证毕。

因此，三角形在这里表示：

```math
\boxed{
\text{三个已知来源的混合，可以由一个平面位置唯一恢复。}
}
```

但分母同时说明：**三角形接近退化时，恢复系数会变大。唯一性没有自动提供稳定性。**

---

## 四、更多来源怎样组成一个“面积总量”？

### 定义3　三阶矩关系矩阵

令 $m_0=1$，定义：

```math
\boxed{
H_2=
\begin{pmatrix}
1&m_1&m_2\\
m_1&m_2&m_3\\
m_2&m_3&m_4
\end{pmatrix}.
}
```

它是三个函数：

```math
1,\quad r,\quad r^2
```

在概率内积：

```math
\langle f,g\rangle_\nu=\mathbb E_\nu[fg]
```

下的 Gram 矩阵，所以：

```math
H_2\succeq0.
```

这种矩与正性之间的关系属于经典矩问题理论；这里使用其有限或紧支撑形式。[arXiv](https://arxiv.org/abs/2008.12698)

### theorem 4: 完整 Gram 体积是所有来源三角形面积平方的加权和

Claim status: open（参考候选，未经本稿的 Lean kernel 核验）。

对每组三个不同支持点，令：

```math
\Delta_{ijk}
=
|(r_j-r_i)(r_k-r_i)(r_k-r_j)|.
```

则：

```math
\boxed{
\det H_2
=
\sum_{i<j<k}
\nu_i\nu_j\nu_k\,\Delta_{ijk}^{\,2}.
}
```

等价地：

```math
\boxed{
\det H_2
=
4\sum_{i<j<k}
\nu_i\nu_j\nu_k\,\mathcal A_{ijk}^{\,2}.
}
```

并且：

```math
\boxed{
\det H_2
=
\det\operatorname{Cov}_\nu(r,r^2).
}
```

#### 证明

将列向量：

```math
v_i=(1,r_i,r_i^2)^{\mathsf T}
```

排列起来，有：

```math
H_2=\sum_i\nu_i v_iv_i^{\mathsf T}.
```

按行列式的多线性展开，只有三个不同列共同出现的项留下，得到各组三阶行列式平方。它们正是 Vandermonde 乘积 $\Delta_{ijk}^2$。

对第一行、第一列作中心化消元，得到协方差行列式。可数支持时，用截断极限或绝对收敛延拓。证毕。

由此：

```math
\boxed{
\det H_2>0
\iff
\nu\text{ 至少支持三个不同响应率}.
}
```

**这不是说内部只有三个来源，而是这三种指定函数已经形成三个独立的关系方向。**

有一百个或可数多个候选深度，仍然可以只考察这三个函数；其秩不能替代完整支持大小。

---

## 五、本轮的关键推导：观察平面与似然平面的两个三角形，共同决定反演

前面只研究“候选来源怎样混合”。现在研究“实际证据怎样推动后验”。

### 定义4　用于灵敏度分析的连续参数化

固定安装先验 $\mu$，将计数公式数学上延拓到实参数 $A,B$：

```math
\nu_{A,B}(k)
=
\frac{\mu(k)r_k^A(1-r_k)^B}{Z(A,B)}.
```

这是分析局部变化的辅助模型。真实读取仍然只产生原合同允许的整数计数与实际历史，**不是增加了分数次读取权限**。

定义：

```math
\Phi(A,B)=(m_1,m_2),
```

其局部变化矩阵为：

```math
\mathsf J=
\frac{\partial(m_1,m_2)}{\partial(A,B)}.
```

对归一化权重求导，得到：

```math
\boxed{
\mathsf J=
\begin{pmatrix}
\operatorname{Cov}(r,\log r)
&
\operatorname{Cov}(r,\log(1-r))
\\
\operatorname{Cov}(r^2,\log r)
&
\operatorname{Cov}(r^2,\log(1-r))
\end{pmatrix}.
}
```

这使用指数族中“参数导数等于协方差”的标准机制；以下面积公式是它在当前 FIB 响应率上的具体展开。[加州大学伯克利分校统计学系](https://statistics.berkeley.edu/tech-reports/649)

### 定义5　同一组三来源的似然三角形

对：

```math
a<b<c,
```

再画三个点：

```math
(\log a,\log(1-a)),
\quad
(\log b,\log(1-b)),
\quad
(\log c,\log(1-c)).
```

其有向双倍面积为：

```math
L(a,b,c)
=
\det
\begin{pmatrix}
1&1&1\\
\log a&\log b&\log c\\
\log(1-a)&\log(1-b)&\log(1-c)
\end{pmatrix}.
```

### theorem 5: 观察三角形与似然三角形的定向始终相反

Claim status: open（参考候选，未经本稿的 Lean kernel 核验）。

```math
\boxed{
L(a,b,c)
=
-\int_a^b\int_b^c
\frac{t-s}{s(1-s)t(1-t)}\,dt\,ds
<0.
}
```

#### 证明

将行列式写成两个区间增量的乘积差：

```math
L
=
\log\frac ba\log\frac{1-c}{1-b}
-
\log\frac cb\log\frac{1-b}{1-a}.
```

用积分表示各对数增量，被积函数为：

```math
-\frac1{s(1-t)}+\frac1{t(1-s)}
=
-\frac{t-s}{s(1-s)t(1-t)}.
```

在 $a<s<b<t<c$ 上严格为负。证毕。

**同一个来源率，投到“实际读数”与“似然权重”两个切面以后，三角形方向相反。**

这不是把集合取补，也不是把物理空间镜像；它是两个明确关系坐标之间的定向结果。

### theorem 6: 局部反演面积是这两类三角形的乘积和

Claim status: open（参考候选，未经本稿的 Lean kernel 核验）。

把每组三个响应率按大小排序，记：

```math
\Lambda_{ijk}=-L(r_i,r_j,r_k)>0.
```

则：

```math
\boxed{
-\det\mathsf J
=
\sum_{i<j<k}
\nu_i\nu_j\nu_k\,
\Delta_{ijk}\Lambda_{ijk}.
}
```

#### 证明

考虑交叉关系矩阵：

```math
M=
\mathbb E_\nu
\left[
\begin{pmatrix}1\\r\\r^2\end{pmatrix}
\begin{pmatrix}1&\log r&\log(1-r)\end{pmatrix}
\right].
```

作均值消元：

```math
\det M=\det\mathsf J.
```

再按 Cauchy–Binet 展开，每一组三个来源贡献：

```math
\nu_i\nu_j\nu_k
\det(1,r,r^2)_{ijk}
\det(1,\log r,\log(1-r))_{ijk}.
```

第一项按递增率排序为正，第二项为负，得到结论。证毕。

**重要之处在于：所有三来源贡献同号，不会彼此抵消。**

因此，只要支持至少三个不同响应率：

```math
\boxed{\det\mathsf J<0.}
```

局部参数反演就不会因不同三角贡献互相抵消而失效。

---

## 六、FIB 响应区间给出一个明确的稳定性系数

项目的全部实际响应率满足：

```math
\frac13\le r_k\le\frac25.
```

因此：

```math
\frac29\le r_k(1-r_k)\le\frac6{25}.
```

### theorem 7: 反演面积与来源 Gram 面积之间，有统一的双边界

Claim status: open（参考候选，未经本稿的 Lean kernel 核验）。

```math
\boxed{
\frac{625}{72}\det H_2
\le
-\det\mathsf J
\le
\frac{81}{8}\det H_2.
}
```

#### 证明

在定理5的积分中：

```math
\frac{625}{36}
\le
\frac1{s(1-s)t(1-t)}
\le
\frac{81}{4}.
```

而：

```math
\int_a^b\int_b^c(t-s)\,dt\,ds
=
\frac12(b-a)(c-a)(c-b).
```

所以：

```math
\frac{625}{72}\Delta
\le\Lambda
\le\frac{81}{8}\Delta.
```

乘上各组三来源的非负概率权重，再使用定理4、6求和。证毕。

**这条关系把“隐藏结构”和“恢复灵敏度”直接接起来：**

```math
\boxed{
\text{来源在观察平面中形成的加权三角面积平方}
}
```

控制：

```math
\boxed{
\text{证据参数变化能在观察平面中展开多少面积}.
}
```

这些常数只属于本篇指定的响应区间与坐标，不是普适物理常数。

### 这怎样接回原金字塔的体积？

同一展开在 $d$ 个目标函数上使用 $d+1$ 个来源点：一维用线段，二维用三角形，三维用四面体。

例如原金字塔的三个占位响应满足：

```math
\boxed{
\begin{aligned}
\det\operatorname{Cov}(x,y,z)
=p_2\bigl(
&p_0p_1p_3+p_0p_1p_{13}\\
&+p_0p_3p_{13}+p_1p_3p_{13}
\bigr).
\end{aligned}
}
```

理由也是同一个：四个底角共面，其四面体体积为零；顶点加任意三个底角具有非零体积，行列式按这些四面体贡献展开。

**此前金字塔的波动体积，与现在后验反演的三角面积，不是两个孤立公式，而是同一套“来源单纯形—关系行列式”计算。**

---

## 七、Fibonacci 递归怎样使关系三角形越来越瘦？

### theorem 8: 三个连续深度的关系面积具有精确 Fibonacci 公式

Claim status: open（参考候选，未经本稿的 Lean kernel 核验）。

取：

```math
r_n=\frac{F_{n+1}}{F_{n+3}},
\quad
r_{n+1}=\frac{F_{n+2}}{F_{n+4}},
\quad
r_{n+2}=\frac{F_{n+3}}{F_{n+5}}.
```

则：

```math
\boxed{
|r_{n+1}-r_n|
=
\frac1{F_{n+3}F_{n+4}},
}
```

```math
\boxed{
|r_{n+2}-r_{n+1}|
=
\frac1{F_{n+4}F_{n+5}},
}
```

```math
\boxed{
|r_{n+2}-r_n|
=
\frac1{F_{n+3}F_{n+5}}.
}
```

因此：

```math
\boxed{
\mathcal A_n
=
\frac1{
2(F_{n+3}F_{n+4}F_{n+5})^2
}.
}
```

#### 证明

Fibonacci 矩阵的行列式交替为 $\pm1$，给出相邻比值的分子行列式为 $\pm1$，得到前两式。

两步之差可由前两步的交替符号相减，结合：

```math
F_{n+5}-F_{n+3}=F_{n+4}
```

得到第三式。

再代入三角面积公式。证毕。

| 三个候选深度 | 关系三角形面积 |
|---|---:|
| $1,2,3$ | $1/28800$ |
| $5,6,7$ | $1/3084265800$ |
| $10,11,12$ | $1/5742277921320200$ |

三个点一直不同，面积一直为正；但它们正沿同一条抛物线聚集。

若三种深度后验等权：

```math
\nu_n=\nu_{n+1}=\nu_{n+2}=\frac13,
```

则：

```math
\boxed{
\det H_2
=
\frac1{
27(F_{n+3}F_{n+4}F_{n+5})^4
}.
}
```

所以：

```math
\mathcal A_n\text{ 的数量级为 }\varphi^{-6n},
```

而：

```math
-\det\mathsf J\text{ 的数量级为 }\varphi^{-12n}.
```

**这里真正趋于退化的，是观察坐标中对不同来源的分离，不是来源标签已经相同。**

### 这份后验不是凭空选择的

对每个固定 $n$，可安装三点先验：

```math
\mu(k)\propto
\frac1{r_k^3(1-r_k)^3},
\qquad k\in\{n,n+1,n+2\}.
```

实际历史：

```math
\beta\alpha\mid\beta\beta\alpha\alpha
```

恰好取得三次 $\alpha$、三次 $\beta$，于是产生上述均匀后验。

这里不同 $n$ 使用不同的安装先验。**不能把它冒充“在一个固定先验上已经证明了所有不稳定性”。**

项目§24另有更强的同先验结果：固定 $\mu(k)=2^{-k}$，存在实际有限历史对，使深度后验的总变差距离趋于一，而完整剩余长度律与转录律的距离趋于零。该结论在理论正文中有单独证明，不能由本篇这个三点例子替代。

---

## 八、连完整未来长度律都可以很接近，但隐藏深度仍完全不同

下面给一个直接的定量界，说明问题不只出在前两个矩。

在活动相位 $p$，固定响应率 $r$，令：

```math
\xi=r(1-r).
```

项目的完整长度律为：

```math
\boxed{
D_r(2j+1)=r\xi^j,
\qquad
D_r(2j+2)=(1-r)^2\xi^j.
}
```

这些对应原解析器的实际停止词，不是额外构造的随机等待过程。

### theorem 9: 完整长度律对响应率是统一连续的

Claim status: open（参考候选，未经本稿的 Lean kernel 核验）。

对：

```math
r,s\in[1/3,2/5],
```

有：

```math
\boxed{
\operatorname{TV}(D_r,D_s)
\le\frac{12}{7}|r-s|.
}
```

#### 证明

逐项求导并使用三角不等式：

```math
\begin{aligned}
\frac12\sum_{\ell\ge1}
\left|\frac{dD_r(\ell)}{dr}\right|
&\le
\frac{2(1-r)}{1-r(1-r)}\\
&\le\frac{12}{7}.
\end{aligned}
```

第一式通过两个几何级数及其导数求和得到；最后的函数在当前区间递减，最大值位于 $r=1/3$。

沿 $r$ 到 $s$ 积分即得。证毕。

因此相邻深度满足：

```math
\boxed{
\operatorname{TV}(D_{r_n},D_{r_{n+1}})
\le
\frac{12}{
7F_{n+3}F_{n+4}
}
\longrightarrow0.
}
```

但是两份确定深度分布：

```math
\delta_n,\qquad\delta_{n+1}
```

的总变差距离始终为一。

**完整未来律的精确单射，不等于其逆映射在所有来源规模上稳定。**

这里比较的是不同确定深度来源；它不替代前面引用的同一个固定先验实际历史定理。两者共同强调的是：

```math
\boxed{
\text{来源区别仍然存在}
\quad\text{而}\quad
\text{当前响应区别可能非常小}.
}
```

---

## 九、三维记录为什么会出现？因为我们选择了三个独立关系函数

> 以下“量子续篇”“附件”“粘贴的文本 (1)”是供稿者的引用措辞；所指附件不可取得，相关实现条件未验证。

你的量子续篇规定：归一化记录的关系矩阵必须正半定；在该纯记录等距实现中，最小记录载体维数等于矩阵秩。它同时强调，这不是物理空间维数。粘贴的文本 (1)

现在先作数学上的记录表示：

```math
v_j=\sum_k\sqrt{\nu(k)}\,r_k^j|k\rangle,
\qquad j=0,1,2.
```

于是：

```math
\langle v_i,v_j\rangle=m_{i+j},
```

所以其 Gram 矩阵正是 $H_2$。

归一化：

```math
e_j=\frac{v_j}{\sqrt{m_{2j}}},
```

得到：

```math
\boxed{
\det\operatorname{Gram}(e_0,e_1,e_2)
=
\frac{\det H_2}{m_2m_4}.
}
```

### corollary 9.1

Claim status: open（参考候选，未经本稿的 Lean kernel 核验）。

若至少有三个不同深度具有正后验，则这三份指定记录的最小 Gram 实现维数为三。

但当响应率越来越接近时，它们的 Gram 体积可以趋近于零。

**所以应当区分：**

```math
\boxed{
\text{精确线性独立的方向数}
}
```

与：

```math
\boxed{
\text{有限精度下仍然能够可靠分辨的方向数}.
}
```

这里没有从经典后验免费制备量子振幅，也没有把 $|k\rangle$ 注册为实际可访问的实验装置。若要把这份表示变成物理记录，仍须供应制备、比较与保真条件。

更不能因为三个函数形成三维 Gram 空间，就说完整深度来源只有三个自由度：我们只选择了三个函数，完整后验可能仍具有可数支持。

附件所说的“正交关系、记录载体、实际后续”必须分开，在这里同样适用。粘贴的文本 (1)

---

## 十、这怎样指导下一步观察，而不是只得到一张漂亮的关系图？

现在可以把三个层次分清。

### 1．当前表示是否唯一

固定先验实际后验族中：

```math
W=(D(1),D(2))
```

可以唯一表示后验与完整允许未来律。

但在任意混合域中，两个矩一般不够。四个不同候选率就可以产生非零带符号权重，满足：

```math
\sum_i d_i=\sum_i d_ir_i=\sum_i d_ir_i^2=0.
```

将它的小幅正负扰动加到严格正的概率律上，就得到同矩、不同来源。

**模型约束在反演中实际承担了信息，不能不声明它。**

### 2．当前表示是否稳定

三角面积与 $\det H_2$ 衡量来源在读数中的分离。

本篇给出：

```math
\boxed{
-\det\mathsf J
\asymp\det H_2
}
```

在明确常数之间成立。但行列式只衡量局部面积倍率；要控制所有方向的误差，还应看最小奇异值、目标范数和允许扰动区域，不能单凭一个非零行列式就宣布数值恢复可靠。

### 3．当前表示是否实际可取得并继续使用

项目§23的同源更新中，取得 $\alpha$ 后：

```math
\nu^\alpha(k)=\frac{\nu(k)r_k}{m_1},
```

所以：

```math
m_1^\alpha=\frac{m_2}{m_1},
\qquad
m_2^\alpha=\frac{m_3}{m_1}.
```

更新会用到 $m_3$。在固定先验实际像上，它能由 $W$ 所表示的后验确定；在任意矩坐标对上，却不能直接补出。这是项目明确保留的限制。

另一方面，最新 #14880 的十五相位任务，即使最终相位只需要十五个不同标签，在其原不可逆读者中仍然需要六个完整八位块。其五块下界的核心，是某些实际候选在第零、二、四个动作上必然沉默，五个目标标签只得到两层有效二值分支，不足以区分。这里的费用是四十八个实际发出的位，不是“坐标维数”。

**这两份模型不同，不能互相转移费用结论；但它们共同排除了同一个误读：一个简短的数学坐标，不等于一个廉价、精确、已经取得的运行时寄存器。**

---

## 本轮最重要的隐藏关系

这次不是再增加一种基础元素，而是把此前的几种元素接进同一套计算：

```math
\boxed{
\text{候选响应点 }r
\longrightarrow
\text{关系曲线 }(r,r^2)
\longrightarrow
\text{三来源面积}
\longrightarrow
\text{Gram 体积}
\longrightarrow
\text{反演灵敏度}.
}
```

其中三项核心结果是：

```math
\boxed{
\det H_2
=
4\sum_{i<j<k}
\nu_i\nu_j\nu_k\,\mathcal A_{ijk}^{\,2};
}
```

```math
\boxed{
\frac{625}{72}\det H_2
\le
-\det\frac{\partial(m_1,m_2)}{\partial(A,B)}
\le
\frac{81}{8}\det H_2;
}
```

```math
\boxed{
\mathcal A_n
=
\frac1{
2(F_{n+3}F_{n+4}F_{n+5})^2
}.
}
```

第一式说明内部候选如何共同贡献观察面积；第二式说明这些面积怎样控制证据到读数的反演；第三式说明 FIB 递归如何使这种分离迅速变小。

> 以下检查数量、精度及“未重跑仓库 Lean，也未修改仓库”的自述均引自原始供稿，属于供稿者报告；脚本与结果不可取得，本稿未复现这些检查。

本次完成了40组连续深度面积与实际后验构造、60组加权三角 Gram 恒等式、60组三来源概率反演、50组金字塔四面体协方差公式，以及有限矩反例和原生长度公式的有理数精确核验。另用100位精度检查了80组对数雅可比公式和40组完整长度律距离界；涉及对数的检查是高精度数值检查，不是符号证明。**本轮未重跑仓库 Lean，也未修改仓库。**

复核材料：fib_moment_triangle_inverse_checks.py[验证脚本](sandbox:/mnt/data/fib_moment_triangle_inverse_checks.py) · fib_moment_triangle_inverse_checks.json[验证结果](sandbox:/mnt/data/fib_moment_triangle_inverse_checks.json)。

**这一轮最实质性的推进，是把“边界能推体”分成了三道必须分别完成的条件：能否唯一恢复、能否稳定恢复、能否通过实际操作取得。**

三角形在这里不是因为边数少而神秘，而是三个来源第一次能够围出非零的关系面积；正方形和更多来源会带来新的混合方向；金字塔把一些共同关系压成均值，Gram 行列式则检查这些关系还留下多大的可分辨体积。

**真正需要追踪的，不只是某项隐藏关系在数学上是否仍然存在，而是它经过递归、归一化、条件更新和有限精度以后，还以多大的差异留在观察者实际能够读取的边界上。**

## 追加锚（本行以下为增补区）
