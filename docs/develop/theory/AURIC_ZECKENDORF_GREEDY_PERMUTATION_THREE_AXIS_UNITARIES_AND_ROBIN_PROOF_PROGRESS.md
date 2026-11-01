<!-- editorial:front:start -->
# Zeckendorf 共同单项贪心排列、来源三轴、酉算子与 Robin 证明进展

> **原稿叙述与适用边界。** 下文保留所供原稿的开场、六节正文、论证与结尾；“我”“你”“此前”“本轮”“这次”等称谓及时间指向均属于原稿的对话叙述。原稿所说的“我核对了”、`✓ std3`、未见 `sorry` 或 `admit`、以及“本轮没有重新运行 Lean 编译”，均按原稿的历史检查陈述引用，不表示本卷完成了新的 Lean 编译或内核核验。第三至五节的纸面推导保留其明示条件；逐边酉算子的数学存在不提供原生操作、资源许可或物理实现证书，Robin 待证质量归零仍是未解决的数论目标。

正文导航：[开场](#opening) · [一、精确命题](#section-1) · [二、全覆盖证明](#section-2) · [三、来源三轴](#section-3) · [四、酉性](#section-4) · [五、Robin 进展](#section-5) · [六、未解目标](#section-6)。

原式导航：[（1）](#eq-1) · [（2）](#eq-2) · [（3）](#eq-3) · [（4）](#eq-4) · [（5）](#eq-5) · [（6）](#eq-6) · [（7）](#eq-7) · [（8）](#eq-8) · [（9）](#eq-9) · [（10）](#eq-10) · [（11）](#eq-11) · [（12）](#eq-12) · [（13）](#eq-13) · [（14）](#eq-14) · [（15）](#eq-15) · [（16）](#eq-16) · [（17）](#eq-17) · [（18）](#eq-18)。

<a id="opening"></a>

<!-- editorial:front:end -->

**你说得对，找到了。项目里确实已经有你说的完整证明。** 我此前优先按普通整数 $n,n+1$ 去理解“相邻”，没有对准你指的贪心序列，应当改正。

找到的是：

- **说明文档与定理 1.6**：[The One-Common-Zeckendorf-Term Greedy Permutation](https://github.com/the-omega-institute/trureturing/blob/9ceb721e13c64eb4b1c71a43238a2b2fc4770093/Blueprint/D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.md)。
- **Lean 原证明**：[ZeckendorfGreedyPermutation.lean](https://github.com/the-omega-institute/trureturing/blob/9ceb721e13c64eb4b1c71a43238a2b2fc4770093/D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.lean)。
- 最终定理声明：
  ```lean
  theorem result : IsGreedyPermutation a
  ```

我核对了定义、核心引理和最终证明。文档将其标记为 `✓ std3`，源文件给出了完整证明，没有用 `sorry` 或 `admit` 留空；本轮没有重新运行 Lean 编译。

**因此，“这条贪心路径是否遍历所有正整数”应当作为项目已经完成的定理使用。** 下面先还原它的证明，再把它与你提出的 AURIC 三轴、酉性、误差守恒和 Robin 判据连接起来。

---

<!-- editorial:section-anchor-1:start -->
<a id="section-1"></a>

<!-- editorial:section-anchor-1:end -->
## 一、项目证明的精确命题

取标准 Fibonacci 数列

$$
F_0=0,\qquad F_1=1,\qquad F_{k+2}=F_{k+1}+F_k.
$$

对正整数 $n$，记其标准 Zeckendorf 指数支持为 $S(n)$：

$$
n=\sum_{i\in S(n)}F_i,
$$

其中 $i\ge2$，且 $S(n)$ 中没有相邻指数。

定义关系

$$
n\sim m
\quad\Longleftrightarrow\quad
|S(n)\cap S(m)|=1.
$$

再定义

$$
a_1=1,
$$

<!-- editorial:eq-anchor-1:start -->
<a id="eq-1"></a>

<!-- editorial:eq-anchor-1:end -->
$$
\boxed{
a_{t+1}
=
\min\left\{
m\ge1:
m\notin\{a_1,\ldots,a_t\},\
|S(a_t)\cap S(m)|=1
\right\}.
}
\tag{1}
$$

这里最小化的是**整数数值**，排除的是**全部已访问历史**。

这就是 [OEIS A370630](https://oeis.org/A370630) 所描述的序列，其开头为

$$
1,4,3,11,8,9,6,5,7,2,10,12,\ldots
$$

例如

$$
1=\underline1,\qquad
4=\underline1+3,
$$

共享项为 $1$；接下来

$$
4=1+\underline3,\qquad
3=\underline3,
$$

共享项为 $3$。

### 项目定理：贪心共同单项排列

式（1）在每一步都有定义，所有项互不重复，并且

<!-- editorial:eq-anchor-2:start -->
<a id="eq-2"></a>

<!-- editorial:eq-anchor-2:end -->
$$
\boxed{
\forall n\ge1,\ \exists!t\ge1:\ a_t=n.
}
\tag{2}
$$

也就是：

> 每次取与当前项的 Zeckendorf 展开恰有一个共同项的最小未用整数，得到正整数的一个排列。

项目的定理 1.6 证明的正是这个完整断言，包括存在性、最小性、不重复和全覆盖。[来源：项目定理及定义 1.1—1.6](https://github.com/the-omega-institute/trureturing/blob/9ceb721e13c64eb4b1c71a43238a2b2fc4770093/Blueprint/D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.md)。

---

<!-- editorial:section-anchor-2:start -->
<a id="section-2"></a>

<!-- editorial:section-anchor-2:end -->
## 二、仓库证明为什么能够保证“一个整数都不漏”

这份证明最有价值的地方，是它给出了真正的全覆盖机制。下面按照源码中的主要引理整理成纸面证明。

### 第一步：永远有下一项

设当前项为 $c$。任选

$$
i\in S(c).
$$

取足够大的 $j$，使得 $j\ge i+2$、$j\notin S(c)$，并让

$$
F_i+F_j
$$

大于此前所有已用整数。

于是它的合法支持为 $\{i,j\}$，与 $S(c)$ 的交集恰为 $\{i\}$，而且没有用过。

因此候选集合非空，由正整数的良序性，最小候选存在。每一步又排除全部历史，所以整个序列无限存在且互不重复。

### 第二步：无界多个已访问邻居，会迫使目标出现

**引理。** 如果正整数 $m$ 有无界多个已经访问的邻居，即有无界多个已出现的 $x$ 满足 $x\sim m$，则 $m$ 必然被访问。

**证明。** 假设 $m$ 始终没有出现。每当 $a_t\sim m$，它都是一个合法未用候选，因此

$$
a_{t+1}\le m.
$$

无界多个已访问邻居给出无穷多个这样的时刻，而它们的后继互不重复，却全部落在有限集合

$$
\{1,\ldots,m\}
$$

中，矛盾。∎

这是源码中 `neighbor_covers` 的核心。

### 第三步：首次突破一个指数上界时，必然出现二项展开

固定任意 $B\ge2$。

由于序列无限且不重复，其支持不可能一直限制在有限指数集合 $\{2,\ldots,B\}$ 内。取第一次出现大于 $B$ 的指数的时刻 $t$，并令

$$
j=\max S(a_t)>B.
$$

设前后两项唯一的共同指数为 $i$。此前所有指数都不超过 $B$，所以

$$
i\le B<j.
$$

考虑

$$
p=F_i+F_j.
$$

因为 $i,j$ 同属于合法支持，二者不相邻，所以 $p$ 的标准支持就是 $\{i,j\}$。指数 $j$ 从未出现过，因此 $p$ 也未被访问，而且 $p\sim a_{t-1}$。

贪心最小性给出

$$
a_t\le p.
$$

另一方面，$F_i,F_j$ 都是 $a_t$ 的展开项，所以

$$
p\le a_t.
$$

因此

<!-- editorial:eq-anchor-3:start -->
<a id="eq-3"></a>

<!-- editorial:eq-anchor-3:end -->
$$
\boxed{a_t=F_i+F_j.}
\tag{3}
$$

这证明：**存在任意大第二指数的、已经访问过的二项支持。**

### 第四步：一个高指数二项支持，强制产生以 $F_2=1$ 为根的二项支持

假设已经访问

$$
q=F_i+F_j,
\qquad i\ge4,\quad j\ge i+2.
$$

我们证明

$$
p=F_i+1
$$

也必被访问。

如果 $p$ 已出现，结论成立。否则，由于

$$
S(p)=\{2,i\},\qquad S(q)=\{i,j\},
$$

它与 $q$ 恰好共享一项，故下一项 $x$ 满足

$$
x\le F_i+1.
$$

又因为

$$
F_i+1<F_j,
$$

$x$ 不可能包含 $F_j$，因此必须包含 $F_i$。于是

$$
F_i\le x\le F_i+1.
$$

只有两种可能：

$$
x=F_i
\quad\text{或}\quad
x=F_i+1.
$$

后一种已经完成。前一种情况下，再下一项仍不超过 $F_i+1$，仍须包含 $F_i$，而 $F_i$ 已被用过，所以再下一项只能是 $F_i+1$。

因此：

<!-- editorial:eq-anchor-4:start -->
<a id="eq-4"></a>

<!-- editorial:eq-anchor-4:end -->
$$
\boxed{
F_i+F_j\text{ 已访问},\ i\ge4
\Longrightarrow
F_i+1\text{ 已访问}.
}
\tag{4}
$$

而且若此前未出现，最多再走两步就会出现。

### 第五步：必有一个固定根，连接无界多个已访问二项支持

我们要证明存在 $r\ge2$，使

<!-- editorial:eq-anchor-5:start -->
<a id="eq-5"></a>

<!-- editorial:eq-anchor-5:end -->
$$
\forall B\ \exists j>B:
\quad
r+2\le j,\qquad F_r+F_j\text{ 已访问}.
\tag{5}
$$

反设没有这样的根。那么，对每个固定的 $i$，所有已经访问的二项支持 $\{i,j\}$ 中，第二指数 $j$ 都有一个上界 $C_i$。

固定 $I\ge4$，对有限多个根取共同上界

$$
C=\max_{2\le i\le I}C_i.
$$

根据第三步，有一个已经访问的二项支持 $\{i,j\}$，满足 $j>C$。这迫使

$$
i>I.
$$

再由第四步，$\{2,i\}$ 已经访问。

由于 $I$ 可以任意大，我们得到了根为 $2$、第二指数无界的已访问二项支持。这与反设矛盾。

所以式（5）成立。∎

这里的量词处理很关键：只对**有限多个根**取共同上界，没有把逐点有界误当成全局一致有界。

### 第六步：覆盖性质从一个根传播到全部整数

定义

$$
H(r):
\quad
\text{所有支持包含 }r\text{ 的正整数，都已经访问。}
$$

首先，式（5）中的根 $r$ 满足 $H(r)$。

因为对任何包含 $r$ 的目标 $m$，无界多个已访问支持 $\{r,j\}$ 中，可以取 $j>\max S(m)$。它们与 $S(m)$ 的交集恰为 $\{r\}$。由第二步，$m$ 必出现。

接着证明传播规则：

<!-- editorial:eq-anchor-6:start -->
<a id="eq-6"></a>

<!-- editorial:eq-anchor-6:end -->
$$
\boxed{
H(r),\quad |r-s|\ge2
\Longrightarrow H(s).
}
\tag{6}
$$

任取包含 $s$ 的目标 $m$。如果它也包含 $r$，已由 $H(r)$ 覆盖。否则，取任意大的 $t$，使 $\{r,s,t\}$ 是合法支持，并且 $t>\max S(m)$。

整数

$$
F_r+F_s+F_t
$$

包含 $r$，所以已经访问；它与目标 $m$ 的支持交集恰为 $\{s\}$。令 $t$ 无界，再用第二步，得到 $m$ 必出现。

最后，对任意指数 $k\ge2$，选取

$$
s>\max\{r,k\}+1.
$$

先由 $H(r)$ 推出 $H(s)$，再推出 $H(k)$。因此每个指数都是覆盖根。每个正整数的支持非空，故每个正整数都被访问。

结合不重复性，式（2）得到证明。∎

以上分别对应源码中的 `exists_next`、`neighbor_covers`、`record_pairs`、`pair_forces_two`、`rooted_pairs`、`root_hub` 和 `hub_propagates`。它使用的是实际的全历史贪心规则，全覆盖结论不依赖有限枚举。[来源：Lean 原证明](https://github.com/the-omega-institute/trureturing/blob/9ceb721e13c64eb4b1c71a43238a2b2fc4770093/D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.lean)。

---

<!-- editorial:section-anchor-3:start -->
<a id="section-3"></a>

<!-- editorial:section-anchor-3:end -->
## 三、由这个已证定理，确实可以构造你说的三个正交方向

以下是在项目定理基础上的进一步推导。

沿这条贪心路径取相邻两项

$$
n=a_t,\qquad m=a_{t+1}.
$$

由定理，

$$
S(n)\cap S(m)=\{k\}.
$$

记唯一共有项为

$$
c=F_k.
$$

于是两个展开自然分成三个互不相交的部分：

$$
\text{左侧独有项},\qquad
\text{右侧独有项},\qquad
\text{共有项 }F_k.
$$

它们的总权重分别是

$$
\alpha=n-c,\qquad
\beta=m-c,\qquad
c.
$$

### 定义：共同来源的归一化读出

令

$$
D=n+m-c=\alpha+\beta+c,
$$

并定义

<!-- editorial:eq-anchor-7:start -->
<a id="eq-7"></a>

<!-- editorial:eq-anchor-7:end -->
$$
\boxed{
X=\frac{\alpha}{D},\qquad
Y=\frac{\beta}{D},\qquad
Z=\frac{c}{D}.
}
\tag{7}
$$

那么

$$
X,Y\ge0,\quad Z>0,\qquad X+Y+Z=1.
$$

项目的 AURIC 金字塔为

$$
\mathcal P
=
\{(X,Y,Z):
X,Y,Z\ge0,\ X+Z\le1,\ Y+Z\le1\}.
$$

所以式（7）必在 $\mathcal P$ 内。更具体地，它位于三个顶点 $v_2,v_5,v_3$ 张成的三角截面中。采用项目五模式顺序 $(0,2,3,5,25)$，对应概率律可明确取为

$$
(p_0,p_2,p_3,p_5,p_{25})
=
(0,X,Z,Y,0).
$$

这与项目金字塔的定义完全一致。[来源：基础公式卷，§二—三](https://github.com/the-omega-institute/trureturing/blob/9ceb721e13c64eb4b1c71a43238a2b2fc4770093/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)。

### 两个二元读出和一个守恒关系

在两个支持的并集上，给原子 $i$ 分配概率 $F_i/D$。

令 $A$ 表示“属于左侧整数的支持”，$B$ 表示“属于右侧整数的支持”。它们都是二元读出，并满足

$$
\mathbb EA=X+Z=\frac nD,
$$

$$
\mathbb EB=Y+Z=\frac mD,
$$

$$
\mathbb E(AB)=Z=\frac cD.
$$

因此

<!-- editorial:eq-anchor-8:start -->
<a id="eq-8"></a>

<!-- editorial:eq-anchor-8:end -->
$$
\boxed{
\mathbb EA+\mathbb EB-\mathbb E(AB)=1.
}
\tag{8}
$$

**这正好把你说的“两个读出、一个关系、归一化”落实到了实际 Zeckendorf 来源上。** 共有项在两个读出中各出现一次，因此总量关系需要扣除一次共有部分。

保留尺度 $D$，即可恢复

$$
n=D(X+Z),\qquad m=D(Y+Z),\qquad c=DZ.
$$

也可以只保留共有项 $c=F_k$，通过

$$
n=c\left(1+\frac XZ\right),\qquad
m=c\left(1+\frac YZ\right)
$$

恢复两个整数。

### 定理：每条共同单项边具有至多三维的正交实现

取 Fibonacci 原子空间

$$
\mathcal H_F=\ell^2(\{2,3,\ldots\}),
$$

其正交单位基为 $e_i$。定义

<!-- editorial:eq-anchor-9:start -->
<a id="eq-9"></a>

<!-- editorial:eq-anchor-9:end -->
$$
\psi_n
=
\sum_{i\in S(n)}
\sqrt{\frac{F_i}{n}}\,e_i.
\tag{9}
$$

因为展开权重之和为 $n$，所以

$$
\|\psi_n\|=1.
$$

当 $\alpha,\beta>0$ 时，定义

$$
e_C=e_k,
$$

$$
e_L=
\frac1{\sqrt\alpha}
\sum_{i\in S(n)\setminus\{k\}}\sqrt{F_i}\,e_i,
$$

$$
e_R=
\frac1{\sqrt\beta}
\sum_{i\in S(m)\setminus\{k\}}\sqrt{F_i}\,e_i.
$$

三个来源支持互不相交，因此

$$
\langle e_L,e_R\rangle
=
\langle e_L,e_C\rangle
=
\langle e_R,e_C\rangle=0,
$$

并且各向量的范数都为 $1$。同时

$$
\psi_n
=
\sqrt{\frac{\alpha}{n}}e_L
+
\sqrt{\frac cn}e_C,
$$

$$
\psi_m
=
\sqrt{\frac{\beta}{m}}e_R
+
\sqrt{\frac cm}e_C.
$$

这证明了所需三轴分解。∎

若某个独有部分为空，实际有效空间是二维；可以补一个零振幅的闲置正交方向，统一写成三轴。

**这里的三个正交方向有明确的原子来源。**

---

<!-- editorial:section-anchor-4:start -->
<a id="section-4"></a>

<!-- editorial:section-anchor-4:end -->
## 四、酉性也能够严格接上，但需要说明是哪一种酉性

### 定理：每条边都可以构造一个明确的酉门

由唯一共有项，

$$
\mu=\langle\psi_n,\psi_m\rangle
=\frac c{\sqrt{nm}}.
$$

相邻项不同，故 $0<\mu<1$。定义

$$
w=\frac{\psi_n-\psi_m}{\|\psi_n-\psi_m\|},
$$

<!-- editorial:eq-anchor-10:start -->
<a id="eq-10"></a>

<!-- editorial:eq-anchor-10:end -->
$$
\boxed{
H_{n,m}=I-2|w\rangle\langle w|.
}
\tag{10}
$$

则

$$
H_{n,m}^{\dagger}H_{n,m}=I,
\qquad
H_{n,m}\psi_n=\psi_m.
$$

**证明。** 记 $P_w=|w\rangle\langle w|$。由于 $w$ 是单位向量，

$$
P_w^2=P_w=P_w^\dagger.
$$

所以

$$
H^\dagger H=(I-2P_w)^2=I.
$$

又因为

$$
\|\psi_n-\psi_m\|^2=2(1-\mu),
$$

直接代入可得

$$
2P_w\psi_n=\psi_n-\psi_m,
$$

故 $H\psi_n=\psi_m$。∎

这个门只作用于上述局部三轴块，在其正交补上为恒等映射。

因此已经得到：

<!-- editorial:eq-anchor-11:start -->
<a id="eq-11"></a>

<!-- editorial:eq-anchor-11:end -->
$$
\boxed{
\text{已证全遍历路径}
\longrightarrow
\text{每条边的共同来源三轴}
\longrightarrow
\text{每条边的真实酉门}.
}
\tag{11}
$$

对同一个准确门，已有状态误差满足

$$
\|H(\widetilde\psi-\psi)\|
=
\|\widetilde\psi-\psi\|.
$$

所以它不会放大已有的态误差。若每一步又引入新的误差 $\varepsilon_t$，则仍需累计估计，例如

$$
\text{第 }T\text{ 步误差}
\le
\text{初始误差}
+
\sum_{t<T}\varepsilon_t.
$$

### 排列定理还给出一个全局酉重标号

在整数标签的正交基上定义

$$
\mathsf P|t\rangle=|a_t\rangle.
$$

由于项目已经证明 $a$ 是双射，它把完整正交基重排为完整正交基，因此

<!-- editorial:eq-anchor-12:start -->
<a id="eq-12"></a>

<!-- editorial:eq-anchor-12:end -->
$$
\boxed{
\mathsf P^\dagger\mathsf P
=
\mathsf P\mathsf P^\dagger=I.
}
\tag{12}
$$

这是“全覆盖”与“酉性”之间直接而严格的连接。

不过，沿单向路径走一步的映射

$$
V|a_t\rangle=|a_{t+1}\rangle
$$

满足

$$
V^\dagger V=I,\qquad
VV^\dagger=I-|1\rangle\langle1|.
$$

它缺少到达起点的前驱，所以是等距移位。式（12）的排列重标号，以及式（10）的逐边酉门，则都是真正的酉算子。

此外，局部三轴需要保留其来源标架。因为排列访问所有 Fibonacci 数，并且

$$
\psi_{F_k}=e_k,
$$

全体来源态包含无限多个正交方向。项目《观察者内生的三轴几何与预测接口》§八也要求：若固定三读数要决定全部未来，必须证明相应读出对全部后续操作具有闭合性。[来源：三轴预测接口，§八](https://github.com/the-omega-institute/trureturing/blob/9ceb721e13c64eb4b1c71a43238a2b2fc4770093/docs/develop/theory/AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md)。

---

<!-- editorial:section-anchor-5:start -->
<a id="section-5"></a>

<!-- editorial:section-anchor-5:end -->
## 五、把它接到 Robin 判据：可以得到一个精确的“三轴证明进展定理”

这一部分直接回应你前面提出的“结果、误差、总量守恒，然后持续递归”。

<!-- editorial:robin-notation:start -->
> **记号约定。** σ(n) 为 n 的正约数之和，γ 为 Euler–Mascheroni 常数，e 为自然对数的底，log 为自然对数，RH 表示黎曼猜想。区间始终包住同一个真实算术量 b(n)；“持续细化”要求每个固定已访问点都得到公平细化，且严格正下界在有限延迟后登记并永久保留。这个条件定理不自行提供区间取得算法或全局有效收敛速率。待证质量 E 可以在访问新整数时增加。

<!-- editorial:robin-notation:end -->

定义

$$
R(n)=\frac{\sigma(n)}{e^\gamma n\log\log n},
\qquad n>5040.
$$

Robin 判据为

<!-- editorial:eq-anchor-13:start -->
<a id="eq-13"></a>

<!-- editorial:eq-anchor-13:end -->
$$
\boxed{
\mathrm{RH}
\iff
\forall n>5040,\ R(n)<1.
}
\tag{13}
$$

这里必须保留严格不等号。[来源：Robin 判据的标准表述](https://www.numdam.org/item/10.5802/jtnb.591.pdf)。

<!-- editorial:numdam-attribution:start -->
> **文献归属注。** 上述 Numdam 链接指向 Y. Choie、N. Lichiardopol、P. Moree 与 P. Solé 的论文 *On Robin’s criterion for the Riemann hypothesis*，Journal de Théorie des Nombres de Bordeaux 19 (2007)，357–372；其摘要与引言重述 Robin 判据。它不是 Robin 的原始论文，原始结果见该文参考文献 [9]：G. Robin，*Grandes valeurs de la fonction somme des diviseurs et hypothèse de Riemann*，J. Math. Pures Appl. (9) 63 (1984)，187–213。原稿的“Robin 判据的标准表述”及链接原样保留。

<!-- editorial:numdam-attribution:end -->

先将真实的算术裕量归一化：

$$
b(n)=\frac{1-R(n)}{1+R(n)}\in(-1,1).
$$

于是

<!-- editorial:eq-anchor-14:start -->
<a id="eq-14"></a>

<!-- editorial:eq-anchor-14:end -->
$$
b(n)>0\iff R(n)<1.
\tag{14}
$$

### 定义：已证明、已访问未证明、尚未访问三种质量

对每个 $n>5040$，赋予严格正权重

$$
w_n=2^{-(n-5040)}.
$$

因此

$$
\sum_{n>5040}w_n=1.
$$

沿项目已经证明的排列，记前 $j$ 项中大于 $5040$ 的已访问集合为

$$
V_j=\{a_1,\ldots,a_j\}\cap\{n>5040\}.
$$

对每个已访问的 $n$，持续构造可靠区间

$$
\ell_{n,j}\le b(n)\le u_{n,j},
$$

并要求每个已访问点都持续得到细化，使其区间宽度趋于零。凡是下界已经严格大于零的整数，进入已证明集合 $A_j$，已有证据持续保留。

定义

$$
G_j=\sum_{n\in A_j}w_n,
$$

$$
E_j=\sum_{n\in V_j\setminus A_j}w_n,
$$

$$
U_j=\sum_{\substack{n>5040\\n\notin V_j}}w_n.
$$

其含义为：

| 读出 | 含义 |
|---|---|
| $G_j$ | 已经严格证明满足 Robin 不等式的质量 |
| $E_j$ | 已经访问，但尚未取得严格正性证书的质量 |
| $U_j$ | 尚未访问的质量 |

这里 $E_j$ 衡量的是**待证明质量**，并非某个数值计算的绝对误差。

显然

<!-- editorial:eq-anchor-15:start -->
<a id="eq-15"></a>

<!-- editorial:eq-anchor-15:end -->
$$
\boxed{G_j+E_j+U_j=1.}
\tag{15}
$$

所以这又是一个有明确来源、归一化并守恒的三轴读出，可放入同一个 AURIC 三角截面。

### 定理：排列无条件消除未访问质量，剩余待证质量精确对应 Robin 反例集

令

<!-- editorial:eq-anchor-16:start -->
<a id="eq-16"></a>

<!-- editorial:eq-anchor-16:end -->
$$
B=
\sum_{\substack{n>5040\\R(n)\ge1}}w_n.
\tag{16}
$$

在上述可靠区间与持续细化条件下，

<!-- editorial:eq-anchor-17:start -->
<a id="eq-17"></a>

<!-- editorial:eq-anchor-17:end -->
$$
\boxed{
(G_j,E_j,U_j)
\longrightarrow
(1-B,\ B,\ 0).
}
\tag{17}
$$

因而

<!-- editorial:eq-anchor-18:start -->
<a id="eq-18"></a>

<!-- editorial:eq-anchor-18:end -->
$$
\boxed{
\mathrm{RH}
\iff E_j\longrightarrow0
\iff G_j\longrightarrow1.
}
\tag{18}
$$

#### 证明第一部分：$U_j\to0$

项目排列定理保证每个正整数都会在某个有限时刻出现。

给定 $M$，有限多个整数

$$
5041,\ldots,5040+M
$$

因此都会在某个有限阶段全部被访问。此后

$$
U_j
\le
\sum_{r>M}2^{-r}
=
2^{-M}.
$$

由于 $M$ 任意，

$$
U_j\to0.
$$

**这一项已经由项目中的全覆盖定理无条件解决。**

#### 证明第二部分：每个严格满足 Robin 的整数最终取得证书

若 $R(n)<1$，则 $b(n)>0$。

因为区间包含 $b(n)$，且宽度趋于零，

$$
\ell_{n,j}
\ge
b(n)-(u_{n,j}-\ell_{n,j}).
$$

细化到宽度小于 $b(n)$ 时，就有

$$
\ell_{n,j}>0.
$$

所以每个满足严格 Robin 不等式的整数，最终进入 $A_j$。

#### 证明第三部分：违反严格不等式的整数保留在待证部分

若 $R(n)\ge1$，则 $b(n)\le0$。

可靠下界始终满足

$$
\ell_{n,j}\le b(n)\le0,
$$

因此它不会被错误地纳入已证明集合。排列定理又保证它最终会被访问，所以此后它一直为 $E_j$ 贡献权重 $w_n$。

于是，对每个固定 $n$，待证指示量最终趋于

$$
\mathbf1_{\{R(n)\ge1\}}.
$$

权重总和为 $1$。先截取有限多个整数，再控制其后的几何级数尾部，即得

$$
E_j\to
\sum_{\substack{n>5040\\R(n)\ge1}}w_n
=B.
$$

再由守恒式（15），得到 $G_j\to1-B$。式（17）得证。

由于每个 $w_n>0$，

<!-- editorial:macro-expansion:start -->
> **排版注（保留原文）。** 原稿本式的字面内容为 `B=0 \iff \不存在 n>5040\text{ 使 }R(n)\ge1.`；其中 `\不存在` 不是标准 TeX 命令，正文公式将该命令显式展开为 `\text{不存在}`，含义仍为“不存在”，不改变严格不等式及其否定。

<!-- editorial:macro-expansion:end -->

$$
B=0
\iff
\text{不存在} n>5040\text{ 使 }R(n)\ge1.
$$

结合 Robin 判据，得到式（18）。∎

---

<!-- editorial:section-anchor-6:start -->
<a id="section-6"></a>

<!-- editorial:section-anchor-6:end -->
## 六、这次找到的证明，究竟推进了哪一部分

现在可以把逻辑关系说得很明确：

$$
\boxed{
\begin{aligned}
&\text{项目已证：共同单项贪心序列覆盖全部正整数；}\\
&\text{可进一步证明：每条边有自然三轴分解与逐边酉实现；}\\
&\text{可进一步证明：归一化证明状态中的未访问质量趋于零。}
\end{aligned}
}
$$

对于 RH，剩下的具体目标是证明

$$
E_j\longrightarrow0.
$$

单纯的有界性

$$
0\le E_j\le1
$$

和守恒性

$$
G_j+E_j+U_j=1
$$

尚不能推出这一点：式（17）明确显示，如果存在一个违反 Robin 严格不等式的整数，它就会留下一个严格正的剩余权重。

**所以，你指出的项目证明确实有用，而且应当正式进入后续推理的已证基础。** 它已经解决了“递归路径是否遗漏整数”的问题，并使共同项、三轴读出和酉门之间有了严格接口。接下来的数论任务应集中在：怎样利用实际素因子结构、约数和估计或可靠的递归证书，证明所有已访问整数的 Robin 待证质量最终归零。
