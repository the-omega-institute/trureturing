# 互读不超自读

> 参考输入：AI 撰写的工作稿，由用户提供于本会话（2026-11-04，Asia/Singapore）。Lean 是仓库的数学真源；本文仅为参考文稿，未作形式化认证。

AURIC 量子关系研究

从有限整数配方重建量子正关系

C130

两份历史互相对照的读数，

不超过它们各自对照读数的平均。

$$
\boxed{2\Re B(f,g)\le\Re B(f,f)+\Re B(g,g),
 \quad f,g\in\mathbb Z[i]^{(X)}.}
$$

$$
B(f,g)=\sum_{h,k}\overline{f(h)}K(h,k)g(k).
$$

原始输入仍只有历史标签集 $X$ 与复数值二元表 $K$。
本轮取消追加次序、余量存在式和公理中的模号；有限配方只需高斯整数系数。
共轭对称、全部有限正性、Hilbert 表示及 C129 的正交续写均由这一个实不等式恢复。

形式配方不等于物理制备；复数、共轭、实部、实数序及全部有限组合仍是明确前件。

固定源码：`8e15c484cf57`
提交时点：2026-11-04 16:25:41，Asia/Singapore
本轮核对与 C129 相同，无新增提交或源码差分

自包含工作稿：定义、定理、证明、反例与精确几何

## 摘要与本轮的简化

本轮的唯一候选是封面的一条互读界。先给任意原始二元表 $K:X\times X\to\mathbb C$，把有限高斯整数配方的比较定义成同核有限和。候选不预给 Hermitian 性、非负自比较、物理态空间或正单位。取第二配方为零先给自比较实部非负；再比较 $nf$ 与 $(n+i)f$，其预算差为 $\Re Q(f)+2n\Im Q(f)$。整数 $n$ 的双向无界性迫使虚部为零。由有限基组合恢复共轭对称，清分母及每张有限矩阵的连续性再给全部复配方的正性。

由此构造 Hilbert 比较空间，并恢复 C129 的奇异 Schur 续写。公理本身只是一条线性预算半空间；对相位和相反尺度的推论分别给三维圆锥与完整二阶正锥，归一截面为 Bloch 球。原矩阵过程的来源核再把同一互读界接到完全正性，完整效果及实际接口接到 Born、仪器、复合和酉时间规则。

与 C129 相比，最初的 $X,K$ 两个对象没有继续减少；简化发生在约束形式、辅助对象和测试系数域。模型类仍恰为复正型核，不能将等价呈现称作逻辑更弱或已经证明的量子物理起源。标准复数结构、有限和规则、无界有限配方与实际相干接口仍须分别保留。

| 项目 | C129 | C130 |
|---|---|---|
| 原始对象 | 历史集合与任意复核 | 相同 |
| 约束形式 | 有序分块续写等式 | 无序的单个实不等式 |
| 辅助见证 | 每步存在 $c,r$ | 不需要存在见证 |
| 测试系数 | 续写中的任意复系数 | 有限高斯整数配方足够 |
| 显式几何 | 旧影子加平方余量 | 互读半空间；圆锥为推论 |
| Hermitian 与正性 | 由块式恢复 | 由整数自比较探针恢复 |
| 物理操作 | 须接原控制与记录 | 同样须认证这些接口 |

## 目录

- [1. 项目定位：从正性图形退到一条实比较](#section-1)
- [2. 唯一候选：两份配方的互读不超自读总额](#section-2)
- [3. 从互读界构造内积，并回收前两轮](#section-3)
- [4. 线性预算如何围成圆锥](#section-4)
- [5. 从互读界恢复有限量子规则](#section-5)
- [6. 内生接续、观察窗口与有限证据](#section-6)
- [7. 本轮唯一候选与完整白话](#section-7)
- [参考文献](#references)

<a id="section-1"></a>

## 1. 项目定位：从正性图形退到一条实比较

<a id="sec-c130-source"></a>

本轮一次性核对默认分支 `dev`，HEAD 仍为
`8e15c484cf5786fe69fef0627fd84a63cfeb5942`，与 C129 完全相同。
提交时点为 2026-11-04 16:25:41（Asia/Singapore）。整提交、理论、量子和概念动力学子树均为零差分；上一轮登记的 Bajnok–Beatty 合并不再算作本轮新进展 [1](#ref-repo-c130-pin)。

### 1.1 项目已有的等价不能重复算成新发现

V71 定义 5.2 与定理 5.3 已在固定 Hermitian 核及其同一半双线性延拓下，证明全部有限复合对象的二元正性等价于全部有限 Gram 正性。C114 定义 5.1、定理 6.1 把同一核心写成每棵有限合成树的每个节点都满足球约束 [2](#ref-repo-c130-v71)、[3](#ref-repo-c130-c114)。

因此，仅把条件改称“任意两个复合对象相容”，不足以形成新的前件简化。
C129 已经退到任意原始复核；本轮在这个起点上，进一步去掉顺序、Schur 余量和模号，并证明高斯整数配方足以承担全部量词。数学选择内容依然是正型核。

C114 例 6.3 还给出

$$
G=\tfrac75I_4-\tfrac25J_4.
$$

每个三阶及更小主块都正定，整个矩阵却有负特征值 $-1/5$。所以“三维有限提升”不能被理解为只检查所有原始三点；本轮的两个输入都允许是任意有限配方。

### 1.2 为什么先检查互读与自读的相容

把每个对象的自比较当作它在同一接口中的读数，把两对象的实交叉比较当作相互读数。候选要求互读的两倍不超过自读合计。若这条关系在某个有限配方上失败，扣除两边的相互响应后会出现负差；若自比较夹有虚部，则把同一配方作整数增益和四分之一相位差的对照，会让预算差向负方向无界变化。

这些后果将在后面严格证明。其物理解释仍以原比较确实对应那些读出为条件；尚未供应的控制不能用形式配方冒充。本文把“满足互读界的关系系统”定义成一个数学模型类，而实际世界是否属于它仍是需要原始证据支持的命题。

**白话。**上轮先说新历史要接成旧影子加余边；这轮退到更早的一步：两边互相对照，不能比两边各自对照合起来读得更多。先只检查有限加减与四分之一相位的配方，内积、圆锥和余边随后才出现。

<a id="section-2"></a>

## 2. 唯一候选：两份配方的互读不超自读总额

<a id="sec-c130-budget"></a>

本轮从集合 $X$ 和任意复值二元核 $K:X\times X\to\mathbb C$ 开始，不预设 Hermitian 性、正性或物理态向量空间。有限配方只是在原标签上写下有限个系数，尚不是已经供应的物理相干操作。

### 定义 2.1（有限整数配方与聚合比较）

令 $\mathcal R_0=\mathbb Z[i]^{(X)}$ 为有限支撑的 Gaussian 整数配方；空配方为 $0$，单标签配方为 $\delta_h$。定义

$$
B(f,g)=\sum_{h,k}\overline{f(h)}K(h,k)g(k),
 \qquad Q(f)=B(f,f).
$$

每次只有有限和，$Q(f)$ 暂时可以是复数。下文的有理或复配方，均指对同一有限求和公式扩充系数，未另加物理态或控制。

### 定义 2.2（C130：二元互读界）

对每两份有限整数配方 $f,g\in\mathcal R_0$，要求

<a id="eq-c130-budget"></a>

$$
\boxed{2\Re B(f,g)\le\Re Q(f)+\Re Q(g).}
\tag{1}
$$

同一核、同一原尺度用于三项比较。两配方可以相同，也可以有一份为空；没有预先给定正单位、追加顺序、伪逆或新余量。

### 定理 2.3（整数配方已决定全部有限正性）

<a id="thm-c130-psd"></a>

以下等价：C130；将其配方系数改为 $\mathbb Q(i)$ 后的同一条件；将其配方系数改为 $\mathbb C$ 后的同一条件；以及 $K$ 为 Hermitian 正型核，即每张有限表 $[K(h_j,h_k)]$ 正半定。零核与空标签集合均包含。

**证明。**
先固定整数配方 $f$，写 $Q(f)=a+ib$。取 $g=0$，得 $a\ge0$。对任意整数 $n$，$F=nf$ 与 $G=(n+i)f$ 仍是合法整数配方。其预算差恰为

<a id="eq-c130-integer-shear"></a>

$$
\Re Q(F)+\Re Q(G)-2\Re B(F,G)=a+2nb.
\tag{2}
$$

若 $b\ne0$，取绝对值足够大的反号整数 $n$，右侧就为负。由标准实数的阿基米德性质，必有 $b=0$。因此所有整数配方的 $Q(f)$ 都是非负实数。

对任意两个标签，$Q(\delta_h)$ 给实对角。$Q(\delta_h+\delta_k)$ 为实，给
$\Im(K(h,k)+K(k,h))=0$；$Q(\delta_h+i\delta_k)$ 为实，给
$\Re(K(h,k)-K(k,h))=0$。两式合起来正是 $K(k,h)=\overline{K(h,k)}$。

任意有限有理配方可用同一个正整数 $N$ 清分母。有限和的定义给
$Q(Nf)=N^2Q(f)$；两配方的预算差也同时乘 $N^2$，所以整数结论延伸到有理配方。在任意固定有限标签表上，用有理实、虚部分逐项逼近复系数。二次多项式连续，非负实轴闭，故所有有限复配方的 $Q(f)$ 仍为非负实数，即全有限正性。这里没有给标签集合 $X$ 添加拓扑，也没有假设实际控制连续可调。

反向，若核为 Hermitian 正型核，则对任意有限复配方，

<a id="eq-c130-difference-square"></a>

$$
\Re Q(f)+\Re Q(g)-2\Re B(f,g)=Q(f-g)\ge0.
\tag{3}
$$

所以复、有理与整数版本全部成立。

**为何不能只看实整数。**

单标签核 $K(h,h)=1+i$ 对所有实整数配方满足式 [(1)](#eq-c130-budget)：其预算差就是 $(f-g)^2$。然而自比较并非实数。允许 $i$ 系数后，式 [(2)](#eq-c130-integer-shear) 将它否决；虚对角没有被取实部悄悄丢弃。

**减少了什么，仍保留什么。**

核心只用两个有限配方的一条实不等式，不再用按序延拓或存在余量；任意精确复幅度也不必出现在候选量词中。其数学内容仍等价正型核，不能据此宣称已经从纯日志顺序推出量子正性。标准复数及共轭、聚合的有限双和公式、全部有限配方及其无统一上界的整数系数仍承重。整数配方在记号上可由四种相位 $1,-1,i,-i$ 与有限重复组成；负系数不是删除已存历史，$nf$ 也不是确定放大未知归一态。这不供应物理复制、任意相干控制或无代价的大幅度实验。

**白话。**先拿两份有限写法，比较它们彼此能读到多少，再与各自读到的总额相对照。只要求互读不透支这两份自读。把同一份写法重复若干次，再错开一个四分之一相位，藏在自比较里的虚部就不能一直蒙混过关。共轭对称与正性因此由同一条比较约束一起出现，尚不用指定谁先写入。

<a id="section-3"></a>

## 3. 从互读界构造内积，并回收前两轮

<a id="sec-c130-hilbert"></a>

正核表示属于经典数学 [5](#ref-aronszajn1950)；这里从本轮条件给出完整构造。

### 定理 3.1（零差商、最小表示与唯一性）

<a id="thm-c130-hilbert"></a>

C130 成立后，构造自由复线性包络 $\mathcal F=\mathbb C^{(X)}$，在其中沿用有限和 $B$。令 $\mathcal N=\{f:Q(f)=0\}$。则 $\mathcal N$ 为根空间，$\mathcal F/\mathcal N$ 具有内积，其完成 $\mathcal H$ 满足

$$
\iota(h)=[\delta_h],\qquad
 K(h,k)=\langle\iota(h),\iota(k)\rangle,
 \qquad\overline{\operatorname{span}\iota(X)}=\mathcal H.
$$

保持同一历史核的最小表示唯一到酉等价，不要求 $\iota$ 单射。

**证明。**
前节已证明 $B$ Hermitian 正半定；半双线性来自有限和定义。若 $Q(f)=0$，则任意复数 $t$ 都给

$$
Q(f+tg)=2\Re(tB(f,g))+|t|^2Q(g)\ge0.
$$

若 $B(f,g)\ne0$，选反号相位和足够小的 $t$ 即矛盾，故 $B(f,g)=0$ 对所有 $g$ 成立。反向显然，所以零集合就是线性根空间，商内积良定义。完成与标签表示遂得。

两份最小表示之间，将同系数有限组合互相对应；两边范数均由同一核计算，因此零向量也对应，映射良定义且等距。稠密性使它唯一延伸为酉算符。零核给零空间，也无例外。

### 3.1 四个自读恢复互读，平方差给真正的距离

同一有限和的极化恒等式为

<a id="eq-c130-polarization"></a>

$$
B(f,g)=\frac14\bigl[Q(f+g)-Q(f-g)
 -iQ(f+ig)+iQ(f-ig)\bigr].
\tag{4}
$$

确实，前两项之差是 $2(B(f,g)+B(g,f))$，后两种自读之差是 $2i(B(f,g)-B(g,f))$，代回即得。整数配方的这四份组合仍为整数配方；数值恢复恒等式不等于已供应四次物理相干制备。

令 $D(f,g)$ 为候选左右之差。通过候选后，式 [(3)](#eq-c130-difference-square) 给
$D(f,g)=Q(f-g)$，而

$$
d(f,g)=\sqrt{D(f,g)}=\|[f]-[g]\|
$$

是配方上的伪距离、零差商上的距离。为核验三角不等式，记 $p=Q(f),q=Q(g),z=B(f,g)$。$q>0$ 时，对 $f-(\bar z/q)g$ 评价给 $|z|^2\le pq$；$q=0$ 时，根空间结论给 $z=0$。于是
$Q(u+v)\le(\sqrt{Q(u)}+\sqrt{Q(v)})^2$，即得三角不等式。
平方 $D$ 本身一般不满足三角不等式：在一维标准比较中，$D(0,2)=4>2=D(0,1)+D(1,2)$。不能把平方差直接当作度量。它也是带尺度的形式向量平方差，不是物理射线距离：归一 $v$ 与 $iv$ 在通常纯态表示中属于同一射线，却有 $D(v,iv)=2$。

### 3.2 C129 的奇异续写成为推论

取旧有限列表与一条新历史，其正表写成
$\left(\begin{smallmatrix}G&b\\b^*&q\end{smallmatrix}\right)$。若 $u\in\operatorname{ker} G$，对应旧组合自比较为零，根空间结论迫使 $u^*b=0$；故 $b\in\operatorname{Ran} G$。
此时才引入数学计算用的 $c=G^+b$。在 $(-c,1)$ 上评价得到
$s=q-b^*G^+b\ge0$，选 $r$ 满足 $|r|^2=s$，恢复

<a id="eq-c130-recovers-c129"></a>

$$
G_{L+h}=\begin{pmatrix}G&Gc\\c^*G&c^*Gc+|r|^2\end{pmatrix}.
\tag{5}
$$

若 $G=0$，结论先强制 $b=0$，再有 $q=|r|^2$；所有奇异边界均保留。伪逆和新余量是定理中的计算坐标，未回到本轮候选的输入。

反向，从空表反复使用这一块式，可写成
$T^*\operatorname{diag}(G,|r|^2)T$，其中 $T=\left(\begin{smallmatrix}I&c\\0&1\end{smallmatrix}\right)$；归纳得到每张有限表正，再由定理 [2.3](#thm-c130-psd) 恢复本轮互读界。因此两种表达选择相同的核类，追加次序不是正性的额外来源。

### 3.3 C128 的微移与正单位的位置

在构造的比较空间中，任意中心 $a$、方向 $z$ 与复系数 $t$ 满足

$$
Q(a+tz)+Q(a-tz)-2Q(a)=2|t|^2Q(z)\in\mathbb R_{\ge0}.
$$

这就回收 C128。反过来，若原半双线性比较已满足 C128，非零微移给全部 $Q\in\mathbb R_{\ge0}$，极化给 Hermitian 性，式 [(3)](#eq-c130-difference-square) 再给互读界。
本轮仍允许零核；正单位与概率归一化不由候选独自出现。若后来原完整记录供应 $Q(e)=1$，两个根空间元素的和不能等于 $e$，也就恢复 C127 的单位不可双零分解。

**白话。**互读界通过以后，两份写法还剩多少不同，就正好成为它们差别的平方。平方为零的写法在全部比较中可互换，把这些零差合并，就得到内积。此前用到的新影子、新余量和相反微移，都能从这个空间重新算出来；本轮把它们从起点挪到了结果里。

<a id="section-4"></a>

## 4. 线性预算如何围成圆锥

<a id="sec-c130-geometry"></a>

本节使用前文从整数配方推出的完整复配方模型。连续相位与相反缩放是该模型的数学后果，不表示原装置已供应这些控制。对两份配方写

$$
p=Q(f)\ge0,\qquad q=Q(g)\ge0,\qquad
 b=B(f,g)=x+iy,\qquad T=\frac{p+q}{2}.
$$

### 4.1 一张预算平面与全部相位的交集

原互读界只画出半空间 $x\le T$。它的边界是一张平面，没有先画圆或假设三维状态球。

### 命题 4.1（相位预算的三维圆锥）

固定 $f,g$ 的自比较，全部相对相位的互读界恰好给

<a id="eq-c130-phase-cone"></a>

$$
x\cos\theta-y\sin\theta\le T\quad(\theta\in\mathbb R)
 \quad\Longleftrightarrow\quad
 T\ge\sqrt{x^2+y^2}=|b|.
\tag{6}
$$

**证明。**
把 $g$ 换为 $e^{i\theta}g$，$q$ 不变，交叉项变为 $e^{i\theta}b$。
其最大实部为 $\sqrt{x^2+y^2}$，所以全部半空间的交集就是所示圆锥。

<a id="fig-c130-budget-cone"></a>

```latex
\begin{tikzpicture}[font=\small,>=Latex]
 \path[use as bounding box] (-0.35,-0.70) rectangle (11.20,3.72);
 \node at (1.75,3.46) {固定 $T=1$：旋转预算线};
 \begin{scope}[xshift=1.75cm,yshift=1.50cm,x=1.05cm,y=1.05cm]
  \fill[teal!8] (0,0) circle[radius=1.05cm];
  \draw[black!38,dashed] (-1,-1) rectangle (1,1);
  \draw[black!42,->] (-1.35,0)--(1.53,0) node[below right] {$x$};
  \draw[black!42,->] (0,-1.35)--(0,1.45);
  \node[left] at (-0.08,1.44) {$y$};
  \draw[teal!75!black,very thick] (0,0) circle[radius=1.05cm];
  \draw[orange!85!black,thick,domain=-0.10:1.50,samples=2,variable=\t]
    plot ({\t},{sqrt(2)-\t});
  \fill[red!70!black] (1,1) circle (1.8pt);
  \node[above right,red!70!black] at (1.03,1.02) {$(1,1)$};
  \node[below left] at (-1,0) {$-1$};
  \node[below right] at (1,0) {$1$};
 \end{scope}
 \node[font=\footnotesize] at (1.75,-0.43) {四相位给方形；全部相位给圆盘};

 \node at (8.45,3.46) {三维预算圆锥};
 \begin{scope}[xshift=8.45cm,yshift=0.45cm,
  x={(0.65cm,-0.22cm)},y={(0.45cm,0.30cm)},z={(0cm,0.80cm)}]
  \fill[teal!7,domain=0:360,samples=121,variable=\ang]
    plot ({2*cos(\ang)},{2*sin(\ang)},2)--cycle;
  \foreach \ang in {0,45,90,135,180,225,270,315}{
   \draw[teal!45!black,line width=0.35pt]
    (0,0,0)--({2*cos(\ang)},{2*sin(\ang)},2);
  }
  \foreach \lev in {0.5,1,1.5,2}{
   \draw[teal!65!black,line width=0.45pt,domain=0:360,samples=121,variable=\ang]
    plot ({\lev*cos(\ang)},{\lev*sin(\ang)},\lev);
  }
  \draw[black!42,->] (-1.15,0,0)--(2.55,0,0) node[below right] {$x$};
  \draw[black!42,->] (0,-1.15,0)--(0,2.55,0) node[above right] {$y$};
  \draw[black!42,->] (0,0,0)--(0,0,3.10) node[right] {$T$};
  \fill[teal!75!black] (0,0,0) circle (1.8pt);
 \end{scope}
 \node at (8.45,-0.43) {$T\ge\sqrt{x^2+y^2}$};
\end{tikzpicture}
```

**图 1。**左图仅画若干预算线：有限相位留下外接多边形，全部相位的交集才是圆盘。橙线排除点 $(1,1)$。右图把不同 $T$ 的圆盘叠成圆锥，只截绘有限高度；这些轴是比较坐标。

单次平面确实较弱：$p=q=1,b=1+i$ 通过 $x\le T$，甚至通过四个直角相位，却在 $\theta=-\pi/4$ 时违反界；其二阶表行列式为 $-1$。
相位圆锥仍未检查双方预算失衡：$p=4,q=1,b=5/2$ 满足 $|b|=T$，行列式却为 $-9/4$。

### 4.2 相反缩放恢复乘积预算与零边界

### 命题 4.2（平衡后的精确二元界）

对已知 $p,q\ge0$ 的两份配方，全部相位及全部相反缩放的预算条件等价于

<a id="eq-c130-balanced-bound"></a>

$$
|b|^2\le pq.
\tag{7}
$$

**证明。**
取 $f\mapsto\lambda f,g\mapsto\lambda^{-1}g$，$\lambda>0$，交叉项 $b$ 不变，而相位优化后的界为

$$
2|b|\le\lambda^2p+\lambda^{-2}q.
$$

当 $p,q>0$ 时，右端下确界为 $2\sqrt{pq}$，在 $\lambda^4=q/p$ 处取得。
若 $p=0<q$，任意 $b\ne0$ 都会在足够大的有限 $\lambda$ 处违例，故 $b=0$；$q=0<p$ 时取足够小的正 $\lambda$，同理。$p=q=0$ 时直接给 $b=0$。
反向由算术–几何平均不等式成立，零边界也成立。

这些二元界作用于任意合成配方，不能缩成只检查原始标签的两坐标主块。上面的不平衡例在 $\lambda=1/\sqrt2$ 时变为 $2|b|=5>2+2$，因而被排除。

### 4.3 更大结构：四维正关系锥及其球截面

再保留失衡坐标 $D=(p-q)/2$，有

<a id="eq-c130-lorentz-cone"></a>

$$
\begin{aligned}
 G_{f,g}=\begin{pmatrix}p&b\\\bar b&q\end{pmatrix}\succeq0
 &\quad\Longleftrightarrow\quad T\ge\sqrt{x^2+y^2+D^2},\\
 \det G_{f,g}&=T^2-x^2-y^2-D^2.
 \end{aligned}
\tag{8}
$$

这是二阶 Hermitian 正矩阵的标准 Lorentz 锥表示 [6](#ref-arrighi2003)。
预算平衡截面 $D=0$ 给图中的三维圆锥；忘掉 $D$ 也投影到同一圆锥，所以这张三维图尚未认证一个已指定的不平衡关系表。

令 $\lambda=e^{s/2}$，上述相反缩放在 $(T,D)$ 上正是

$$
\begin{pmatrix}T_s\\D_s\end{pmatrix}
 =\begin{pmatrix}\cosh s&\sinh s\\\sinh s&\cosh s\end{pmatrix}
 \begin{pmatrix}T\\D\end{pmatrix},
 \qquad x_s=x,\quad y_s=y.
$$

它保持 $T^2-D^2=pq$。这是关系预算重配的双曲变换，不是已经推出物理时空或观察者运动。

若 $T>0$，用表自身的迹 $2T$ 归一：

$$
\frac{G_{f,g}}{2T}=\frac{I+\mathbf r\cdot\boldsymbol\sigma}{2},
 \qquad \mathbf r=\left(\frac xT,-\frac yT,\frac DT\right),
 \qquad \|\mathbf r\|\le1.
$$

球面对应秩一，内部对应秩二；$p=0<q$ 和 $q=0<p$ 给两极。$T=0$ 则整张表为零，保留为锥顶而不能归一。
完整锥的秩一边界允许预算不平衡；相位优化的半和界取等还要求 $p=q$，二者不是同一边界。
这里先得到比较表的几何，实际可制备范围仍由原接口说明。

### 4.4 没有删除相位，也没有预选手性

判据只使用实读出，并未丢弃核的虚部，因为整数配方 $ig$ 已满足

$$
\Re B(f,ig)=-\Im B(f,g).
$$

三元环 $K_{12}K_{23}K_{31}$ 非零时，仍能携带重相位不变的 Bargmann 相位 [7](#ref-bargmann1999)。
但 $\mathbb Z[i]$ 对共轭封闭，且
$B_{\bar K}(f,g)=\overline{B_K(\bar f,\bar g)}$，所以整个核复共轭仍满足同一候选；它不选择空间手性或时间方向。
复标量、共轭及 $B$ 的配方仍为输入。圆与平方因子来自这些算术关系，不能称为从无复数校准推出平方律；数学相位重配也不自动供应实际相位门。

**白话。**先只画一条最朴素的界：两份历史沿同一实轴互相读出的量，不能超过两边自比较的平均预算。换相位时仍用同一条界，所有方向合起来才围成圆；再允许一边放大、另一边等比缩小，预算失衡也被检查，完整的正关系锥才显出来。球是这只锥按自身总量切出的截面。相位关系一直保留在原比较里，左右和先后仍须由相应的内部记录来说明。

<a id="section-5"></a>

## 5. 从互读界恢复有限量子规则

<a id="sec-c130-quantum"></a>

互读界先恢复正核与比较空间。要接回原过程，须使用它实际对应的乘法、复线性、记录与联合接口；自由表的任意正完成不能替代这些关系。以下给一套有限复矩阵理论的条件性闭合，标准表示与概率定理有成熟来源 [8](#ref-watrous2018)、[9](#ref-busch2003)。

### 5.1 一张有限来源表选择完全正过程

### 定义 5.1（事件的原始核）

取 $d,m\ge1$。对仅给复线性的 $\Phi:M_d(\mathbb C)\to M_m(\mathbb C)$，以 $(a,u)\in M_d\times\mathbb C^m$ 为原始历史标签，定义

$$
K_\Phi((a,u),(b,v))=\langle u,\Phi(a^*b)v\rangle.
$$

不预设 $\Phi$ 保伴随、正、完全正或归一化。

### 定理 5.2（有限来源表的互读界与 CP）

<a id="thm-c130-cp"></a>

固定一来源行 $p$。以下等价：

1. 核 $K_\Phi$ 满足 C130；

2. 对有限列表 $((E_{pi},e_\mu))_{i,\mu}$，其全部高斯整数配方对满足互读界；

3. $\Phi$ 完全正。

成立后 $\Phi$ 自动保伴随，且存在 $d\times m$ 矩阵 $A_\alpha$，使

$$
\Phi(x)=\sum_\alpha A_\alpha^*xA_\alpha.
$$

**证明。**
该列表的比较表第 $((i,\mu),(j,\nu))$ 项为
$\langle e_\mu,\Phi(E_{ij})e_\nu\rangle$，即 Choi 表 $C_\Phi=[\Phi(E_{ij})]$。
由互读界与正核的等价，(2) 恰要求 $C_\Phi\succeq0$。
将其分解为 $\sum_\alpha w_\alpha w_\alpha^*$，写
$w_\alpha=\sum_i e_i\otimes A_\alpha^*e_i$，比较各块即得 Kraus 式；它的每一级矩阵放大都将正矩阵送到正矩阵，所以给 (3)。
CP 反向作用于任意正块表 $[a_i^*a_j]$，再用向量族评价，得到

$$
\sum_{ij}\bar z_i K_\Phi((a_i,u_i),(a_j,u_j))z_j\ge0.
$$

于是全核正，互读定理给 (1)；(1) 显然给 (2)。

在核商空间上令 $\pi(x)[a,u]=[xa,u]$。它保零差，因为
$\langle\pi(x)h,k\rangle=\langle h,\pi(x^*)k\rangle$。
取 $b=(\|x\|^2I-x^*x)^{1/2}$，有
$\|x\|^2Q(h)-Q(\pi(x)h)=Q(\pi(b)h)\ge0$，故有界。
核公式也保证 $Vu=[I,u]$ 对 $u$ 线性，直接得到

$$
\Phi(x)=V^*\pi(x)V.
$$

这里 $V$ 不必等距；单位效果未归一时不能补出等距结论。零映射使用零比较空间及空 Kraus 和，也满足本轮候选。

### 5.2 完整记录、Born 与读后态

### 命题 5.3（原记录的归一化）

若原事件族 $\Phi_j:M_{d_j}\to M_m$ 各满足候选，并另有完整记录约束 $\sum_j\Phi_j(I)=I$，则态方向过程

$$
\mathcal T_j(\rho)=\sum_\alpha A_{j\alpha}\rho A_{j\alpha}^*,
 \qquad \sum_{j,\alpha}A_{j\alpha}^*A_{j\alpha}=I
$$

构成完整 CP 仪器。各支迹不增，总输出保迹。

**证明。**
令 $E_j=\Phi_j(I)=\sum_\alpha A_{j\alpha}^*A_{j\alpha}\ge0$，则
$I-E_j=\sum_{k\ne j}E_k\ge0$。迹循环给 $\operatorname{Tr}\mathcal T_j(\rho)=\operatorname{Tr}(\rho E_j)$，即得支迹界与总保迹。

概率本身需要一致的效果评价。对全部 $0\le E\le I$ 给 $p(E)\ge0$，满足 $p(I)=1$，且 $E+F\le I$ 时 $p(E+F)=p(E)+p(F)$；同一效果在不同完整测试中赋同值。

### 定理 5.4（效果评价与纯态）

该评价唯一为 $p(E)=\operatorname{Tr}(\rho E)$，其中 $\rho\ge0,\operatorname{Tr}\rho=1$。
密度态的极点恰是秩一态；对归一纯态与秩一投影有 $p=|\langle\varphi,\psi\rangle|^2$。

**证明。**
可加性给有理齐次性，非负性给单调性，有理夹逼给实齐次性。对 $B\ge0$，以 $s>0,s\ge\|B\|$ 定义 $f(B)=s\,p(B/s)$，它与 $s$ 无关且在正锥可加。由正负分解延伸为 Hermitian 空间上的实线性泛函；有限迹配对给唯一 Hermitian $\rho$，正性与归一分别给 $\rho\ge0$ 和迹一。
秩至少二时可反向微调两个正谱权，得非平凡凸分解；秩一态的正分解只能支持同一射线，故它是极点。对两个秩一矩阵直接相乘取迹，即得 Born 平方律。相同纯态的归一向量只差整体相位。

该全效果版本包括二维 [9](#ref-busch2003)。候选未自动供应全部物理效果。
原支有 $p_j=\operatorname{Tr}(\rho E_j)$；仅当 $p_j>0$ 时定义 $\rho_j=\mathcal T_j(\rho)/p_j$。
若同空间支效果为投影 $P$，且保持 $\operatorname{Ran} P$ 内每条纯射线，则得到 Lüders 更新：$P=0$ 时所有 Kraus 项为零；$P\ne0$ 时效果先给 $A_\alpha(I-P)=0$，射线保持使每个 $A_\alpha v$ 与 $v$ 共线。对基向量及两两和应用，得 $A_\alpha=c_\alpha P$。效果给 $\sum|c_\alpha|^2=1$，故 $\mathcal T(\rho)=P\rho P$。仅有结果可重复性不排除结果子空间内的旋转。

### 5.3 可观测量、不确定界与独立复合

有限锐测量由正交投影 $\sum_iP_i=I$ 和实结果 $a_i$ 给自伴算符 $A=\sum_i a_iP_i$，反向由有限谱分解得到。其期望为 $\operatorname{Tr}(\rho A)$。
对自伴 $A,B$ 中心化为 $A_0,B_0$，在算符历史上用
$\Gamma_\rho(X,Y)=\operatorname{Tr}(\rho X^*Y)$。二元 Gram 行列式非负给

$$
\operatorname{Var}_\rho(A)\operatorname{Var}_\rho(B)
 \ge |\operatorname{Tr}(\rho A_0B_0)|^2
 \ge\tfrac14|\operatorname{Tr}(\rho[A,B])|^2.
$$

第二步保留复数的虚部。具体位置、动量及交换常数并非互读界选出。

若 $M_d,M_m$ 保单位保星地嵌入同一非零联合代数，两像交换并共同生成，则
$a\otimes b\mapsto\iota_A(a)\iota_B(b)$ 是满的保单位星同态。定义域 $M_d\otimes M_m\cong M_{dm}$ 简单：非零理想经矩阵单位左右相乘即含全部矩阵单位。故核为零，给张量联合。
CP 串接与并接的 Kraus 族分别为 $B_\beta A_\alpha$ 与 $A_\alpha\otimes B_\beta$。完整局部保迹过程不改变另一侧边缘，因为其伴随把 $I\otimes E$ 送回 $I\otimes E$。条件于特定结果时，边缘可变，所选标签的信息不能丢去。

### 5.4 可逆、时间及物理接口

### 命题 5.5（同维可逆过程与时间群）

同维 CPTP 过程若有 CPTP 左逆，则为酉共轭。若再给连续一参数 CPTP 群，则存在自伴 $H$，使

$$
\mathcal T_t(\rho)=e^{-itH/\hbar}\rho e^{itH/\hbar},
 \qquad i\hbar\dot\rho=[H,\rho].
$$

**证明。**
两过程的 Kraus 族记为 $A_i,B_j$。恒等通道 Choi 秩一给 $B_jA_i=c_{ji}I$。
对一个非零 $A_i$，逆过程保迹保证至少一个乘积非零；同维使相应 $B_j$ 可逆，从而所有 $A_i$ 共线。合并成一个 $A$ 后，保迹给 $A^*A=I$，方阵即酉。
有限维连续群写为 $e^{t\mathcal L}$；酉共轭性使生成元为保星导子。取 $D=\sum_k\mathcal L(E_{k1})E_{1k}$，导子律给 $[D,E_{ij}]=\mathcal L(E_{ij})$；保星性使 $D+D^*$ 为中心。换成反自伴部分并写成 $-iH/\hbar$，得到公式。

选定纯态相位代表后有 $i\hbar\dot\psi=H\psi$。具体钟、生成元与 $\hbar$ 标定并非原始核给出的事实。内积、正过程、完整概率、独立联合与时间的来源必须逐层对应。

| 通常规则 | 本轮推导与保留条件 |
|---|---|
| Hilbert 与叠加 | 正核的自由复包络及零差商；实际叠加仍须原控制接口。 |
| CP 与过程表示 | 指定复线性矩阵事件的来源核；有限 Choi 表的整数配方互读界。 |
| 概率与仪器 | 全效果一致可加评价；原完整记录归一化。 |
| 测量更新 | 已给 CP 仪器；逐射线保持时才选出 Lüders。 |
| 复合与局部性 | 交换且共同生成的独立子代数；完整局部保迹。 |
| 酉与时间 | 同维 CPTP 左逆；连续群和另行标定的物理时钟。 |

**白话。**互读不超自读，先选择正比较表；接上原过程的乘法与复线性，就选择完全正过程。完整记录给归一化，一致的效果赋值给 Born 规则，独立联合和可逆时间再给张量与酉演化。每一步都来自具体内部关系；公式更短，并没有免除这些关系实际存在的要求。

<a id="section-6"></a>

## 6. 内生接续、观察窗口与有限证据

<a id="sec-c130-scope"></a>

### 6.1 保核接续给等距，逆接续才给酉

### 命题 6.1（原历史动作的表示）

设原动作幺半群 $M$ 作用于 $X$，并满足
$K(ah,ak)=K(h,k)$。则 $T_a\iota(h)=\iota(ah)$ 在最小比较空间上定义等距表示。
若 $a$ 在原动作中有逆，则 $T_a$ 为酉。

**证明。**
对每个有限组合，保核等式给 $Q(T_af)=Q(f)$，故保持零空间，下降到商并等距延拓到完成。动作乘法在标签上成立，因此在稠密包络及完成上成立。有逆时 $T_{a^{-1}}$ 为双侧逆，等距于是满射。

这是 V71 第 7 节既有重建在 C130 入口下的恢复 [2](#ref-repo-c130-v71)。反例 $K(m,n)=\delta_{mn}$、$m,n\in\mathbb N_0$ 的加一动作重建为 $Se_n=e_{n+1}$，保范数但像不含 $e_0$。记录持续追加并不自动给出酉群。

若另外给群差核 $K(g,h)=F(g^{-1}h)$ 与 $F(e)=1$，可取源向量 $\xi=\iota(e)$，得到 $K(g,h)=\langle T_g\xi,T_h\xi\rangle$。同一固定来源核的最小循环实现酉等价唯一；该唯一性没有证明所有来源核必须相同，也没有给出每个形式向量的可制备性。

### 6.2 观察者增长的是可回答的问题

在同一比较空间中，设实际认证的闭可见子空间嵌套为 $\mathcal H_n\subseteq\mathcal H_{n+1}$，对应投影为 $P_n$。对固定目标 $v$，正交分解给

$$
\|v-P_nv\|^2-\|v-P_{n+1}v\|^2
 =\|(P_{n+1}-P_n)v\|^2\ge0.
$$

令 $\mathcal H_\infty=\overline{\bigcup_n\mathcal H_n}$。用某个有限窗口中的向量逼近 $P_\infty v$，再用投影的最小距离性，得到 $P_nv\to P_\infty v$。
两个观察者都完整恢复给定目标 $v$ 的充分必要条件是 $v$ 同时属于双方极限可见空间。未覆盖处与未知交叉关系不会因互读界而自动得到。

C117 第 9 节已有这类定理，但先给正状态与嵌套窗口；本轮先从互读界构造比较空间，再使用实际嵌套条件 [4](#ref-repo-c130-c117)。
若每个窗口含单位历史，在 GNS 表示中 $P_n[I]=[I]$；增长的是可比较的问题，不是源向量不断补长。
比较投影不自动是可执行 CP 门；时间轨迹、条件态与每个固定问题的比较收敛也不同。

C130 对标签换序与整体复共轭均相容。原档案若按保留式协议追加，前缀提供序向；非实三元环的相位可携带复定向。两者都可以是整体内部关系，互读界并不为它们选出唯一绝对方向。

### 6.3 为什么有限三点或有限系数菜单不够

### 命题 6.2（严格失败具有有限整数见证）

若原始核不满足 C130，存在有限支持高斯整数配方 $f,g$，使

$$
D_K(f,g):=\Re Q(f)+\Re Q(g)-2\Re B(f,g)<0.
$$

与有限正核等价地说，每个非 Hermitian 或非正核，都有这样的有限严格反例。

**证明。**
非 Hermitian 情况下，基向量、两基之和或带 $i$ 的两基之和中至少一个有非实自比较；整数探针产生负 $D_K$。Hermitian 非正情况有一张有限表及严格负的复二次型方向；连续性保留附近高斯有理方向的负号，清分母后取 $(f,0)$ 即得整数见证。

这个结论没有给统一的配方大小、精度或搜索时间。有效枚举寻找还需要可枚举标签和可计算、可认证的核值。若 $X$ 不可数，也不能称全体配方是可数集。

仅使用实整数配方时，$K=iI$ 的全部实部检查都是 $0\le0$，却不是 Hermitian 正核。因此 $i$ 的相位方向承担实质工作。

### 命题 6.3（有限整数菜单的精确剩余）

单标签取 $K=a+ib$，$a,b\in\mathbb R$。固定整数 $N\ge1$，只检验 $f,g\in\mathbb Z[i]$，且其实部、虚部的绝对值不超过 $N$。全部这些检查通过，当且仅当

$$
a\ge2N|b|.
$$

**证明。**
令 $d=g-f$，则

$$
D_K(f,g)=a|d|^2+2b\Im(\bar f d),\qquad
 |\Im(\bar f d)|\le N(|\Re d|+|\Im d|)\le N|d|^2.
$$

最后一步使用 $d$ 的分量是整数。因此 $a\ge2N|b|$ 时全部检查非负。
反向取 $(f,g)=(N,N+i)$ 和 $(-N,-N+i)$，两对均在菜单内，分别给 $a+2Nb\ge0$ 与 $a-2Nb\ge0$，所以 $a\ge2N|b|$，同时覆盖 $b=0$。

有限 $N$ 留下窄楔 $a\ge2N|b|$；所有层的交集才是 $a\ge0,b=0$ 的非负实轴。
例如 $K=1+i/(4N)$ 通过该整份有限菜单，却不是 Hermitian 核。
这说明“每份配方有限”不等于“存在统一有限配方上界”，也没有断言任意观察者实际能完成全部层。

原始支持大小也不能统一截断。第一节的四阶表通过全部三点子表，却在 $f=(1,1,1,1)$、$g=0$ 上给 $D_K=-4/5$。
有限三维图是每次二元检查的几何；“任何有限配方”才承接更大关系网络。

### 6.4 有限误差下的稳定否定

在同一有限标签表上，设 $\|K-\widehat K\|_{\mathrm{op}}\le\varepsilon$，配方系数为 $c,d$。则

$$
|D_K(c,d)-D_{\widehat K}(c,d)|
 \le\varepsilon(\|c\|_2+\|d\|_2)^2.
$$

这是将 $|c^*Ed|\le\|E\|_{\mathrm{op}}\|c\|_2\|d\|_2$ 分别用于三个项得到的。
所以若观测表的负缺陷超过右侧误差界，就得到对该有限误差域稳健的否定。无需在近奇异旧表上求伪逆。
然而整数放大也放大误差预算，不能用任意大 $n$ 代替测量精度或实际增益资源。

### 6.5 原关系的内生性与复相位保留

若原标签声明 $h_3=\alpha h_1+\beta h_2$，这条关系在重建空间中成立，当且仅当

$$
K(k,h_3)=\alpha K(k,h_1)+\beta K(k,h_2)
 \quad\text{对全部声明的 }k.
$$

因为相应差向量与稠密张成空间正交。这样可把相干、乘法、单位与联合接口写成原比较之间的约束，但它们必须各有实际依据。
例如正核 $K(a,b)=|a|^2|b|^2$ 的最小表示为 $\iota(a)=|a|^2$，原标签 $a\mapsto ia$ 并未变成表示中的相位门。

普通成对实距离也不足以替代复核：两组三点 $\{0,e_1,ie_1\}$ 与 $\{0,e_1,e_2\}$ 的距离同为 $1,1,\sqrt2$，但前者的两非零向量同属一条复射线，后者正交。其归一跃迁概率分别为一和零。C130 保留复比较，且有 $\Re B(f,ig)=-\Im B(f,g)$，没有在实不等式中抹去相位方向。

形式整数系数不是实际拷贝未知态、确定放大归一态或删除历史。比较商也不必分离原地址；被合并的当前比较仍可能有不同的程序身份。
有噪声的比较估计允许修正，旧报告及修正来源应保留。
全部有限量词是理论兼容条件，不是观察者已经取得全域、全部交集或不相容测量的未发生结果。

最后，复数、共轭、实部、实数序、同核有限和与无界有限配方仍有实质内容。经典模型同样能满足该候选；本轮没有由它唯一选出物理复结构、时空、粒子谱或相互作用。定义满足互读界的类是数学工作，实际过程属于该类仍须读出证据。

<a id="section-7"></a>

## 7. 本轮唯一候选与完整白话

<a id="sec-c130-final"></a>

给原始历史集合 $X$、同一复数值比较 $K$，以同一有限和定义整数配方比较。唯一新增约束为

$$
\boxed{2\Re B(f,g)\le\Re B(f,f)+\Re B(g,g),
 \qquad f,g\in\mathbb Z[i]^{(X)}.}
$$

它的闭合链为

$$
\text{整数配方互读界}
 \Longleftrightarrow\text{全有限复正核}
 \Longleftrightarrow\text{最小 Hilbert 表示}
 \Longleftrightarrow\text{C129 正交续写}.
$$

Hermitian 性、实非负自读和平方差由本轮不等式恢复；相位与尺度推论给圆锥，完整二元表归一后给 Bloch 球。矩阵过程接口接回 CP，其余原记录、效果、联合和时间关系接回通常量子规则。

输入对象数量与 C129 相同，约束形式更短；标准复数与全有限组合的内容仍然存在。本轮给出一个完整等价候选和条件重建理论，不声称已唯一推出全部量子物理、标准模型或宇宙本体。

### 本轮完整白话

**白话。**先保留历史之间原来怎样比较，再拿两份有限写法互相对照。两边互读的两倍，不能超过两边各自读数的合计。写法只需有限加减、重复和四分之一相位；重复是比较配方里的系数，不是复制未知量子态。如果自读里还藏着虚部，把同一写法重复若干次，再错开一个四分之一相位，迟早会让互读透支；所有有限写法都不透支，自读便只能落在非负实轴上。此后，两边扣掉相互读数留下的差额，正好成为它们差别的平方，内积与上轮的垂直余边也就重新出现。几何上，一条互读界像一面直的挡板；转过所有相位，同样的挡板围成圆，带上总读数就形成圆锥。再允许两边重新平衡尺度，圆锥就接到完整二元正关系，归一后得到 Bloch 球。观察者仍只取得自己已经验证的关系；记录的追加规定先后，闭环的相位记录定向。所有配方、比较、参照和回读都可以留在整体内部。本轮进一步退到一句话：两份历史互相对照，不能比它们各自对照合起来读得更多。

<a id="references"></a>

## 参考文献

<a id="ref-repo-c130-pin"></a>

### [1]

The Omega Institute, *trureturing*, immutable commit
[8e15c484cf5786fe69fef0627fd84a63cfeb5942](https://github.com/the-omega-institute/trureturing/commit/8e15c484cf5786fe69fef0627fd84a63cfeb5942)。
2026-11-04 08:25:41 UTC，16:25:41 Asia/Singapore。
本轮默认分支核对与 C129 相同；整提交及相关子树零差分。没有新增量子源码或 C130 Lean 形式化。

<a id="ref-repo-c130-v71"></a>

### [2]

The Omega Institute, *AURIC Universal Binary Relation Kernels, Quotient Residuals and Unbounded Recursion V71*。
[固定快照全文](https://github.com/the-omega-institute/trureturing/blob/8e15c484cf5786fe69fef0627fd84a63cfeb5942/docs/develop/theory/AURIC_UNIVERSAL_BINARY_RELATION_KERNELS_QUOTIENT_RESIDUALS_AND_UNBOUNDED_RECURSION_V71.md)。
本文直接核读第 5–7、12 节：定理 5.3 已有全复合二元正性与正核等价；第 6 节保奇异 Schur 值域；第 7 节区分保核等距与有逆酉表示。其 Hermitian、原复组合、可逆及读出前件均保留。

<a id="ref-repo-c130-c114"></a>

### [3]

The Omega Institute, *AURIC Quadratic Readout and Recursive Relational Compatibility C114*。
[固定快照全文](https://github.com/the-omega-institute/trureturing/blob/8e15c484cf5786fe69fef0627fd84a63cfeb5942/docs/develop/theory/AURIC_QUADRATIC_READOUT_AND_RECURSIVE_RELATIONAL_COMPATIBILITY_C114.md)。
本文直接核读第 5–6 节及第 7 节新增记录定理与证明。例 6.3 给三点检查不足的四阶反例；定理 7.2 含值域条件。实际相干、混合、独立、参考及仪器接口不由球图单独供应。

<a id="ref-repo-c130-c117"></a>

### [4]

The Omega Institute, *AURIC Common Source Self Reference and Observer Sequences C117*。
[固定快照全文](https://github.com/the-omega-institute/trureturing/blob/8e15c484cf5786fe69fef0627fd84a63cfeb5942/docs/develop/theory/AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md)。
继承 C129 对相同快照第 9–11 节的核读；本轮不重复声称审计全文。正窗口、目标残差及源向量不增长的边界，正文另给所用证明。

<a id="ref-aronszajn1950"></a>

### [5]

N. Aronszajn, “Theory of reproducing kernels”,
*Transactions of the American Mathematical Society* **68**(3), 337–404 (1950).
[原始论文扫描件](https://pages.stat.wisc.edu/~wahba/stat860public/pdf2/aronszajn.pdf)；
[doi:10.1090/S0002-9947-1950-0051437-7](https://doi.org/10.1090/S0002-9947-1950-0051437-7)。
正核与 Hilbert 表示的经典来源；本文的零差商证明自包含，不将这项对应称为新发现。

<a id="ref-arrighi2003"></a>

### [6]

P. Arrighi and C. Patricot,
“A note on the correspondence between qubit quantum operations and special relativity” (2003).
[arXiv:quant-ph/0212135v3](https://arxiv.org/pdf/quant-ph/0212135)，第 I 节、Lemma 1。
二阶 Hermitian 正锥与四维 Lorentz 锥的坐标对应。本文只使用并直接证明该代数几何，不由预算重配推导物理时空或引力。

<a id="ref-bargmann1999"></a>

### [7]

E. M. Rabei, Arvind, N. Mukunda and R. Simon,
“Bargmann invariants and geometric phases: A generalized connection”,
*Physical Review A* **60**, 3397 (1999).
[arXiv:quant-ph/9907080](https://arxiv.org/pdf/quant-ph/9907080)。
三元相位的文献定位；非零重叠、相位参考和几何相位约定需保留。

<a id="ref-watrous2018"></a>

### [8]

J. Watrous, *The Theory of Quantum Information*, Cambridge University Press (2018).
[作者公开第 2 章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)，Theorem 2.22。
有限 Choi、Kraus、Stinespring 等价。正文另证明有限来源表的整数互读界如何选出 CP，零过程单独包含。

<a id="ref-busch2003"></a>

### [9]

P. Busch, “Quantum states and generalized observables: a simple proof of Gleason's theorem”,
*Physical Review Letters* **91**, 120403 (2003).
[arXiv:quant-ph/9909073](https://arxiv.org/pdf/quant-ph/9909073)。
全效果一致可加评价的 Born 表示，包括二维；该评价及完整效果菜单是明确前件。
