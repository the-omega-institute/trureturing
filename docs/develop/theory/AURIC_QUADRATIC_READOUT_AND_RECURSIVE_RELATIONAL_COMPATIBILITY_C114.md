**AURIC 量子关系研究续篇**

# 从二次读出 到递归关系相容

**候选 C114：同一条二元规则贯穿全部有限合成**

**本轮核心**

交叉项在提升后的关系坐标中成为线性读出。将三维球约束用于每一次二元合成，包括已经合成的对象之间的比较，恰好得到整体关系核的正性。共同参考解释后的剩余关系满足同一规则；这一递归可以处理奇异与零强度情形，并构造最小 Hilbert 实现。

**准确起点**

$$
a^2+2ab+b^2=(a+b)^2,
 \qquad (a^2-b^2)^2+(2ab)^2=(a^2+b^2)^2.
$$

前一个式子的等值线退化；后一个式子揭示归一化后真正的关系圆。

**版本与来源范围**

本稿衔接已经交付的 C113，暂记 C114；编号属于本轮工作稿。C113 记载的仓库快照为

`40e161f1b410721daad15d8ceaad34c3d7e19759`

本轮核读了 C113 源稿和仓库公开的局部相关盲区源码。最新 HEAD 与理论主卷端点未取得，因此该快照只作为前稿记载，不声称本轮重新验证了最新仓库版本。以下证明自足，不依赖未取得的主卷正文。

**证明范围**

有限维复比较结构上的纸笔定理与条件重构。未作 Lean 编译或仓库合并认证。正核、Schur 补、射影几何、Born 配对及完全正映射均为成熟数学；本稿的贡献定位是组织项目候选、明确递归接口和补齐证明边界，不作原创优先权声明。

2026 年 11 月 3 日  新加坡

## 目录

- [1. 与项目当前可核读工作的连接](#section-1)
- [2. 二次式：圆、椭圆与退化读口](#section-2)
- [3. 真正的关系圆与三维球](#section-3)
- [4. 读口归一化与缺失的相位信息](#section-4)
- [5. 完整候选 C114：内部比较的递归相容](#section-5)
- [6. 主定理：每层三维相容等价于整体正性](#section-6)
- [7. 关系的关系：扣除共同参考后的剩余](#section-7)
- [8. 三角相位、手性与一个共同本体态](#section-8)
- [9. Hilbert 空间是不可辨别关系的商](#section-9)
- [10. 从候选逐项重构量子力学](#section-10)
- [11. 保留 C113：怎样唯一选出理想滤波](#section-11)
- [12. 更大的几何与内生性的准确含义](#section-12)
- [13. 删除条件后的明确后果](#section-13)
- [14. 完整白话描述](#section-14)
- [参考文献](#references)

<a id="section-1"></a>

## 1. 与项目当前可核读工作的连接

前稿 C113 研究同一效果下的有限均衡比较如何唯一选出平方根更新，并计算两个规范滤片接续后的极酉旋转。它也明确留下一个结构事实：多个合法二元 Gram 块并不自动属于同一个整体。本稿将这一事实推进为递归相容的等价定理 [1](#ref-c113)。

本轮能核读的仓库源码给出另一条相关而不同的边界：Bell 纯态与等权经典相关混合态可具有完全相同的两个局部边缘，却保留不同的整体相关。一般 $m\times n$ Hermitian 张量模型的局部未读相关子空间实维数是 $(m^2-1)(n^2-1)$ [2](#ref-repo-blind)。该结果说明必须保留关系读口；它不直接证明本稿的相容定理，也不把完整量子公理从零推出。

两类问题需要分别处理：一份已经合法的整体，局部读口能否确定它；一份给定的局部关系表，究竟能否拼成任何合法整体。本稿集中解决后一类有限问题，并再接回标准量子结构。

<a id="section-2"></a>

## 2. 二次式：圆、椭圆与退化读口

设 $a,b,x\in\mathbb R$，定义

$$
q_x(a,b)=a^2+xab+b^2,
 \qquad M_x=\begin{pmatrix}1&x/2\\x/2&1\end{pmatrix}.
$$

### 命题 2.1（完整等值线分类）

令 $u=(a+b)/\sqrt2$、$v=(a-b)/\sqrt2$，则

$$
q_x=(1+x/2)u^2+(1-x/2)v^2.
$$

所以 $q_x=1$ 在 $x=0$ 时为单位圆，在 $0<|x|<2$ 时为椭圆，在 $x=\pm2$ 时分别为 $a\pm b=\pm1$ 的两条平行线，在 $|x|>2$ 时为双曲线。$M_x\succeq0$ 当且仅当 $|x|\le2$。

**证明。**
直接代入 $a=(u+v)/\sqrt2$、$b=(u-v)/\sqrt2$。两个系数即矩阵本征值，符号决定结论。

这里 $xab$ 对固定的一个振幅是线性的，对 $(a,b)$ 整体是双线性的。准确的线性化将在下一节发生。若 $u_0,v_0$ 为单位向量，

$$
\|au_0+bv_0\|^2=a^2+2\Re\langle u_0,v_0\rangle ab+b^2.
$$

在实比较中，$x=2\langle u_0,v_0\rangle$；$x=0$ 表示正交，$x=2$ 表示两个方向重合。因而 $x=2$ 的秩一退化有明确含义：读口只保留共同方向，差方向不可见。

另可写 $x=2\cos\theta$，得到

$$
q_x(a,b)=|a+b e^{i\theta}|^2.
$$

当 $\sin\theta\ne0$，系数平面中的椭圆经线性映射成为输出复平面中的单位圆；在 $x=2$ 时该映射失去一个维度。必须说明圆究竟位于哪个坐标空间。

<a id="section-3"></a>

## 3. 真正的关系圆与三维球

### 定理 3.1（实振幅的精确关系提升）

定义

$$
s=a^2+b^2,\quad Z=a^2-b^2,\quad X=2ab.
$$

则

<a id="eq-real-lift"></a>

$$
\boxed{s^2=Z^2+X^2,\qquad q_x=s+\frac{x}{2}X.}
\tag{1}
$$

当 $s=1$，$(Z,X)$ 位于单位圆；$q_x$ 是这个圆上的仿射读出。

**证明。**
展开 $(a^2-b^2)^2+4a^2b^2$ 即得第一式，第二式来自定义。更一般地，若要求
$(a^2-b^2)^2+(k ab)^2=(a^2+b^2)^2$ 对所有 $a,b$ 成立，比较 $a^2b^2$ 系数得到 $k^2=4$。因此交叉坐标的尺度确实必须是 $\pm2$。

若 $a=\cos\theta$、$b=\sin\theta$，则 $(Z,X)=(\cos2\theta,\sin2\theta)$。共同变号的两组振幅给同一个关系点。

```latex
\begin{tikzpicture}[>=Stealth,scale=1.15]
\begin{scope}[shift={(-3,0)}]
\draw[->,gray] (-1.5,0)--(1.6,0) node[right] {$a$};
\draw[->,gray] (0,-1.5)--(0,1.6) node[above] {$b$};
\draw[thick,teal!80!black] (0,0) circle(1);
\begin{scope}\clip (-1.4,-1.4) rectangle(1.4,1.4);
\draw[thick,dashed,orange!90!black] (-1,2)--(2,-1);
\draw[thick,dashed,orange!90!black] (-2,1)--(1,-2);
\end{scope}
\node[align=center,text width=5.1cm,font=\small] at (0,-2.05) {原振幅平面\\实线：$q_0=1$；虚线：$q_2=1$};
\end{scope}
\begin{scope}[shift={(3,0)}]
\draw[->,gray] (-1.5,0)--(1.6,0) node[right] {$Z$};
\draw[->,gray] (0,-1.5)--(0,1.6) node[above] {$X$};
\draw[very thick,teal!80!black] (0,0) circle(1);
\fill[orange!90!black] (0,1) circle(0.045);
\node[anchor=south west,font=\small] at (0.03,1.03) {$a=b=1/\sqrt2$};
\node[align=center,text width=5.1cm,font=\small] at (0,-2.05) {归一化关系平面\\$Z^2+X^2=1$，$q_2=1+X$};
\end{scope}
\end{tikzpicture}
```

**图 1。**同一个系数 $2$ 的两种作用：原等值线中的秩一退化，以及关系提升中的圆闭合。

### 定理 3.2（复振幅与 Bloch 球面）

对 $a,b\in\mathbb C$ 定义

$$
s=|a|^2+|b|^2,\quad Z=|a|^2-|b|^2,\quad
 X=2\Re(\bar a b),\quad Y=2\Im(\bar a b).
$$

则 $s^2=X^2+Y^2+Z^2$。归一化后

$$
\rho=\begin{pmatrix}a\\b\end{pmatrix}(\bar a,\bar b)
 =\frac12\begin{pmatrix}1+Z&X-iY\\X+iY&1-Z\end{pmatrix}.
$$

共同相位不改变 $\rho$，且每个单位球面点唯一确定一条复射线。

**证明。**
$X^2+Y^2=4|a|^2|b|^2$，加上 $Z^2$ 得结论。若 $Z\ne-1$，可选
$a=\sqrt{(1+Z)/2}$、$b=(X+iY)/\sqrt{2(1+Z)}$；南极取 $(0,1)$。这些表示只差共同相位。

因此归一化复二元纯态的几何是 $S^3/U(1)\cong\mathbb{CP}^1\cong S^2$；实振幅只给 $Y=0$ 的大圆。未归一化 Hermitian 二阶矩阵有四个实坐标，归一化后有三个，纯态球面只有两个独立实参数。

### 命题 3.3（二元正性就是三维球约束）

<a id="prop-ball"></a>

令

$$
G=\begin{pmatrix}p&c\\\bar c&q\end{pmatrix},\quad
 s=p+q,\quad \mathbf r=(2\Re c,-2\Im c,p-q).
$$

则

$$
\det G=\frac{s^2-|\mathbf r|^2}{4},\qquad
 G\succeq0\iff s\ge|\mathbf r|.
$$

若 $s>0$，$\mathbf r/s$ 位于闭单位球；若 $s=0$，正性迫使 $G=0$。

**证明。**
本征值为 $(s\pm|\mathbf r|)/2$，因而结论直接成立。

**白话。**交叉关系并没有消失。它从振幅的乘积，变成关系空间中的一个坐标。实比较给一个圆；补齐关系的另一正交分量后，才得到完整的三维球。

<a id="section-4"></a>

## 4. 读口归一化与缺失的相位信息

在 $a^2+b^2=1$ 上，$q_2$ 的最大值是二。正确的两个互补概率为

$$
p_+=\frac{(a+b)^2}{2}=\frac{1+X}{2},\qquad
 p_-=\frac{(a-b)^2}{2}=\frac{1-X}{2}.
$$

更一般地

$$
E_x=\frac12\begin{pmatrix}1&x/2\\x/2&1\end{pmatrix},\qquad
 0\le E_x\le I\iff |x|\le2,
$$

且 $E_{-x}=I-E_x$。此时 $x$ 标记读口，$x=0$ 是 $I/2$ 的无信息读口；这与上一节把 $x$ 当作生成方向 Gram 相关系数的角色不同。

### 例 4.1（两个实读口不能恢复手性）

$$
\psi_+=\frac{(1,i)}{\sqrt2},\qquad
 \psi_-=\frac{(1,-i)}{\sqrt2}
$$

有相同的 $|a|^2,|b|^2,\Re(\bar a b)$，但 $Y=\pm1$，且两态正交。因此固定坐标手性无法代替未知态自己的相位符号。实际需要另一相位敏感读口或明确的历史限制。

例如

$$
\frac{|a\pm e^{i\phi}b|^2}{2}
 =\frac{1\pm(X\cos\phi-Y\sin\phi)}2
$$

可读取两个正交相位分量。这为 AURIC 三轴提供一个精确实现；它尚未证明原生五个 FIB 标签与这些操作完全等价。

<a id="section-5"></a>

## 5. 完整候选 C114：内部比较的递归相容

### 定义 5.1（内部比较数据）

$\Omega$ 保留原始记录、合成历史、比较接口、读口和过程标签。在一个固定相干扇区内取标签 $e_i$，令 $V$ 为其有限复线性组合空间。比较表满足

$$
K_{ij}=R(e_i,e_j),\quad K_{ji}=\overline{K_{ij}},\qquad
 R\Bigl(\sum_i a_ie_i,\sum_j b_je_j\Bigr)
 =\sum_{ij}\bar a_i b_jK_{ij}.
$$

记 $q(u)=R(u,u)$。公式定义合成读出；不同的来源树仍保留在 $\Omega$ 中。

下面给出本轮完整候选的结构条件。前三项形成对象与概率理论，后面三项将其接到标准复合、过程和理想测量。

1. **C114.1.** **共同有向比较与精确合成。** 所有比较使用同一可相容的复参考；有限复权重合成与其交叉关系按上述式子更新，括号分组不改变同一读出。跨超选择扇区不擅自允许相干合成。

2. **C114.2.** **递归二元正性。** 原始记录的自身强度非负。每个实际纳入模型的有限合成及再次比较，都满足命题 [3.3](#prop-ball) 的球约束；零总强度时整个二元块为零。候选的完整矩阵版本要求覆盖该扇区所有有限复权重组合。

3. **C114.3.** **混合与读出一致。** 允许所有纯态的凸混合，并明确要求：若两种准备具有同一关系矩阵 $\sum_s w_sP_{\psi_s}=\sum_t v_tP_{\phi_t}$，则全部允许读口给相同概率。概率对混合仿射，取值在 $[0,1]$。完备结果总概率为一。完整效果版本另要求相应合法效果实际可供使用。

4. **C114.4.** **独立合成。** 有双线性的积记录，比较因子化，且联合纯记录由积记录的线性组合张成。该条件只作用于已供应的独立合成接口。

5. **C114.5.** **内部参考延伸。** 过程保留混合关系；同一过程接任意未操作的内部参考后仍保持正性；确定过程保持总强度。闭系统过程和逆过程均合法，所考虑的时间演化形成连续单参数群。

6. **C114.6.** **理想滤片选择。** 对指定效果的同一个成功分支，保留 C113 的有限二阶均衡同向饱和条件，详见第 [11](#sec-filter) 节。一般有噪仪器不要求满足这一理想选择条件。

**本轮唯一新增核心是 C114.2 的递归量词与其构造定理。** C114.1、3–6 明列重构的承重接口。把条件记录在 $\Omega$ 内消除了外部操作者，但这些数学条件的物理成立仍须解释或检验。特别是共同复结构、全体相干组合、独立合成和连续时间都不能由“在同一个整体中”这句话自动得到。

任意复系数是结构闭包的量词，不宣称任意增益、任意未知态相加都能作为确定性实验操作实现。物理组合需相应已知路径、相位参考和必要的成功归一化；受限菜单只保证其所覆盖方向的相容。

<a id="section-6"></a>

## 6. 主定理：每层三维相容等价于整体正性

### 定理 6.1（递归二元闭合）

<a id="thm-recursive"></a>

在固定的 Hermitian 复比较表与精确合成律下，以下条件等价：

1. **(i)** 每个有限标签集的比较矩阵 $K$ 半正定；

2. **(ii)** 每个有限组合 $u$ 都满足 $q(u)\ge0$；

3. **(iii)** 叶节点强度非负，且每棵有限二元合成树中，每个节点比较的二元块都满足三维球约束。

**证明。**
若 $u=\sum_i a_ie_i$，则 $q(u)=a^*Ka$，故 (i) 与 (ii) 等价。若 (i) 成立，任意两个组合 $u,v$ 的系数组成矩阵 $C$，其二元关系块为 $C^*KC\succeq0$，得到 (iii)。

反之，在一个节点，球约束给 $|R(u,v)|^2\le q(u)q(v)$，故

$$
\begin{aligned}
q(u+v)&=q(u)+q(v)+2\Re R(u,v)\\
 &\ge q(u)+q(v)-2\sqrt{q(u)q(v)}\\
 &=\bigl(\sqrt{q(u)}-\sqrt{q(v)}\bigr)^2\ge0.
\end{aligned}
$$

叶节点强度为 $q(a_ie_i)=|a_i|^2K_{ii}\ge0$；允许零记录和单端口比较，单端口条件也可在 $(e_i,0)$ 上读取。任意有限复线性组合都能写成二元树，逐层归纳得 (ii)。

### 例 6.2（原始两两合法，合成后失败）

令 $K=2I_3-J_3$，即对角元为一、非对角元为负一。每个二阶主块的本征值为零与二，但 $K(1,1,1)^T=-(1,1,1)^T$，因此

$$
q(e_1+e_2+e_3)=-3.
$$

设 $u=e_1+e_2$、$v=e_3$，则 $q(u)=0$、$q(v)=1$、$R(u,v)=-2$。零自身强度仍承载非零交叉关系，该递归二元块恰好暴露整体矛盾。

### 例 6.3（三元检查也不能替代任意有限递归）

取四阶矩阵 $K=\tfrac75I_4-\tfrac25J_4$。任一 $m$ 阶主块的本征值为 $7/5$（重数 $m-1$）与 $(7-2m)/5$。所有 $m\le3$ 的主块正定，但四阶块有本征值 $-1/5$。因此固定只检验两元或三元都不足以认证任意规模。

### 推论 6.4（没有独立三阶强度项）

在同一合成规则下，

$$
\begin{aligned}
0={}&q(u+v+w)-q(u+v)-q(v+w)-q(w+u)\\
&+q(u)+q(v)+q(w).
\end{aligned}
$$

**证明。**
展开二次型，各自权重与每条交叉关系的系数分别抵消。

下一节出现的三角相位是二元系数之间的相容约束，不是给上述强度公式再加一个独立三阶项。实际多路径实验还需保持同一准备与比较条件，才能使用这个代数恒等式。

**白话。**把两项合在一起以后，仍要带着它们同其余各项的关系。原来两个小块各自没有问题，合成后却可能互相矛盾。同一条球约束必须跟着合成继续走。

<a id="section-7"></a>

## 7. 关系的关系：扣除共同参考后的剩余

### 定理 7.1（三元约束化为剩余二元约束）

<a id="thm-schur3"></a>

设 $G=(c_{ij})_{i,j=1}^3$ Hermitian，$c_{ii}=p_i$，且 $p_1>0$。定义

$$
s_2=p_2-\frac{|c_{12}|^2}{p_1},\quad
 s_3=p_3-\frac{|c_{13}|^2}{p_1},\quad
 d=c_{23}-\frac{c_{21}c_{13}}{p_1}.
$$

则

<a id="eq-residual"></a>

$$
\boxed{
 G\succeq0\iff
 \begin{pmatrix}s_2&d\\\bar d&s_3\end{pmatrix}\succeq0
 \iff s_2,s_3\ge0,\quad |d|^2\le s_2s_3.
}
\tag{2}
$$

**证明。**
将第二、三个形式向量替换为
$e'_j=e_j-(c_{1j}/p_1)e_1$，得到与原矩阵可逆合同的块对角矩阵
$\operatorname{diag}(p_1,S)$，其中 $S$ 正是显示的剩余矩阵。合同保持半正定性。最后使用二阶正性判据。

当 $s_2+s_3>0$，剩余的三维坐标是

$$
\frac{(2\Re d,-2\Im d,s_2-s_3)}{s_2+s_3},
$$

仍必须在单位球内。这条公式给出“二元关系的关系”的直接运算：先扣掉共同参考解释的部分，再对未解释的两个部分使用同一约束。

### 定理 7.2（一般新增记录、奇异边界与最小维数）

<a id="thm-extension"></a>

设 $K\in M_n(\mathbb C)$、$K\succeq0$、$c\in\mathbb C^n$、$p\in\mathbb R$，$K^+$ 为 Moore–Penrose 逆。则

<a id="eq-extension"></a>

$$
\boxed{
 \begin{pmatrix}K&c\\c^*&p\end{pmatrix}\succeq0
 \iff c\in\operatorname{Ran} K,\quad \delta:=p-c^*K^+c\ge0.
}
\tag{3}
$$

若条件成立，新增块的秩为 $\operatorname{rank} K+\mathbf1_{\{\delta>0\}}$。

**证明。**
若 $z\in\ker K$，在 $(tz,1)$ 上评价二次型得到
$p+2\Re(\bar t z^*c)$。对所有 $t\in\mathbb C$ 非负迫使 $z^*c=0$，因此 $c\in(\ker K)^\perp=\operatorname{Ran} K$。在这一条件下，

$$
\begin{pmatrix}K&c\\c^*&p\end{pmatrix}
 =\begin{pmatrix}I&0\\c^*K^+&1\end{pmatrix}
 \begin{pmatrix}K&0\\0&\delta\end{pmatrix}
 \begin{pmatrix}I&K^+c\\0&1\end{pmatrix}.
$$

外侧因子互为伴随且可逆，故得到正性等价和秩公式。

### 推论 7.3（有限递归构造）

任意有限 Hermitian 关系表可逐步用式 [(3)](#eq-extension) 构造或拒绝。当前主元为负时立即拒绝。若当前主元为零，半正定性要求其整条当前剩余行列为零；满足时可删除该行列继续。若当前主元为正，则使用 Schur 补继续。全部通过当且仅当原表半正定。

**证明。**
零主元情形由 $|c_{ij}|^2\le p_ip_j$ 得零行列；正主元情形用合同分解。有限维归纳结束。若已实现 $K=V^*V$，新向量在旧空间中的分量可取 $VK^+c$，其平方范数是 $c^*K^+c$；再加一个与旧空间正交、长度 $\sqrt\delta$ 的分量即可。

**零边界不可省略。** 取 $K=0$、$c\ne0$、$p=1$，则形式数 $p-c^*K^+c=1$ 为正，但整个块不正。遗漏 $c\in\operatorname{Ran} K$ 会把不可能的关系判成合法。

**白话。**新内容有多少能由已有关系解释，可以精确计算。已有部分解释不了的份量必须非负；它为零时不增加维度，为正时正好增加一个新方向。已经没有份量的方向，也不能继续承载非零关系。

<a id="section-8"></a>

## 8. 三角相位、手性与一个共同本体态

### 命题 8.1（首个闭环关系）

三阶 Hermitian 表的行列式为

<a id="eq-triangle"></a>

$$
\begin{aligned}
\det G={}&p_1p_2p_3+2\Re(c_{12}c_{23}c_{31})\\
&-p_1|c_{23}|^2-p_2|c_{31}|^2-p_3|c_{12}|^2.
\end{aligned}
\tag{4}
$$

在 $p_i=1$、$c_{ij}=r_{ij}e^{i\phi_{ij}}$ 时，正性要求

$$
1-r_{12}^2-r_{23}^2-r_{31}^2
 +2r_{12}r_{23}r_{31}\cos(\phi_{12}+\phi_{23}+\phi_{31})\ge0.
$$

**证明。**
直接展开行列式。对三阶 Hermitian 矩阵，连同全部一阶、二阶主子式非负，该条件也充分。

独立改相位 $e_i\mapsto e^{i\theta_i}e_i$ 改变单边相位，但乘积 $c_{12}c_{23}c_{31}$ 不变。若归一化的全部边都饱和 $|c_{ij}|=1$，正性迫使所有三角相位为零，此时各向量共线。对不饱和的多方向关系，环相位通常可以非零。

### 命题 8.2（秩一相位闭合的充分性）

若 $p_i>0$，$|c_{ij}|=\sqrt{p_ip_j}$，并且完整图上每个三角积为正实数，则该表是半正定秩一表。

**证明。**
先除以 $\sqrt{p_ip_j}$。选择参考顶点一，用各顶点相位把所有 $c_{1j}$ 变为一。三角 $(1,i,j)$ 的闭合随后迫使每个 $c_{ij}=1$。因此原表对角酉合同于 $(\sqrt{p_i p_j})_{ij}$，为秩一正表。

### 定理 8.3（三条射线的有向体积读出）

<a id="thm-bargmann"></a>

对三个纯 qubit 投影 $P_j=(I+\mathbf r_j\cdot\boldsymbol\sigma)/2$，定义
$B_{123}=\operatorname{Tr}(P_1P_2P_3)$。则

<a id="eq-bargmann"></a>

$$
\boxed{
 B_{123}=\frac{1+\mathbf r_1\cdot\mathbf r_2+\mathbf r_2\cdot\mathbf r_3
 +\mathbf r_3\cdot\mathbf r_1
 +i\,\mathbf r_1\cdot(\mathbf r_2\times\mathbf r_3)}4.
}
\tag{5}
$$

**证明。**
使用 $(\mathbf u\cdot\boldsymbol\sigma)(\mathbf v\cdot\boldsymbol\sigma)
=(\mathbf u\cdot\mathbf v)I+i(\mathbf u\times\mathbf v)\cdot\boldsymbol\sigma$，展开三项乘积，再使用 $\operatorname{Tr} I=2$、$\operatorname{Tr}\sigma_j=0$。

取 $\psi_1=\lvert 0\rangle$、$\psi_2=(\lvert 0\rangle+\lvert 1\rangle)/\sqrt2$、
$\psi_3=(\lvert 0\rangle+i\lvert 1\rangle)/\sqrt2$，其 Bloch 向量为 $z,x,y$。三个两两转移概率都是 $1/2$，但

$$
B_{123}=\langle \psi_1,\psi_2\rangle\langle \psi_2,\psi_3\rangle\langle \psi_3,\psi_1\rangle
 =\frac{1+i}{4}.
$$

把 $i$ 换成 $-i$ 保持全部两两概率，却把闭环相位反向。这个成熟的 Bargmann 不变量正好把“关系的关系”与三维手性联系起来 [3](#ref-oszmaniec)、[4](#ref-mukunda)。两两点积决定夹角，有向三重积保留相位符号。

**唯一整体源与非零环相位相容。** 取 $\Omega_0=\lvert 0\rangle$，内部操作
$T_1=I,T_2=H,T_3=SH$，其中

$$
H=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix},\qquad
 S=\begin{pmatrix}1&0\\0&i\end{pmatrix}.
$$

上述三个状态全是 $T_j\Omega_0$，关系核为
$K_{ij}=\langle \Omega_0,T_i^*T_j\Omega_0\rangle$，仍有 $B_{123}=(1+i)/4$。
一个纯态在一个固定基底中的秩一密度表满足相位闭合；同一纯源经不同内部操作所得的多条射线，其重叠表不必秩一。二者不能混同。

<a id="section-9"></a>

## 9. Hilbert 空间是不可辨别关系的商

### 定理 9.1（最小实现与唯一性）

<a id="thm-hilbert"></a>

对固定有限标签集，在递归相容成立时，令

$$
N=\{u:q(u)=0\},\qquad \mathcal H=V/N,
 \qquad \langle [u],[v]\rangle=R(u,v).
$$

则该内积定义良好且正定。有限标签情形 $\dim\mathcal H=\operatorname{rank} K$。任何张成的最小向量实现都在酉变换意义下唯一。

**证明。**
任意二元块正性给 $|R(u,v)|^2\le q(u)q(v)$。若 $u\in N$，它与所有向量的关系为零，故 $N$ 为线性根空间，商内积定义良好且正定。$V=\mathbb C^n$ 时根空间为 $\ker K$，维数结论来自秩零化度定理。

若两组张成向量 $v_i,w_i$ 有相同 Gram 表，映射 $\sum a_iv_i\mapsto\sum a_iw_i$ 的良定义来自两边同一零范数关系；它保持内积并满射，故为酉。

这一商只合并比较意义上的不可辨别差异。$\Omega$ 中的源、时间标签、来源树与历史仍可不同。这与项目保留丰富历史后再做读出商的方向相容。

### 命题 9.2（任意有限归一化正核可由同一纯源读出）

若非空有限关系表满足 $K\succeq0$、$K_{ii}=1$，存在维数 $\operatorname{rank} K$ 的空间、单位向量 $\Omega_0$ 与酉操作 $U_i$，使

$$
K_{ij}=\langle \Omega_0,U_i^*U_j\Omega_0\rangle.
$$

**证明。**
最小 Gram 实现给单位向量 $v_i$。任取单位 $\Omega_0$，将 $\Omega_0$ 与各 $v_i$ 分别补成正交基，得到 $U_i\Omega_0=v_i$。代入即可。

这证明一个共同源的实现存在；它不决定唯一本体，也不证明这些 $U_i$ 都属于给定实验菜单。

<a id="section-10"></a>

## 10. 从候选逐项重构量子力学

### 10.1 态、效果、Born 形式与谱读出

纯操作态为射线 $P_\psi=\lvert \psi\rangle\langle \psi\rvert$，混合态为其凸组合，即
$\rho\succeq0$、$\operatorname{Tr}\rho=1$。反向由谱分解，每个正的迹一矩阵都是这样的混合。秩至少二的态可沿两个正本征权重作相反微调，从而分解成两个不同态的均值；秩一态的任何凸分解都必须支撑在同一条射线上。因此这些射线恰好是凸状态集的极端点。

### 定理 10.1（仿射概率的唯一矩阵表示）

<a id="thm-born"></a>

任一满足混合一致性的概率函数 $f$ 唯一写成

$$
f(\rho)=\operatorname{Tr}(\rho E),\qquad 0\le E\le I.
$$

若一个射线检验对 $\phi$ 必定接受、对其正交子空间必定拒绝，则 $E=P_\phi$，从而

$$
p(\phi\mid\psi)=|\langle \phi,\psi\rangle|^2.
$$

**证明。**
迹一正矩阵在迹一 Hermitian 仿射超平面中有内点，因此仿射函数唯一延伸到该超平面。常数项用 $\operatorname{Tr}\rho=1$ 吸收，有限维迹配对给某个 Hermitian $E$。在所有纯态上的 $0\le f\le1$ 正好给 $0\le E\le I$。若两个效果给相同函数，其差在每条射线上二次型为零，由极化恒等式差矩阵为零。

射线检验条件给 $\langle \phi,E\phi\rangle=1$、在 $\phi^\perp$ 上评价为零。正性使零评价方向处于 $E$ 的核；$I-E\succeq0$ 使 $E\phi=\phi$。因此 $E=P_\phi$。最后直接计算迹。

这条证明也适用于 qubit，不误用只针对更高维投影框架的原始 Gleason 假设。若结果效果 $E_k$ 总概率恒为一，分离性给 $\sum_kE_k=I$。自伴可观测量 $A=\sum_k a_kP_k$ 的谱检验由投影 $P_k$ 和输出值 $a_k$ 给出。

### 例 10.2（只有互补归一化不迫出平方律）

在单位球面的射线投影上规定 $f(P_{\mathbf n})=(1+n_z^3)/2$。它连续、非负且
$f(P_{\mathbf n})+f(P_{-\mathbf n})=1$，但不是关于 $\mathbf n$ 的仿射函数。它可以按加权平均延伸到“带准备标签的射线分布”，却不能在相同关系矩阵的准备等价商上良定义。因此互补和为一、甚至保留准备标签时的混合仿射都不够；C114.3 明列的关系矩阵等价承担实质工作。
例如，以 $3/4,1/4$ 混合北极和南极，与等权混合 $\mathbf n_\pm=(\pm\sqrt3/2,0,1/2)$，都给 Bloch 向量 $(0,0,1/2)$。前一种准备的上述读数是 $3/4$，后一种是 $9/16$，直接违反准备等价。

### 10.2 独立合成、偏迹与纠缠

### 定理 10.3（独立比较迫出张量内积）

若积记录满足

$$
R_{AB}(u_A\otimes u_B,v_A\otimes v_B)
 =R_A(u_A,v_A)R_B(u_B,v_B),
$$

且联合空间由积记录张成，则零关系商后的联合 Hilbert 空间酉等价于
$\mathcal H_A\otimes\mathcal H_B$。

**证明。**
双线性给代数张量积的线性映射；显示公式使它保持内积。商去零范数后为等距，张成条件使其满射。

局部读出 $\operatorname{Tr}[\rho_{AB}(E_A\otimes I)]$ 唯一确定 $\rho_A=\operatorname{Tr}_B\rho_{AB}$。联合纯态不必为积态，例如 $(\lvert 00\rangle+\lvert 11\rangle)/\sqrt2$ 有混合边缘。共同历史本身也可产生经典相关或积态，因此共享历史和纠缠不是等价定义。

### 10.3 过程延伸、完全正性与记录

仿射过程在未归一化正锥上通过
$\Phi(X)=\operatorname{Tr} X\,\Phi(X/\operatorname{Tr} X)$ 延伸，$X=0$ 时置零，得到加性齐次映射，再线性延伸。分支过程则保留成功权重，不先条件归一化。

### 定理 10.4（内部参考正性给 Kraus 形式）

对 $\Phi:M_d(\mathbb C)\to M_m(\mathbb C)$，若 $\Phi\otimes\operatorname{id}_k$ 对每个有限参考 $k$ 保持正性，则存在矩阵 $A_\mu$ 使

$$
\Phi(X)=\sum_\mu A_\mu X A_\mu^*.
$$

保迹等价于 $\sum_\mu A_\mu^*A_\mu=I$；不增迹等价于该和不超过 $I$。

**证明。**
取未归一化最大纠缠向量 $\Gamma=\sum_{i=1}^d e_i\otimes e_i$。假设给
$C_\Phi=(\Phi\otimes\operatorname{id}_d)(\lvert \Gamma\rangle\langle \Gamma\rvert)\succeq0$。
谱分解写 $C_\Phi=\sum_\mu\lvert a_\mu\rangle\langle a_\mu\rvert$，按输入输出双指标把 $a_\mu$ 重排为矩阵 $A_\mu$。逐个矩阵单位比较，得到所述公式。迹条件由
$\operatorname{Tr}\Phi(X)=\operatorname{Tr}[X\sum A_\mu^*A_\mu]$ 得到。反向每项在任意参考扩张后仍是正的合同变换。

普通正性不够：转置在单系统上正且保迹，但其作用于两 qubit Bell 投影的一个因子后得到交换算子的一半，在反对称方向有本征值 $-1/2$。

对总和保迹的仪器 $\{A_{k\mu}\}$，

$$
V\psi=\sum_{k,\mu}A_{k\mu}\psi\otimes\lvert k,\mu\rangle
$$

满足 $V^*V=I$。结果和未读信息都成为内部正交记录；读取 $k$ 给相应分支，忽略记录给总通道。条件概率分母为零时，不定义该成功后态。

### 10.4 可逆群、酉性与 Schrödinger 形式

### 定理 10.5（同维可逆量子过程为酉共轭）

若同一有限矩阵系统上的保迹完全正映射 $\Phi$ 有保迹完全正逆 $\Psi$，则
$\Phi(X)=UXU^*$，其中 $U$ 酉。连续单参数群由某个自伴 $H$ 生成：

$$
U_t=e^{-itH/\hbar},\qquad i\hbar\dot\psi=H\psi.
$$

**证明。**
写 $\Phi$ 与 $\Psi$ 的 Kraus 算子为 $A_i,B_j$。恒等通道的 Choi 矩阵秩一，所以
$B_jA_i=c_{ji}I$。至少有一项 $c_{ji}\ne0$，对应 $A_i,B_j$ 可逆；固定该 $j$，全部 $A_k$ 都与 $A_i$ 成比例。于是 $\Phi$ 是单 Kraus 形式 $AXA^*$；保迹给 $A^*A=I$，同维使 $A$ 酉。

连续单参数群在恒等附近有连续矩阵对数；由于群内元素彼此交换，局部对数满足加法律，连续性使其为 $tD$。所以该群可微，其生成元 $D$ 是 $*$ 导子。

这里内导子结论可直接验证。对矩阵单位令 $L=\sum_kD(E_{k1})E_{1k}$。由 $E_{ij}E_{k1}=\delta_{jk}E_{i1}$ 的导子律得到 $[L,E_{ij}]=D(E_{ij})$，因而 $D=[L,\cdot]$。保伴随性迫使 $L+L^*$ 是实标量矩阵；减去该标量的一半后可令 $L^*=-L$，于是 $L=-iH/\hbar$，其中 $H=H^*$。积分得到所列共轭与波函数形式。整体相位及 $H$ 的加常数不改变通道。

连续群、时间标尺和具体 $H$ 均是附加的实际运动结构。三维球或静态整体本身不选定运动方程的系数，也不推出任意轨迹必为圆弧或椭圆弧。

### 10.5 不确定性是同一条二元球约束

对自伴 $A,B$，令 $\Delta A=A-\operatorname{Tr}(\rho A)I$、$\Delta B=B-\operatorname{Tr}(\rho B)I$。在 Hilbert–Schmidt 比较中取
$u=\Delta A\sqrt\rho$、$v=\Delta B\sqrt\rho$。二元正性立刻给

$$
\begin{aligned}
\operatorname{Var}_\rho(A)\operatorname{Var}_\rho(B)
 &\ge|\operatorname{Tr}(\rho\Delta A\Delta B)|^2
\end{aligned}
\tag{6}
$$

$$
\begin{aligned}
&=\left(\frac12\operatorname{Tr}\rho\{\Delta A,\Delta B\}\right)^2
 +\left(\frac1{2i}\operatorname{Tr}\rho[A,B]\right)^2.
\end{aligned}
\tag{7}
$$

两项分别是同一二元关系的实、虚坐标。因此不确定关系在这里成为已证明正性规则的一个具体实例。

<a id="section-11"></a>

## 11. 保留 C113：怎样唯一选出理想滤波

<a id="sec-filter"></a>

Born 效果 $E$ 只决定概率。$K=U\sqrt E$ 对不同酉 $U$ 都有 $K^*K=E$，却给出不同后态。为完整接回理想投影更新，本候选明确保留前稿的选择条件。

令 $T(X)=\sum_\mu K_\mu XK_\mu^*$，$\sum K_\mu^*K_\mu=E$。选有限带权纯态 $P_s$、$w_s>0$，满足

$$
\sum_s w_sP_s\otimes P_s=\frac{I+\mathsf F}{d(d+1)},\qquad
 \sum_s w_s=1,
$$

其中 $\mathsf F$ 交换两个因子。定义

$$
R(T)=\sum_s w_s\operatorname{Tr}[P_sT(P_s)],\quad
 Q(E)=\sum_s w_s\bigl(\operatorname{Tr}[P_s\sqrt E]\bigr)^2.
$$

理想分支要求 $R(T)\ge Q(E)$。这是同一过程在同一有限均衡菜单上的饱和要求。

### 定理 11.1（有限同向饱和的唯一性）

总有 $R(T)\le Q(E)$，等号当且仅当 $T(X)=\sqrt E X\sqrt E$，包括奇异效果。

**证明。**
二阶矩给

$$
R(T)=\frac{\operatorname{Tr} E+\sum_\mu|\operatorname{Tr} K_\mu|^2}{d(d+1)},\qquad
 Q(E)=\frac{\operatorname{Tr} E+(\operatorname{Tr}\sqrt E)^2}{d(d+1)}.
$$

在 $A=\sqrt E$ 的本征基 $e_j$ 中写 $Ae_j=\lambda_je_j$、
$v_j=(\langle e_j,K_\mu e_j\rangle)_\mu$。效果等式给
$\|v_j\|^2\le\sum_\mu\|K_\mu e_j\|^2=\lambda_j^2$。
所以

$$
\sum_\mu|\operatorname{Tr} K_\mu|^2=\Big\|\sum_jv_j\Big\|^2
 \le\Big(\sum_j\|v_j\|\Big)^2\le\Big(\sum_j\lambda_j\Big)^2.
$$

若非零效果达到等号，每个范数界均饱和，全部非零 $v_j$ 共同正向，且每个 $K_\mu e_j$ 无其他基分量。因而 $K_\mu=c_\mu A$、$\sum|c_\mu|^2=1$。零效果迫使全部 $K_\mu=0$。反向直接代入。

这一成熟平方根最小扰动结果及其均衡设计联系见 Barnum [5](#ref-barnum)；本稿复述证明是为使完整候选自足。有限均衡菜单在每个维数都可构造：基向量各权 $1/[d(d+1)]$，以及
$(e_1+z_2e_2+\cdots+z_de_d)/\sqrt d$，$z_j\in\{1,i,-1,-i\}$，各权 $d/[(d+1)4^{d-1}]$。四次单位根的四阶平均只保留配对项，得到显示的二阶矩。

成功概率非零时

$$
\rho\longmapsto\frac{\sqrt E\rho\sqrt E}{\operatorname{Tr}(\rho E)}.
$$

投影 $E=P$ 给 Lüders 更新。这个唯一性只适用于被选为理想滤片的分支；一般仪器允许额外旋转或未读记录。

<a id="section-12"></a>

## 12. 更大的几何与内生性的准确含义

二元块的未归一化正锥是四实维的未来 Lorentz 锥

$$
s\ge\sqrt{X^2+Y^2+Z^2}.
$$

迹一截面为 Bloch 球，秩一边界为球面。一般有限对象给 Hermitian 正锥，纯态截面为 $\mathbb{CP}^{d-1}$。不同局部比较是这些大结构的二元压缩；它们共享同一核而非各自任意选取标尺。闭环关系提供 Bargmann 相位，连续有向比较可与射线丛上的几何相位相连 [3](#ref-oszmaniec)、[4](#ref-mukunda)。

对应 AURIC 的一个可检查坐标建议是：归一总强度对应参考方向，三个关系分量对应三个可比较轴，完整交叉核负责共同历史与接续。要将这一建议等同到原生五模式

$$
F[\mathrm{null}],\quad F[1],\quad F[2],\quad F[3],\quad F[1,3],
$$

还需要明确五个接口的状态、操作、合成和读出映射；五个名称本身不携带这些运算。

**一个共同内部模型。** 对有限仪器历史，逐次使用内部等距记录算子，便可把输入、滤片、结果与后续条件放进一个更大的固定纯态。观察者读取一组记录时获得条件态，忽略其他记录时获得混合态。整个描述不需假设本体之外另有观察者。第 [9.1](#thm-hilbert) 定理同时保证可观测等价不擦除原始历史。

**定义和物理选择。** 定义某类对象为满足 C114 的关系网，能够使这些约束成为对象内部的一致性条件。证明物理世界属于该类，则是额外任务。实比较核也满足递归正性；经典对角模型也满足非负归一与混合一致。选择复数、完整相干扇区、实际复合和运动仍有内容。现有量子重构文献同样保留信息原理或 Jordan 结构与复合条件 [6](#ref-cdp)、[7](#ref-barnumwilce)。

| 所需量子结构 | 本候选的准确来源 |
|---|---|
| Hilbert 空间 | 共同复比较、精确有限合成、递归二元正性，随后商去零差异。 |
| 三维 qubit 几何 | 二阶 Hermitian 正锥的迹一截面；纯态为秩一边界。 |
| Born 规则 | 全体纯态混合与仿射概率；射线检验的标定选出秩一效果。 |
| 张量积与纠缠 | 独立比较因子化、双线性及积记录张成；局部态由偏迹给出。 |
| 一般量子过程 | 混合线性与所有内部参考下的正性；Choi 分解给 Kraus 形式。 |
| 理想投影更新 | C113 有限均衡同向饱和的附加选择；单凭效果不够。 |
| 酉与 Schrödinger | 同维双向合法的确定过程，加连续单参数群与时间单位。 |
| 不确定关系 | 涨落对象构成的二元 Gram 块正性。 |
| 唯一物理本体 | 本稿给共同源实现与内部相容性，没有证明物理本体的唯一性。 |

<a id="section-13"></a>

## 13. 删除条件后的明确后果

| 删去的约束 | 可出现的失败 |
|---|---|
| 共同相位标尺 | 各二元表可独立重定向，无法当作同一个核的条目；循环相位不再可比较。 |
| 合成后的继续检查 | $2I_3-J_3$ 的每个原始二元块合法，三元总强度却为负。 |
| 任意有限层级 | 四阶等相关反例通过全部三阶检查，仍无整体正实现。 |
| 零主元必须零关系 | $K=0,c\ne0$ 会被仅检查剩余标量的伪规则误判。 |
| 混合一致性 | $(1+n_z^3)/2$ 通过互补归一，却不满足 Born 仿射形式。 |
| 内部参考延伸 | 转置通过单系统正性，却破坏纠缠参考下的正性。 |
| 理想滤波选择 | $U\sqrt E$ 给相同成功概率，却给不同后态。 |
| 实际连续可逆群 | 正性只描述允许的内容，不能确定时间演化或具体 Hamiltonian。 |

这些反例把每条条件作用的对象和后果分别固定。它们也说明，内生性应落实为可检查的运算相容，不能只靠改名减少前提。

<a id="section-14"></a>

## 14. 完整白话描述

每份内容不仅有自己的份量，还带着它与其他内容的相对关系。把两份内容放在一起比较，份量差、同向关系和转向关系可以放进一个三维球。球内表示这些关系可以共同成立，球面表示这一次二元比较没有独立的剩余方向。

把两份内容合起来以后，它们同其余内容的关系也必须一并带过去。再遇到新内容，就先扣掉共同历史已经解释的部分，对剩下的两个部分继续做同样的三维检查。新内容不能欠下负的份量，也不能在一个已经没有份量的方向上留下关系。要求每一层都做到这一点，整个有限关系网就能放进同一个正的比较空间；把任何比较都看不出的差异暂时合并，就得到量子态使用的 Hilbert 空间。

测量是读取这张关系网的一个方向。在关系坐标中它是线性的，在振幅坐标中便写成平方。不同关系沿环路接起来，还会保留有向的相位，这就是两两距离看不见的手性。多个部分的共同关系无法拆成独立关系时，可以出现纠缠。保留全部比较关系的连续可逆变化给出酉运动；理想滤片再由内部均衡比较选择出平方根更新。

内容、读口、滤片、相位参考、历史和观察者都可以属于同一个固定整体。观察者看到的改变来自它所读取和条件化的内部记录。这个候选现在已经能明确说明哪些关系推出哪些量子结构；仍需要继续解释的，是共同复比较、实际操作供应及具体运动为何恰好采取这些形式。

<a id="references"></a>

## 参考文献

<a id="ref-c113"></a>

### [1]

 AURIC C113，《内部均衡校准与滤波组合几何》，2026-11-03，先前交付的源稿。
[已核读的 C113 TeX](https://chatgpt.com/library?file_id=libfile_66026db71e50819193e34b26d89d03e4&account_id=personal)。其记载的仓库快照为 `40e161f1b410721daad15d8ceaad34c3d7e19759`；本轮未重新取得该快照的主卷正文。

<a id="ref-repo-blind"></a>

### [2]

 the-omega-institute/trureturing,
[LocalMarginalCorrelationBlindSpot.lean](https://github.com/the-omega-institute/trureturing/blob/dev/D5/S3/Quantum/Entanglement/LocalMarginalCorrelationBlindSpot.lean)，本轮核读公开 dev 页面；未重新执行其 Lean 构建。

<a id="ref-oszmaniec"></a>

### [3]

 M. Oszmaniec, D. J. Brod, E. F. Galvão,
*Measuring relational information between quantum states, and applications*,
[arXiv:2109.10006v1](https://arxiv.org/html/2109.10006v1) (2021).

<a id="ref-mukunda"></a>

### [4]

 E. M. Rabei, Arvind, R. Simon, N. Mukunda,
*Bargmann Invariants and Geometric Phases: A Generalised Connection*,
[arXiv:quant-ph/9907080](https://arxiv.org/abs/quant-ph/9907080); Phys. Rev. A 60, 3397 (1999).

<a id="ref-barnum"></a>

### [5]

 H. Barnum,
*Information-disturbance tradeoff in quantum measurement on the uniform ensemble and on the mutually unbiased bases*,
[arXiv:quant-ph/0205155](https://arxiv.org/abs/quant-ph/0205155) (2002).

<a id="ref-cdp"></a>

### [6]

 G. Chiribella, G. M. D'Ariano, P. Perinotti,
*Informational derivation of Quantum Theory*,
[arXiv:1011.6451](https://arxiv.org/abs/1011.6451); Phys. Rev. A 84, 012311 (2011).

<a id="ref-barnumwilce"></a>

### [7]

 H. Barnum, A. Wilce,
*Local tomography and the Jordan structure of quantum theory*,
[arXiv:1202.4513](https://arxiv.org/abs/1202.4513) (2012/2013).
