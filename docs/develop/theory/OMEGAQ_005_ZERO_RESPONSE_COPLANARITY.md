# 无响应即同面

> 参考输入：AI 撰写的工作稿，由用户提供于本会话（2026-11-04，Asia/Singapore）。Lean 是仓库的数学真源；本文仅为参考文稿，未作形式化认证。

QUANTUM ORIGINS / $\Omega Q$-005

只锁定二元关系的零处，再推出三维、面积与量子结构

从同一原来源定义内容 $W$、参照 $e$、可逆作用 $G$ 与正比较 $B$。本轮只保留一个原非零转向 $A$，要求

$$
\boxed{\quad B(x,Ay)=0
\quad\Longleftrightarrow\quad
e,x,y\text{ 线性相关}\quad(x,y\in W).\quad}
$$

三条箭头都从原中心出发。“同面”包括共线和零向量，表示它们可以放入一个至多二维的*线性*平面。它不指任意三个仿射点的共面。

一个方向的无响应者恰好由它和原参照拼成；把被转出的方向补上，就容纳了全部原内容。因此只有三维。面积平方关系、复数和 Born 表示随后成为结论。

 本会话新系列第五篇，承接 $\Omega Q$-004。

日期：2026-11-04，Asia/Singapore。

固定版本：`dev@7c2b901642e29adbf2907b53d6a5f7db831e7df1`。

提交时间：2026-11-04 06:16:14，新加坡时间。

范围：有限原预测窗口上的条件重建与普通数学证明。

本轮降低约束的量词层级，不声称逻辑严格弱化或文献首创。

已只读核对来源；未修改仓库，未重新构建或认证 Lean。

## 本轮真正简化了什么

上一轮要求一个保持原准备的转向，在 $W/\mathbb R e$ 上不可约。本轮不再把商空间、$Ae=0$、所有不变内容片作为候选的表达部分，只约束两个原内容向量之间的比较响应何时为零。

两个候选在同一原前端、同一 $e,A$ 上等价。本轮的三维证明不需要谱分解，孤立几何引理甚至不需要先验有限维。原预测前端仍保留有限容量，以获得紧作用和内部比较；本文不将局部引理的加强冒充整个前端已去除有限性。

此外，比较尺直接由原来源轨道的协方差定义，无需先任选一份内积。零条件确定几何和转向线；原转向的速度、正负取向及成功过程的原强度继续保留。

<a id="section-1"></a>

## 1. 最新项目进展及本轮接点

相对上一轮固定提交 `2d80e2d87f58d687ee660169fbeb4b8f07f2e1f5`，本轮固定比较含 50 个提交。完整公开 diff 核对出 1,424 个改变路径；REST 首批的 300 项是截断列表。相关理论正文实际改变的只有下列三份。 [1](#ref-repocompare)

| 正文 | 新增部分 | 准确推进 |
|---|---|---|
| C123/C124 | §§18–20，271 行 | 保留成功尺度的双返回，分类指定 Lorentz 比较群 |
| Four-path II | §44，414 行 | 依赖布居的全局谱下界、完整饱和集和严格排除区 |
| FIB Appendix III | §§142–144，348 行 | 同一确定性精确秩二分区序列逼近全部 64 项联合律 |

C113、C117、C122、C115、V95 与 V96 continuation 六份正文逐字未变。HEAD 标题中的 C117/C122 ingest 是来源登记，不是本轮新增量子起源证明。

本轮接点有两个。第一，归一条件作用相同，原成功强度仍可不同，并改变它们所在的大群。第二，任意精度的共同读数逼近，仍不等于一份实际对象精确实现全部关系。第 [8](#sec-lorentz) 节重述并证明最新 Lorentz 分类的关键链；第 [9](#sec-updates) 节说明其余增量的边界。它们不作为本轮三维起源的前提。

<a id="section-2"></a>

## 2. 原定义：来源、内容、转向与无外加选择的比较

<a id="sec-front"></a>

### 定义 2.1（同一原全未来预测窗口）

在同一 $\Omega$ 内取一个原归一准备。原总可逆控制词菜单 $\mathcal L$ 含空词，封闭于接续，并含同菜单的准确统计逆。共同合法未来域保留全部原终端标签，包括失败。定义

$$
x_a(f,w)=p(a;f,w),\quad
p(a;f,w)\ge0,\quad \sum_wp(a;f,w)=1,
\quad p(ag;f,w)=p(a;gf,w).
$$

设原行空间 $V=\operatorname{span}_\mathbb R\{x_a\}$ 有限维，但维数未知。归一化泛函 $u(x_a)=1$，并定义

$$
W=\ker u=\operatorname{span}\{x_a-x_b\},\qquad T_gx_a=x_{ag}.
$$

所有内容差都按全部共同合法未来定义；没有先删去隐藏记忆、原标签或可用性差别。

### 引理 2.2（紧作用与原来源循环性）

接续 $T_g$ 良定义，其响应群在 $GL(V)$ 内的闭包 $H$ 紧。取原行的 Haar 平均 $c$，令

$$
u(c)=1,\quad V=\mathbb R c\oplus W,\quad
G=H|_W,\quad \mathfrak g=\operatorname{Lie}(G),\quad
e=x_\epsilon-c.
$$

则 $G$ 忠实，并有

<a id="eq-cyclic"></a>

$$
\boxed{W=\operatorname{span}(Ge).}
\tag{2.1}
$$

**证明。**
原行关系在全部未来为零，故在以 $g$ 开头的未来也为零，接续良定义。选有限实际行基与有限分离终端坐标；所有接续后基行的坐标仍在 $[0,1]$，所以 $T_g$ 一致有界。统计逆给逆的一致有界，闭包紧且不含奇异矩阵。平均得固定 $c$。固定 $c$ 且在 $W$ 上恒等的算子在 $V$ 上恒等，故限制忠实。每个 $x_a-c=T_ae$，这些差行张成 $W$，有限维取闭包不改变张成，得 [(2.1)](#eq-cyclic)。

这复用 C117 的全未来入口的一般部分，不复用容量四作为输入。 [2](#ref-repo117) 数学闭包中的指数不是已供应的精确有限门。

### 定义 2.3（原来源轨道的比较尺）

若 $W=0$，本轮非零转向候选直接不成立。对非平凡窗口，以归一 Haar 测度定义

$$
\mathcal K:W^*\longrightarrow W,\qquad
\mathcal K\alpha=\int_G\alpha(ge)\,ge\,dg.
$$

再定义

<a id="eq-cov"></a>

$$
B_0(x,y)=(\mathcal K^{-1}x)(y),\qquad
B(x,y)=\frac{B_0(x,y)}{B_0(e,e)}.
\tag{2.2}
$$

### 引理 2.4（内生正比较）

$\mathcal K$ 可逆，$B_0,B$ 对称正定且 $G$-不变。本定义由同一原来源与原作用唯一确定这两份比较，并满足

$$
B_0(e,e)=\dim W,\qquad B(e,e)=1.
$$

**证明。**
对非零 $\alpha$，循环性保证某个 $\alpha(ge)\ne0$。连续非零函数在一个非空开集非零，而紧群 Haar 测度在该集为正，故

$$
\alpha(\mathcal K\alpha)=\int_G\alpha(ge)^2\,dg>0.
$$

有限维因此给出对称正定可逆 $\mathcal K$。左平移 Haar 不变性给
$g\mathcal K g^*=\mathcal K$，其中 $g^*\alpha=\alpha\circ g$，从而 $B_0(gx,gy)=B_0(x,y)$。最后，秩一算子的迹公式给

$$
\dim W=\operatorname{Tr}(\mathcal K\mathcal K^{-1})
=\int_GB_0(ge,ge)\,dg=B_0(e,e).
$$

归一化后结论成立。

这里的平均是定义比较的数学运算，不声称原菜单能够实施 Haar 随机混合。原时间与原概率没有由这个平均重定义。

<a id="section-3"></a>

## 3. 唯一候选：二元零关系与同面关系相同

<a id="sec-candidate"></a>

对原 $A\in\mathfrak g$，定义内部比较响应

$$
\omega_A(x,y)=B(x,Ay)
=\left.\frac{d}{dt}B(x,e^{tA}y)\right|_{t=0}.
$$

它是两个内容向量 $x,y$ 的二元关系；$A$ 是一个原转向见证。它尚不是自动可调用的原终端效果或事件概率。

**候选 $\Omega Q$-005。**存在 $A\in\mathfrak g\setminus\{0\}$，使

<a id="eq-Q5"></a>

$$
\boxed{\forall x,y\in W:\quad
\omega_A(x,y)=0
\quad\Longleftrightarrow\quad
\dim\operatorname{span}\{e,x,y\}\le2.}
\tag{3.1}
$$

三条箭头都从同一个原中心出发：两份内容间没有转向响应，恰好表示它们与原参照在同一线性平面中。零向量、共线和反向情况都包含在内。

**先反着推。**

若只要求“同面必无响应”，原非零转向仍能在不动轴以外藏着彼此独立的变化。取原球面预测模型 $W=\mathbb R^5$、$G=SO(5)$、原源 $e=e_1$，完整读数

$$
p(\pm\mid n,r)=\tfrac12(1\pm n\cdot r),\qquad \|n\|=\|r\|=1.
$$

这些读数分离 $V=\mathbb R\oplus W$，原来源轨道张成 $W$。令

$$
A=0\oplus J_2\oplus J_2,\qquad
J_2=\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
$$

它只固定 $\mathbb R e$，也满足同面必无响应；但 $x=e_2,y=e_4$ 有 $\omega_A(x,y)=0$，而 $e,x,y$ 独立。两片甚至同速旋转，故问题不只是存在不同频率。完整反向要求禁止的正是这种**仍可被原未来区别的额外静默方向**。

反过来，若只要求“无响应必同面”，二维圆盘 $W=\mathbb R^2,G=SO(2),e=e_1$ 的非零转向就满足它，因为任何三个向量都相关，却通常 $Ae\ne0$。若再允许 $A=0$，同一个圆盘模型甚至满足完整双向零关系。两个方向与非零性都有确定作用。

<a id="section-4"></a>

## 4. 三维有限提升：一次补方向即封闭

<a id="sec-main"></a>

### 定理 4.1（零关系的三维刚性）

孤立地设 $W$ 为任意实向量空间，$B$ 为对称非退化双线性型，$A\ne0$ 为线性算子。若式 [(3.1)](#eq-Q5) 成立，则

$$
e\ne0,\qquad Ae=0,\qquad
B(x,Ay)=-B(Ax,y),\qquad \dim W=3.
$$

这一步不要求先验有限维。

**证明。**
若 $e=0$，任意 $e,x,y$ 相关，故 $B(x,Ay)=0$ 对所有 $x,y$ 成立；非退化性给 $A=0$，矛盾。令 $y=e$，同样得到 $Ae=0$。令 $y=x$ 并极化，得到斜对称性。

取 $Ay\ne0$。则 $e,y$ 独立，且非零线性泛函
$\ell_y(x)=B(x,Ay)$ 满足

$$
\boxed{\ker\ell_y=\operatorname{span}(e,y).}
$$

选 $z$ 使 $\ell_y(z)=1$。每个 $x$ 都分解为

$$
x=\underbrace{x-\ell_y(x)z}_{\in\operatorname{span}(e,y)}
+\ell_y(x)z.
$$

因此 $W=\operatorname{span}(e,y,z)$，而三者独立，故恰好三维。

### 推论 4.2（正比较下的显式三轴分解）

使用原正定 $B$，将 $y$ 换成 $y-B(e,y)e$，其 $Ay$ 不变。此时 $e,y,Ay$ 两两正交，而且

<a id="eq-three"></a>

$$
\boxed{x=B(x,e)e+
\frac{B(x,y)}{B(y,y)}y+
\frac{B(x,Ay)}{B(Ay,Ay)}Ay\qquad(x\in W).}
\tag{4.1}
$$

**证明。**
$Ae=0$ 与斜对称性给 $B(e,Ay)=B(y,Ay)=0$。从任意 $x$ 减去最后一项，剩余落在 $\ker\ell_y=\operatorname{span}(e,y)$；再用正交性给出前两项。

```latex
\begin{tikzpicture}[>=Latex,every node/.style={font=\small},scale=1.0]
\fill[pale] (-0.65,-0.8)--(2.2,-0.4)--(2.2,1.75)--(-0.65,1.35)--cycle;
\draw[accent] (-0.65,-0.8)--(2.2,-0.4)--(2.2,1.75)--(-0.65,1.35)--cycle;
\draw[->,thick,ink] (0,0)--(0,2.15) node[above] {$e$：原参照};
\draw[->,thick,ink] (0,0)--(2.65,0.37) node[right] {$y$};
\draw[->,very thick,accent] (0,0)--(-1.7,-1.15) node[left] {$Ay$};
\node[align=center] at (1.23,1.12) {$\omega_A(x,y)=0$\\$\ker\ell_y=\spn(e,y)$};
\node[align=center] at (0.75,-2.15) {同面的一切无响应；$Ay$ 补出唯一独立的离面分量。\\平面与箭头均为透视投影，全部从同一中心出发。};
\end{tikzpicture}
```

### 定理 4.3（三份原关系生成全部旋转）

在原预测前端与候选 [(3.1)](#eq-Q5) 下，

$$
\boxed{\dim W=3,\quad \dim V=4,\quad
\mathfrak g=\mathfrak{so}(W,B),\quad G^\circ=SO(3).}
$$

完整原群为 $SO(3)$ 或 $O(3)$。

**证明。**
还须证明原控制足够丰富。若 $Xe=0$ 对全部 $X\in\mathfrak g$ 成立，则

$$
X(ge)=g(\operatorname{Ad}_{g^{-1}}X)e=0\qquad(g\in G).
$$

全群正规化其 Lie 代数，且 $Ge$ 张成 $W$，故所有 $X=0$，与原 $A\ne0$ 矛盾。因此存在原 $X$ 使 $p=Xe\ne0$。

由三维、斜对称及 $Ae=0$，$\ker A=\mathbb R e$。又 $p\perp e$，故 $p,Ap$ 非零正交。三份原生成元

$$
A,\qquad X,\qquad [A,X]
$$

线性独立：将其线性关系作用于 $e$，得到 $p,Ap$ 的关系，先迫使对应两系数为零，再由 $A\ne0$ 得最后系数为零。由于 $\mathfrak g\subseteq\mathfrak{so}(W,B)$，右边恰三维，故相等。群结论随之成立。

这段证明直接显示关系的关系：原内容方向 $Xe$ 与原顺序差 $[A,X]e=A(Xe)$ 给出两个横向方向。不需要先假定稳定子交换，也覆盖不连通的原群。

**为何保留单源循环性。**

若人为规定 $W=\mathbb R^3$、$G=SO(2)\times\{\pm1\}$，前者转横向平面，后者翻转 $e$ 轴，则中心化原轨道只有 $\{\pm e\}$。零关系可以在这个人为三维载体上成立，但原 Lie 代数只有一维。其问题是原轨道不张成所声称的 $W$；额外平面没有来自原来源。这不反驳完整前端。

<a id="section-5"></a>

## 5. 零处先锁住，面积大小随后被迫出现

<a id="sec-area"></a>

令

$$
\lambda^2=-\tfrac12\operatorname{Tr}_W(A^2)>0,\qquad J_e=A/\lambda,\qquad U=e^\perp.
$$

二维斜对称性给 $J_e^2=-P_U$。取 $B$-单位 $p\in U$，令 $q=J_ep$，则

$$
Ap=\lambda q,\qquad Aq=-\lambda p.
$$

### 定理 5.1（零关系推出完整面积平方式）

对全部 $x,y\in W$，

<a id="eq-area"></a>

$$
\boxed{\omega_A(x,y)^2
=\lambda^2\det\operatorname{Gram}_B(e,x,y).}
\tag{5.1}
$$

特别地，对 $x,y\in U$，

<a id="eq-pyth"></a>

$$
\boxed{B(x,y)^2+\lambda^{-2}\omega_A(x,y)^2
=B(x,x)B(y,y).}
\tag{5.2}
$$

**证明。**
写 $x=\alpha e+up+vq$、$y=\beta e+sp+tq$，则
$\omega_A(x,y)=\lambda(vs-ut)$，而 Gram 行列式为 $(ut-vs)^2$。式 [(5.2)](#eq-pyth) 是横向二阶 Gram 行列式的展开。

所以候选没有预给面积恒等式或平方大小。在原线性作用与正比较下，零集的相等迫使非零值的比例关系。该比例仍保留原 $\lambda$，不是从零集得到了物理钟速。

### 命题 5.2（取向线与共同运输）

同一 $e,B$ 下的两个合格转向 $A_1,A_2$ 必满足 $A_2=tA_1$、$t\ne0$。对原 $g\in G$，同时运输 $e\mapsto ge$、$A\mapsto gAg^{-1}$ 保持零关系。

**证明。**
固定 $e$ 的三维斜对称算子空间一维，故前项成立；后项由 $B$ 不变和线性相关在可逆运输下保持得出。

**正定比较的准确作用。**

非退化零关系负责三维，正定性负责椭圆转向。若孤立地改为
$B=\operatorname{diag}(1,1,-1)$、$e=e_1$，并取 $Ae_2=e_3,Ae_3=e_2,Ae_1=0$，则

$$
B(x,Ay)=x_2y_3-x_3y_2
$$

仍满足完整零关系，但 $A^2|_{e^\perp}=+I$，是双曲而非圆转向。它不满足原紧预测前端。后面 $V$ 上的 Lorentz 型也不能替代这里 $W$ 上的正比较：两者载体和作用不同。

### 5.1 同一见证上的压缩与有限证书

本轮推出 $Ae=0$ 和二维非零横向旋转，故同一 $A$ 满足上一轮不可约条件。反向，上轮候选给三维与同一非零 $A$，上述基计算立刻给零关系。因此

$$
Q_4(e,A)\ \Longleftrightarrow\ Q_5(e,A).
$$

旧的

$$
\Xi_{A,e}:\mathfrak g/\mathbb R A\to W/\mathbb R e,\qquad
[X]\mapsto[[A,X]e]
$$

也自动为同构：$[X]\mapsto Xe$ 将控制商同构到 $U$，再复合可逆 $A|_U$。本文主证明不借用旧刚性定理。

在已识别的完整原 $W$ 内，确认 $A\in\mathfrak g\setminus\{0\}$、$Ae=0$，选任一 $Ay\ne0$，只需核对

$$
\ker[B(\,\cdot\,,Ay)]=\operatorname{span}(e,y)
$$

即可认证完整候选。它是一个线性核计算，免去所有不变子空间的搜索。若另有 $x$ 在此核中而不在该张成内，$(x,y)$ 就是明确反证对。

该证书消费完整原空间的识别；有限采样不认证未知未来没有额外方向。简化是从不变子空间量化降为原向量对的一个零关系，且三维证明更短；“线性相关”依然是实质低秩约束。

<a id="section-6"></a>

## 6. 更大结构：响应、复振幅、球面与原概率

<a id="sec-quantum"></a>

### 6.1 同一转向恢复全部二元响应

对 $x=\alpha e+u$、$y=\beta e+v$，$u,v\in U=e^\perp$，定义

<a id="eq-D"></a>

$$
\boxed{D_xy=\alpha J_ev-\beta J_eu+B(J_eu,v)e.}
\tag{6.1}
$$

在正交基 $(e,p,q)$、$q=J_ep$ 上，直接计算为

$$
D_ep=q,\qquad D_pq=e,\qquad D_qe=p.
$$

所以 $D$ 是这个取向的三维叉积，$D_x\in\mathfrak g$，并满足

$$
D_xx=0,\quad
-\tfrac12\operatorname{Tr}(D_xD_y)=B(x,y),\quad
D_xD_yz=B(x,z)y-B(x,y)z.
$$

反对称性、Jacobi 与面积公式均由这些关系推出。实际 $A=\lambda D_e$，其速度没有抹去。正旋转运输 $D$；全 $O(3)$ 作用有

$$
D_{gx}=\det(g)\,gD_xg^{-1}.
$$

在 $\mathbb R1\oplus W$ 定义

$$
(\alpha,x)\circ(\beta,y)
=(\alpha\beta+B(x,y),\,\alpha y+\beta x),\qquad L_ab=a\circ b.
$$

将 $D$ 在单位方向上延为零。三重积给

$$
\boxed{[L_a,L_b]+[D_a,D_b]=0,\qquad [D_a,L_b]=L_{D_ab}.}
$$

这就是比较与响应的 Jordan–Lie 相容结构：原响应同时运输内容和内容间的对称关系。

### 6.2 结合完成与中心复单位

定义最小实含幺结合代数

$$
\mathcal A=\operatorname{Cl}_{3,0},\qquad
xy+yx=2B(x,y)1,\quad x^*=x\quad(x,y\in W).
$$

置 $J=epq$。生成关系给

$$
J^2=-1,\qquad J^*=-J,\qquad Jx=xJ,\qquad
xy=B(x,y)1+JD_xy.
$$

$J$ 是代数的中心复单位；$J_e=A/\lambda$ 则是横向内容上的算子，两者类型不同。

### 定理 6.1（复二维振幅）

$$
\boxed{\mathcal A\cong M_2(\mathbb C_J),\qquad
\mathcal H=\mathcal A p_+\cong\mathbb C_J^2,\qquad p_+=(1+e)/2.}
$$

**证明。**
反交换关系把任意词约到八个实基词。将 $(p,q,e)$ 送至

$$
\sigma_1=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
\sigma_2=\begin{pmatrix}0&-J\\J&0\end{pmatrix},\quad
\sigma_3=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
$$

它们满足生成关系，八个像实线性独立并张成 $M_2(\mathbb C_J)$，故同构。$\mathcal A p_+$ 以 $p_+,pp_+$ 为复基，且
$\xi^*\eta=\langle\xi,\eta\rangle p_+$ 给正内积，范数平方为 $|z_1|^2+|z_2|^2$。

这里明确采用最小结合数学完成；所有矩阵并未自动成为原实际门。

### 6.3 原概率的 Born 表示

原准备轨道闭包为 $c+S^2$，最小闭凸完成为 $c+\overline B^3$，相应正锥为

$$
C=\{tc+w:t\ge\|w\|_B\}.
$$

定义 $S(w)=\sum_iw_i\sigma_i$、$\rho_w=(I+S(w))/2$。

### 定理 6.2（保留原数值的概率表示）

对每个原未来事件 $f$，存在唯一 $0\le E_f\le I$，使

$$
\boxed{f(c+w)=\operatorname{Tr}(\rho_wE_f),\qquad \|w\|\le1.}
$$

每个完整原测试仍有 $\sum_jE_j=I$，保留所有原标签。

**证明。**
$S(w)^2=\|w\|^2I$，故 $\rho_w\ge0$、$\operatorname{Tr}\rho_w=1$。原事件是行空间上的线性泛函，写作 $f(tc+w)=\alpha t+B(b,w)$。它在原轨道取值于 $[0,1]$，由闭包与凸性给
$\|b\|\le\min(\alpha,1-\alpha)$。所以 $E_f=\alpha I+S(b)$ 是效果，迹计算保持配对。原归一关系 $\sum_jf_j=u$ 给效果和为单位。

对纯方向 $n,m$，$P_n=(I+n\cdot\sigma)/2$ 为秩一投影，故

$$
\operatorname{Tr}(P_nP_m)=\frac{1+n\cdot m}{2}
=\cos^2\frac{\theta}{2}
=|\langle\psi_n,\psi_m\rangle|^2.
$$

相位几何是

$$
\boxed{S^1\longrightarrow S^3\longrightarrow S^2\cong\mathbb{CP}^1,}
$$

其映射为

$$
(z_1,z_2)\mapsto
(2\Re\bar z_1z_2,\ 2\Im\bar z_1z_2,\ |z_1|^2-|z_2|^2),
\quad |z_1|^2+|z_2|^2=1.
$$

旋转提升 $U_n(\theta)=\exp[-J\theta S(n)/2]$ 解释半角与 $4\pi$ 振幅复原。原稳定子的转角与 Hopf 相位通过此提升相接，不能在证明前认作同一个对象。

三维指内容差维数，不是物理空间维数。若原效果只有
$(I\pm\eta n\cdot\sigma)/2$、$0<\eta<1$，仍可分离全部方向并满足候选，却没有实际锐读口。最小闭凸完成也不声称全局 $\Omega$ 纯态或每个极限准备已可调用。

<a id="section-7"></a>

## 7. 完整有限量子理论及准确接口

<a id="sec-full"></a>

以下在已重建的块上发展有限数学完成，逐项写出复合和实际过程所需条件。普通矩阵工具可与 Watrous 第 2 章核对。 [6](#ref-watrous)

### 7.1 复合、状态与测量

### 命题 7.1（复张量代数）

若局部 $M_m(\mathbb C_J),M_n(\mathbb C_J)$ 以同一复中心含幺 $*$-嵌入联合 $*$-代数，两个像交换且乘积复线性张成联合代数，则

$$
\mathcal A_{AB}\cong M_m(\mathbb C_J)\otimes_{\mathbb C_J}M_n(\mathbb C_J)
\cong M_{mn}(\mathbb C_J).
$$

**证明。**
$a\otimes b\mapsto\iota_A(a)\iota_B(b)$ 为满射含幺 $*$-同态；源代数是单矩阵代数，其核只能为零或全体，含幺排除全体。

复合量子比特得到 $M_{2^N}$。取数学投影角和有限直和，得到全部
$\mathcal A=\bigoplus_jM_{d_j}(\mathbb C_J)$。实际角和经典记录仍需原附接与支持返回。

### 命题 7.2（密度、效果与可观测量）

标准正锥上的全部归一正泛函唯一表示为

$$
\omega(a)=\sum_j\operatorname{Tr}(\rho_ja_j),\qquad
\rho_j\ge0,\quad\sum_j\operatorname{Tr}\rho_j=1.
$$

效果为 $0\le E\le I$，测量为 $\sum_kE_k=I$。自伴 $H$ 的谱分解 $H=\sum_kh_kP_k$ 给概率 $\operatorname{Tr}(\rho P_k)$ 与均值 $\operatorname{Tr}(\rho H)$。

**证明。**
非退化迹配对给唯一自伴密度；在每个秩一正投影上的正性迫使各密度块非负；单位上的取值给总迹一。反向直接成立。自伴谱定理给最后结论。

实际联合态是否供应整个标准正锥须另核；单个球或张量代数同构不证明此供应。

### 7.2 完整参考、一般过程与反射

### 定理 7.3（参考正性到 Kraus 表示）

设同一原分支在自伴部实线性，并复线性延拓为 $\mathcal E:M_d\to M_n$。若实际参考含完整 $M_r$ 块、$r\ge d$，且 $\mathcal E\otimes\operatorname{id}_r$ 在完整标准联合正锥上保正，则

$$
\mathcal E(\rho)=\sum_\mu K_\mu\rho K_\mu^*.
$$

对完整数学正锥的所有归一态不增总概率，等价于
$\sum_\mu K_\mu^*K_\mu\le I$。完整仪器在该完整态空间归一，等价于
$\sum_{k,\mu}K_{k\mu}^*K_{k\mu}=I$，其中 $k$ 保留全部原记录。

**证明。**
在参考中取 $d$ 维数学子空间与
$|\Omega\rangle=\sum_i|i\rangle\otimes|i\rangle$。完整联合正性给

$$
C_{\mathcal E}=(\mathcal E\otimes\operatorname{id})(|\Omega\rangle\langle\Omega|)\ge0.
$$

谱分解为正秩一项，将向量重排为矩阵 $K_\mu$，比较矩阵单位系数即得公式。逆向每项共轭在任意参考上保正。迹配对给概率条件。

经典标签的总维数不能代替完整矩阵参考，乘积态测试也不够。数学 Kraus 指标不是自动可访问的原标签。

一个代表性的 Bloch 反射为转置 $T$，且

$$
(T\otimes\operatorname{id})(|\Phi^+\rangle\langle\Phi^+|)
=\tfrac12\operatorname{Swap}
$$

有负特征值 $-1/2$。任意取向反转元是它与正旋转的复合。因此同一原控制族若满足完整参考条件，就不含反射；若原菜单确已含反射，则该实例不满足这个后续条件，不能删掉它来冒认同一实例完成。

### 7.3 理想更新与连续可逆演化

### 定理 7.4（Lüders 形式）

简单块上，CP 分支若效果为投影 $P$，且不扰动每个支撑于 $P$ 的态，则

$$
\mathcal E(\rho)=P\rho P.
$$

**证明。**
$\sum_\mu K_\mu^*K_\mu=P$ 给 $K_\mu=K_\mu P$。对每个 $\psi\in P\mathcal H$，不扰动要求
$\sum_\mu|K_\mu\psi\rangle\langle K_\mu\psi|=|\psi\rangle\langle\psi|$。
正秩一和迫使各 $K_\mu\psi$ 与 $\psi$ 共线。对两个独立向量及其和用线性得 $K_\mu=c_\mu P$、$\sum_\mu|c_\mu|^2=1$。秩一支撑直接成立，$P=0$ 给零分支。

成功概率正时才归一为 $P\rho P/\operatorname{Tr}(\rho P)$。只保持一组基态或仅可重复都不足够，支撑内退相干可反驳。有限直和按中心块分别处理。

### 定理 7.5（幺正演化形式）

同一简单块上的连续 CPTP 单参数群若逆也 CP，则

$$
\mathcal E_t(\rho)=U_t\rho U_t^*,\qquad
U_t=e^{-JtH/\hbar},\quad H=H^*.
$$

所以 $J\hbar\dot\psi=H\psi$、$\dot\rho=-(J/\hbar)[H,\rho]$。

**证明。**
对偶及其逆均保单位且 CP。分别应用 Schwarz 不等式，得等号
$T(a^*a)=T(a)^*T(a)$。极化给乘法保持，故是 $*$-自同构。矩阵单位的像可用酉基变换实现，连续单参数自同构的内导子给酉指数。标量相位不影响态。连续群不能置换有限离散中心，直和逐块成立。

物理时钟、具体 $H$、精确连续调用与 $\hbar$ 数值仍需原物理内容。

局部完整 CPTP 操作并忘去全部结果时，

$$
\operatorname{Tr}_B[(\operatorname{id}\otimes\mathcal E_B)(\rho_{AB})]=\operatorname{Tr}_B\rho_{AB},
$$

给出无信号性；后选择或任意联合操作不在此命题内。状态半内积的 Cauchy–Schwarz 给

$$
\operatorname{Var}_\rho(H)\operatorname{Var}_\rho(K)
\ge\left|\frac1{2J}\operatorname{Tr}(\rho[H,K])\right|^2.
$$

### 7.4 既有实际供应仍按原对象接入

C124 的原子、必然、非中心指针配对 $d=cp,\alpha(d)=1$，其中 $0<c\le1$、$p$ 是同一非经典块中的秩一投影，给

$$
1=\operatorname{Tr}(\rho_\alpha cp)\le c\operatorname{Tr}\rho_\alpha\le c\le1,
$$

故 $d=\rho_\alpha=p$。其整个原指针内的两方向配合

$$
U_E=\begin{pmatrix}\sqrt E&-\sqrt{I-E}\\
\sqrt{I-E}&\sqrt E\end{pmatrix}
$$

在其余指针方向及其余中心块上取恒等，再接原准备、原破坏性读口，可供应成功支
$\sqrt E\,\rho\,\sqrt E$。这消费其完整原联合 P/G/D、准确门调用、原记录、合法连线、失败补全与丢弃条件；局部候选没有自动给出这些条件，也不要求数学二维角已是实际 qubit 对象。 [3](#ref-repo124)

<a id="section-8"></a>

## 8. 接入最新 C124：球锥为何扩成 Lorentz 几何

<a id="sec-lorentz"></a>

用本轮所得内容坐标写

$$
X(t,w)=\tfrac12(tI+w\cdot\sigma),\qquad
\det X=\tfrac14(t^2-\|w\|^2).
$$

正矩阵对应未来锥 $C=\{(t,w):t\ge\|w\|\}$，归一截面是 Bloch 球。这是四维*未归一化响应*几何；$t$ 是质量，不是物理时间。

**接入前的同一对象条件。**

C123/C124 新 §18 已把此四维锥作为前提。本轮可以先推导相容的数学球锥，但不能借新 §18 反向证明三维。加入成功词和可读旧档案后，扩充的全部未来仍由同一 $V$ 充分表示，须另核。新源还要求原可逆有限字的全部闭包恰为

$$
K=\{\operatorname{diag}(1,R):R\in SO(3)\}.
$$

本轮先允许 $O(3)$；只有原菜单本就取向保持，或同一完整参考合同已排除反射时，才接入这个 $K$，不能静默丢掉原反射。

### 定义 8.1（具名原双返回及指定比较群）

另已给两个合法原成功词 $S,U$，在同一整个 $V,C$ 上满足

$$
S(C),U(C)\subseteq C,\quad uS\le u,\quad uU\le u,\qquad
US=SU=qI,\quad 0<q<1.
$$

全部原成功率、失败支、细记录和合法性保留。预先指定

$$
\mathscr H=\overline{\langle\mathcal R,S,U\rangle}^{GL(V)},\qquad
\mathcal L=SO^+(1,3),
$$

其中 $\overline{\mathcal R}=K$。定义

$$
\lambda_S=|\det_\mathbb R S|^{1/4},\quad
\alpha=\frac{\log\lambda_S}{\log q},\quad
\chi=\operatorname{arcosh}\frac{u(Sc)}{\lambda_S}.
$$

这里用 $\lambda_S$ 区别原转向速度 $\lambda$。群中的数学逆和极限不自动成为原可调用词。

### 定理 8.2（C124 新定理 18.3 的分类）

在上述同一对象条件下，$\chi\ge0$，

$$
qe^\chi\le\lambda_S\le e^{-\chi},\qquad q\le e^{-2\chi},
$$

并且

<a id="eq-lorentz"></a>

$$
\boxed{
\mathscr H^\circ=
\begin{cases}
K,&\chi=0,\ \alpha\in\mathbb Q,\\
\mathbb R_{>0}K,&\chi=0,\ \alpha\notin\mathbb Q,\\
\mathcal L,&\chi>0,\ \alpha\in\mathbb Q,\\
\mathbb R_{>0}\mathcal L,&\chi>0,\ \alpha\notin\mathbb Q.
\end{cases}}
\tag{8.1}
$$

因此它在整个 $C^\circ$ 上传递，当且仅当 $\chi>0$ 且 $\alpha\notin\mathbb Q$。 [3](#ref-repo124)

**证明。**
双返回给 $S^{-1}=q^{-1}U\ge0$，故 $S$ 是锥序自同构。令 $\eta=\operatorname{diag}(1,-1,-1,-1)$。$S$ 保持全部零边界，因此

$$
(S(1,n))^{\mathsf T}\eta S(1,n)=0\qquad(\|n\|=1).
$$

将该二次型写为 $a+2b\cdot n+n^{\mathsf T}Mn$，比较 $n,-n$ 得 $b=0$，球面上常值给 $M=-aI$，内锥保持给 $a>0$。由行列式得

$$
S=\lambda_S L,\qquad L^{\mathsf T}\eta L=\eta,\quad LC=C,\qquad
U=(q/\lambda_S)L^{-1}.
$$

$Lc=(\cosh\chi,\sinh\chi\,n)$。在 $u(x)=1$ 的整个锥截面上，
$\max u(Lx)=\max u(L^{-1}x)=e^\chi$，两条质量界即给所述不等式。

若 $\chi>0$，写 $L=B_{\chi,n}\operatorname{diag}(1,R)$、$R\in O(3)$，其中 $B_{\chi,n}$ 为 boost。$R$ 正规化 $SO(3)$，所以

$$
SKS^{-1}=B_{\chi,n}KB_{\chi,n}^{-1}.
$$

两份连通旋转群都在 $\mathscr H^\circ$。取 $n=e_3$，令旋转生成元 $J_{13}$ 满足 $J_{13}e_3=e_1,J_{13}e_1=-e_3$，令 boost $B_1c=e_1,B_1e_1=c$，其余方向为零。矩阵乘法给

$$
\operatorname{Ad}_{B_{\chi,e_3}}J_{13}
=\cosh\chi\,J_{13}-\sinh\chi\,B_1.
$$

因此原两个旋转稳定子的 Lie 代数生成 $B_1$，再由 $K$ 共轭取得全部三个 boost。三旋转与三 boost 张成 $\mathfrak{so}(1,3)$，连通矩阵群的指数生成给 $\mathcal L\subseteq\mathscr H^\circ$。 [7](#ref-hall)

剩下判径向尺度。连续同态
$\ell(T)=\frac14\log|\det_\mathbb R T|$ 在生成元上的值属于
$\mathbb Z\log\lambda_S+\mathbb Z\log q$。当 $\alpha$ 有理时该子群离散，单位分支的 $\ell$ 为零，故非中心情形恰为 $\mathcal L$。

当 $\alpha$ 无理时，$qI=US\in\mathscr H$。即使 $L$ 反取向，$L^2\in\mathcal L$，所以
$\lambda_S^2I=S^2(L^2)^{-1}\in\mathscr H$。两个不可公度对数的整数线性组合在 $\mathbb R$ 稠密，闭包给全部正标量，故为 $\mathbb R_{>0}\mathcal L$。

若 $\chi=0$，则 $S=\lambda_S\operatorname{diag}(1,R)$，整个群在
$\mathbb R_{>0}\operatorname{diag}(1,O(3))$ 内。因 $R^2\in SO(3)$，有
$S^2\operatorname{diag}(1,R^{-2})=\lambda_S^2I$。同一离散或稠密尺度论证分别给 $K$ 或 $\mathbb R_{>0}K$。

最后，$\mathcal L$ 保持 $t^2-\|w\|^2$，只能在每个 $t^2-\|w\|^2=d>0$ 的未来双曲面上传递；加入正标量后才能连接任意两个内点。中心两种群保持 $\|w\|/t$，都不能在整个内锥上传递。

若允许 $q=1$，质量界迫使 $\chi=0,\lambda_S=1$，没有非中心解。增加其他可逆生成器会改变必要性判据。无理性需要准确参数证明，不是有限精度统计的稳健证书。

### 8.1 相同条件作用为何能给出不同大结构

源命题 19.2 的完整模型使用相同成功算子

$$
F=\operatorname{diag}(1,1/2),\qquad S(X)=FXF^*,
$$

并取

$$
R_q=\sqrt q\,\operatorname{diag}(1,2),\qquad U_q(X)=R_qXR_q^*,
\qquad q_1=\tfrac14,\quad q_2=\tfrac19.
$$

失败算子分别保留为

$$
C_F=\operatorname{diag}(0,\sqrt3/2),\qquad
D_q=\operatorname{diag}(\sqrt{1-q},\sqrt{1-4q}).
$$

各装置的成功、失败效果和为单位。$FR_q=R_qF=\sqrt q I$ 给准确全空间双返回。

直接计算得

$$
Sc=(5/8,0,0,3/8),\quad
\lambda_S=\tfrac12,\quad \chi=\log2.
$$

而

$$
\alpha_1=\tfrac12\in\mathbb Q,\qquad
\alpha_2=\frac{\log2}{2\log3}\notin\mathbb Q.
$$

后一无理性由素分解唯一性证明。因此一个群为 $\mathcal L$，另一个为 $\mathbb R_{>0}\mathcal L$，但两个成功词的条件作用相同，因为 $U_{q_2}=(q_2/q_1)U_{q_1}$。原成功率和失败效果不同。 [3](#ref-repo124)

这与本轮零关系形成准确分工：零关系不变于 $A\mapsto tA$、$t\ne0$，故不给钟速；成功条件化不变于正标量缩放，故不给原强度。二者都必须把被商掉的尺度留在原历史中。

在二维复矩阵完成中，可逆滤波 $X\mapsto FXF^*$ 除去
$|\det_\mathbb C F|$ 后给 proper Lorentz 作用，这是成熟的滤波几何。 [8](#ref-filter)
但新源 §20.1 只在原效果双空间、原自对偶比较和预先指定群身份核对后，并且 $\chi>0,\alpha\notin\mathbb Q$ 时，补上该局部对象的 G 子句。它不供应其他对象的 P/G/D、完整参考、AC、精确门或物理时钟。

<a id="section-9"></a>

## 9. 其余最新结果：同一对象、精确与逼近

<a id="sec-updates"></a>

### 9.1 FIB：同一精确秩二序列的全部联合逼近

FIB Appendix III 新定理 142.1–143.2 在其完整原端点、源、解析与时钟前件下，仍在原空间、原时刻 $2d,3d,4d$ 上工作，以 $\theta$ 汇总该源原参数。该文原空间记作 $G$，不是本文的量子控制群；下文把它记成 $\mathcal X$。令 $m$ 为其原概率测度，$P=T_d$、$g=g_{2d}$，原三时配对为

$$
\mathcal C(u,v,w)=\int_{\mathcal X}g\,u\,P(vPw)\,dm.
$$

固定该源定义 136.1 的实际粗分区 $E=(S,C,B)\in\mathscr E_\theta$，保留转动不变性及九条原边缘后，新定理 142.1 对任意有限
$\Psi\subset L^1(m;\mathbb R)$，给同一个全空间 Borel 奇号 $v$，满足

$$
v^2=\mathbf1_S,\quad v\circ R_\pi=-v\ \text{a.e.},\quad
\int\psi v\,dm=0\ (\psi\in\Psi),\quad
\int g\,v\,P((P\mathbf1_C)v)\,dm=0.
$$

证明将有限无原子向量测度分割与原正负二次型方向结合，保持所有有限矩，再用保持矩的连续换号路径获得零二次型。实际终端 $P\mathbf1_C$ 没有换成目标随机终端。 [4](#ref-repofib)

新定理 143.2 将它接成同一确定性共同分区序列 $D_n$，使每个成员满足全部十二条准确边缘和

$$
\operatorname{rank} A^{D_n}=2,
$$

同时对原随机目标 $f$ 有

$$
\mathbf1_{D_{n,y}}\overset{*}{\rightharpoonup}f_y,\qquad
\|\nu_{D_n}^{(3)}-\nu_f^{(3)}\|_{\rm TV}\longrightarrow0.
$$

后式覆盖全部 $4^3=64$ 个联合坐标；同一个 $D_n$ 用于三个原时刻，末标签始终消费实际 $P\mathbf1_{D_{n,w}}$。这是本轮真实增量，不能只概括成旧的“存在秩二分区”。

### 命题 9.1（为何仍不等于一份精确实现）

该构造的 $B$ 分量满足

$$
\mathbf1_{D_{n,B}}\overset{*}{\rightharpoonup}\tfrac14,\qquad
\left\|\mathbf1_{D_{n,B}}-\tfrac14\right\|_1\longrightarrow\tfrac38.
$$

因此该分量无 $L^1$ 收敛子列。

**证明。**
对常数测试得 $m(D_{n,B})\to1/4$。每个指示函数都有

$$
\|\mathbf1_D-\tfrac14\|_1=\tfrac14+\tfrac12m(D).
$$

若有 $L^1$ 收敛子列，其极限由弱极限唯一性必须为 $1/4$，与距离趋 $3/8$ 矛盾。

源 §144 因此只结算准确边缘且准确秩二类上的联合误差下确界为零；没有结算某一个 $D$ 精确达到全部 64 条、$A^D=A^f$ 或普遍 $F_{64}$。非紧也不证明另一份精确实现不存在。原生源／演化／读出桥仍待建立。 [4](#ref-repofib)

这与本轮的有限零核证书相接：不能用已见坐标的任意好逼近，认证全部原未来上的精确零关系。FIB 的秩二与本文内容三维是不同载体上的命题。

### 9.2 Four-path：严格谱排除不等于全局最优闭合

Four-path II 新 §44 保留原 $\operatorname{Dens}_2\times U(4)$、两个优化器符号、普通转置及同一个实际共享反馈。其证书基中的效果写为

$$
F=\begin{pmatrix}p&z\\\bar z&1-p\end{pmatrix},\qquad
\epsilon=2\det F,\quad H=\operatorname{diag}(d^2,e^2),\quad d,e>0.
$$

在固定同一实际反馈下，源证明给出行 $a$ 满足 $a^*a\le H$。令

$$
C=H^{1/2}FH^{1/2},\qquad b=aH^{-1/2},\qquad
g_{\rm def}=\operatorname{Tr} C-bCb^*.
$$

于是 $\|b\|\le1$，直接得到

$$
g_{\rm def}\ge\lambda_{\min}(C)
=\frac{D(p)-\sqrt{D(p)^2-2d^2e^2\epsilon}}2,
\qquad D(p)=d^2p+e^2(1-p).
$$

此处 $g_{\rm def}$ 是该源缺陷，不是本文群元素。源还给出该下界的完整实际饱和集；令 $\xi=\rho(E,U)$ 为原联合距离，并保留原 $\kappa$ 及 $f(E,U)=g_{\rm def}-\kappa\xi$。使用其既有数值参数，对

$$
0<\xi\le13/4,\qquad
\epsilon\ge \frac p2+\frac{e^2}{d^2}\left(\frac38-\frac p2\right)
$$

得到 $f(E,U)-N_{\rm geo}(\xi)>3/16$。这筛除了一批可能竞争者，却未求出原约束层级的全部最优包络、精确阈值或所有相位等号集。 [5](#ref-repofour)

以上源定理均不补出本候选的存在性；本轮未把来源登记算作 Lean 证明，也没有使用不同反馈替代原共享反馈。

<a id="section-10"></a>

## 10. 内生性、简化账本与理论范围

<a id="sec-boundary"></a>

| 层次 | 原定义或明确条件 | 结论 |
|---|---|---|
| 原预测窗口 | 单源全部未来、未知有限容量、准确统计逆 | 原 $W,e,G,\mathfrak g$，紧性、循环性 |
| 内部比较 | 原轨道协方差及其逆 | 唯一规定的正比较 $B$，不增加外来尺 |
| 唯一候选 | 非零原转向的二元零响应等于同面关系 | 原内容三维，原旋转完整，原准备静止 |
| 关系完成 | 三维响应及最小结合闭包 | 面积、Jordan–Lie、中心复数与 $\mathbb C^2$ |
| 原概率 | 原事件线性与概率界 | 数值不变的 Born 表示及完整 POVM |
| 复合与参考 | 共同复中心与交换张成；足够大的实际完整矩阵参考，同一分支在完整联合正锥保正 | 复张量、CP/Kraus，同一原控制族不含反射 |
| 理想更新与时间 | 支撑内全部态不扰动；连续 CPTP 群及 CP 逆 | Lüders、幺正演化形式 |
| 实际供应 | 原联合 P/G/D、指针 AC、精确控制、记录和连线 | C124 既有有限端点；不自动供应任意完成 |
| 原过滤尺度 | 扩充后同一全未来四维、同锥双返回、预先指定群 | 新 C124 Lorentz 分类与径向判据 |

**本轮的压缩有明确比较对象。**

从上一轮的“存在静止转向，其全部横向内容不可约”，改成一个二元零关系同一式。不变子空间的量化、商空间与谱分解不再进入核心证明；静止性也由关系本身推出。比较尺改由原轨道定义，控制代数由 $A,X,[A,X]$ 三份关系恢复。没有增加一份自由响应 $D$。

两轮在同一前端和同一见证上等价，故不宣称逻辑更弱或全局最小。线性相关仍是实质选择条件。它明确给出为何只有三维，不能因为改称“同面”就声称不存在选择。

**公理内生的精确位置。**

原内容、原参照、原转向、原比较，以及“能否由两个已有方向拼出”的关系，都已在同一 $\Omega$ 内定义。本轮候选锁定的是这两种定义关系的同一：

$$
\text{比较响应为零}\quad=\quad\text{没有增加第三个线性方向}.
$$

但“所有对象属于 $\Omega$”不蕴含“$\Omega$ 内一定存在这样的窗口”；五维完整预测反模型说明选择有内容。可以把满足它的窗口定义为本理论的初等块。证明自然界或指定原来源供应这种块，仍需更早的整体存在性论证。

**完成范围。**

有限状态、测量、过程、复合、理想更新和连续可逆演化的数学理论已经在明列接口下闭合。无限维场、正则对易表示、具体相互作用、原物理钟速和 $\hbar$ 没有同时被推导。零关系不等于零概率；三维不等于物理时空维数；Haar 定义、数学闭包与实际精确供应也各有对象。

本轮没有构造 $\zeta$ 零点与原二元响应之间的保真映射。二者都出现“零”并不构成连接，因此没有离临界线零点判据或黎曼猜想结论。

## 一段白话完整描述本轮候选

把整体自己给出的当前准备画成从中心伸出的一根参照箭头，再拿两份能被未来读数区别的内容，也从这个中心画成箭头。整体里有一种真实关系所给出的转向；我们只要求：一份内容对另一份内容的转向完全没有响应，恰好就是这三根箭头能放在同一个平面里。这样，参照自己必然不动。拿出一根会被转动的箭头，它和参照张成的平面容纳了全部无响应内容；把它被转出的方向补上，就容纳了整个窗口，不再剩第四个独立方向。三维、面积和平方关系因此一起出现。原来源还给出自己的比较尺，原转向给出左右手；把这些关系接成可结合的乘法，就得到复数、两分量振幅和球面上的 Born 概率。再按明确的复合、参考和过程条件连接这些块，就是有限量子理论。转得多快、成功多少次，仍是原历史中的数值；不能因为只画了方向、只看了成功后的状态，就把这些尺度和未来会返回的记忆擦掉。

<a id="references"></a>

## 参考文献

<a id="ref-repocompare"></a>

### [1]

 The Omega Institute, *trureturing*，固定提交 `7c2b901642e29adbf2907b53d6a5f7db831e7df1`。本轮比较：[https://github.com/the-omega-institute/trureturing/compare/2d80e2d87f58d687ee660169fbeb4b8f07f2e1f5...7c2b901642e29adbf2907b53d6a5f7db831e7df1](https://github.com/the-omega-institute/trureturing/compare/2d80e2d87f58d687ee660169fbeb4b8f07f2e1f5...7c2b901642e29adbf2907b53d6a5f7db831e7df1)。

<a id="ref-repo117"></a>

### [2]

 同仓库，*Common Source Self Reference and Observer Sequences C117*，§16，本轮未变。[https://github.com/the-omega-institute/trureturing/blob/7c2b901642e29adbf2907b53d6a5f7db831e7df1/docs/develop/theory/AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md](https://github.com/the-omega-institute/trureturing/blob/7c2b901642e29adbf2907b53d6a5f7db831e7df1/docs/develop/theory/AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md)。

<a id="ref-repo124"></a>

### [3]

 同仓库，*Native Reciprocal Comparison and Finite Endpoint Quantum C123*；C124 既有 §§10–17，本轮新增 §§18–20。[https://github.com/the-omega-institute/trureturing/blob/7c2b901642e29adbf2907b53d6a5f7db831e7df1/docs/develop/theory/AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md](https://github.com/the-omega-institute/trureturing/blob/7c2b901642e29adbf2907b53d6a5f7db831e7df1/docs/develop/theory/AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md)。

<a id="ref-repofib"></a>

### [4]

 同仓库，*FIB Atom Recursive Holographic Boundary Geometry, Appendix III*，新增 §§142–144。[https://github.com/the-omega-institute/trureturing/blob/7c2b901642e29adbf2907b53d6a5f7db831e7df1/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_III.md](https://github.com/the-omega-institute/trureturing/blob/7c2b901642e29adbf2907b53d6a5f7db831e7df1/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_III.md)。

<a id="ref-repofour"></a>

### [5]

 同仓库，*Quantum Reality Four Path Full Record Recovery Bound, Continuation II*，新增 §44。[https://github.com/the-omega-institute/trureturing/blob/7c2b901642e29adbf2907b53d6a5f7db831e7df1/docs/develop/theory/QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_II.md](https://github.com/the-omega-institute/trureturing/blob/7c2b901642e29adbf2907b53d6a5f7db831e7df1/docs/develop/theory/QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_II.md)。

<a id="ref-watrous"></a>

### [6]

 John Watrous, *The Theory of Quantum Information*, 2018，第 2 章，尤其定理 2.22。[https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)。

<a id="ref-hall"></a>

### [7]

 Brian C. Hall, *An Elementary Introduction to Groups and Representations*, 2000，矩阵 Lie 群、局部指数及连通群生成。[https://arxiv.org/abs/math-ph/0005032](https://arxiv.org/abs/math-ph/0005032)。

<a id="ref-filter"></a>

### [8]

 F. Verstraete, J. Dehaene, B. De Moor, *Local filtering operations on two qubits*, Phys. Rev. A 64, 010101(R), 2001。[https://arxiv.org/abs/quant-ph/0011111](https://arxiv.org/abs/quant-ph/0011111)。

<a id="ref-previous"></a>

### [9]

 本会话 $\Omega Q$-004，*静止转向不可拆*，2026-11-04。[https://chatgpt.com/library?file_id=libfile_086c7591c64c8191b7c2a550d4470cad&account_id=personal](https://chatgpt.com/library?file_id=libfile_086c7591c64c8191b7c2a550d4470cad&account_id=personal)。
