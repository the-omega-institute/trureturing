**QUANTUM ORIGINS / $\Omega Q$-004**

# 静止转向不可拆

**保持当前准备不变的一种转向，不能让其余内容各转各的**

一个更短的候选：原关系、反例、三维提升与有限量子理论

当前参照直接取原初始准备的中心化预测行 $e=x_\epsilon-c$。不另外选内容试针，不预给响应映射，不要求先构造一张内容–控制对应图。

$$
\boxed{\exists A\in\mathfrak g\setminus\{0\}:\quad
Ae=0,\qquad \overline A\text{ 在 }W/\mathbb R e\text{ 上实不可约}.}
$$

$Ae=0$ 表示当前准备看不出这份转向；不可约表示其余*全部原内容*不能拆成两套互不来往的变化。一个方向与它被转动的方向构成平面；新条件迫使这就是全部横向内容，加上原参照轴，恰好三维。

 本会话新系列第四篇，承接 $\Omega Q$-003。

稿件日期：2026-11-04，Asia/Singapore。

固定项目版本：`dev@2d80e2d87f58d687ee660169fbeb4b8f07f2e1f5`。

提交时间：2026-11-03 21:42:36 UTC；新加坡时间 11 月 4 日 05:42:36。

范围：有限维条件重建与普通数学证明；未修改仓库，未作 Lean 认证。

本轮减少原始供应和关系检查；不声称逻辑上严格更弱、全局最少或已证明自然界必须满足该条件。

上一轮 $\Omega Q$-003 用

$$
\Xi_{A,e}:\mathfrak g/\mathbb R A\longrightarrow W/\mathbb R e,
\qquad [X]\longmapsto [[A,X]e]
$$

的同构要求锁定三维，并恢复 $D$。本轮把它替换为**一个原转向在全部横向内容上的不可分性**。参照 $e$ 不再另外选择，直接来自原初始准备；候选只消费一次二元作用 $(A,y)\mapsto Ay$，无需先比较全部控制交换子与内容的维数。

新的证明顺序也更短：先由一个实旋转平面推出原内容三维，再由单源循环性推出原控制代数为 $\mathfrak{so}(3)$。无需上一轮的最大频率升降、四元数余项及 Jacobi 排维论证。旧 $\Xi$ 成为本轮定理的结论。

**完整结果。**同一原预测前端加本轮唯一候选，推出

$$
\dim W=3,\qquad \dim V=4,\qquad
\mathfrak g=\mathfrak{so}(W),\qquad G^\circ=SO(3).
$$

由原准备定单位、由原转向定取向后，响应 $D$、面积、横向复线、中心复数、$M_2(\mathbb C)$、球面与 Born 配对均可重建。复合、参考正性、理想更新、时间及实际供应的接口仍分别明写。

<a id="section-1"></a>

## 1. 本轮项目新增：活动记忆不能被单次读数抹掉

<a id="sec-repo"></a>

相对上一轮固定提交 `0d2719a1091903642f361f04994da098acd20e22`，本轮固定比较含 38 个提交、119 个改变路径。相关理论正文唯一变化是 C113 新增 §§25–27，共 405 行。C117、C122、C123/C124、C115、V95、V96 continuation、FIB Appendix III 与 Four-path continuation II 均逐字未变。 [1](#ref-repohead)、[2](#ref-repo113)

**新定理做了什么。**

C113 在同一个完整原联合 CP 仪器、全部保留记忆 $M$、忠实乘积校准 $\tau\ge\lambda I$、全部原记录的单 Kraus 目标及效果线性独立等前件下，从系统校准误差推出完整联合仪器的 diamond 预算，再得到已供应的 $N$ 次完整协议误差界。第 [9](#sec-memory) 节给出精确情形证明及正误差公式。

**新反例为何影响本轮起点。**

同一个固定装置可以第一次对系统表现为恒等，第二次却出现相位翻转；原因是第一次准备没有覆盖会在以后返回的内部记忆方向。另一个反例中，单次全部原记录的边缘校准都精确，但连续记录仍有隐藏相关。**原内容必须按全部合法未来区别定义，不能拿一次平均读数来代替。**

这些新结果已经假定复 Hilbert 空间与原联合 CP 仪器，不是量子起源的新证明，也不删除 C123/C124 的原比较、响应和供应条件。本轮继续简化的是更早的初等关系入口；不把新校准定理当成它的前提替代品。

<a id="section-2"></a>

## 2. 原定义：内容来自未来，转向来自接续

<a id="sec-front"></a>

### 定义 2.1（同一原来源的预测窗口）

在同一 $\Omega$ 中取一个原归一准备。令 $\mathcal L$ 为从它出发的总可逆控制词，含空词，封闭于接续，并含每个词在同菜单内的准确统计逆。令 $\mathcal F$ 为共同的全部合法未来域，保留全部终端标签，包括失败。原概率满足

$$
p(a;f,w)\ge0,\qquad \sum_w p(a;f,w)=1,
\qquad p(ag;f,w)=p(a;gf,w).
$$

定义

$$
x_a(f,w)=p(a;f,w),\qquad
V=\operatorname{span}_\mathbb R\{x_a\},\qquad \dim V<\infty.
$$

归一化泛函 $u$ 满足 $u(x_a)=1$。原内容差空间为

$$
W=\ker u=\operatorname{span}\{x_a-x_b\}.
$$

维数未知，不输入三维、容量四或复数振幅。

### 引理 2.2（紧性与原源的循环性）

接续 $T_gx_a=x_{ag}$ 在 $V$ 上良定义，其双边可逆群闭包 $H$ 紧。存在 $H$ 固定的 $c$，$u(c)=1$，使

$$
V=\mathbb R c\oplus W.
$$

令 $G=H|_W$、$\mathfrak g=\operatorname{Lie} G$，则 $G$ 忠实且保某个正定型 $B_0$。原参照

<a id="eq-source"></a>

$$
\boxed{e:=x_\epsilon-c}
\tag{1}
$$

满足

$$
\boxed{W=\operatorname{span}(G e).}
$$

**证明。**
原行的线性关系在全部未来为零，故在所有以 $g$ 开头的未来也为零，所以接续良定义。有限维允许选有限分离终端坐标及实际行基。所有接续后基行的这些坐标仍在 $[0,1]$，故全部 $T_g$ 一致有界；原统计逆给逆的一致有界，矩阵闭包因此紧且不含奇异矩阵。

对原行作 Haar 平均得 $c$，对任意正定型作群平均得 $B_0$。作用在 $W$ 上恒等且固定 $c$ 的元素在 $V$ 上也恒等，所以限制忠实。每个中心化行为 $x_a-c=T_a e$。这些行张成 $W$：它们在 $W$ 内，而所有 $x_a-x_b$ 都在它们的张成内。有限维取闭包不改变张成，故 $W=\operatorname{span}(G e)$。

这沿用 C117 全未来入口的一般部分，不沿用后续容量四输入。 [3](#ref-repo117) 群闭包及其 Lie 生成元用来定义和证明；“其中每个指数都已有精确有限门实现”并不是此引理的结论。

### 定义 2.3（原准备的静止转向）

设

$$
\mathfrak h_e=\{X\in\mathfrak g:Xe=0\}.
$$

它由原作用定义，是原准备的稳定子 Lie 代数。对 $A\in\mathfrak h_e$，$e^{tA}e=e$：当前准备的全部原未来概率保持不变，但别的准备仍可变化。取

$$
Q=W/\mathbb R e,
$$

$A$ 在其上诱导 $\overline A[y]=[Ay]$。这是良定义的原二元作用，不另供响应表。

<a id="section-3"></a>

## 3. 先反向检验：一条不动轴仍可藏着两套变化

<a id="sec-counter"></a>

### 例 3.1（五维原内容中的两套旋转）

取实三维单位向量 $v$，准备 $\rho_v=vv^{\mathsf T}$，原控制为全部 $R\in SO(3)$，原完整测试为

$$
p_i(R,v)=|(Rv)_i|^2,\qquad i=1,2,3.
$$

全部未来效果分离 $\operatorname{Sym}(3,\mathbb R)$，所以

$$
\dim V=6,\qquad W=\operatorname{Sym}_0(3,\mathbb R),\qquad\dim W=5.
$$

以 $v=e_3$ 为原源，$c=I/3$、$e=e_3e_3^{\mathsf T}-I/3$。绕第三轴的非零转向 $A$ 保持 $e$，且在整个 $W$ 上只有 $\mathbb R e$ 一条不动轴。

但横向内容分成两个不变平面：

$$
U_1=\operatorname{span}\{E_{13}+E_{31},\ E_{23}+E_{32}\},
$$

$$
U_2=\operatorname{span}\{E_{11}-E_{22},\ E_{12}+E_{21}\}.
$$

$U_1$ 按原角频率转动，$U_2$ 按两倍频率转动。原稳定子就是这条轴旋转，所以每个非零静止转向都有上述分解；不是仅挑到了一份不合格见证。

这些方向都能被原终端概率区别。不能只留下第一片，再称原内容已成二维横向平面。这不是一般高维量子系统矛盾，而是它不属于本候选识别的初等窗口。

**非零条件也必要。**

取 $W=\mathbb R^2$、$G=SO(2)$，以 $e=e_1$ 为原源，并配完整读数
$p(\pm|n,r)=(1\pm n\cdot r)/2$。取 $A=0$，则 $Ae=0$，一维商 $W/\mathbb R e$ 上的零作用仍不可约。若不排除零转向，会把这种圆盘窗口纳入三维结论。

**保持参照是类型条件。**

同一二维模型的非零旋转 $A$ 在整个 $W$ 上不可约，却有 $Ae\notin\mathbb R e$。此时 $[e]=0$ 而 $[Ae]\ne0$，商上的 $\overline A$ 根本不良定义。因此不能删去 $Ae=0$ 后继续使用同一个商作用。

**完整前端也不能被省掉。**

若取 $GL_2^+(\mathbb R)$ 标准作用、$e=e_1$、$A=\operatorname{diag}(0,1)$，则 $Ae=0$、$A\ne0$，一维商上的非零作用不可约，却不是三维。这个非紧轨道无界，不能具有分离它且处处落在 $[0,1]$ 的全部原线性概率。它说明紧预测前端有实质作用，不能保留该前端全部前件却假装删掉其紧性结论。

<a id="section-4"></a>

## 4. 本轮唯一候选：静止转向不可拆

<a id="sec-axiom"></a>

**候选 $\Omega Q$-004。**参照 $e$ 固定为式 [(1)](#eq-source) 的原源差。要求存在原 $A\in\mathfrak g\setminus\{0\}$，使

<a id="eq-axiom"></a>

$$
\boxed{Ae=0,\qquad
\overline A:W/\mathbb R e\longrightarrow W/\mathbb R e
\text{ 的实作用不可约}.}
\tag{2}
$$

不可约的意思严格限定为：商空间非零，并且只有零空间与全空间两个不变实子空间。等价地，对任何原线性内容片 $L$，

$$
\mathbb R e\subseteq L\subseteq W,\quad A L\subseteq L
\quad\Longrightarrow\quad L=\mathbb R e\ \text{或}\ L=W.
$$

这是同一个候选的展开，不是另外一条公理。它要求*全部原横向内容*不可拆，不能先挑选一个方便的旋转平面。

受比较的两个元是原转向 $A$ 与原内容差 $y$，二元关系为 $Ay$。$A$ 是从原 Lie 代数中取的存在见证，并非从外面加入的新门。原稳定子整体无需预先假定交换，也无需检查全部两两控制关系。

### 4.1 不遍历无限子空间的有限证书

取 $U=e^{\perp_{B_0}}$，它自然表示 $Q$，且被 $A$ 保持。记 $A_0=A|_U$。令 $\operatorname{Sym}_0(U)$ 为对 $B_0$ 自伴且迹零的实算子空间，定义

$$
\Gamma_A(S)=[A_0,S]=A_0S-SA_0.
$$

结果仍自伴且迹零。

### 命题 4.1（有限线性检验）

在原 $A\ne0$、$Ae=0$ 下，候选的不可约条件等价于

$$
\boxed{\ker\Gamma_A=0.}
$$

**证明。**
若 $0\ne L\ne U$ 为 $A_0$ 不变片，斜对称性使 $L^\perp$ 也不变。其正交投影 $P_L$ 与 $A_0$ 可交换，故
$S=P_L-(\dim L/\dim U)I$ 是非零核元。反向，非零自伴无迹核元 $S$ 必非标量，它的真谱空间给出 $A_0$ 不变片。

因此只需在已识别的原有限空间内，求解一组线性交换方程。它仍以原容量、原生成元资格及共同未来域为前件，不从有限采样认证这些无限量词。

<a id="section-5"></a>

## 5. 三维有限提升：这次只需要一个旋转平面

<a id="sec-proof"></a>

### 引理 5.1（不可拆的实斜对称作用只有一个平面）

非零斜对称实算子 $T$ 若在有限维实空间 $U$ 上不可约，则

$$
\dim U=2,\qquad T^2=-\lambda^2I_U\quad(\lambda>0).
$$

**证明。**
$-T^2=T^*T$ 为非零正半定算子，取正特征值 $\lambda^2$ 的单位特征向量 $y$。令 $z=Ty/\lambda$。则 $y,z$ 正交归一，且

$$
Ty=\lambda z,\qquad Tz=-\lambda y.
$$

所以 $\operatorname{span}\{y,z\}$ 是非零不变平面。不可约迫使它就是整个 $U$。

### 定理 5.2（原内容与原控制同时重建）

在第 [2](#sec-front) 节前端及候选 [(2)](#eq-axiom) 下，

$$
\boxed{\dim W=3,\quad\dim V=4,\quad
\mathfrak g=\mathfrak{so}(W,B_0),\quad G^\circ=SO(3).}
$$

完整群只能是 $SO(3)$ 或 $O(3)$。

**证明。**
$e=0$ 会由原循环性 $W=\operatorname{span}(G e)$ 导致 $W=0$，与原 $A\ne0$ 矛盾，故 $e\ne0$。$Ae=0$ 与斜对称性使 $U=e^\perp$ 不变。$A|_U\ne0$，否则 $A$ 在整个 $W=\mathbb R e\oplus U$ 上为零。商不可约等价于 $U$ 不可约；上引理给 $\dim U=2$，所以 $\dim W=3$。

还必须证明原群能移动参照，不能从三维载体直接跳到全部三维旋转。令

$$
T_e=\{Xe:X\in\mathfrak g\}\subseteq U.
$$

若 $T_e=0$，则对每个 $g\in G$、$X\in\mathfrak g$，

$$
X(ge)=g(\operatorname{Ad}_{g^{-1}}X)e=0.
$$

$\mathfrak g$ 在全群共轭下保持，原 $Ge$ 又张成 $W$，故每个 $X$ 为零，矛盾。这里不要求 $G$ 连通。

另外，$A(Xe)=[A,X]e\in T_e$，所以 $T_e$ 是非零 $A|_U$ 不变片。不可约给 $T_e=U$。稳定子 $\mathfrak h_e$ 由固定 $e$ 的斜对称算子组成，嵌入一维 $\mathfrak{so}(U)$，且含非零 $A$，故 $\dim\mathfrak h_e=1$。由 $X\mapsto Xe$ 的核与像，

$$
\dim\mathfrak g=\dim\mathfrak h_e+\dim U=1+2=3.
$$

因此 $\mathfrak g\subseteq\mathfrak{so}(W,B_0)$ 两侧同维，必相等。群结论随之成立。

```latex
\begin{tikzpicture}[>=Latex,scale=1.05,every node/.style={font=\small}]
\fill[pale] plot[domain=0:360,samples=100,variable=\t]
({2.3*cos(\t)-1.15*sin(\t)},{0.15*cos(\t)-0.75*sin(\t)}) -- cycle;
\draw[accent,thick] plot[domain=0:360,samples=100,variable=\t]
({2.3*cos(\t)-1.15*sin(\t)},{0.15*cos(\t)-0.75*sin(\t)});
\draw[->,thick,ink] (0,-1.0)--(0,2.35) node[above] {$e$：原准备的参照轴};
\draw[->,thick,ink] (0,0)--(2.3,0.15) node[right] {$y$};
\draw[->,thick,ink] (0,0)--(-1.15,-0.75) node[below left] {$Ay/\lambda$};
\draw[->,very thick,accent] plot[domain=0:75,samples=35,variable=\t]
({2.3*cos(\t)-1.15*sin(\t)},{0.15*cos(\t)-0.75*sin(\t)});
\node[text=accent] at (2.0,1.0) {$A$：保持 $e$，转动其余差别};
\node[align=center] at (0,-1.65) {不可拆迫使这一个平面就是全部横向内容。\\图中椭圆仅是圆的平面投影。};
\end{tikzpicture}
```

**单源条件为何不能消失。**

若任意规定 $W=\mathbb R^3$、只允许绕 $e$ 的 $SO(2)$ 控制，候选在这个人为载体上成立，但原群并非 $SO(3)$。它的 $e$ 轨道只有一点，不能张成 $W$。本轮使用的循环性来自同一原准备生成全部所选行，不是后来添加的群完备性公理。

### 5.1 上一轮的对应图现在是定理

由上证，$\mathfrak h_e=\mathbb R A$、$\mathfrak g e=U$，且 $A|_U$ 可逆。因此

$$
\Xi_{A,e}([X])=[[A,X]e]=[A(Xe)]
$$

是

$$
\mathfrak g/\mathbb R A\xrightarrow{[X]\mapsto Xe}U
\xrightarrow{A|_U}U\cong W/\mathbb R e
$$

三个同构的复合。**旧的一一对应要求已被推导，不再独立检查。**

反向，上一轮主定理已从 $\Xi$ 推出 $G^\circ=SO(3)$、$\dim W=3$。对本轮固定的原 $e\ne0$，选绕它的非零原生成元，就满足本轮候选。因此在同一前端上两轮选择相同模型类；旧刚性定理仅用于这项版本比较，本轮重建证明本身不依赖它。 [5](#ref-previous)

<a id="section-6"></a>

## 6. 从一个原转向恢复比较、响应与复数

<a id="sec-recover"></a>

### 6.1 原源定单位，原转向定取向

设

$$
B(x,y)=\frac{B_0(x,y)}{B_0(e,e)},\qquad B(e,e)=1.
$$

主定理后，所有 $G$ 不变正定型只差正比例：两个型之比对应的自伴算子与全部 $SO(3)$ 旋转可交换，故为标量。这个归一化消掉辅助型的选择，$B$ 由原作用与原源确定。

由二维引理，$A^2|_U=-\lambda^2I$，其中

$$
\lambda^2=-\tfrac12\operatorname{Tr}_W(A^2)>0.
$$

令

$$
J_e=A/\lambda.
$$

则

$$
J_e e=0,\qquad J_e^2=-P_U.
$$

所以 $\mathbb R[J_e|_U]\cong\mathbb C$，原横向平面自然成为一条复线。**这是横向内容的复结构；它还不是振幅 Hilbert 空间。**奇维 $W$ 上的 $J_e$ 不可能是全局复单位，后面须区别于中心元 $J$。

### 定义 6.1（由同一转向恢复全部二元响应）

将 $x=\alpha e+u$、$y=\beta e+v$，其中 $u,v\in U$，定义

<a id="eq-D"></a>

$$
\boxed{D_xy=\alpha J_ev-\beta J_eu+B(J_eu,v)e.}
\tag{3}
$$

### 定理 6.2（响应与面积）

$D_x\in\mathfrak g$，并且

$$
D_e=J_e,\qquad D_xx=0,\qquad
-\tfrac12\operatorname{Tr}_W(D_xD_y)=B(x,y).
$$

令 $[x,y]_W=D_xy$，则它反对称、满足 Jacobi，且

$$
\begin{aligned}
B([x,y]_W,[x,y]_W)&=B(x,x)B(y,y)-B(x,y)^2,
\end{aligned}
\tag{4}
$$

$$
\begin{aligned}
D_xD_yz&=B(x,z)y-B(x,y)z.
\end{aligned}
\tag{5}
$$

对 $g\in G^\circ$，$D_{gx}=gD_xg^{-1}$；对全 $O(3)$ 则有取向扭转 $D_{gx}=\det(g)gD_xg^{-1}$。

**证明。**
选任意 $B$ 单位 $p\in U$，令 $q=J_ep$。则 $e,p,q$ 正交归一，式 [(3)](#eq-D) 给

$$
D_ep=q,\qquad D_pq=e,\qquad D_qe=p.
$$

故它就是这个有向正交基下的三维叉积。其算子斜对称，因 $\mathfrak g=\mathfrak{so}(W,B)$ 属于原控制代数。迹、面积、三重积及共同运输由这些基关系双线性验证。

实际原生成元仍为 $A=\lambda D_e$，其速度没有丢失。把 $A$ 乘正数不改变归一响应，把它反号会反转取向。原无向概率没有自然选出 $A$ 与 $-A$ 中的一个；这是内部见证的取向自由，不是从几何算出了物理时间或 $\hbar$。

### 6.2 更大结构：Jordan–Lie 的相容与结合闭包

在 $\mathbb R1\oplus W$ 上定义

$$
(\alpha,x)\circ(\beta,y)
=(\alpha\beta+B(x,y),\alpha y+\beta x).
$$

令 $L_ab=a\circ b$，并把 $D$ 在单位方向上延为零。三重积直接给

$$
\boxed{[L_a,L_b]+[D_a,D_b]=0,\qquad [D_a,L_b]=L_{D_ab}.}
$$

第一式是对称比较与有向响应的顺序差相消，第二式说响应运输整个对称关系。这些关系均为本轮候选的结论。

定义最小实含幺结合闭包

$$
xy+yx=2B(x,y)1,\qquad x^*=x.
$$

它是 $\operatorname{Cl}_{3,0}$。用响应正向基 $(e,p,q)$，定义中心体积元

$$
\boxed{J=epq.}
$$

生成关系给

$$
J^2=-1,\qquad J^*=-J,\qquad Jx=xJ,
\qquad xy=B(x,y)1+JD_xy.
$$

这个 $J$ 是结合代数的中心复单位，与横向算子 $J_e$ 类型不同。

### 定理 6.3（复二维振幅表示）

$$
\operatorname{Cl}_{3,0}\cong M_2(\mathbb C_J),\qquad
\mathcal H=\mathcal A\frac{1+e}{2}\cong\mathbb C_J^2.
$$

**证明。**
反交换关系把任意词约到八个实基词。将 $(p,q,e)$ 送到

$$
\sigma_1=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
\sigma_2=\begin{pmatrix}0&-J\\J&0\end{pmatrix},\quad
\sigma_3=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
$$

这些矩阵满足生成关系，八个像实线性独立且张成全部 $M_2(\mathbb C_J)$。因此为同构。置 $p_+=(1+e)/2$，最小左理想以 $p_+,pp_+$ 为复基；由
$\xi^*\eta=\langle \xi,\eta\rangle p_+$ 定内积，其范数平方为 $|z_1|^2+|z_2|^2$。

结合闭包是明确的数学完成定义。它不把所有代数元素自动提升为原实际门，也没有从一个横向复一维空间直接跳称振幅已经二维。

<a id="section-7"></a>

## 7. 简单几何与原 Born 概率

<a id="sec-born"></a>

原 $e$ 已归一化为 $B(e,e)=1$。由 $G^\circ=SO(3)$，原准备轨道的闭包为 $c+S^2$，其最小闭凸完成为

$$
S_{\min}=c+\overline B^3.
$$

相应正锥为 $\{tc+w:t\ge0,\ \lVert w\rVert_B\le t\}$，即四维 Lorentz 锥。

### 定理 7.1（保持原数值的 Born 表示）

设 $S(w)=\sum_iw_i\sigma_i$。定义

$$
\rho_w=\frac{I+S(w)}2,\qquad \lVert w\rVert_B\le1.
$$

每个原未来事件 $f$ 都有唯一效果 $0\le E_f\le I$，满足

$$
\boxed{f(c+w)=\operatorname{Tr}(\rho_wE_f).}
$$

完整测试仍保全部成功和失败标签，并满足 $\sum_jE_j=I$。

**证明。**
$S(w)^2=\lVert w\rVert^2 I$，所以 $\rho_w\ge0$、$\operatorname{Tr}\rho_w=1$。原事件是行空间上的线性泛函，可写
$f(tc+w)=\alpha t+B(b,w)$。它在原轨道取值于 $[0,1]$，由闭包和凸性得
$\lVert b\rVert\le\min(\alpha,1-\alpha)$。因此 $E_f=\alpha I+S(b)$ 为效果，迹计算保持原配对。完整性由原泛函求和为 $u$ 得到。

对球面方向 $n,m$，其秩一投影为 $P_n=(I+n\cdot\sigma)/2$，故

$$
\operatorname{Tr}(P_nP_m)=\frac{1+n\cdot m}{2}
=\cos^2\frac{\theta(n,m)}2
=|\langle \psi_n,\psi_m\rangle|^2.
$$

于是纯态为复射线，归一振幅及其相位纤维为

$$
\boxed{S^1\longrightarrow S^3\longrightarrow S^2\cong\mathbb{CP}^1.}
$$

映射明确为

$$
(z_1,z_2)\longmapsto
(2\operatorname{Re}\overline z_1z_2,\ 2\operatorname{Im}\overline z_1z_2,\ |z_1|^2-|z_2|^2),
\quad |z_1|^2+|z_2|^2=1.
$$

$U_n(\theta)=\exp(-J\theta S(n)/2)$ 的共轭给内容旋转；振幅的 $2\pi$ 变号、$4\pi$ 复原是双覆盖的结果。原稳定子在横向平面上的圆转动与 Hopf 相位纤维通过这一半角提升相接，不能在证明前把两者直接当成同一个对象。

**几何与供应的区别。**

三维是所选可区分内容的维数，不是物理空间维数结论。最小闭凸完成中的纯态不自动成为更大 $\Omega$ 中全局纯态。若原效果仅有 $(I\pm\eta n\cdot\sigma)/2$、$0<\eta<1$，仍能满足候选并区分全部方向，却没有精确锐读口。闭包中的准备、门与数学角，也不自动有精确有限实现。

<a id="section-8"></a>

## 8. 完整有限维量子理论：定义、定理与接口

<a id="sec-full"></a>

以下发展本候选的有限数学完成，并逐项保留实际实例化条件。它复用的普通矩阵理论可对照 Watrous 第 2 章；需要的证明在此给出。 [6](#ref-watrous)

### 8.1 状态、测量与复合

### 命题 8.1（复合代数）

若两个已得块 $M_m(\mathbb C_J)$、$M_n(\mathbb C_J)$ 以同一个中心复数、含幺且保持 $*$ 的方式嵌入非零联合结合代数，两像可交换且其乘积张成联合代数，则联合代数恰为 $M_{mn}(\mathbb C_J)$。

**证明。**
$a\otimes b\mapsto\iota_A(a)\iota_B(b)$ 为满含幺 $*$-同态。定义域 $M_m\otimes_\mathbb C M_n\cong M_{mn}$ 简单，核只能是零或全体；含幺排除全体。

反复复合得 $M_{2^N}$。数学秩 $d$ 投影的角 $pM_{2^N}p$ 是 $M_d$，有限直和加入经典扇区，所以数学完成包含全部

$$
\mathcal A=\bigoplus_jM_{d_j}(\mathbb C_J).
$$

同一复中心、局部可交换与乘积张成是复合接口，不由单个球自动产生。实际角或标签仍须原附接及支持返回。

### 命题 8.2（密度矩阵与全部数学效果）

取上述代数的标准正锥，其每个归一正泛函唯一为

$$
\omega(a)=\sum_j\operatorname{Tr}(\rho_j a_j),\qquad
\rho_j\ge0,\quad\sum_j\operatorname{Tr}\rho_j=1.
$$

数学效果为 $0\le E\le I$，完整测量为 $\sum_kE_k=I$。

**证明。**
非退化迹配对给唯一 Hermitian 密度；作用于各秩一正投影的正性，逐块迫使密度非负；单位取值给迹归一。反向直接成立。

纯态对应简单块中的秩一投影，混态为其凸组合；自伴可观测量的谱分解 $H=\sum_kh_kP_k$ 给 $p_k=\operatorname{Tr}(\rho P_k)$ 与 $\langle H\rangle=\operatorname{Tr}(\rho H)$。这里取全部正泛函是数学完成；原联合态锥是否等于该锥，是额外实际条件。

### 8.2 参考正性、一般过程与反射

### 定理 8.3（一般分支的 Kraus 形式）

设原分支在自伴部上实线性，并唯一复线性延拓为 $\mathcal E:M_d\to M_n$。若一个实际参考含完整 $M_r$ 块、$r\ge d$，且同一原分支 $\mathcal E\otimes\operatorname{id}_r$ 在完整标准联合正锥上保正，则

$$
\mathcal E(\rho)=\sum_\mu K_\mu\rho K_\mu^*.
$$

分支对完整数学正锥上的全部归一态不增加总概率，等价于 $\sum_\mu K_\mu^*K_\mu\le I$。同理，若完整仪器在该完整态空间上归一，则 $\sum_{k,\mu}K_{k\mu}^*K_{k\mu}=I$，其中 $k$ 保留全部原记录。

**证明。**
在参考块中取 $d$ 维数学子空间，令 $\lvert \Omega\rangle=\sum_i\lvert i\rangle\otimes\lvert i\rangle$。联合正性给正 Choi 矩阵
$C_{\mathcal E}=(\mathcal E\otimes\operatorname{id})(\lvert \Omega\rangle\langle \Omega\rvert)\ge0$。对其谱分解 $\sum_\mu\lvert v_\mu\rangle\langle v_\mu\rvert$，重排 $v_\mu$ 为矩阵 $K_\mu$，比较矩阵单位系数得所求式。反向对任意参考逐项共轭保正。迹不等式给概率条件。

足够多的经典标签不能替代完整矩阵参考；仅检查乘积态或可分态也不够。数学 Kraus 指标不自动成为原可访问记录。

局部候选仍允许 $G=O(3)$。一个代表性 Bloch 反射对应转置 $T$，任意取向反转元都是它与正旋转的复合，而

$$
(T\otimes\operatorname{id})(\lvert \Phi^+\rangle\langle \Phi^+\rvert)
=\tfrac12\operatorname{Swap}
$$

在反对称向量上有特征值 $-1/2$。因此同一原控制若也满足完整参考合同，就不能含反射。若原菜单确已含反射，结论是其不满足这个后续合同，而不是先删掉原控制再声称同一实例完成。

### 8.3 理想投影更新

### 定理 8.4（Lüders 形式）

简单块上的 CP 分支若效果为投影 $P$，且不扰动每个支撑于 $P$ 的态，则

$$
\mathcal E(\rho)=P\rho P.
$$

**证明。**
$\sum_\mu K_\mu^*K_\mu=P$ 给 $K_\mu=K_\mu P$。对每个 $\psi\in P\mathcal H$，不扰动使正项之和
$\sum_\mu\lvert K_\mu\psi\rangle\langle K_\mu\psi\rvert=\lvert \psi\rangle\langle \psi\rvert$ 秩一，故各 $K_\mu\psi$ 与 $\psi$ 共线。对两个独立向量及其和用线性，得 $K_\mu=c_\mu P$，且 $\sum_\mu|c_\mu|^2=1$。秩一支撑直接成立；$P=0$ 给零分支。

成功概率正时才归一为 $P\rho P/\operatorname{Tr}(\rho P)$。仅可重复或仅保持某组基态不够：支撑内退相干是反例。直和逐中心块证明，不使用跨中心相干向量。

### 8.4 连续可逆时间与量子动力学

### 定理 8.5（幺正时间形式）

若同一有限简单块的 $\mathcal E_t$ 是连续 CPTP 单参数群，且逆也是受同一参考条件约束的原过程，则

$$
\mathcal E_t(\rho)=U_t\rho U_t^*,\qquad
U_t=e^{-JtH/\hbar},\quad H=H^*.
$$

所以 $J\hbar\dot\psi=H\psi$、$\dot\rho=-(J/\hbar)[H,\rho]$。

**证明。**
Heisenberg 对偶及其逆都保单位且 CP。对映射和逆分别用 Schwarz 不等式，迫使 $T(a^*a)=T(a)^*T(a)$，极化得乘法保持。于是 $T$ 为 $*$-自同构。矩阵单位的像为另一组矩阵单位，可选正交基及相位将其写成酉共轭。连续单参数自同构的生成元为内导子，故可取所述酉指数；标量相位不影响状态。有限直和的连续群不能置换离散中心，故逐块成立。

物理时钟、具体 $H$、可调用的连续流与 $\hbar$ 数值仍待原物理输入。局部完整 CPTP 操作并忘去其结果时，迹结构给无信号性：

$$
\operatorname{Tr}_B[(\operatorname{id}\otimes\mathcal E_B)(\rho_{AB})]=\operatorname{Tr}_B\rho_{AB}.
$$

这不把后选择分支或任意联合操作也算作无信号局部过程。状态半内积的 Cauchy–Schwarz 给

$$
\operatorname{Var}_\rho(H)\operatorname{Var}_\rho(K)
\ge\left|\frac1{2J}\operatorname{Tr}(\rho[H,K])\right|^2.
$$

这些是已完成的有限矩阵理论的后果，不把无限维场、正则对易关系或具体相互作用一并算作已推导。

### 8.5 实际有限测量的既有供应接口

C123/C124 本轮未变。其原子、必然、非中心指针效果满足 $d=cp$、$\alpha(d)=1$，故

$$
1=\operatorname{Tr}(\rho_\alpha cp)\le c\operatorname{Tr}\rho_\alpha\le c\le1
$$

迫使 $d=\rho_\alpha=p$，其中 $p$ 位于非经典块。使用同一完整指针内两个方向构造

$$
U_E=\begin{pmatrix}\sqrt E&-\sqrt{I-E}\\
\sqrt{I-E}&\sqrt E\end{pmatrix}
$$

并在其余方向取恒等，接原准备和原破坏性读口，得到实际成功支 $\sqrt E\rho\sqrt E$。这仍需其完整原联合 P/G/D、精确门调用、同记录接续、失败及输出丢弃条件；本文局部候选没有自动供应它们，也未删除其所有联合对象的原 $D$。指针可以没有实际 qubit 对象。 [4](#ref-repo124)

<a id="section-9"></a>

## 9. 把新候选接到最新活动记忆结果

<a id="sec-memory"></a>

### 9.1 先用同一个装置的反例看清未来区别

C113 的固定酉装置为

$$
U=I\otimes\lvert 1\rangle\langle 0\rvert+Z\otimes\lvert 0\rangle\langle 1\rvert,
\qquad Z=\operatorname{diag}(1,-1).
$$

对校准记忆 $\tau=\lvert 0\rangle\langle 0\rvert$，第一次有

$$
U(\rho\otimes\lvert 0\rangle\langle 0\rvert)U^*=\rho\otimes\lvert 1\rangle\langle 1\rvert.
$$

系统校准精确恒等。但第二次同一个装置给 $Z\rho Z$，对 $\lvert +\rangle$ 变为正交的 $\lvert -\rangle$。没有更换装置；被漏掉的是以后会到达的记忆方向。 [2](#ref-repo113)

因此，本轮不可约条件的载体必须是原全部未来 $W$。不能在一次校准中找到一个二维片，就宣称原世界已经没有其他内容。

### 9.2 精确校准何时足以排除这种记忆影响

### 命题 9.1（C113 精确情形的有限证明）

取非零有限维复 Hilbert 空间 $H,K,M$，以及同一个完整联合 CP 仪器
$V_j:\mathcal B(H\otimes M)\to\mathcal B(K\otimes M)$，包含全部原成功和失败标签。设 $\tau>0$、$\operatorname{Tr}\tau=1$ 为忠实乘积校准状态，且

$$
\operatorname{Tr}_M V_j(X\otimes\tau)=K_jXK_j^*,\qquad K_j\ne0.
$$

若 $E_j=K_j^*K_j$ 实线性独立并满足 $\sum_jE_j=I$，则存在比较记忆 CPTP 映射 $\widehat B_j$，使

$$
V_j=\operatorname{Ad}_{K_j}\otimes\widehat B_j.
$$

**证明。**
取有限 Stinespring 算子 $A_j:H\otimes M\to K\otimes M\otimes Z_j$，将忠实记忆对角化为 $\tau=\sum_\mu p_\mu\lvert \mu\rangle\langle \mu\rvert$、$p_\mu>0$。按输出环境基 $a$ 分块为系统算子 $A_{j,a\mu}$。校准 Choi 恒等式为

$$
\sum_{a,\mu}p_\mu\lvert A_{j,a\mu}\rangle\!\langle A_{j,a\mu}\rvert
=\lvert K_j\rangle\!\langle K_j\rvert,
$$

这里以向量化理解各算子。右边秩一，左边为正项之和，且每个 $p_\mu>0$，故所有 $A_{j,a\mu}$ 与 $K_j$ 共线，得到 $A_j=K_j\otimes B_j$。

完整仪器给

$$
\sum_j E_j\otimes(B_j^*B_j-I_M)=0.
$$

用效果的真实线性对偶逐项提取，得 $B_j^*B_j=I_M$。所以
$\widehat B_j(Y)=\operatorname{Tr}_{Z_j}(B_jYB_j^*)$ 保迹且 CP，因子化成立。

这条论证已经使用复 Hilbert、CP、忠实记忆及原效果独立性，不能倒过来当作这些结构的起源证明。若效果相关，原标签仍可在各次调用间保留隐藏相关；不能靠合并标签来宣称原历史不再有区别。比较记忆的存在也不开放实际记忆端口。

### 9.3 正误差的原预算与有限历史

保留上一命题的全部有限维复载体、同一个完整原联合 CP 仪器和全部非零目标 $K_j$，仍要求 $E_j=K_j^*K_j$ 实线性独立且 $\sum_jE_j=I$。仅将精确校准等式放宽为同时误差合同。校准仍使用同一个归一化乘积记忆 $\tau$，$\operatorname{Tr}\tau=1$，并对全部原标签取 $\delta_j\ge0$：

$$
\tau\ge\lambda_M I_M,\quad\lambda_M>0,\quad
\lVert \operatorname{Tr}_M V_j(\,\cdot\,\otimes\tau)-\operatorname{Ad}_{K_j}\rVert_\diamond
\le\delta_j.
$$

取自伴效果对偶 $F_j$，$\operatorname{Tr}(F_jE_\ell)=\delta_{j\ell}$。令

$$
h_j=\sqrt{d\delta_j/\lambda_M},\qquad
\epsilon_j=(2+h_j)h_j,\qquad
t_j=\lVert F_j\rVert_1\sum_\ell\epsilon_\ell,
$$

其中 $d=\dim H$，要求全部 $t_j<1$。新 C113 定理保证存在仅用于数学比较的 CPTP 记忆 $\widehat B_j$。定义同类型的完整旗标通道

$$
\mathfrak V(X)=\sum_j\lvert j\rangle\langle j\rvert\otimes V_j(X),\qquad
\mathfrak W(X)=\sum_j\lvert j\rangle\langle j\rvert\otimes
(\operatorname{Ad}_{K_j}\otimes\widehat B_j)(X).
$$

它们满足未减半 diamond 界 $\lVert \mathfrak V-\mathfrak W\rVert_\diamond\le\Delta$，其中

$$
\Delta=\min\left\{2,\sum_j\left[
\epsilon_j+\lVert E_j\rVert_{\rm op}f(t_j)\right]\right\},
\qquad
f(t)=\frac{(\sqrt{1+t}+1)t}{1+\sqrt{1-t}}.
$$

其证明先将目标秩一 Choi 的正交余项，用 $\tau\ge\lambda_M I$ 提升到全部原记忆输入方向；再用完整仪器及效果对偶控制各记忆保迹缺陷；最后以极分解修正为比较 CPTP 记忆。忠实下界、效果条件数与完整记录都不可在此链中省略。 [2](#ref-repo113)

取已供应的同一有限合法协议。全部完整控制器均 CPTP，按同一原经典历史选择，在私有 $M$ 上为恒等，并包含失败补全。令 $\mathcal P_V,\mathcal P_W$ 分别为在相同调用槽中使用 $\mathfrak V,\mathfrak W$ 的完整协议通道；后者只作数学比较，不要求其记忆映射属于原菜单。至多调用 $N$ 次时

$$
\lVert \mathcal P_V-\mathcal P_W\rVert_\diamond
\le\varepsilon_N:=\min\{2,N\Delta\}.
$$

允许初始记忆相关、后续不复位。对同一初态和同一完整输出的同一成功事件，令两边未归一化正输出为 $Y_V,Y_W$，概率为 $p=\operatorname{Tr} Y_V$、$q=\operatorname{Tr} Y_W$。当 $p,q>0$ 时，

$$
|p-q|\le\varepsilon_N/2,\qquad
\lVert Y_V/p-Y_W/q\rVert_1
\le\min\{2,\varepsilon_N/\max(p,q)\}.
$$

后一界消费共同补事件预算，不适用于任意未归一化算子的随意配对；零概率一侧不定义条件态。所有调用、控制器和失败补全本来就须合法，误差定理不供应新操作。

### 9.4 本轮不可拆证书的局部稳定性

对同一个已识别的原 $U,B_0$，定义

$$
\gamma(A)=\inf_{\substack{S=S^*,\ \operatorname{Tr} S=0\\\lVert S\rVert_{\rm HS}=1}}
\lVert [A|_U,S]\rVert_{\rm HS}.
$$

候选的 $A\ne0$、$Ae=0$ 保证 $\dim U\ge2$，所以这个单位球非空。有限维下 $\gamma(A)>0$ 恰是 $\ker\Gamma_A=0$ 的证书。若 $U$ 为二维、$A|_U=\lambda J_2$，在两个标准自伴无迹基上直接计算得

$$
\gamma(A)=2|\lambda|.
$$

若同一载体上的另一个原候选生成元 $\widetilde A$ 仍斜对称且固定 $e$，且
$\lVert \widetilde A-A\rVert_{\rm op}\le\epsilon$，则乘子估计给

$$
\lVert [(\widetilde A-A),S]\rVert_{\rm HS}
\le2\epsilon\lVert S\rVert_{\rm HS},
\qquad
\gamma(\widetilde A)\ge\gamma(A)-2\epsilon.
$$

这给固定原载体上的有限稳定性。若真实横向内容另有一块，
$A_{\rm full}=\lambda J_2\oplus\mu J_2$，则
$S=\operatorname{diag}(I_2,-I_2)$ 非零、对称、无迹且与它可交换，故完整 $\gamma$ 为零。一个已见二维片的正间隙不能认证未知容量或遗漏记忆。C113 的有限预算同样不认证无限未来一直使用同一装置。

<a id="section-10"></a>

## 10. 内生性、简化程度与完整理论的边界

<a id="sec-status"></a>

| 层次 | 保留或新定义的关系 | 所得结论 |
|---|---|---|
| 原预测前端 | 单源全部未来、未知有限容量、准确统计逆 | 原 $W,G,\mathfrak g,e$，紧性与循环性 |
| 本轮唯一候选 | 一个原非零静止转向在全部横向内容上不可拆 | 原内容三维、原控制 $\mathfrak{so}(3)$、旧 $\Xi$ 为结论 |
| 原单位与取向 | 原 $e$ 定比较单位，原 $A$ 定响应取向 | 内部 $D$、面积、横向复线 |
| 最小结合完成 | 由三维比较定义 Clifford 关系 | 中心 $J$、$M_2(\mathbb C)$、复二维振幅 |
| 原概率配对 | 原事件的线性与 $[0,1]$ 界 | Born 表示及完整 POVM |
| 复合与参考 | 共同复中心、交换与张成；足够大的实际完整矩阵参考，同一分支在完整联合正锥保正 | 复张量积、CP/Kraus；参考合同成立时同一控制族不含反射 |
| 理想更新与时间 | 支撑内所有态不扰动；连续 CPTP 群及 CP 逆 | Lüders 更新、幺正演化形式 |
| 实际供应与校准 | C124 原完整联合合同；C113 同装置、忠实记忆、效果独立 | 有限端点与已供应有限历史预算 |

**本轮实际删掉了什么。**

相对 $\Omega Q$-003：删去自由内容试针，改用已有原源；删去控制商到内容商的同构要求；删去为该证书计算全控制交换子读出的任务。只留下一个原生成元的不可约性，可以用有限线性交换方程检查。三维证明从先排整个控制 Lie 代数，缩成一个实旋转平面。$D$ 也可直接用式 [(3)](#eq-D) 恢复。

这是一项原始供应与证明结构的等价压缩。不可约本身是实质选择条件，在紧实单算子背景中正是选中一个旋转平面的条件；不能把它改叫“不可分”就声称已从无前提推出三维。一个受限量子菜单也可能没有足够的原静止转向，不能据此判定它不是量子系统。

**公理内生的精确含义。**

原内容由未来读数定义，原转向由接续定义，原参照由同一来源定义，稳定子与不变内容片由这些对象的作用定义。因此新候选是同一 $\Omega$ 内定义产物之间的约束，没有另塞一份响应表。

但同样前端确有可约反模型，所以“$\Omega$ 包含一切”本身不蕴含这个约束。可以把满足它的窗口定义为本理论的初等块；要证明自然出现这样的块，仍须从更早的整体原理证明其存在。若只在大窗口里任意挑一个二维不变片，却没有证明其余原读数可被保真处理，就没有完成内生重建。

**有限理论以外。**

以上已经闭合有限状态、观测、过程、复合、理想更新与连续可逆演化。无限维正则表示、场、具体相互作用、实际时钟和 $\hbar$ 数值没有随之给出。FIB 本轮无新增正文；其条件秩二结果与此处内容三维不是同一个命题。本轮未建立到 $\zeta$ 零点或离临界线零点的原对象桥，因而没有 RH 结论。

先把整体自己已经给出的当前准备放在中间，不另找一个外来的参照。整体里有一种转向，对这份准备看不出任何变化，却会改变其他可能的差别。我们只要求：在这同一种转向下面，其余全部能被读出的差别不能分成两拨，各自在自己的小圈里转，永远不碰到另一拨。拿出一个方向，再看它被转向带到哪里，这两个方向自然围成一个旋转平面；既然不能再分家，这个平面就必须容纳全部横向内容。加上原来不动的参照轴，恰好三维。原准备给出单位，原转向给出左右手，面积和每份内容的响应都能算出来；平面里转四分之一圈给出横向复结构，三维关系的结合闭包再给出复振幅和相位圈，原读数就成为 Born 概率。把这些块按明确的复合和参考规则接起来，就是有限维量子理论。所有以后还会回来影响读数的记忆，也属于这里的“全部内容”，不能因为第一次没有看见就把它删掉。

<a id="references"></a>

## 参考文献

<a id="ref-repohead"></a>

### [1]

 The Omega Institute, *trureturing*, 固定提交 `2d80e2d87f58d687ee660169fbeb4b8f07f2e1f5`。本轮比较：[https://github.com/the-omega-institute/trureturing/compare/0d2719a1091903642f361f04994da098acd20e22...2d80e2d87f58d687ee660169fbeb4b8f07f2e1f5](https://github.com/the-omega-institute/trureturing/compare/0d2719a1091903642f361f04994da098acd20e22...2d80e2d87f58d687ee660169fbeb4b8f07f2e1f5)。

<a id="ref-repo113"></a>

### [2]

 同仓库，*AURIC Internal Balanced Calibration and Filter Composition Geometry C113*，新增 §§25–27。[https://github.com/the-omega-institute/trureturing/blob/2d80e2d87f58d687ee660169fbeb4b8f07f2e1f5/docs/develop/theory/AURIC_INTERNAL_BALANCED_CALIBRATION_AND_FILTER_COMPOSITION_GEOMETRY_C113.md](https://github.com/the-omega-institute/trureturing/blob/2d80e2d87f58d687ee660169fbeb4b8f07f2e1f5/docs/develop/theory/AURIC_INTERNAL_BALANCED_CALIBRATION_AND_FILTER_COMPOSITION_GEOMETRY_C113.md)。

<a id="ref-repo117"></a>

### [3]

 同仓库，*AURIC Common Source Self Reference and Observer Sequences C117*，§16，本轮未变。[https://github.com/the-omega-institute/trureturing/blob/2d80e2d87f58d687ee660169fbeb4b8f07f2e1f5/docs/develop/theory/AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md](https://github.com/the-omega-institute/trureturing/blob/2d80e2d87f58d687ee660169fbeb4b8f07f2e1f5/docs/develop/theory/AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md)。

<a id="ref-repo124"></a>

### [4]

 同仓库，*AURIC Native Reciprocal Comparison and Finite Endpoint Quantum C123*，C124 为 §§10–17，本轮未变。[https://github.com/the-omega-institute/trureturing/blob/2d80e2d87f58d687ee660169fbeb4b8f07f2e1f5/docs/develop/theory/AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md](https://github.com/the-omega-institute/trureturing/blob/2d80e2d87f58d687ee660169fbeb4b8f07f2e1f5/docs/develop/theory/AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md)。

<a id="ref-previous"></a>

### [5]

 本会话 $\Omega Q$-003，*顺序差与内容差等价*，2026-11-04。[https://chatgpt.com/library?file_id=libfile_514c9238b11c8191b70f805c11c086a8&account_id=personal](https://chatgpt.com/library?file_id=libfile_514c9238b11c8191b70f805c11c086a8&account_id=personal)。

<a id="ref-watrous"></a>

### [6]

 John Watrous, *The Theory of Quantum Information*, 2018，第 2 章，尤其定理 2.22。[https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)。
