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

## 11. 无预置有限容量的全未来紧性入口

本节给出一个与前面有限维定义相容、但不把有限预测维数作为前提的入口。它只在同一原来源上使用实际未来的事件坐标；紧性是单个实际循环行轨道的范数性质。后面的不可约条件是额外的原作用条件，不能由紧性单独推出。

### 定义 11.1（原始全未来行与实际预测距离）

固定一个原归一准备，记 $\mathcal L$ 为从它得到的全部合法可逆控制词，包含空词并且对接续及统计逆封闭。$\mathcal F$ 是同一个原来源允许的全部未来协议：其中保留所有合法控制次序、自适应和有限并行历史，记录及会返回的记忆，类型、父位置和 ready 条件，时钟与参考标签，相关联合条件，以及成功、失败、停止和销毁分支。每个 $f\in\mathcal F$ 的终端标签集合记为 $\mathcal W_f$；失败、停止和销毁标签仍是 $\mathcal W_f$ 的元素。

把实际事件坐标集写成

$$
 \mathcal R=\{(f,w):f\in\mathcal F,\ w\in\mathcal W_f\}\,\cup\,\{(f,\top_f):f\in\mathcal F\},
$$

其中 $\top_f$ 是这个实际未来的“得到某个终端标签”事件，而不是一个抽象的额外坐标。对每个准备行 $a\in\mathcal L$，定义

$$
 x_a(f,w)=p(a;f,w),\qquad x_a(f,\top_f)=1,\qquad
 \sum_{w\in\mathcal W_f}x_a(f,w)=1.
 \tag{11.1}
$$

所有这些等式都对原来的完整未来域成立。若 $g\in\mathcal L$，原统计逆的要求是

$$
 p(ag;f,w)=p(a;gf,w),\qquad
 T_{g^{-1}}T_gx_a=x_a=T_gT_{g^{-1}}x_a
 \tag{11.2}
$$

对每个实际行及每个实际事件坐标成立。式 (11.2) 只要求统计逆在实际行上的两个复合恒等式；它不要求 $f\mapsto gf$ 在语法上是一个未来映射的双射，也不要求擦除原历史。定义

$$
 d_\infty(x,y)=\sup_{r\in\mathcal R}|x(r)-y(r)|.
 \tag{11.3}
$$

这是同一全未来的统一预测距离，且实际总事件坐标在它中被保留。

### 定义 11.2（行的 Banach 完成与循环轨道条件）

在 $\ell^\infty(\mathcal R;\mathbb R)$ 中取

$$
 E_0=\operatorname{span}_{\mathbb R}\{x_a:a\in\mathcal L\},\qquad
 V=\overline{E_0}^{\,d_\infty}.
 \tag{11.4}
$$

$V$ 是由实际预测行完成得到的 Banach 空间。令 $u$ 为任意一个总事件坐标的评价泛函；由 (11.1) 它满足 $u(x_a)=1$。本节的紧性前件是单个原循环行轨道

$$
 \mathcal O=\{x_a:a\in\mathcal L\}
 \tag{11.5}
$$

在 $d_\infty$ 下全有界。这里的全有界性量化的是全部实际未来事件，不能由有限个已经看见的读数替代。

### 引理 11.3（统计逆给出紧的强算子群）

在定义 11.1--11.2 的条件下，接续 $T_gx_a=x_{ag}$ 唯一延拓为 $V$ 上的线性等距。其强算子闭包 $K$ 是一个紧拓扑群；闭包中的每个算子仍为满射等距，而不是只得到一个可能不可逆的收缩半群。

**证明。**若 $\sum_i\alpha_i x_{a_i}=0$，则对任意 $f,w$ 有

$$
 \sum_i\alpha_i x_{a_ig}(f,w)=\sum_i\alpha_i x_{a_i}(gf,w)=0,
$$

所以 $T_g$ 在 $E_0$ 上良定义。直接由坐标重标记，$\|T_gz\|_\infty\le\|z\|_\infty$；(11.2) 对行成立，线性和及连续性把 $T_{g^{-1}}T_g=T_gT_{g^{-1}}=I$ 延拓到 $V$，故不等式变为等式。

令 $C=\overline{\mathcal O}$。它是紧度量空间，且每个 $T_g|_C$ 是 $C$ 上的满射等距。等距族在 $C^C$ 的逐点拓扑中等度连续；取其闭包并同时取逆算子的子网，可得任意极限 $S$ 与另一个极限 $R$ 满足 $RS=SR=I_C$。因此 $S$ 在 $C$ 上仍是满射，而不是把逆性在极限中丢掉。因为 $\operatorname{span}C$ 在 $V$ 中稠密，$S$ 在线性包上按

$$
 S\Bigl(\sum_i\alpha_i y_i\Bigr)=\sum_i\alpha_iS(y_i),\qquad y_i\in C,
$$

唯一延拓为等距；同样由 $R$ 得到其逆。逐点收敛在 $C$ 上等价于在 $\operatorname{span}C$ 上的强收敛，并由等距性延拓为 $V$ 上的强收敛。于是这些延拓的集合正是强算子闭包 $K$，它在强算子拓扑下紧并且封闭于乘法和逆。证毕。

这个论证没有使用维数、内积、Hilbert 空间、Lie 群或有界生成元。特别地，若只对一列算子逐点取极限而不保留逆算子的同一紧子网，不能推出满射；满射性来自原统计逆和紧轨道的联合取极限。

### 引理 11.4（原源的 Haar 中心与完整循环差空间）

令 $\mu_K$ 为引理 11.3 的紧群 $K$ 的 Haar 概率，定义

$$
 c=\int_K kx_\epsilon\,d\mu_K(k),\qquad e=x_\epsilon-c,\qquad W=\ker u.
 \tag{11.6}
$$

则 $c\in V$、$u(c)=1$、$kc=c$ 对所有 $k\in K$ 成立，并且

$$
 V=\mathbb Rc\oplus W,\qquad
 W=\overline{\operatorname{span}}\{ke:k\in K\}.
 \tag{11.7}
$$

因此 $W$ 是完整的循环差空间，而不是把有限个横向坐标挑出来的片。

**证明。**紧轨道上的连续 $V$ 值函数可作 Bochner 积分；Haar 不变性给 $kc=c$，总事件评价给 $u(c)=1$。每个实际行是 $x_a=c+T_ae$，故右端闭线性包包含全部行差。反过来，若有限行组合的系数和为零，它等于相应 $T_ae$ 的有限线性组合；对任意 $v\in\ker u$，用行组合逼近 $v$，再减去其系数和乘以 $c$，得到右端的极限。故两边相等。由于 $u(c)=1$，$V=\mathbb Rc\oplus\ker u$。证毕。

### 定理 11.5（Banach 紧表示的实标量桥）

在上述前端上，设有一个强连续的一参数作用

$$
 \alpha:\mathbb R\longrightarrow K,\qquad \alpha(t)e=e,
 \tag{11.8}
$$

其在非零商空间 $Q=W/\mathbb Re$ 上的作用非平凡，并且在拓扑意义下实不可约：$Q$ 没有非零真闭的、对所有 $\alpha(t)$ 不变的实线性子空间。则

$$
 \dim_{\mathbb R}Q=2,\qquad \dim_{\mathbb R}W=3,\qquad \dim_{\mathbb R}V=4.
 \tag{11.9}
$$

**证明。**先处理商中看不见的剪切。取 $W=\mathbb Re\oplus Y$ 的任意连续补空间。若一个紧群元素固定 $e$ 且在 $Q$ 上为恒等，则在 $Y$ 上必有

$$
 y\longmapsto y+\ell(y)e
$$

其中 $\ell\in Y^*$. 这些元素的复合把 $\ell$ 相加；紧的加法子群只能是 $\{0\}$，因为非零 $\ell$ 的整数倍无界。因此紧性排除了任何非平凡的商不可见剪切。特别地，(11.8) 的非平凡性确实发生在 $Q$ 上，而不是藏在一个无界的剪切族中。

令 $L=\overline{\alpha(\mathbb R)}$. 它是 $K$ 的紧连通交换子群。先只使用 Eisner--Farkas--Haase--Nagel 的 Banach 表示分解（定理 15.14）：对复化 $Q_{\mathbb C}=Q\oplus iQ$ 的连续表示，$Q_{\mathbb C}$ 是有限维 $L$-不变子空间并的闭包。因此存在非零有限维复不变子空间 $F$；$F+\overline F$ 的共轭固定部分给出非零有限维实 $L$-不变子空间（对非零 $v\in F$，$\operatorname{Re}v$ 与 $\operatorname{Im}v$ 至少一个非零）。实不可约性迫使这个子空间就是 $Q$，所以 $Q$ 在这里第一次被证明为有限维。这一步没有使用内积或矩阵生成元。

现在才在有限维 $Q$ 上任取辅助内积并作 Haar 平均，使 $L$ 的作用正交；这只是有限性已经得到后的表示整理。复化表示由命题 15.16 与推论 15.18 分解为一维连续字符 [7](#ref-efhn)。这也是 Shiga 的闭子空间约定下的同一 Banach 供应 [8](#ref-shiga)，而不是把 Hilbert 结构偷偷加入前端。

现在作实标量桥。一个实不可约块的复化若只有一个实字符，则该字符给出一维实作用；但 $L$ 连通，连续的非平凡实一维字符只能取正值，而紧性又迫使其为恒等，和 $Q$ 上的非平凡性矛盾。于是出现一个非实字符 $\chi$ 及其共轭 $\overline\chi$。$\chi$ 与 $\overline\chi$ 的复一维块的共轭固定点是二维实旋转块。若还存在另一字符块或字符重数超过一，便得到 $Q$ 的非零真闭不变实子空间，违反实不可约性。因此

$$
 Q_{\mathbb C}=L_\chi\oplus L_{\overline\chi},\qquad
 Q=(L_\chi\oplus L_{\overline\chi})^{\mathrm{conj}},\qquad
 \dim_{\mathbb R}Q=2.
$$

由 $Q=W/\mathbb Re$ 且 $Q\ne0$ 得 $\dim W=3$；引理 11.4 给出 $V=\mathbb Rc\oplus W$，故 $\dim V=4$。只有在这个有限性结论之后，才可把 $\alpha(t)$ 写成有限维矩阵指数并引入有界生成元；前面的论证没有使用它。证毕。

### 推论 11.6（接回 $\Omega Q$-004 的有限控制结论）

在定理 11.5 的条件下，有限维 Banach 前端自动落入第 2 节的有限行设置。其有限维紧群作用忠实于 $W$，一参数作用有矩阵生成元 $A$，满足 $Ae=0$；二维实旋转块使 $A|_{W/\mathbb Re}$ 非零且不可约。因而可直接复用定理 5.2，而不重复其有限维证明：

$$
 G^\circ=SO(3),\qquad \mathfrak g=\mathfrak{so}(W,B_0),\qquad
 G\in\{SO(3),O(3)\}.
 \tag{11.10}
$$

这里 $G$ 是原全群在 $W$ 上的作用；$G^\circ=SO(3)$ 是恒等元所在的连通分支，完整群是否含取向反转元仍由后续参考条件决定。若存在第 8.2 节所要求的完整参考块 $M_r$（$r\ge d$，其中 $d$ 是该局部矩阵块的维数），并且同一个实际分支 $\mathcal E\otimes\operatorname{id}_r$ 在完整联合正锥上保正，则取向反转的转置型代表在反对称向量上给出负值，故反射不能属于同一实际控制族；这个额外参考合同把可能的 $O(3)$ 收缩为 $SO(3)$。仅有局部事件概率、可分参考或数学闭包不作此排除。

接回时保留原卷已有的全部条件：总事件和失败标签的线性完整性、定理 7.1 的 Born 配对、共同中心复数及命题 8.1 的复合张成、定理 8.3 的完整参考与 CP 正性、定理 8.4 的支撑内不扰动和仪器更新、定理 8.5 的物理时间连续 CPTP 群与逆，以及 C113/C123/C124 的忠实记忆、联合校准、记录接续和失败补全条件。定理 11.5 只供应有限维入口，既不供应这些实际接口，也不改变 $\hbar$、物理时钟或可调用门的来源条件。

### 11.1 旧前件、新前件与结论强度

| 同一原模型类别中的位置 | 旧组合 | 新组合 | 结论边界 |
|---|---|---|---|
| 预测空间 | 直接假定 $\dim V<\infty$，再用有限维紧群 | 用实际全未来行轨道的 $d_\infty$ 全有界性，取 Banach 完成 | 紧性本身允许无限秩；它不是有限维的同义词 |
| 可逆性 | 有限维矩阵闭包中的统计逆 | 实际行上的两个统计逆恒等式，加上引理 11.3 的强闭包 | 不要求文字语法上的未来双射 |
| 三维选择 | 已有 $A\ne0,\ Ae=0$ 及有限维商不可约 | 另加定理 11.5 的源固定一参数作用及全商实拓扑不可约 | 由定理 11.5 后才取得有限维，再复用定理 5.2 |
| 实际量子接口 | 原事件、Born、共同中心、复合、CP、仪器、更新、时间条件 | 原条件逐项保留 | 没有把数学闭包当作实际门或参考 |

所以这是“有限维假设换成全未来紧性并加入不可约作用”的条件应用。紧性单独不能给出三维；新组合也不被宣称严格包含旧的完整模型类、普遍必要或最小。三维是预测内容的数学维数，不是物理空间维数；有限样本或有限校准不能认证全未来的全有界性、循环完备性或不可约性，也没有因此完成量子起源。

### 11.2 无穷秩的紧行反模型：衰减坐标与破坏性终端读

下面给出一个具有完整抽象未来语法的共同来源例子。它用于证明“行轨道紧”并不等于“行空间有限维”；它是一个明确受限的破坏性终端读模型，不是原 Omega 的 CountRead 或更宽操作菜单的替代。

令

$$
 W_\infty=c_0(\mathbb N;\mathbb R^2),\qquad
 V_\infty=\mathbb R c\oplus W_\infty,\qquad
 a_n=2^{-n-3},\qquad
 e=((a_n,0))_{n\ge1},
 \tag{11.11}
$$

并取 $\|(s,z)\|=\max\{|s|,\|z\|_\infty\}$、$u(s,z)=s$。实际控制群是有限支撑直和

$$
 \Gamma=\bigoplus_{n\ge1}SO(2),\qquad
 (T_\theta z)_n=R_{\theta_n}z_n,
 \tag{11.12}
$$

其数学强闭包是 $K=\prod_{n\ge1}SO(2)$。实际准备行是 $x_\theta=c+T_\theta e$，其中 $\theta\in\Gamma$。

**完整抽象未来语法。** 一个 ready 节点带有有限类型、父位置、返回记忆、记录、时钟、参考和相关条件标签；它可以执行任意有限支撑的 $\Gamma$ 控制词，控制词可按已经保留的经典记录自适应，也可在有限个经典分支上并行组织。物理分支只能在一个终端节点调用一次 $\operatorname{Read}(n,q)$，其中 $n\ge1$、$q\in S^1$；终端标签含成功的 $+$、$-$、failure、stop 和 destruction。销毁以后，未来只能对已经保留的记录和返回记忆作任意有限经典后处理，不能再作控制或物理读。所有有限协议树、全部上述标签和每一个合法相关条件都属于 $\mathcal F$；不存在把某个未列出的未来偷偷删掉的坐标。无限支撑的 $\prod SO(2)$ 元只属于闭包，不自动成为实际控制。

在一个读节点，若最终横向状态为 $z$，定义

$$
 \begin{aligned}
 p(+\mid n,q,z)&=\frac14+\frac12\,q\mathbin{\cdot}z_n,&
 p(-\mid n,q,z)&=\frac14-\frac12\,q\mathbin{\cdot}z_n,\\
 p(\mathrm{failure})&=\frac14,&
 p(\mathrm{stop})&=p(\mathrm{destruction})=\frac18.
 \end{aligned}
 \tag{11.13}
$$

因为 $\lvert q\cdot z_n\rvert\le a_n\le1/16$，五个概率分别落在 $[7/32,9/32]$、$1/4$、$1/8$ 内并且总和为 $1$。没有读的停止或失败节点是相应的点质量；经典后处理只是把这些终端分布经随机核推前，所以仍满足非负性和总事件坐标 (11.1)。在准备 $\theta$ 后先执行未来控制 $h$ 时，式 (11.13) 中的 $z$ 是 $T_hT_\theta e$，故接续和统计逆按 (11.2) 精确成立。

这个模型的实际预测距离可精确计算。对任意 $\theta,\eta\in\Gamma$，(11.13) 给出

$$
 d_\infty(x_\theta,x_\eta)\le\frac12\|T_\theta e-T_\eta e\|_\infty.
$$

取不带前置控制、坐标为达到上确界的 $n$，再令 $q$ 平行于 $(T_\theta e-T_\eta e)_n$，便得到等号：

$$
 \boxed{d_\infty(x_\theta,x_\eta)=\frac12\|T_\theta e-T_\eta e\|_\infty.}
 \tag{11.14}
$$

若 $\varepsilon>0$，取 $N$ 使 $\sup_{n>N}a_n<\varepsilon$；前 $N$ 个圆的有限 $\varepsilon$-网与尾部估计给出 $\mathcal O$ 的有限 $\varepsilon$-网。因此实际轨道全有界，$K$ 的作用在行闭包上紧。另一方面，改变单个坐标 $n$ 的角度并取行差，可以得到只支撑在 $E_n=\mathbb R^2$ 的任意向量；有限支撑向量在 $c_0$ 中稠密，所以

$$
 \overline{\operatorname{span}}\{T_\theta e-T_\eta e:\theta,\eta\in\Gamma\}=c_0(\mathbb N;\mathbb R^2)=W_\infty.
 \tag{11.15}
$$

这确实是无穷秩的完整循环差空间。对任意 $S\subseteq\mathbb N$，

$$
 W_S=\{z\in c_0:z_n=0\text{ for }n\notin S\}
 \tag{11.16}
$$

是闭的、非零时可真、并且对 $\Gamma$、$K$ 以及任意坐标一参数子群不变；单坐标 $E_n$ 已给出最小的显式反例。因此这里不存在定理 11.5 所需的整个商不可约性。

### 11.3 未来记录给出的严格失败边界

在同一个衰减坐标模型中，若把终端破坏性读扩展为保持状态的弱测试，并允许给定状态下条件独立地重复任意次，令一次测试的二元分布为

$$
 \Pr(+\mid n,z)=\frac12+z_{n,1},\qquad
 \Pr(-\mid n,z)=\frac12-z_{n,1}.
 \tag{11.17}
$$

比较 $\theta^{(n)}$（只把第 $n$ 个分量转到角 $\pi$）与恒等控制。两者在第 $n$ 次测试的成功概率分别为 $1/2-a_n$ 与 $1/2+a_n$。对 $k$ 次条件独立记录取事件 $E_n$：“经验成功频率至少为 $1/2$”。Hoeffding 界给出

$$
 \Pr_{1/2+a_n}(E_n^c)\le e^{-2ka_n^2},\qquad
 \Pr_{1/2-a_n}(E_n)\le e^{-2ka_n^2}.
 \tag{11.18}
$$

取 $k_n\ge(\log4)/(2a_n^2)$，则同一个合法未来事件在两行下的概率相差至少 $1/2$。由于 $a_n\to0$ 而 $k_n$ 仍是每次有限的合法长度，序列 $\{x_{\theta^{(n)}}\}$ 的两两距离有统一正下界，实际全未来行轨道不再全有界。这个结论依赖三个明确条件：弱测试不销毁状态、条件独立性在重复中成立、以及任意大的有限记录和阈值事件属于未来域。

另一种破坏机制是可读的无界前缀档案。若未来能返回任意前缀 $(z_{1,1}/a_1,\ldots,z_{N,1}/a_N)$ 的符号记录，并且该记录事件可按坐标区分正负，则对 $\theta^{(n)}$ 与 $\theta^{(m)}$（$n\ne m$）取 $N\ge\max\{m,n\}$，第 $n$ 个符号事件的概率相差 $1$；这给出一个分离族。这里的归一化档案是额外的原读出能力，确实改变了 $(11.3)$ 的实际坐标族。破坏性终端读模型本身没有这种档案。

因此，重复的非破坏性弱测量或可读无界档案会摧毁本例的范数紧性，但这不是对所有原 Omega 操作的普遍不可能性断言。是否存在这些未来，必须由原记录、记忆、停止和销毁规则逐项决定；若它们存在，就不能把衰减坐标的紧性反模型误作原全源的证明。

### 11.4 适用范围

定理 11.5 说明一种可检验的条件链：全未来实际行的全有界性给出 Banach 紧群，源固定的一参数作用在完整非零商上实拓扑不可约，成熟的紧 Banach 表示供应再给二维实字符对，最后才进入已有定理 5.2 的三维及有限量子接口。紧性、群闭包和 Haar 中心是数学结构；它们不自动是准备、门、读口或校准程序。定理 7.1、命题 8.1、定理 8.3--8.5 以及 C113/C123/C124 的实际条件仍各自承担原来的证明义务。

该链没有声称旧组合的严格类包含、必要性或全局最小性，没有把三维解释为物理空间三维，也没有给出经验上的有限认证或完成的量子起源。其反模型与记录边界保留了一个可推翻的判据：只要原合法未来能实现 (11.17)--(11.18) 的任一条件，必须重新检查全未来预测紧性。

## 参考文献增补

<a id="ref-efhn"></a>

### [7]

T. Eisner、B. Farkas、M. Haase、R. Nagel，*Operator Theoretic Aspects of Ergodic Theory*，定理 15.14、命题 15.16、推论 15.18，pp. 280--282。[PDF](https://www.math.uni-leipzig.de/~eisner/book-EFHN.pdf)。

<a id="ref-shiga"></a>

### [8]

Koji Shiga，*Representations of a compact group on a Banach space*，定义 1、定理 2，尤其闭子空间约定。[J-stage PDF](https://www.jstage.jst.go.jp/article/jmath1948/7/3/7_3_224/_pdf)，DOI [10.2969/jmsj/00730224](https://doi.org/10.2969/jmsj/00730224)。

<a id="ref-deleeuw"></a>

### [9]

K. de Leeuw、I. Glicksberg，*Applications of almost periodic compactifications*，引理 4.5--4.7。[原文](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/5916-11511_2007_Article_BF02559535.pdf)，DOI [10.1007/BF02559535](https://doi.org/10.1007/BF02559535)。

<a id="append-anchor"></a>

## 追加锚（本行以下为增补区）
