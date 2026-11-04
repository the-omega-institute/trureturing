**QUANTUM ORIGINS / $\Omega Q$-001**

# 二元差额的保真运输

**从“零不能复活”到三维刚性、内部相位与有限量子理论**

新系列第一篇：一个完整候选的定义、定理、证明和反模型

两份内容的比较，一部分是重合，另一部分是有方向的差额。两部分必须恰好保留原有比较量。由整体内部的一份内容带动它们时，先形成关系再移动，与先移动两端再形成关系，必须得到同一份关系。已经完全抵消的内容，换一个读口也不能重新出现。

$$
\boxed{\ \langle x,y\rangle^{2}+\lVert x\times y\rVert^{2}=\lVert x\rVert^{2}\lVert y\rVert^{2}\ },\qquad
\boxed{\ U_x(t)(y\times z)=(U_x(t)y)\times(U_x(t)z)\ }.
$$

 本会话另开独立系列：$\Omega Q$-001，后续递增。

编号不是仓库版本，也不是数学首创或物理认证声明。

固定核查版本：`dev@a41b3dc77a15de8ceeabfcba85d60b17bad3df6b`。

版本提交时间：2026-11-03 17:25:27 UTC。

相关量子校准与 FIB 结果首先核读于 `5ccf20964da0a6695170f80f89e8383c92913a6c`。

范围：有限维、普通数学证明；没有将本稿提交到项目，也未运行 Lean 认证。

本稿只提出一个候选：**二元差额的保真运输**。它把正性、面积和相容性分别放回三个内部定义之间：自比较为零与所有读口不可分辨；两元重合与实际转向响应；移动两元与移动它们的关系。有限实线性接口、正标尺和内部响应的存在是明确起点，不声称从“整体存在”四个字自动获得。

核心结论有三层。第一，零关系不能在新读口下复活，迫使对称比较半正定；商掉所有零方向后，得到欧氏空间。第二，二元面积式已经让每一对独立方向闭合成三维片段，但七维八元数表明这些片段不一定能按同一内部响应拼接。补上运输相容后，一个不依赖叉积分类表的短证明排除第四个方向，含两份独立有效内容的初等块恰为三维。第三，这个三维结构在实数上生成结合的四元数，再由一个内部单位参照选出复数子域，使同一实四维空间成为复二维 Hilbert 空间。相位圆、Bloch 球、Hopf 纤维和 Born 重叠形状由此共同出现。

要发展为完整的*有限维操作理论*，仍须公开加入效果拆并、共同复标尺下的独立复合、参考扩张正性、理想投影分支中性及连续可逆物理时间等接口条件。本稿逐项证明它们给出密度矩阵、Born 规则、张量积、Kraus 表示、Lüders 更新与 Schrödinger 方程。数学理论取全部满足规则的状态与过程；若原菜单只供应其中一部分，则得到量子子理论，不能由表示定理跳成全部过程实际可实现。没有把这些条件藏进局部面积式。

与项目的衔接也分清层级：C113 的新结果已将仅正分支的有限校准缺口转为对平方根量子分支的 diamond 距离界；本稿补上同一有限接续词的误差传播。FIB III 的新结果在同一真实历史下实现精确秩三压缩，但尚未证明精确秩二，且其有序比较型不能直接识别成量子正内积。

“公理内生”的严格版本是：**约束的两端都由同一个 $\Omega$ 的内容、比较和响应定义，再证明它们能否一致。**这消除了外部赋予的复数载体，却没有消除逻辑前提。任意整体是否供应这些内部结构，仍是需要项目原生协议证明的实例化问题。

## 目录

- [1. 接到项目最新进展的哪一个位置](#section-1)
- [2. 一个完整候选：把定义的相容写清楚](#section-2)
- [3. 反着推正性：零关系不能在整体中复活](#section-3)
- [4. 由二元关系到三维：完整刚性证明](#section-4)
- [5. 不遵守会怎样：七维反例和有限分离](#section-5)
- [6. 三维是哪一个更大结构的一部分](#section-6)
- [7. 复数、相位和量子球怎样由内部产生](#section-7)
- [8. 从几何重叠到概率：密度矩阵和 Born 规则](#section-8)
- [9. 从一个基本块到整体：复合、相位与纠缠](#section-9)
- [10. 过程公理：参考正性、Kraus 表示与更新](#section-10)
- [11. 动力学：什么时候得到 Schrödinger 方程](#section-11)
- [12. 共同来源如何内生地给出全部有限态](#section-12)
- [13. 回到实际校准：同一有限历史的误差定理](#section-13)
- [14. 完成了哪一门理论，保留了哪些前件](#section-14)
- [参考文献](#references)

<a id="section-1"></a>

## 1. 接到项目最新进展的哪一个位置

本稿固定在 `dev@a41b3dc77a15de8ceeabfcba85d60b17bad3df6b`，并直接核读有关文件。最新提交标题本身不能替代内容核查。本轮的相关推进主要来自 C113 第 20–22 节与 FIB III 附录第 136–140 节 [1](#ref-repo113)、[2](#ref-repofib)。从首先核读的 `5ccf2096` 到此版本只新增两次提交，调整了两份振子定义的状态记录；重新下载核对表明上述核心文件字节未变。这不等于新增了振子本征、完备性或算子闭包定理。

### 1.1 C113：不预设完全正，也能控制到量子分支的距离

对输入维数 $d$、输出维数 $k$，令 $T$ 只是正的复线性映射，且 $T^\dagger(I)=E\in[0,I]$。指定同一个等距嵌入 $J$、同一份实际有限精确 projective 2-design 以及完整输出读回。设

$$
L(X)=J\sqrt E\,X\sqrt E\,J^\dagger,\quad
r=\operatorname{rank} E,\quad M=\lVert E\rVert,\quad t=\operatorname{Tr} E,
\quad D=d(d+1)\delta,
$$

其中 $\delta$ 是同一校准的理想最优分数与实际分数之差。项目证明 $D\ge0$，并得到

<a id="eq-repobound"></a>

$$
\lVert T-L\rVert_{\diamond}\le
\min\left\{t+M,\sqrt{2kMD},2\sqrt{dMD},
(\sqrt{2r}+3)\sqrt{MD}\right\}.
\tag{1}
$$

该界不含最小正本征值的倒数，允许奇异效应和矩形输出。$E=0$ 时两分支均为零。$D=0$ 时迫使 $T=L$，因而完全正是结论；$D>0$ 再小，也不保证 $T$ 本身完全正。第 [13](#sec-calibration) 节给出其反例及有限历史推论。

这比“先假定全部原过程是量子信道再校准”更接近原生桥，但实际设计、支持读口和固定嵌入仍是前提，不能由一个分数代替资源供应证明。

### 1.2 FIB III：同一历史中的三维压缩，不等于量子三维

新附录保留同一个 $\theta$、源、热半群 $P=T_d$、三个时刻 $2d,3d,4d$、同一联合分区和终端因子 $q_E=P1_C$。实际有序比较为

$$
Q_E(u,v)=\int g\,u\,P(q_Ev)\,\,\mathrm d m.
$$

它一般不对称。用一个真实符号分裂把 $S$ 分为 $D_0,D_1$，保留其余格子后，项目构造可逆换基矩阵 $J$，满足

$$
J^{\mathsf T}A^D J=\operatorname{diag}(A_E,0),\qquad
\operatorname{rank} A^D=\operatorname{rank} A_E\le3,
$$

并证明每个原 $\theta$ 都有精确秩三实例。实际行列式像为区间，包含正值，且零属于其闭包；**尚未证明零被实际达到**，所以精确秩二仍未解决。非零角向的负指数不能冒充同时满足所需矩条件和有序交叉条件的零角向见证。

对本轮最有用的启示是：三维提升必须保留**同一份历史及其交叉关系**。统计矩阵的秩三、Bloch 标签的实维数三、振幅空间的复维数二是三个不同命题。本稿不会把它们仅凭数字相同连接起来。

### 1.3 与前一轮及 C117 的关系

前一轮 C122 用两种响应的曲率相消构造有限复矩阵代数；项目 C117 在欧氏二元块中已有旁观方向条件、三维性和共同来源讨论 [3](#ref-repo117)。本轮把局部前端改写成“面积不丢失”和“同一关系由同一次运动运输”，并给出七维反例与有限误差见证。它在该类欧氏基本块中与既有结论相容，**没有证明这是严格更弱、绝对最少或首次发现的公理**。

<a id="section-2"></a>

## 2. 一个完整候选：把定义的相容写清楚

### 定义 2.1（有限内部比较接口）

以 $\Omega$ 表示包含被比较内容、比较装置、记录与观察者的总结构。选定一个有限接口，允许已声明内容的全部有限带符号实线性组合，形成有限维实空间 $E$。

给定对称双线性比较 $B:E\times E\to\mathbb R$，记 $q(x)=B(x,x)$，不预设正性。存在一个内部正标尺 $e$，使 $q(e)>0$。允许归一化 $q(e)=1$。

给每个内容 $x$ 一个内部响应 $D_x\in\operatorname{End}_\mathbb R(E)$，标签映射 $x\mapsto D_x$ 线性，满足

<a id="eq-response"></a>

$$
B(D_xy,z)+B(y,D_xz)=0,\qquad D_xx=0.
\tag{2}
$$

第一式说响应保持同一比较，第二式说由自己生成的转向不转动自己。定义 $x\times y:=D_xy$。此时尚未假定 Jacobi、三维性、复数或 Hilbert 空间。

### 定义 2.2（候选 $\Omega Q$-001 的局部保真律）

对被声明为初等的同一内部比较接口，要求以下三个相容关系：

<a id="eq-Z"></a>

$$
\begin{aligned}
q(x)=0&\ \Longrightarrow\ B(x,y)=0\quad\text{对全部 }y; \tag{Z}
\end{aligned}
$$

<a id="eq-A"></a>

$$
\begin{aligned}
q(D_xy)+B(x,y)^2&=q(x)q(y); \tag{A}
\end{aligned}
$$

<a id="eq-T"></a>

$$
\begin{aligned}
U_x(t)(y\times z)&=(U_x(t)y)\times(U_x(t)z),\quad
U_x(t)=e^{tD_x}. \tag{T}
\end{aligned}
$$

零关系条件作用于全部已纳入接口的带符号组合。运输条件作用于同一个二元关系 $(y,z)$，由第三个内部标签 $x$ 运输它。它是主动响应的相容条件，不能以被动换坐标恒等式替代。

这是一个完整候选的一组精确条款，不把三条独立数学承诺包装成“没有任何前提的一句话”。后文发展全部有限量子接口时，还将逐项列出概率、复合及操作的连接条件。

本稿的 $W$ 是满足面积饱和的**初等比较块**，不是整个 $\Omega$ 的全部可观测量空间。“二元”表示比较两份内容，并未预先规定三维；三维将由定理推出。面积饱和本身选择了这一类基本块。这里尚未证明原生 $\Omega$ 如何识别或生成这些初等接口；把“初等”定义为满足面积式的接口，只完成分类，没有完成供应证明。

不能将 (A) 强加给一般高维系统的全部无迹可观测量。例如三能级系统中的 $a=\operatorname{diag}(1,-1,0)$ 与 $b=\operatorname{diag}(1,1,-2)$ 非零、迹内积正交，却对易。若 $D_ab=(ab-ba)/(2i)$，则响应为零而面积不为零。因此高维量子系统必须由基本块的相容复合构造，不能声称所有矩阵对都直接满足 (A)。

<a id="section-3"></a>

## 3. 反着推正性：零关系不能在整体中复活

### 定理 3.1（零的定义相容等价于半正定性）

在定义 2.1 的实双线性接口中，正标尺存在时，以下三项等价：

1. $q(x)\ge0$ 对全部 $x$ 成立；

2. 零关系条件 (Z)；

3. $x\sim y\Longleftrightarrow q(x-y)=0$ 是传递关系。

此时 $N=\{x:q(x)=0\}=\operatorname{Rad} B$ 是线性子空间，$W=E/N$ 上诱导的比较正定。

**证明。**
先设 $B$ 半正定且 $q(x)=0$。对任意实 $t$，

$$
0\le q(x+ty)=2tB(x,y)+t^2q(y).
$$

选择足够小且符号合适的 $t$，可知必须 $B(x,y)=0$。故 (Z) 成立，零集合等于根空间，是线性空间，$\sim$ 传递。

反过来，若存在 $v$ 使 $q(v)<0$，用正标尺做代数正交化：

$$
w=v-\frac{B(e,v)}{q(e)}e,\qquad
B(e,w)=0,\qquad q(w)=q(v)-\frac{B(e,v)^2}{q(e)}<0.
$$

令 $\lambda=\sqrt{q(e)/(-q(w))}$。那么

$$
q(e+\lambda w)=0,\qquad B(e+\lambda w,e)=q(e)>0,
$$

违反 (Z)。所以 (Z) 排除所有负平方。

若仅假定传递性，令 $x=e+\lambda w$、$y=e-\lambda w$。两者均为零平方，故 $x\sim0\sim-y$，但 $q(x+y)=4q(e)>0$，同样矛盾。最后商掉根空间，内积与代表元无关且正定。有限维自动完备。证毕。

正标尺不可省略：负定比较也没有非零零向量，会平凡满足 (Z)。因此这里没有从一个无符号定义里凭空选出正号。将 (Z) 称为“内生正性”，准确含义是正性被等价重写成内部不可分辨的相容，**不是已经证明任意原生比较都满足它**。

### 引理 3.2（响应双变量都能下降到零商）

式 [(2)](#eq-response) 与 (Z) 保证

$$
\overline D_{[x]}[y]=[D_xy]
$$

在 $W=E/N$ 上定义良好。

**证明。**
极化 $D_{x+y}(x+y)=0$ 得 $D_xy=-D_yx$。若 $n\in N$，则
$B(D_xn,z)=-B(n,D_xz)=0$，故 $D_xn\in N$；而 $D_ny=-D_yn\in N$。改变任意一个输入的代表元，都只改变一个零方向。

以下均在商空间中书写，使用 $\langle x,y\rangle$ 和 $\lVert x\rVert$，并省去横线。

### 例 3.3（每三个都能提升，四个却没有共同实现）

设四个形式标签的比较表为

$$
G_{ii}=1,\qquad G_{ij}=-\frac12\quad(i\ne j).
$$

每个三阶主块的本征值为 $0,3/2,3/2$，能用复二维空间中的三个实向量实现；每个二阶块也正定。但完整 $G$ 的本征值为

$$
-\frac12,\quad\frac32,\quad\frac32,\quad\frac32,
$$

所以不能共同实现于正内积空间。

失败的实际两元关系十分具体。令 $u=e_1+e_2+e_3$，前三份内容要求 $q(u)=0$，第四份内容却要求

$$
B(u,e_4)=-\frac32\ne0.
$$

也就是局部已经相消的关系，在另一个内部读口下复活。进一步 $q(u+e_4)=-2$。问题不在少画了一幅局部图，而在这些局部图没有保留同一份零关系。

### 命题 3.4（饱和局部片的共同拼接）

给定 Hermitian 比较表

$$
G=\begin{pmatrix}A&C\\mathbb C^*&D\end{pmatrix},\qquad A>0,\quad A\in M_k(\mathbb C).
$$

若每个“固定基标签加一个新标签”的块均半正定且秩仍为 $k$，并且其局部零关系在全部其他读口下保持为零，则

$$
D=C^*A^{-1}C,\qquad
G=\begin{pmatrix}I\\mathbb C^*A^{-1}\end{pmatrix}A
\begin{pmatrix}I&A^{-1}C\end{pmatrix}\ge0,
\quad\operatorname{rank} G=k.
$$

**证明。**
设 $c_j$ 是对应新标签的列，局部秩饱和给 $D_{jj}=c_j^*A^{-1}c_j$。残差
$r_j=e_j-\sum_{\ell}(A^{-1}c_j)_\ell e_\ell$ 为零平方；其与全部标签的比较必须为零，故所有交叉项被固定为 $D_{jh}=c_j^*A^{-1}c_h$。因子分解随即成立。

这里复版本仅是已给定复比较时的拼接引理，不是局部核心偷放复数的前提。取 $k=2$ 时，它说明固定同一对振幅基和全部三态片段，确可在零关系相容后拼成共同 qubit；未饱和情形则仍有 Schur 余量及交叉自由。

<a id="section-4"></a>

## 4. 由二元关系到三维：完整刚性证明

由斜对称响应及 $D_xy=-D_yx$，三线性型

$$
T(x,y,z)=\langle x\times y,z\rangle
$$

全反对称。因此 $x\times y\perp x,y$。面积式成为

<a id="eq-area"></a>

$$
\lVert x\times y\rVert^{2}=\lVert x\rVert^{2}\lVert y\rVert^{2}-\langle x,y\rangle^{2}.
\tag{3}
$$

对单位 $x$，映射 $F_x(y)=(\langle x,y\rangle,D_xy)$ 是从 $W$ 到 $\mathbb R\oplus W$ 的等距映射。其含义是重合分量与实际转向分量恰好用完同一比较量；这不是归一化本身能推出的事实。

### 引理 4.1（面积律已经给出每对的三维闭合）

面积式推出

<a id="eq-Dsquare"></a>

$$
\begin{aligned}
D_x^2y&=x\langle x,y\rangle-\lVert x\rVert^{2}y,
\end{aligned}
\tag{4}
$$

<a id="eq-polar"></a>

$$
\begin{aligned}
D_uD_v+D_vD_u&=uv^{\mathsf T}+vu^{\mathsf T}-2\langle u,v\rangle I.
\end{aligned}
\tag{5}
$$

若 $u,v$ 正交且为单位向量，$w=u\times v$，则 $u,v,w$ 正交归一，且

$$
u\times v=w,\qquad v\times w=u,\qquad w\times u=v.
$$

因此每对独立内容都在 $\operatorname{span}\{u,v,w\}$ 中形成标准三维叉积片段。

**证明。**
由 $D_x^*=-D_x$，有
$-\langle y,D_x^2y\rangle=\lVert x\rVert^{2}\lVert y\rVert^{2}-\langle x,y\rangle^{2}$。
关于 $y$ 极化，得到 [(4)](#eq-Dsquare)；再关于 $x$ 极化，得到 [(5)](#eq-polar)。面积与正交性给 $w$ 是单位法向；将 $y=v$ 或交换 $u,v$ 代入 [(4)](#eq-Dsquare)，立即得到循环乘法表。

### 引理 4.2（运输相容恰好给出导子相容）

有限维中 (T) 等价于

<a id="eq-jacobi"></a>

$$
D_x(y\times z)=(D_xy)\times z+y\times(D_xz),
\qquad [D_x,D_y]=D_{x\times y}.
\tag{6}
$$

**证明。**
对 (T) 在 $t=0$ 求导，得到第一式；移项就是第二式。反过来，若第一式成立，对
$U_x(-t)((U_x(t)y)\times(U_x(t)z))$ 求导为零，故它等于初值 $y\times z$，得到 (T)。

式 [(6)](#eq-jacobi) 是 Jacobi 恒等式的响应形式。仅知道全部 $D_x$ 都斜对称，并不能免费得到它。

### 定理 4.3（三维刚性，不使用叉积维数分类）

满足候选局部条件的 $W$，其维数只能为 $1$ 或 $3$。若存在两份线性无关的有效内容，则

$$
\boxed{\dim_\mathbb R W=3,\qquad x\times y\text{ 是某个取向下的标准叉积。}}
$$

**证明。**
取正交单位 $u,v$，令 $w=u\times v$。它们是正交单位三元组。
假设存在单位向量 $z\perp u,v,w$。由 [(5)](#eq-polar)，

$$
D_uD_vz=-D_vD_uz.
$$

再由运输相容，

<a id="eq-one-two"></a>

$$
D_wz=[D_u,D_v]z=2D_uD_vz.
\tag{7}
$$

面积式给 $\lVert D_wz\rVert=1$ 与 $\lVert D_vz\rVert=1$；又因为

$$
\langle u,D_vz\rangle=\langle u\times v,z\rangle=\langle w,z\rangle=0,
$$

同一面积式给 $\lVert D_uD_vz\rVert=1$。式 [(7)](#eq-one-two) 却要求 $1=2$，矛盾。因此没有第四个独立方向。

三维中的交替三线性型是体积形式的常数倍；面积式把该常数的绝对值固定为一，取向吸收其符号。一维的零乘积直接满足条件。正标尺保证 $W\ne0$；若移去正标尺要求，零维亦为退化代数解。证毕。

三维不是先画好再称为量子。面积律先替每对内容补出一个法向。真正排除七维的，是不同三维片段都由同一内部响应运输：如果还有第四个独立方向，同一转动按一条规则只能响应一份，按另一条规则却必须响应两份。

<a id="section-5"></a>

## 5. 不遵守会怎样：七维反例和有限分离

### 例 5.1（每对都正确，整体运输仍会反向）

取七维虚八元数空间 $W=\operatorname{Im}\mathbb O$，

$$
x\times y=\frac{xy-yx}{2}.
$$

它满足正内积、斜对称响应及精确面积式，每对独立元素也产生标准三维片段，但一般不满足 Jacobi。八元数与叉积性质见 Baez 原文 [5](#ref-baez)。

采用作者乘法表，相关条目为

$$
e_1e_2=e_4,\quad e_2e_3=e_5,\quad e_1e_3=e_7,\quad
e_1e_5=e_6,\quad e_4e_3=e_2e_7=-e_6,\quad e_4e_7=-e_5.
$$

选内部运输标签 $e_1$，被运输的两个元为 $e_2,e_3$。一条路径给

$$
D_{e_1}(e_2\times e_3)=e_6,
$$

另一条路径给

$$
(D_{e_1}e_2)\times e_3+e_2\times(D_{e_1}e_3)=-2e_6.
$$

两者残差为 $3e_6$。令 $U_t=e^{tD_{e_1}}$，可直接算出

<a id="eq-oct-one"></a>

$$
\begin{aligned}
U_t(e_2\times e_3)&=\cos t\,e_5+\sin t\,e_6,
\end{aligned}
\tag{8}
$$

<a id="eq-oct-two"></a>

$$
\begin{aligned}
(U_te_2)\times(U_te_3)&=\cos(2t)e_5-\sin(2t)e_6.
\end{aligned}
\tag{9}
$$

当 $t=\pi/3$ 时，两条路径给出严格相反的答案。

```latex
\begin{tikzpicture}[scale=2.1,>=Latex]
\draw[gray!40] (0,0) circle (1);
\draw[->,gray] (-1.3,0)--(1.35,0) node[right] {$e_5$};
\draw[->,gray] (0,-1.2)--(0,1.25) node[above] {$e_6$};
\draw[->,very thick,accent] (0,0)--(60:1) node[above right,align=left,font=\small] {先形成关系\\再运输};
\draw[->,very thick,warm] (0,0)--(240:1) node[below left,align=right,font=\small] {先运输两端\\再形成关系};
\draw[->,accent] (.35,0) arc (0:60:.35);
\node[accent,font=\small] at (.49,.29) {$\pi/3$};
\end{tikzpicture}
```

 图中是同一七维模型在 $e_5,e_6$ 平面的精确计算，而非示意性的误差方向。

八元数并没有数学矛盾；它违反的是本候选要求的*自生成*运输保关系。八元数确有自同构群 $G_2$，但一般的 $D_x:y\mapsto x\times y$ 不属于其导子。不能因为更大的结构存在，就把任意内部转向当成该结构的自同构。

### 定理 5.2（精确面积条件下的有限运输分离）

只假定正内积、响应条件和精确面积式，若 $\dim W\ge4$，则存在单位 $u,v,z$，使

$$
\lVert [D_u,D_v]z-D_{u\times v}z\rVert\ge1.
$$

更具体地，令

$$
\mathcal E(t)=U_u(t)(v\times z)-(U_u(t)v)\times(U_u(t)z),
$$

可选这些单位方向使

$$
\lVert \mathcal E(t)\rVert\ge |t|-\frac52t^2,\qquad
\lVert \mathcal E(1/5)\rVert\ge\frac1{10}.
$$

**证明。**
用上一节的 $u,v,w,z$，无须运输相容，也有 $\lVert [D_u,D_v]z\rVert=2$ 与 $\lVert D_wz\rVert=1$，反三角不等式给第一式。

有 $\mathcal E(0)=0$，$\mathcal E'(0)=[D_u,D_v]z-D_{u\times v}z$。单位 $u$ 给 $\lVert D_u\rVert=1$，面积式又给 $\lVert a\times b\rVert\le\lVert a\rVert\lVert b\rVert$。对 $\mathcal E$ 两次微分，各项估计合计为 $1+1+2+1=5$，所以 $\lVert \mathcal E''(t)\rVert\le5$。Taylor 积分余项给所述下界。

这是**面积精确**且归一化固定时的数学间隔，不是同时带面积噪声的完整稳定性定理。实际实验还必须供应同一个真实控制和相应参数，不能把数学指数直接冒充可执行装置。

<a id="section-6"></a>

## 6. 三维是哪一个更大结构的一部分

### 定义 6.1（从二元比较直接生成实乘法）

在已证明的 $W\cong\mathbb R^3$ 上，令 $Q=\mathbb R\oplus W$，定义

<a id="eq-quat"></a>

$$
(a,x)(b,y)=\bigl(ab-\langle x,y\rangle,\ ay+bx+x\times y\bigr).
\tag{10}
$$

定义 $(a,x)^*=(a,-x)$，$N(a,x)=a^2+\lVert x\rVert^2$。

### 定理 6.2（比较和差额共同组成结合的四元数）

乘法 [(10)](#eq-quat) 有单位 $(1,0)$，结合，且

$$
pq\text{ 的共轭为 }q^*p^*,\qquad q^*q=N(q)1,
\qquad N(pq)=N(p)N(q).
$$

因此 $Q\cong\mathbb Q$，其单位范数元集合是 $S^3$。

**证明。**
单位、共轭及 $q^*q$ 可直接展开。范数乘法性只用面积式和正交性：展开后标量与向量的交叉项抵消，剩下
$(a^2+\lVert x\rVert^2)(b^2+\lVert y\rVert^2)$。

结合子三线性，含单位的项为零，故只需检查纯虚 $x,y,z$。其标量部分由交替三线性型相消；向量部分为

$$
-\langle x,y\rangle z+\langle y,z\rangle x+(x\times y)\times z-x\times(y\times z)=0,
$$

最后一步使用已得到的三维向量三重积公式。选取正交正向三元组，乘法表即 $i^2=j^2=k^2=ijk=-1$。

较大结构因此十分简洁：每对的重合提供乘积标量部，每对的有向差额提供向量部；三维运输相容恰好让四维乘法的括号不再影响结果。不是先输入四元数，再回头找到三维。

### 6.1 旧的曲率相消成为本轮的推论

在 $V=\mathbb R1\oplus W$ 定义对称响应

$$
(a,x)\circ(b,y)=(ab+\langle x,y\rangle,ay+bx),\qquad
R_x(s,z)=(\langle x,z\rangle,sx),\quad D_x(s,z)=(0,x\times z).
$$

直接计算得到

<a id="eq-lorentz"></a>

$$
[D_x,D_y]=D_{x\times y},\quad
[D_x,R_y]=R_{x\times y},\quad
[R_x,R_y]=-D_{x\times y}.
\tag{11}
$$

所以前一轮的 $[R_x,R_y]+[D_x,D_y]=0$，现在是在这个基本块内由面积与运输证明的结论。$R,D$ 共同给出 $\mathfrak{so}(1,3)$ 的标准结构。其自然锥是

$$
\{(a,x):a\ge\lVert x\rVert\},
$$

后文会识别为 $2\times2$ 正矩阵锥。这个 Lorentz 几何属于比较锥，尚未证明它就是物理时空。

<a id="section-7"></a>

## 7. 复数、相位和量子球怎样由内部产生

### 定义 7.1（内部复参照）

选一个内部单位方向 $u\in W$。因 $u^2=-1$，

$$
\mathbb C_u=\{a+bu:a,b\in\mathbb R\}\subset Q
$$

是内部复数子域。把 $Q$ 看作右 $\mathbb C_u$ 模，定义

$$
\pi_u(z)=\frac12(z-u z u),\qquad
h_u(p,q)=\pi_u(p^*q).
$$

### 定理 7.2（同一实四维结构就是复二维 Hilbert 空间）

若 $v\perp u$ 也是单位方向，则每个 $q\in Q$ 唯一写作
$q=\alpha+v\beta$，$\alpha,\beta\in\mathbb C_u$，且

$$
h_u(\alpha+v\beta,\gamma+v\delta)
=\bar\alpha\gamma+\bar\beta\delta.
$$

故 $\mathcal H_u=(Q,h_u)\cong\mathbb C_u^2$。单位四元数 $p=\gamma+v\delta$ 的左乘在此基下为

$$
L_p=\begin{pmatrix}\gamma&-\bar\delta\\\delta&\bar\gamma\end{pmatrix}\in SU(2),
$$

且所有 $SU(2)$ 矩阵都以此形式出现。

**证明。**
$1,u,v,vu$ 是实基，故分解唯一。用 $uv=-vu$ 展开 $p^*q$，沿 $1,u$ 的投影恰为所列 Hermitian 形式，且 $h_u(q,q)=N(q)>0$。左乘矩阵由同样的乘法展开得到；单位范数恰给列正交归一和行列式一。

不同 $u$ 是内部参照选择，不是绝对指定的复轴。若 $u'=s u s^{-1}$，其中 $N(s)=1$，定义

$$
\phi_s(a)=s a s^{-1},\qquad T_s(q)=q s^{-1}.
$$

则 $T_s(qa)=T_s(q)\phi_s(a)$，并有

$$
h_{u'}(T_sp,T_sq)=\phi_s(h_u(p,q)).
$$

因此不同内部参照给出等价复描述。旋转对称性并不挑选一个唯一的 $u$；可证明的是选择等价，而不是选择不存在。

### 定理 7.3（Hopf 纤维、射线与 Born 重叠形状）

对单位 $q\in Q$ 定义

$$
r(q)=-q u q^*\in S^2.
$$

这个映射满射，纤维为 $q\{e^{\theta u}\}$，从而

<a id="eq-hopf"></a>

$$
S^3/U(1)\cong S^2\cong\mathbb C P^1.
\tag{12}
$$

任意单位 $p,q$ 满足

<a id="eq-born-geometry"></a>

$$
\boxed{\ |h_u(p,q)|^2=\frac{1+\langle r(p),r(q)\rangle}2\ }.
\tag{13}
$$

**证明。**
四元数共轭实现三维旋转，故映射满射；也可对任意 $r\ne u$ 取一个将 $-u$ 转向 $r$ 的轴角四元数直接构造。两份单位四元数给同一 $r$，当且仅当它们的右比值与 $u$ 对易。与 $u$ 对易的虚部 $x$ 必满足 $x\times u=0$，面积式迫使 $x\parallel u$，故纤维恰为 $\mathbb C_u\cap S^3=U(1)$。

令 $p^*q=a+x$。则
$|h_u(p,q)|^2=a^2+\langle x,u\rangle^2$。由四元数乘法展开，

$$
\langle u,(a+x)u(a-x)\rangle=2(a^2+\langle x,u\rangle^2)-1.
$$

左边正是 $\langle r(p),r(q)\rangle$，得到 [(13)](#eq-born-geometry)。

球上两方向夹角为 $\theta$ 时，式 [(13)](#eq-born-geometry) 为 $\cos^2(\theta/2)$。这里先得到的是重叠的几何形状；将其解释成实验频率，还需下一节的概率接口。

### 7.1 泡利代数由同一运算生成

令内部复乘为 $J=R_u:q\mapsto qu$，定义 $A_x=L_xR_u$。注意这里 $R_u$ 是四元数右乘，区别于上一节的对称响应 $R_x$。$L_x$ 与 $R_u$ 对易且均斜自伴，因此 $A_x$ 自伴。计算给

<a id="eq-pauli"></a>

$$
A_xA_y=\langle x,y\rangle I+J A_{x\times y},\qquad A_x^2=\lVert x\rVert^2 I.
\tag{14}
$$

对非零 $x$，取 $y\perp x$，可用 $A_y$ 将正负本征空间互换，所以 $\operatorname{Tr} A_x=0$。于是 $I,A_{e_1},A_{e_2},A_{e_3}$ 是全部 $\operatorname{Herm}_2(\mathbb C_u)$ 的实基；它们的复线性包络是 $M_2(\mathbb C_u)$。

对单位 $q$ 及单位方向 $n\in S^2$，

$$
h_u(q,A_xq)=\langle x,r(q)\rangle,\quad
P_n=\frac{I+A_n}{2},\quad
\rho_q=\frac{I+A_{r(q)}}2=\lvert q\rangle\langle q\rvert.
$$

一般 $aI+A_x$ 的本征值为 $a\pm\lVert x\rVert$，所以正性恰好是 $a\ge\lVert x\rVert$。迹为一的正矩阵构成实三维单位球，极点是球面；其作为全部数学状态的解释由下一节给出，不代替实际可制备性。

内部运输的半角为

<a id="eq-half-angle"></a>

$$
U_x(t)y=e^{tx/2}\,y\,e^{-tx/2}.
\tag{15}
$$

这是因为四元数交换子为 $2x\times y$。转动 $2\pi$ 在自旋振幅上得到 $-1$，在射线与球方向上回到原处。

### 7.2 这幅几何图还具有哪些性质

在局部坐标

$$
\psi(\theta,\varphi)=
\begin{pmatrix}\cos(\theta/2)\\e^{i\varphi}\sin(\theta/2)\end{pmatrix}
$$

中，直接微分得到投影度量与相位联络

$$
\begin{aligned}
\,\mathrm d s^2&=h(\,\mathrm d\psi,\,\mathrm d\psi)-|h(\psi,\,\mathrm d\psi)|^2
=\frac14(\,\mathrm d\theta^2+\sin^2\theta\,\,\mathrm d\varphi^2),
\end{aligned}
\tag{16}
$$

$$
\begin{aligned}
\mathcal A&=\operatorname{Im} h(\psi,\,\mathrm d\psi)=\frac{1-\cos\theta}{2}\,\mathrm d\varphi,
\qquad \,\mathrm d\mathcal A=\frac12\sin\theta\,\,\mathrm d\theta\wedge\,\mathrm d\varphi.
\end{aligned}
\tag{17}
$$

因此纯态几何是 Fubini–Study 半径 $1/2$ 的圆球，局部曲率积分给几何相位：按水平提升约定，相位为包围立体角的负一半，模 $2\pi$。总曲率积分为 $2\pi$，反映 Hopf 纤维非平凡；不存在覆盖整个球面的单一连续相位选择。若存在全局截面，将得到 $S^3\cong S^2\times S^1$，与两者的基本群不同矛盾。几何量子力学的标准背景见  [9](#ref-ashtekar)。

所以必须保留合法的物理环相位。运输相容要求同一关系的两个计算路径一致，**不是要求所有物理闭环相位都等于一**。一般物理时间演化未必是此联络的水平提升；这里得到的是几何部分，总相位还可含动力学部分。一个单位四元数作为“制备某个态”的代表，与它作为“作用在所有输入上的门”，也不是同一个等价关系：固定参照下的右相位不改制备态，却一般会改变整个门。

<a id="section-8"></a>

## 8. 从几何重叠到概率：密度矩阵和 Born 规则

到这里已经构造 $M_2(\mathbb C_u)$，但一个几何等式不是概率解释。下面明确写出从量子基本块发展操作理论的接口，不把它们暗藏为结论。

### 定义 8.1（效果与内部拆并相容）

在已构造的有限矩阵接口 $M_d(\mathbb C)$ 上，效果是 $0\le F\le I$。状态读出为函数 $f$，满足

$$
0\le f(F)\le1,\qquad f(I)=1,
\qquad f(F+G)=f(F)+f(G)\quad(F,G\ge0,\ F+G\le I).
$$

相同效果在不同拆并中使用同一个 $f(F)$。这要求*全部声明效果*的非情境拆并，不仅是某几组投影的加和。是否全部数学效果都由原菜单供应，须另证。

### 定理 8.2（效果拆并唯一给出密度矩阵）

上述条件等价于存在唯一 $\rho\ge0$、$\operatorname{Tr}\rho=1$，使

<a id="eq-born"></a>

$$
\boxed{f(F)=\operatorname{Tr}(\rho F).}
\tag{18}
$$

此结论包括 $d=2$。纯态是秩一投影；其对秩一效果的概率为平方内积。

**证明。**
对固定 $F$，有限拆分先给有理比例齐次性；正性给单调性，用有理上下夹逼得到实比例齐次性。对 $A\ge0$，选 $\lambda>0$ 且 $\lambda\ge\lVert A\rVert$，定义

$$
\Phi(A)=\lambda f(A/\lambda).
$$

齐次性使定义与 $\lambda$ 无关，足够大的共同缩放使 $\Phi$ 在正锥上可加。再令 $\Phi(A-B)=\Phi(A)-\Phi(B)$，它与正负分解无关，从而得到 $\operatorname{Herm}_d(\mathbb C)$ 上的实线性泛函。

迹配对非退化，故存在唯一 Hermitian $\rho$ 使 $\Phi(X)=\operatorname{Tr}(\rho X)$。对任意向量 $v$，$\langle v\rvert\rho\lvert v\rangle=\Phi(\lvert v\rangle\langle v\rvert)\ge0$，所以 $\rho\ge0$；$\Phi(I)=1$ 给迹一。反方向直接验证。

若 $\rho$ 有至少两个正本征值，可以微量增减这两个值，写成两个不同状态的凸组合，故非极端；秩一状态的任何正分解都只能位于同一一维支持，因此是极端。最后代入 $\rho=\lvert q\rangle\langle q\rvert$、$F=\lvert p\rangle\langle p\rvert$，得到 $|h(p,q)|^2$。

这是效果版 Gleason 路线的有限维证明，标准原始来源见 Busch [6](#ref-busch)。在基本块中把 [(13)](#eq-born-geometry) 代入 [(18)](#eq-born)，便得到

$$
p(n\mid r)=\frac{1+n\cdot r}{2}=\cos^2(\theta/2).
$$

### 例 8.3（只要求投影加和，qubit 仍可有非 Born 赋值）

对单位 $n\in S^2$ 令 $P_n=(I+A_n)/2$，定义

$$
f(P_n)=\frac{1+n_z^3}{2}.
$$

它非负，且 $f(P_n)+f(P_{-n})=1$，满足全部二结果正交投影加和。然而它不是 $\operatorname{Tr}(\rho P_n)$：$f(P_{e_z})=1$ 已迫使 Born 状态沿 $e_z$，其他方向却不再线性。因此效果拆并条件不能省成一句“概率总和为一”。

### 推论 8.4（测量、期望和不确定关系）

一份有限测量是效果族 $F_i\ge0$、$\sum_iF_i=I$，其概率为 $p_i=\operatorname{Tr}(\rho F_i)$。若标签值为 $a_i\in\mathbb R$，其一阶可观测量为 $A=\sum_i a_iF_i$；尖锐测量对应 $A$ 的谱投影。

任意 Hermitian $A,B$ 满足

$$
\Delta_\rho A\,\Delta_\rho B\ge\frac12|\operatorname{Tr}(\rho[A,B])|.
$$

**证明。**
概率与期望来自线性。令 $A_0=A-\operatorname{Tr}(\rho A)I$、$B_0=B-\operatorname{Tr}(\rho B)I$，对半内积 $\operatorname{Tr}(\rho X^*Y)$ 使用 Cauchy–Schwarz，得
$\Delta A\Delta B\ge|\operatorname{Tr}(\rho A_0B_0)|$；其虚部是 $\operatorname{Tr}(\rho[A,B])/(2i)$，故得结论。

<a id="section-9"></a>

## 9. 从一个基本块到整体：复合、相位与纠缠

局部的内部 $\mathbb C_u$ 已构造出来，但每个窗口各自选一个复轴，尚不等于这些窗口共用同一个联合复标尺。完整候选需把**复数识别、乘法和联合读口**一起纳入整体相容。

### 定义 9.1（独立复合接口）

两份已构造矩阵接口 $M_m(\mathbb C)$、$M_n(\mathbb C)$ 的联合操作形成一个含单位的结合复 $*$-代数 $\mathcal B$。给定保持共同标量、单位与伴随的代数嵌入 $\iota_A,\iota_B$，其像互相交换，并共同生成 $\mathcal B$。

这是一项显式的独立复合前提：从原生过程去证明共同标量、联合有序乘法和这种生成性，仍是项目的整体桥。定义中没有先把联合空间规定为张量积。

### 定理 9.2（张量积由联合生成推出）

独立复合接口唯一给出

$$
\mathcal B\cong M_m(\mathbb C)\otimes M_n(\mathbb C)\cong M_{mn}(\mathbb C).
$$

**证明。**
交换性使 $a\otimes b\mapsto\iota_A(a)\iota_B(b)$ 成为 $*$-同态；生成性给满射。源代数 $M_m\otimes M_n\cong M_{mn}$ 是简单代数，核只能是零或全部；保持非零单位排除全部，故为同构。

从 qubit 开始，有限次独立复合给 $M_{2^k}(\mathbb C)$。如果接口还对已供应的支持投影角封闭，则秩 $d\le2^k$ 的角 $PM_{2^k}P\cong M_d(\mathbb C)$。再允许带经典记录的有限互斥直和，即得到

$$
\bigoplus_jM_{d_j}(\mathbb C),
$$

覆盖全部有限维复量子代数。相应状态由各块的正矩阵组成，总迹为一；经典概率权重由各块迹给出。投影角与全部经典记录的实际供应也是闭包假设，不是局部三维定理的隐含结论。

### 9.1 联合正性为何约束局部镜像

在单个 qubit 上，转置 $\Theta(X)=X^{\mathsf T}$ 保持正性和迹，表现为球面一次镜像。若只对联合系统的一侧执行转置，则对

$$
\lvert \Phi\rangle=\frac{\lvert 00\rangle+\lvert 11\rangle}{\sqrt2}
$$

有

$$
(\operatorname{id}\otimes\Theta)(\lvert \Phi\rangle\langle \Phi\rvert)=\frac12\operatorname{SWAP},
$$

其反对称方向本征值为 $-1/2$。因此在这个已供应的共同 Bell 关系上，不能把一侧镜像当作可任意执行的正过程。部分转置的原始判据见 Peres [8](#ref-peres)。

这说明联合关系可以检测局部相位取向的不相容。但它**没有**证明任意原生窗口都已供应 Bell 态、共同复中心及正确联合乘法；也不能把不同表示之间正确变换的换坐标，误判为实际非正过程。

### 9.2 边缘、纠缠与局部读口

由对全部局部效果要求

$$
\operatorname{Tr}\bigl(\rho_{AB}(F_A\otimes I)\bigr)=\operatorname{Tr}(\rho_A F_A)
$$

及迹配对唯一性，得到 $\rho_A=\operatorname{Tr}_B\rho_{AB}$。同理得到另一边缘。纯 Bell 态是纠缠态：若它是产品态混合，正性与秩一迫使每一项都落在同一 Bell 射线上，而该射线的系数矩阵秩二，不能是产品向量。

对参考侧任意完整操作 $\sum_j K_j^*K_j=I$，丢弃结果时

$$
\operatorname{Tr}_B\sum_j(I\otimes K_j)\rho_{AB}(I\otimes K_j^*)=\operatorname{Tr}_B\rho_{AB}.
$$

因此内部条件化改变条件描述，忽略记录则不改变远端边缘。这里的因果性是所声明独立复合接口的性质，未额外推导物理时空。

<a id="section-10"></a>

## 10. 过程公理：参考正性、Kraus 表示与更新

### 定义 10.1（内部过程接口）

一个分支对混合线性，因而由有限矩阵间的复线性映射 $T:M_d\to M_k$ 表示。要求它在全部声明的内部参考扩张后仍保持正性，且迹不增：

$$
(\operatorname{id}_r\otimes T)(X)\ge0\quad(X\ge0),\qquad T^\dagger(I)\le I.
$$

若所有维数 $r$ 均在接口中，此条件就是完全正性。实际供应全部参考，或至少足以检验该条件的参考，是有内容的前提。

### 定理 10.2（参考正性等价于 Kraus 分支）

假设声明的参考包括维数 $d$，并要求 $\operatorname{id}_d\otimes T$ 对*所有*正联合矩阵保持正性，而不仅检查乘积态或可分态。这样的分支恰为

<a id="eq-kraus"></a>

$$
T(X)=\sum_\alpha K_\alpha X K_\alpha^*,\qquad
\sum_\alpha K_\alpha^*K_\alpha\le I.
\tag{19}
$$

数学上，维数 $d$ 的参考已经足够。

**证明。**
令未归一化向量 $\lvert \Omega\rangle=\sum_i\lvert i\rangle\lvert i\rangle$，则参考正性给

$$
C_T=(\operatorname{id}_d\otimes T)(\lvert \Omega\rangle\langle \Omega\rvert)
=\sum_{ij}\lvert i\rangle\langle j\rvert\otimes T(\lvert i\rangle\langle j\rvert)\ge0.
$$

谱分解为 $C_T=\sum_\alpha\lvert v_\alpha\rangle\langle v_\alpha\rvert$。将 $v_\alpha$ 的输入索引与输出索引重排为矩阵 $K_\alpha$，比较每个 $ij$ 块，就得到 Kraus 形式。反之每项 $I\otimes K_\alpha$ 的共轭作用保持正性，因此所有参考扩张都正。迹不增等价于所列矩阵不等式。

这就是标准 Choi–Kraus 表示的有限维证明，见  [7](#ref-watrous)。若只有无参考的正性，上一节转置反例直接阻止结论。

一个测量仪器是一组分支 $T_i$，使 $\sum_iT_i$ 保迹。其效果为

$$
F_i=T_i^\dagger(I)=\sum_\alpha K_{i\alpha}^*K_{i\alpha},
$$

于是 $p_i=\operatorname{Tr}(\rho F_i)$，成功条件态为 $T_i(\rho)/p_i$。$p_i=0$ 时不定义该条件态。

### 定理 10.3（理想尖锐分支唯一给出 Lüders 更新）

设 $P$ 是投影，完全正分支 $T$ 的效果为 $P$。额外要求它不改变任何已位于 $P$ 支持内的态：

$$
T(\rho)=\rho\quad\text{若 }P\rho P=\rho.
$$

则

$$
T(X)=PXP,\qquad
\rho\longmapsto\frac{P\rho P}{\operatorname{Tr}(\rho P)}.
$$

**证明。**
$\sum_\alpha K_\alpha^*K_\alpha=P$ 蕴含每个 $K_\alpha=K_\alpha P$。对支持内任意纯态 $\lvert v\rangle\langle v\rvert$，正和
$\sum_\alpha\lvert K_\alpha v\rangle\langle K_\alpha v\rvert=\lvert v\rangle\langle v\rvert$ 迫使每个 $K_\alpha v$ 平行于 $v$。一个线性算子若把该子空间的每条射线都保持，必是其上的标量算子：对独立 $v,w$ 再检查 $v+w$ 即知标量相同。故 $K_\alpha=c_\alpha P$，且 $\sum|c_\alpha|^2=1$，从而得到结论。秩一时论证直接成立，$P=0$ 时所有分支为零。

仅有效果 $P$ 不够。例如 $T(\rho)=\operatorname{Tr}(P\rho)\sigma$，其中固定状态 $\sigma$ 支持于 $P$，是同效果、甚至重复检测必成功的分支，却通常重置了支持内的态。因此“相同概率”不等于“相同更新”；理想性必须有实际的中性定义。对一般 $E$，$\sqrt E\rho\sqrt E$ 也不是由效果本身唯一选出，而可由项目完整校准饱和来选出。

<a id="section-11"></a>

## 11. 动力学：什么时候得到 Schrödinger 方程

局部 $U_x(t)$ 的 $t$ 起初只是内部比较流参数。要谈物理演化，另要求给定连续的一参数可逆确定过程族 $\mathcal T_t$，正反过程均满足包含上述足够参考的正性，且 $\mathcal T_{s+t}=\mathcal T_s\mathcal T_t$。

### 定理 11.1（连续可逆量子过程的 Hamilton 形式）

在简单矩阵块 $M_d(\mathbb C)$ 上，上述条件推出存在自伴 $H$，使

$$
\begin{aligned}
\mathcal T_t(\rho)&=e^{-itH/\hbar}\rho e^{itH/\hbar},
\end{aligned}
\tag{20}
$$

$$
\begin{aligned}
i\hbar\frac{\,\mathrm d\rho}{\,\mathrm d t}&=[H,\rho].
\end{aligned}
\tag{21}
$$

对连续选定相位的纯态，可写

$$
i\hbar\frac{\,\mathrm d\psi}{\,\mathrm d t}=H\psi.
$$

**证明。**
在 Heisenberg 图像，$\Phi_t=\mathcal T_t^\dagger$ 是含单位完全正映射，逆映射亦如此。完全正的 Schwarz 不等式给
$\Phi_t(A^*A)\ge\Phi_t(A)^*\Phi_t(A)$；再对逆映射使用同一不等式，夹逼得等号。逆映射可逆，故原差也为零。极化等号得到 $\Phi_t(AB)=\Phi_t(A)\Phi_t(B)$，所以每个 $\Phi_t$ 是 $*$-自同构。

有限维连续一参数群有生成元 $\delta$，且乘法求导给导子律。用矩阵单位 $E_{ij}$，取

$$
K=\sum_i\delta(E_{i1})E_{1i}.
$$

将 $\delta$ 作用于 $E_{kl}E_{i1}$ 并求和，可直接验证 $[K,E_{kl}]=\delta(E_{kl})$，故 $\delta(A)=[K,A]$。伴随保持使 $K+K^*$ 与全部矩阵对易，是标量；减去中心实部后，可令 $K=iH/\hbar$、$H=H^*$。指数化得到 Heisenberg 演化，取迹对偶得到所列状态演化。

对于纯态，$\rho_t$ 已确定射线；选择去掉任意时间相位的代表向量，便得到向量方程。$H$ 的标量项只改变该整体相位。

这里 $\hbar$ 是把内部生成元与所选时间、能量标尺连接的转换常数，未由三维几何计算出其数值。给定具体 Hamiltonian、相互作用、空间传播和实际钟的供应，仍需要模型及实验输入。有限维也不能精确满足 $[Q,P]=i\hbar I$，因为交换子迹为零；无限维正则对易关系、无界算子域与场论需要额外发展。

<a id="section-12"></a>

## 12. 共同来源如何内生地给出全部有限态

在已经重构的一个简单 $d$ 维量子接口中，可以给“同一整体来源、不同内部读口”一个完整的构造，而不是仅作比喻。

### 定理 12.1（固定来源与目标依赖的内部滤波）

固定配对正交基，令

$$
\lvert \Phi_d\rangle=\frac1{\sqrt d}\sum_{i=1}^d\lvert i\rangle_A\lvert i\rangle_R.
$$

对任意密度矩阵 $\rho$，取参考侧滤波
$K_\rho=\sqrt{\rho^{\mathsf T}}$，则 $0\le K_\rho\le I$，且

<a id="eq-common-source"></a>

$$
\operatorname{Tr}_R\left[(I\otimes K_\rho)\lvert \Phi_d\rangle\langle \Phi_d\rvert
(I\otimes K_\rho)\right]=\frac{\rho}{d}.
\tag{22}
$$

成功率为 $1/d$，成功条件下的边缘态正好为 $\rho$。

**证明。**
对任意矩阵 $K$，展开最大关联向量可得

$$
\operatorname{Tr}_R\left[(I\otimes K)\lvert \Phi_d\rangle\langle \Phi_d\rvert
(I\otimes K^*)\right]=\frac{(K^*K)^{\mathsf T}}d.
$$

代入正自伴 $K_\rho$ 即得公式。密度矩阵本征值不超过一，所以滤波确为收缩；取迹得成功率。

目标信息进入了内部滤波 $K_\rho$ 的选择，不能说来源无需地址或控制就自动产生任何指定态。补上失败算子 $\sqrt{I-\rho^{\mathsf T}}$ 后，两个未归一化边缘是 $\rho/d$ 与 $(I-\rho)/d$；忽略成功记录仍为 $I/d$。

这证明的是：**如果同一个来源、所需滤波和成功读口已被供应，那么全部同维度态都可由内部条件化得到。**它不证明 $\Omega$ 有唯一本体态，也不提供一个覆盖所有无界维数的有限最大关联源。非平凡经典中心之间的相干与纯化还需额外接口，不能把简单矩阵块的纯来源结论直接搬到所有直和。

<a id="section-13"></a>

## 13. 回到实际校准：同一有限历史的误差定理

<a id="sec-calibration"></a>

项目最新 C113 的式 [(1)](#eq-repobound) 已对仅正分支成立。其 diamond 范数指对任意数学参考和任意输入矩阵的完全有界迹范数，**并不声称仅正的 $T\otimes\operatorname{id}$ 也输出正态**。这种区分使它可在尚未证明原分支完全正时提供距离控制。

### 例 13.1（近似饱和仍可不是完全正）

设 $E=a^2P$，$P$ 的秩为 $r\ge2$，$0<a\le1$。固定 $P$ 支持中的转置，令

$$
T_\varepsilon(X)=a^2J\left[(1-\varepsilon)PXP+
\varepsilon(PXP)^{\mathsf T}\right]J^*,\quad0<\varepsilon\le1.
$$

它正，且效果为 $E$；与平方根分支的校准缺口满足
$D=a^2\varepsilon r(r-1)\to0$。但其 Choi 矩阵在反对称方向的本征值是 $-a^2\varepsilon$，所以每个 $\varepsilon>0$ 都不是完全正。该反例也在 C113 新节中明确保留 [1](#ref-repo113)。

### 定理 13.2（固定实际有限接续词的 diamond 误差）

设 $T_i$ 为维数相容的原分支，$L_i$ 为对应理想完全正分支，且

$$
\lVert T_i-L_i\rVert_\diamond\le b_i,\qquad
\lVert L_i\rVert_\diamond\le M_i\le1.
$$

则

<a id="eq-word"></a>

$$
\boxed{\
\lVert T_N\cdots T_1-L_N\cdots L_1\rVert_\diamond
\le\prod_{i=1}^N(M_i+b_i)-\prod_{i=1}^NM_i=: \epsilon_N.
\ }
\tag{23}
$$

特别地，可以逐段使用 C113 的界作为 $b_i$。对平方根分支，$M_i=\lVert E_i\rVert$。

**证明。**
三角不等式给 $\lVert T_i\rVert_\diamond\le M_i+b_i$。精确接续差展开为

$$
T_N\cdots T_1-L_N\cdots L_1
=\sum_{i=1}^N T_N\cdots T_{i+1}(T_i-L_i)L_{i-1}\cdots L_1.
$$

对每项使用 diamond 范数次乘性，得到

$$
\sum_i b_i\prod_{j>i}(M_j+b_j)\prod_{j<i}M_j,
$$

它恰是式 [(23)](#eq-word) 右侧的标量乘积差。完全正 $L$ 的 diamond 范数等于 $\lVert L^\dagger(I)\rVert$：Stinespring 形式的上界由 $\lVert V\rVert^2$ 给出，达到效应最大本征值的正输入给下界。

这个范数证明对任意复线性 $T_i$ 都成立；原分支的正性只在把普通输入输出解释成态时使用。不能使用“正且迹不增，故 diamond 范数至多一”的错误步骤，转置已是反例。

### 推论 13.3（成功率可不同的条件态控制）

设归一化正输入 $\rho\ge0$、$\operatorname{Tr}\rho=1$ 经过原接续与理想接续，得到 $A,B\ge0$，成功率分别为 $p=\operatorname{Tr} A$、$q=\operatorname{Tr} B$。若 $p\ge p_0>\epsilon_N$，则 $q>0$，且

<a id="eq-postselect"></a>

$$
\left\lVert\frac Ap-\frac Bq\right\rVert_1
\le\min\left\{2,\frac{2\epsilon_N}{p_0}\right\}.
\tag{24}
$$

**证明。**
$\lVert A-B\rVert_1\le\epsilon_N$，故 $|p-q|\le\epsilon_N$。
再写

$$
\lVert A/p-B/q\rVert_1
\le\frac{\lVert A-B\rVert_1}{p}+\lVert B\rVert_1\left|\frac1p-\frac1q\right|
\le\frac{2\epsilon_N}{p_0}.
$$

两者都是密度矩阵，距离又至多二。

常数二不能一般去掉：取 $A=\operatorname{diag}(p_0-\epsilon,\epsilon)$、$B=\operatorname{diag}(p_0-\epsilon,0)$ 即达到 $2\epsilon/p_0$。若额外知道 $p=q$，才能改为 $\epsilon/p$。

本节是由项目单段界推得的**固定实际有限词**结论，不是仓库已经声明的全菜单认证，也不提供任意长度统一误差。精确 design、精确效果、同一 $J$、共同历史及读回仍是条件；若这些也带噪声，须另估其误差。它也不能替代 C118 的实际控制目录、支持返回和参考接入合同。

<a id="section-14"></a>

## 14. 完成了哪一门理论，保留了哪些前件

### 定理 14.1（候选的有限量子重构总表述）

给定满足 (Z)、(A)、(T)、且含两份独立有效内容的初等块。再给定：

1. 全效果非情境拆并；

2. 共同内部复标尺下的独立复合、支持投影角与有限经典直和；

3. 对混合线性的过程，供应至少输入维数的内部参考，并对全部正联合输入保持正性；

4. 对理想尖锐分支的支持内中性；

5. 在讨论时间演化时，另给连续可逆的物理时间群；

6. 数学接口的完备性：将全部满足所列规则的状态、效果和分支纳入理论。若声称原项目实际实现全理论，还须给出这些对象的供应证明。

则上述各节构造并证明一个完整的有限维复量子操作理论：有限复矩阵直和、密度矩阵、效果测量、Born 读出、张量复合、完全正仪器、理想 Lüders 更新和 Hamilton 动力学。通常的复量子理论在初等 qubit 块上满足局部条件，其有限矩阵系统满足所列整体接口；经典系统可作为退化边界。

若没有最后的完备性，只能说每个实际状态或过程落在所构造量子形式内，未必覆盖全部量子态与操作。特别是仅有局部制备与独立并置，可始终只制备可分态；矩阵代数的线性生成本身不会供应纠缠源或任意全局控制。这是表示、数学闭包与物理实现之间必须保留的区别。

subsection*{量子公理对应表}

| 通常的量子公理或结构 | 本稿得到它的推理 | 不能隐藏的输入 |
|---|---|---|
| 正内积 | 零不复活 $\Rightarrow B\ge0$，商去根空间 | 实线性比较、正标尺、全部组合的零相容 |
| 复二维 Hilbert 空间 | 面积与运输 $\Rightarrow\mathbb R^3\Rightarrow\mathbb Q\Rightarrow\mathbb C_u^2$ | 初等块范围、内部响应及非平凡性 |
| 射线与相位 | Hopf 纤维 $S^3/U(1)=S^2$ | 内部参照选择；选择等价而非唯一 |
| Born 与密度矩阵 | 全效果拆并 $\Rightarrow f(F)=\operatorname{Tr}\rho F$ | 非情境效果概率接口 |
| 高维与张量积 | 两个交换矩阵像共同生成 $M_{mn}$；支持角及直和 | 共同复标尺、联合结合乘法、独立复合与闭包 |
| Kraus 与量子仪器 | 参考正性 $\Rightarrow C_T\ge0\Rightarrow$ Kraus | 混合线性、所需内部参考实际可用 |
| Lüders 更新 | 效果 $P$ 加支持内中性 $\Rightarrow P\rho P$ | 理想性；效果本身不足 |
| Schrödinger 方程 | 连续可逆 CP 群 $\Rightarrow$ 内导子 | 物理时间、能量标尺和具体 Hamiltonian |
| 共同来源 | 固定 $\Phi_d$ 加目标依赖参考滤波 | 来源、滤波与成功记录；不推出唯一宇宙态 |

### 14.1 有限核验与真正的开放问题

有限维情况下，面积残差是双二次型。对基 $e_i$ 定义

$$
S=\{e_i\}\cup\{e_i+e_j:i<j\}.
$$

检查全部 $x,y\in S$ 的面积等式，再做两次极化，就足以证明该有限接口的全部面积式；仅检查基向量对不够。运输生成残差对三个输入三线性，检查全部基三元组即可，然后指数化得到数学上的有限运输相容。这是有限代数核验，不是对无界 $\Omega$ 的自动认证。

最重要的后续问题因而十分具体：从原生记录和控制定义 $B,D$；证明零关系在全部后续读口中仍为零；证明 (A) 的面积饱和与 (T) 的主动协变；给出同一整体中基本块之间的共同复标尺、联合乘法和实际参考。这些问题若解决，内生性的桥才真正从“存在一个量子实现”提升为“原项目实现被迫量子”。

四维及更高维的生成残差界提供了明确反驳路径。相反，一个通过某个有限窗口的候选，仍可能在新窗口、新历史或新参考上失败。将一个模型类定义为满足关系，不能逻辑上证明实际 $\Omega$ 必然属于该类；本稿不把这个区别抹去。

### 14.2 与 zeta 零点的关系只到哪一层

本轮不需要 zeta 零点来建立量子核心。项目同一快照的算术支线已对
$P(t)=e^{-|t|/2}\operatorname{trivialT}(|t|)$ 给出完整正混合谱恒等式及对数乘子界 [4](#ref-repolean)。这说明某个明确核具有可证明的谱正性；它不是整个含素数的 actual kernel，也不能直接推出 Riemann 假设或排除临界线外零点。

二者可比较的方法是：正核的零组合必须在其他读口下仍为零，且局部核证据必须保留同一整体的交叉项。但“都涉及正性”不构成从本稿到 RH 的证明。仍需精确算术核、素数与连续部分的耦合、目标判据与全部量词的桥接。

把整个世界看成一个内部可以比较、转动和留下记录的整体。拿出两份内容，它们有多少重合，就先记下多少；剩下不重合的部分，形成一份有方向的差额。重合与差额加起来，必须恰好保留原有比较量。若几份内容已经完全抵消，就真的等于没有，换到任何其他内部读口旁边都不能重新出现。接着让整体内部的一份内容带动这两份内容：先形成它们的差额再一起移动，与先移动两端再形成差额，必须是同一件事。每一对内容因此先长出一个三维片段；所有片段又必须按同一个移动规则拼接。若还能藏进第四个独立方向，同一个响应就会一边被算成一份、一边被算成两份，所以放不进去。这个三维片段与一份标量合起来，形成四元数；在其中选一个内部参照，同一结构就能写成两个复数分量。只看准备出的方向得到一个量子球，沿球上每一点仍有一圈相位自由。再让概率服从同一效果的拆并，让独立部分使用共同相位并保持联合比较，让过程接上内部参考后仍保持正性，便得到熟悉的量子态、Born 概率、纠缠、测量更新与幺正演化。新候选的要点是：这些对象都从同一整体的关系中构造，而每一步需要的相容条件都明确写出；没有把尚未证明的整体供应说成已经自动发生。

<a id="references"></a>

## 参考文献

<a id="ref-repo113"></a>

### [1]

 The Omega Institute, *AURIC Internal Balanced Calibration and Filter Composition Geometry, C113*, 固定版本 `a41b3dc77a15de8ceeabfcba85d60b17bad3df6b`，重点第 20–22 节。
newline
[https://github.com/the-omega-institute/trureturing/blob/a41b3dc77a15de8ceeabfcba85d60b17bad3df6b/docs/develop/theory/AURIC_INTERNAL_BALANCED_CALIBRATION_AND_FILTER_COMPOSITION_GEOMETRY_C113.md](https://github.com/the-omega-institute/trureturing/blob/a41b3dc77a15de8ceeabfcba85d60b17bad3df6b/docs/develop/theory/AURIC_INTERNAL_BALANCED_CALIBRATION_AND_FILTER_COMPOSITION_GEOMETRY_C113.md)

<a id="ref-repofib"></a>

### [2]

 The Omega Institute, *FIB Atom Recursive Holographic Boundary Geometry, Continuation III, Appendix III*, 同一固定版本，重点第 136–140 节。
newline
[https://github.com/the-omega-institute/trureturing/blob/a41b3dc77a15de8ceeabfcba85d60b17bad3df6b/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_III.md](https://github.com/the-omega-institute/trureturing/blob/a41b3dc77a15de8ceeabfcba85d60b17bad3df6b/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_III.md)

<a id="ref-repo117"></a>

### [3]

 The Omega Institute, *AURIC Common Source Self Reference and Observer Sequences, C117*, 二元块、共同来源与相位的相关前端。
newline
[https://github.com/the-omega-institute/trureturing/blob/a41b3dc77a15de8ceeabfcba85d60b17bad3df6b/docs/develop/theory/AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md](https://github.com/the-omega-institute/trureturing/blob/a41b3dc77a15de8ceeabfcba85d60b17bad3df6b/docs/develop/theory/AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md)

<a id="ref-repolean"></a>

### [4]

 The Omega Institute, *ActualKernelMomentMixture.lean* 及对应 Blueprint，同一固定版本；本稿只读源码与说明，未运行 Lean 构建。
newline
[https://github.com/the-omega-institute/trureturing/blob/a41b3dc77a15de8ceeabfcba85d60b17bad3df6b/D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentMixture.lean](https://github.com/the-omega-institute/trureturing/blob/a41b3dc77a15de8ceeabfcba85d60b17bad3df6b/D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentMixture.lean)

<a id="ref-baez"></a>

### [5]

 John C. Baez, *The Octonions*, Bulletin of the AMS 39 (2002), 145–205. 叉积、八元数乘法表与 $G_2$ 的原始综述。
newline
[https://arxiv.org/abs/math/0105155](https://arxiv.org/abs/math/0105155)
newline
[https://math.ucr.edu/home/baez/octonions/node3.html](https://math.ucr.edu/home/baez/octonions/node3.html)
newline
[https://math.ucr.edu/home/baez/octonions/node14.html](https://math.ucr.edu/home/baez/octonions/node14.html)

<a id="ref-busch"></a>

### [6]

 Paul Busch, *Quantum states and generalized observables: a simple proof of Gleason's theorem*, Physical Review Letters 91, 120403 (2003).
newline
[https://arxiv.org/abs/quant-ph/9909073](https://arxiv.org/abs/quant-ph/9909073)

<a id="ref-watrous"></a>

### [7]

 John Watrous, *The Theory of Quantum Information*, Cambridge University Press (2018), 作者公开稿，特别是完全正映射与范数章节。
newline
[https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)

<a id="ref-peres"></a>

### [8]

 Asher Peres, *Separability Criterion for Density Matrices*, Physical Review Letters 77, 1413–1415 (1996).
newline
[https://arxiv.org/abs/quant-ph/9604005](https://arxiv.org/abs/quant-ph/9604005)

<a id="ref-ashtekar"></a>

### [9]

 Abhay Ashtekar and Troy A. Schilling, *Geometrical Formulation of Quantum Mechanics* (1997), in *On Einstein's Path*.
newline
[https://arxiv.org/abs/gr-qc/9706069](https://arxiv.org/abs/gr-qc/9706069)
