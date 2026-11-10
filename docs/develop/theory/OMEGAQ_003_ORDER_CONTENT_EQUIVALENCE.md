**QUANTUM ORIGINS / $\Omega Q$-003**

# 顺序差与内容差等价

**删去额外的响应映射，从原控制的二元关系恢复量子几何**

一个候选：反例、有限三维提升、定义、定理与证明

取整体内部的一个转向 $A$ 和一份内容差 $e$。比较 $A$ 与另一转向 $X$ 的先后顺序，把所得回路作用在 $e$ 上。除去参照自身的那一条线，要求这份读出恰好把转向的差别与内容的差别一一对应。

$$
\boxed{\exists A\ne0,\ e\ne0:\quad
\Xi_{A,e}:\mathfrak g/\mathbb R A\overset{\cong}{\longrightarrow}W/\mathbb R e,
\quad [X]\longmapsto [[A,X]e].}
$$

原控制已经有矩阵交换子。无需先供应 $D:W\to\mathfrak g$，也不先指定差空间三维。

 本会话新系列第三篇，承接 $\Omega Q$-002。

稿件日期：2026-11-04，Asia/Singapore。

固定项目版本：`dev@0d2719a1091903642f361f04994da098acd20e22`。

提交时间：2026-11-03 20:51:09 UTC；新加坡时间 11 月 4 日 04:51:09。

范围：有限维条件重建与普通数学证明；未提交仓库，未作 Lean 认证。

编号表示本会话候选序列，不表示数学首创、逻辑最弱或物理实例化已经完成。

上一轮把内容 $x$ 对应到一个原控制生成元 $D_x$，再要求自静止、共同运输和单参照唯一静止轴。本轮向前回溯一步：**原控制的先后顺序已经定义了二元交换子，能否由这一个已有关系恢复整张 $D$？**

答案是一个严格的条件定理。以原全未来概率行定义有限预测空间 $V$，取其归一差空间 $W$。准确统计逆和概率有界给出紧预测群 $G$，其实际矩阵 Lie 代数记为 $\mathfrak g$。只要求存在原生 $(A,e)$，使上述商读出 $\Xi_{A,e}$ 是线性同构，就能证明

$$
\dim\mathfrak g=\dim W=3,\qquad \dim V=4,\qquad G^\circ=SO(3).
$$

证明先把最大频率平面提升为一个闭合三维片；假设还有剩余方向，则它们被迫形成半频率的四元数片，而三个顺序差的 Jacobi 和非零，矛盾。这是有限矩阵证明，不需要预设球面或调用紧 Lie 代数分类。

随后用 $A,e$、交换子、作用和迹给出显式公式，**将上一轮的 $D$ 恢复为结论**。面积恒等式、三维球面、内部复单位、$M_2(\mathbb C)$、二维 Hilbert 空间与原概率的 Born 表示依次出现。再把复合、参考正性、理想更新和连续可逆时间各自的接口写明，得到一门闭合的有限维量子理论。

这轮简化的是**待额外供应的原始结构**：删去整张 $D$ 及其全空间相容检查，改为一个原参照对和一张有限回路矩阵的秩条件。对连通预测群，它与上一轮选择相同的初等模型类；没有证明逻辑上严格更弱，也没有把复合、实际门或实际锐读口藏进一个词中。完整群还可能含反射，后续参考正性才排除它。

## 目录

- [1. 核对项目最新进展：真正新增的是 C124](#section-1)
- [2. 先反着看：控制三维，为什么内容未必三维](#section-2)
- [3. 从原终端概率定义内容、控制与二元关系](#section-3)
- [4. 本轮唯一候选：顺序差与内容差等价](#section-4)
- [5. 有限三维提升：先闭合一片，再排除所有余项](#section-5)
- [6. 把上一轮的响应映射算出来](#section-6)
- [7. 它属于什么更大结构：Jordan--Lie 与内部复数](#section-7)
- [8. 几何与原概率：球面、相位圈和 Born 规则](#section-8)
- [9. 从初等块发展完整有限维理论：逐项写明接口](#section-9)
- [10. 接上 C124：怎样获得实际有限平方根滤波](#section-10)
- [11. 本轮的完整前提账本与内生性的精确定义](#section-11)
- [参考文献](#references)

<a id="section-1"></a>

## 1. 核对项目最新进展：真正新增的是 C124

<a id="sec-repo"></a>

固定提交相对上一轮 `8171c9756da2b5c654cba2eb1d04a4d93a9fadeb` 有 36 个提交、66 个改变路径。所用文件已下载固定原文并比较。C117、C122、C113、C115、V95、V96 continuation 与 FIB Appendix III 均逐字未变；不能再次把上一轮新增内容说成本轮更新。 [1](#ref-repohead)

**与本轮最相关的新增。**

C123 文件末尾追加 §§10–17，即 C124。它将此前指定量子比特的实际端点，改为整个实际可附接指针 $P$ 内的一个原子、必然、非中心读口：成功效果 $d$ 的射线是整个数学正锥的极射线，某个原准备 $\alpha$ 满足未经条件化的 $\alpha(d)=1$，且该效果非中心。 [3](#ref-repo124)

在已经取得有限复矩阵直和的结构之后，这三个条件迫使 $d$ 与准备密度恰好是同一个非经典块内的秩一投影。整个指针可以是 $\mathbb C\oplus M_3(\mathbb C)$，实际对象域甚至可以没有任何 $M_2(\mathbb C)$ 对象；仍可在完整指针内部的两个方向上构造有限平方根滤波词。第 [10](#sec-supply) 节写出证明及失败记录的正确处理。

**不能把端点拓宽等同于整套前提减少。**

C124 仍保留原 P/G/D、联合对象的 P/G/D、精确 $N_u$、张量与同记录执行、全部合法历史的 R、完整 F 及支持返回等合同。其 $D$ 仍独立给出。该稿也明确不声称总独立前提更少或全局最简。本文的新工作因此放在更早处：从原预测控制恢复初等块的 $D$，而不是再次给端点改名。

**其他进展与本轮的关系。**

Four-path continuation II 新 §43 给局部相位图及选定行列式为正时的定量隔离；行列式为零只给一个 Hessian 零方向，不能直接宣称高阶分岔。新 bc-ghost Borcherds 文件处理全整数模式的恒等式，不等于物理态正性或 BRST 目标已经完成。这两项不补足本文的内容–控制对应缺口。FIB 仍止于原条件下的 §141 秩二结果，没有新增全 64 坐标取得或 $A^D=A^f$。 [4](#ref-repofour)、[5](#ref-repofib)

<a id="section-2"></a>

## 2. 先反着看：控制三维，为什么内容未必三维

<a id="sec-reverse"></a>

### 例 2.1（真实可读的五维内容）

取实际准备 $\rho_v=vv^{\mathsf T}$，其中 $v\in S^2$ 为实单位向量。实际可逆控制为全部 $R\in SO(3)$，原完整测试有三个结果：

$$
p_i(R,v)=|(Rv)_i|^2,\qquad i=1,2,3.
$$

三项非负且和为一。全部未来效果为实秩一投影，它们分离整个 $\operatorname{Sym}(3,\mathbb R)$。于是

$$
V=\operatorname{Sym}(3,\mathbb R),\quad \dim V=6,
\qquad W=\operatorname{Sym}_0(3,\mathbb R),\quad \dim W=5.
$$

控制在这些原行上的作用为 $Q\mapsto RQR^{\mathsf T}$，忠实控制代数为三维 $\mathfrak{so}(3)$。每个非零生成元在控制代数内都只有一维中央化子，但实际内容仍有五维。

这不是一个不合法的量子系统；它是一个不能被忠实压成量子比特的模型。把“内容”重新定义成控制代数，会删掉原本能被测出的区别。甚至全部一阶控制期望都可能为零：若 $A_x$ 实斜对称，$H_x=-iA_x$，则

$$
\operatorname{Tr}(\rho_v H_x)=0
$$

对每个实准备都成立，然而上述未来概率依然区分这些准备。差别藏在二阶响应里。

**一个完全有限的见证。**

取六个方向

$$
e_1,e_2,e_3,\quad
\frac{e_1+e_2}{\sqrt2},\quad
\frac{e_1+e_3}{\sqrt2},\quad
\frac{e_2+e_3}{\sqrt2}.
$$

以它们分别作准备和单个原测试结果，得到概率子表

$$
P=\begin{pmatrix}
1&0&0&1/2&1/2&0\\
0&1&0&1/2&0&1/2\\
0&0&1&0&1/2&1/2\\
1/2&1/2&0&1&1/4&1/4\\
1/2&0&1/2&1/4&1&1/4\\
0&1/2&1/2&1/4&1/4&1
\end{pmatrix},\qquad \det P=\frac18.
$$

每列效果都可以补成一个三结果完整测试，不作后选择。用左上 $I_3$ 消元，下方 Schur 补为 $\tfrac12 I_3$，故秩确为六。任何量子比特状态–效果表的秩至多四，所以没有保留这些原概率的比特表示。

**反推得到的要求。**

不能只检查“原控制之间有没有额外不动的方向”，还要检查它们的顺序差是否**读尽原内容的全部横向方向**。新候选把两件事放在同一张原矩阵的单射性和满射性中。

<a id="section-3"></a>

## 3. 从原终端概率定义内容、控制与二元关系

<a id="sec-front"></a>

这里沿用 C117 全未来预测前端的一般有限维部分，**不沿用其后输入的容量四**。 [2](#ref-repo117)

### 定义 3.1（同一原来源的有限预测窗口）

在同一 $\Omega$ 中选一个实际归一准备。令 $\mathcal L$ 为从它出发的总可逆有限控制词，含空词，封闭于接续，每个词的准确统计逆也在这同一菜单中。令 $\mathcal F$ 为共同的全部合法未来域。未来末端保留全部有限标签，包括失败，原概率满足

$$
p(a;f,w)\ge0,\qquad \sum_w p(a;f,w)=1,
\qquad p(ag;f,w)=p(a;gf,w).
$$

定义全未来行及其实际实线性空间：

$$
x_a(f,w)=p(a;f,w),\qquad
V=\operatorname{span}_{\mathbb R}\{x_a:a\in\mathcal L\},\qquad \dim V<\infty.
$$

任一完整终端测试的求和在 $V$ 上定义同一个 $u$，满足 $u(x_a)=1$。内容差空间为

$$
W=\ker u=\operatorname{span}\{x_a-x_b\}.
$$

### 引理 3.2（原接续给紧预测群）

$T_gx_a=x_{ag}$ 在 $V$ 上良定义。其双边可逆群的矩阵闭包 $H$ 紧。存在 $H$ 固定的 $c\in V$，$u(c)=1$，使

$$
V=\mathbb R c\oplus W.
$$

$G=H|_W$ 是忠实紧矩阵群，并保某个正定内积 $B_0$。

**证明。**
若 $\sum_i t_i x_{a_i}=0$，则它在所有未来 $gf$ 上也为零，故 $\sum_i t_i x_{a_i g}=0$。这证明线性接续良定义，原统计逆给其逆。

有限维使一组有限终端坐标足以分离 $V$；选实际行组成基。任一基行经任意接续后的上述坐标仍在 $[0,1]$，所以所有 $T_g$ 一致有界。逆仍在同一群中，逆也一致有界，因此矩阵极限不可能奇异，闭包是紧子群。对任一原行作 Haar 平均得到 $c$；对任一正定内积作群平均得到 $B_0$。作用在 $W$ 上为恒等且固定 $c$ 的元素在整个 $V$ 上就是恒等，故限制忠实。

### 定义 3.3（原控制的顺序差）

令 $\mathfrak g=\Lie G\subseteq\operatorname{End}(W)$。其二元关系是实际矩阵交换子

$$
[A,X]=AX-XA.
$$

它来自接续的结合律，自动满足双线性、反对称与 Jacobi。小回路给

$$
e^{tA}e^{sX}e^{-tA}e^{-sX}
=I+ts[A,X]+O(t^2s+ts^2).
$$

这里的二元关系作用在两个转向 $A,X$ 之间；原内容 $e$ 用来读取该关系的作用。整个候选因此有一个参照对 $(A,e)$，不是声称一个无载体的纯二元符号足以描述全部物理。群闭包中的指数和极限用于定义与证明，并不自动等于一个已经有精确有限实现的原门。

<a id="section-4"></a>

## 4. 本轮唯一候选：顺序差与内容差等价

<a id="sec-axiom"></a>

**候选 $\Omega Q$-003。**在上述同一原预测窗口中，存在
$A\in\mathfrak g\setminus\{0\}$、$e\in W\setminus\{0\}$，使

<a id="eq-axiom"></a>

$$
\boxed{\Xi_{A,e}:\mathfrak g/\mathbb R A\longrightarrow W/\mathbb R e,
\qquad X+\mathbb R A\longmapsto[A,X]e+\mathbb R e
\quad\text{为线性同构}.}
\tag{1}
$$

这两个商只是线性空间商；$\mathbb R A$ 未必为理想，不能把左边当作 Lie 代数商。$[A,A]=0$ 保证映射良定义。右侧取商仅是本项证书的比较方式，**不把原状态作商，也不删除任何终端概率**。

紧性使 $A,X,[A,X]$ 都对 $B_0$ 斜对称，所以

$$
B_0([A,X]e,e)=0.
$$

因此候选等价于

<a id="eq-twohalves"></a>

$$
\ker(X\mapsto[A,X]e)=\mathbb R A,
\qquad \{[A,X]e:X\in\mathfrak g\}=e^{\perp_{B_0}}.
\tag{2}
$$

第一项说除参照转向外，没有多余的不可见转向；第二项说没有被所有这些回路遗漏的横向内容。两者都是真实要求。

同一个候选也可以用更直观的完整分解表达：每份原内容差都能唯一写成

$$
w=\lambda e+[A,X]e,
\qquad (\lambda,\,X+\mathbb R A)\text{ 唯一}.
$$

参照方向上的系数 $\lambda$ 始终保留，并没有被商掉。$e$ 是原行之间的线性差别，不须另外把它当作一个归一物理准备。

选任意线性商基，以原作用计算矩阵 $M$。有限判据为

$$
\operatorname{rank} M=\dim\mathfrak g-1=\dim W-1.
$$

它是两个秩等式，不是“一比特条件”。有限预测容量已知时，矩阵证书是有限的；从有噪声的有限观测推断全未来容量、精确逆与精确 Lie 闭包，是另外的辨识问题。

候选的量词是“存在”：一对合格参照就给正见证；找到一对不合格参照只说明这对参照不够用。反驳整个窗口需要维数或其他统一障碍，证明所有参照对都失败。

### 4.1 分别删除两半会怎样

在第 [2](#sec-reverse) 节五维内容模型中，取绕第三轴的 $A$，取轴对称无迹矩阵
$e=\operatorname{diag}(-1/3,-1/3,2/3)$。$\Xi$ 从二维控制商单射到四维内容商，但不能满射；原内容确有未被这次回路读出的方向。

反过来，令 $G=SO(5)$ 标准作用于 $W=\mathbb R^5$，取 $e=e_5$，

$$
A=\operatorname{diag}(J_2,J_2,0),\qquad
J_2=\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
$$

此时 $Ae=0$，$A$ 在 $e^\perp$ 上可逆，且 $Xe$ 扫满 $e^\perp$。因此
$[A,X]e=A(Xe)$ 满射到 $e^\perp$，但左商维数九、右商维数四，有五维额外核。该模型可配以全部完整二结果概率 $p(\pm|n,r)=(1\pm n\cdot r)/2$，并非形式空壳。

紧前端也不能删除。若 $A=\operatorname{diag}(1,0)$、$X=E_{12}$、$W=\mathbb R^2$、$e=e_2$，则 $[A,X]=X$，$\Xi$ 仍是两个一维商之间的同构，却得到二维非紧仿射代数。它不能保持正定型，也不满足上述有限有界原概率的双边群前端。

<a id="section-5"></a>

## 5. 有限三维提升：先闭合一片，再排除所有余项

<a id="sec-rigidity"></a>

### 引理 5.1（一维中央化子的有限刚性）

有限维实 Lie 代数 $\mathfrak k$ 具有正定不变内积。若某个非零 $a$ 满足
$\ker\ad_a=\mathbb R a$，则 $\dim\mathfrak k=1$ 或 $3$。

**证明。**
把 $a$ 归一化。若 $\ad_a=0$，核条件直接给出一维。以下设它非零。

**第一步：两方向提升成闭合三维片。**

$\ad_a$ 斜对称，取其最大正频率 $\lambda>0$，选正交单位 $u,v$ 满足

$$
[a,u]=\lambda v,\qquad [a,v]=-\lambda u.
$$

Jacobi 给 $[a,[u,v]]=0$，故 $[u,v]=ca$。内积不变性给
$c=\langle [u,v],a\rangle=\langle u,[v,a]\rangle=\lambda$。因此

$$
P=\operatorname{span}\{e_1,e_2,e_3\},\qquad(e_1,e_2,e_3)=(a,u,v)
$$

闭合，且 $[e_1,e_2]=\lambda e_3$ 及其循环式成立。令 $M=P^\perp$。不变性保证 $[P,M]\subseteq M$。

**第二步：若还有方向，频率只能减半。**

在 $M$ 上设 $B_i=\ad_{e_i}/\lambda$。它们斜对称，且
$[B_1,B_2]=B_3$ 及其循环式成立。$B_1$ 无零频率，频率绝对值至多一。

暂时把有限实矩阵复化以检验其谱。这只是证明工具，不是物理复数输入。设

$$
H=-2iB_1,\qquad E=B_2-iB_3,\qquad F=-B_2-iB_3.
$$

直接计算得

$$
H^*=H,\quad F=E^*,\quad [H,E]=2E,\quad
[H,F]=-2F,\quad [E,F]=H,
$$

而 $\operatorname{spec}H\subseteq[-2,2]$，在 $M$ 上没有零特征值。

取 $Hw=\mu w$、$\mu>0$。若 $Ew\ne0$，其权为 $\mu+2>2$，不可能，故 $Ew=0$。于是

$$
\lVert Fw\rVert^2=\langle w,EFw\rangle=\mu\lVert w\rVert^2>0.
$$

若 $\mu=2$，非零 $Fw$ 有零权，矛盾。若 $0<\mu<2$，$F^2w$ 的权小于 $-2$，故为零；然而

$$
EF^2w=(HF+FH)w=2(\mu-1)Fw.
$$

所以 $\mu=1$。实共轭给相应负权 $-1$，覆盖全部重数。因而

$$
B_1^2=-\tfrac14 I_M.
$$

**第三步：余项只能形成四元数片。**

交换关系给出

$$
e^{tB_3}B_1e^{-tB_3}=\cos t\,B_1+\sin t\,B_2,
$$

循环同理。所有单位线性组合 $B(n)=\sum n_iB_i$ 都在这些内部旋转下与 $B_1$ 共轭。因此平方并极化可得

$$
B_i^2=-\tfrac14I,\qquad B_iB_j+B_jB_i=0\quad(i\ne j).
$$

令 $J_i=2B_i$，则

$$
J_i^2=-I,\qquad J_1J_2=J_3
$$

及循环关系成立。

在整个 $\mathfrak k_{\mathbb C}$ 上，$P$ 的 $H$ 权为 $0,\pm2$，$M$ 的权只有 $\pm1$。Jacobi 使括号权相加，因此 $[M,M]\subseteq P$。内积不变性完全确定该括号：

$$
[m,n]=\frac\lambda2\sum_{i=1}^3\langle J_i m,n\rangle\,e_i.
$$

**第四步：三个顺序差不能闭合。**

假定 $M\ne0$，取单位 $m\in M$。$m,J_1m,J_2m,J_3m$ 正交归一，且

$$
[m,J_1m]=\tfrac\lambda2e_1,\quad
[J_1m,J_2m]=\tfrac\lambda2e_3,\quad
[J_2m,m]=-\tfrac\lambda2e_2.
$$

故其 Jacobi 和为

$$
\begin{aligned}
&[m,[J_1m,J_2m]]+[J_1m,[J_2m,m]]+[J_2m,[m,J_1m]]\\
&\hspace{2cm}=-\frac{3\lambda^2}{4}J_3m\ne0.
\end{aligned}
$$

这与原交换子必满足的 Jacobi 恒等式矛盾，故 $M=0$，整个代数就是上述三维片。

### 定理 5.2（从原顺序差锁定原内容维数）

在第 [3](#sec-front) 节前端及候选 [(1)](#eq-axiom) 下，

$$
\boxed{\dim\mathfrak g=\dim W=3,\quad \dim V=4,
\quad G^\circ=SO(W,B_0).}
$$

完整 $G$ 只能是 $SO(3)$ 或 $O(3)$。

**证明。**
若 $[A,X]=0$，则 $\Xi([X])=0$。由单射性得 $X\in\mathbb R A$，所以
$\ker\ad_A=\mathbb R A$。在 $\mathfrak g$ 上，

$$
\langle X,Y\rangle_{\mathfrak g}=-\operatorname{Tr}_W(XY)
$$

正定且不变：在 $B_0$ 正交坐标中 $-\operatorname{Tr}(X^2)=\lVert X\rVert_{\rm HS}^2$，迹循环性给不变性。上引理适用。

同构的维数等式给 $\dim\mathfrak g=\dim W$。若两者都为一，则
$\mathfrak g\subseteq\mathfrak{so}(1)=0$，与 $A\ne0$ 矛盾。因此两者都为三。
$\mathfrak g\subseteq\mathfrak{so}(W,B_0)$ 两侧同维，必相等；连通群就是 $SO(3)$。完整群在 $O(3)$ 内且含 $SO(3)$，只余所述两种。

```latex
\begin{tikzpicture}[>=Latex, every node/.style={font=\small}, scale=0.9]
\node[draw=accent,rounded corners,fill=pale,minimum width=25mm] (a) at (0,2.1) {$a$：参照轴};
\node[draw=accent,rounded corners,fill=pale,minimum width=25mm] (u) at (-2.6,0) {$u$：频率方向};
\node[draw=accent,rounded corners,fill=pale,minimum width=25mm] (v) at (2.6,0) {$v$：顺序差};
\draw[->,thick,accent] (a) -- node[left] {$[a,u]=\lambda v$} (u);
\draw[->,thick,accent] (u) -- node[below] {$[u,v]=\lambda a$} (v);
\draw[->,thick,accent] (v) -- node[right] {$[v,a]=\lambda u$} (a);
\node[align=center,text=ink] at (0,-1.15) {三维片之外的方向必须成半频率四元数片；\\其三条回路的余项同向，违反 Jacobi。};
\end{tikzpicture}
```

这张图表示闭合关系，不把三个结点当作空间中的三个物理粒子。三维先在控制侧证明，再由同一 $\Xi$ 传到原内容侧，避免了高自旋反例中的维数跳跃。

<a id="section-6"></a>

## 6. 把上一轮的响应映射算出来

<a id="sec-D"></a>

主定理之后，才允许使用三维叉积坐标作验证。写
$A=C_a$、$X=C_x$，其中 $C_a y=a\times y$。则

$$
[A,X]e=(a\times x)\times e
=(a\cdot e)x-(x\cdot e)a.
$$

所以 $\Xi$ 同构当且仅当 $a\cdot e\ne0$。原 $e$ 未必满足 $Ae=0$；不能直接宣称 $D_e=A$。

### 定理 6.1（只用原参照对恢复 $D$）

定义

$$
\tau(X,Y)=-\tfrac12\operatorname{Tr}_W(XY),\qquad \nu^2=\tau(A,A)>0,
$$

<a id="eq-phi"></a>

$$
h=\left(I+\frac{A^2}{\nu^2}\right)e,
\qquad
\Phi(X)=\frac{[A,X]h+\tau(A,X)h}{\nu^2}.
\tag{3}
$$

则 $h\ne0$、$Ah=0$，$\Phi:\mathfrak g\to W$ 为 $G^\circ$ 等变线性同构。定义

$$
\boxed{D_x:=\Phi^{-1}(x).}
$$

它满足

$$
D_h=A,\quad D_xx=0,\quad
D_{gx}=gD_xg^{-1}\ (g\in G^\circ),\quad \ker D_h=\mathbb R h.
$$

**证明。**
辅助三维正交坐标中，$\tau(C_x,C_y)=x\cdot y$，且
$I+A^2/\nu^2$ 正是到轴 $\ker A$ 的投影。故 $h=ta$，其中
$t=(a\cdot e)/\lVert a\rVert^2\ne0$。代入 [(3)](#eq-phi) 得

$$
\Phi(C_x)=t x.
$$

可逆性、$\Phi(A)=h$、连通等变性及其余结论立即成立。三维坐标仅验证原矩阵公式，不是另一个前件。

在全 $O(3)$ 上，正确关系为

$$
D_{gx}=\det(g)\,gD_xg^{-1}.
$$

因此这里只恢复上一轮的连通版本。若另一个参照对也通过测试，得到的 $D$ 可相差非零共同尺度及取向；这不会提供绝对的时间单位或 $\hbar$。

### 推论 6.2（比较、面积和三重积成为结论）

令

$$
B_D(x,y)=-\tfrac12\operatorname{Tr}_W(D_xD_y),\qquad [x,y]_W=D_xy.
$$

则 $B_D$ 正定，且

$$
\begin{aligned}
B_D([x,y]_W,[x,y]_W)
&=B_D(x,x)B_D(y,y)-B_D(x,y)^2,
\end{aligned}
\tag{4}
$$

<a id="eq-triple"></a>

$$
\begin{aligned}
D_xD_yz&=B_D(x,z)y-B_D(x,y)z.
\end{aligned}
\tag{5}
$$

特别地，$D_x^2y=B_D(x,y)x-B_D(x,x)y$。

**证明。**
由 $\Phi(C_x)=tx$，有 $D_y=C_{y/t}$、$B_D(y,z)=(y\cdot z)/t^2$。代入通常三维向量恒等式，两边尺度完全一致。$D$ 亦把 $W$ 上括号同构到 $\mathfrak g$ 的交换子，故 Jacobi 和不变性同时得到。

<a id="section-7"></a>

## 7. 它属于什么更大结构：Jordan–Lie 与内部复数

<a id="sec-algebra"></a>

### 7.1 对称关系与顺序关系共同组成乘法

在 $\mathbb R1\oplus W$ 上定义

$$
(\alpha,x)\circ(\beta,y)
=(\alpha\beta+B_D(x,y),\ \alpha y+\beta x).
$$

令 $L_a b=a\circ b$，并扩展 $D_{\alpha1+x}(\beta1+y)=(0,D_xy)$。直接使用 [(5)](#eq-triple) 得

$$
[L_a,L_b]+[D_a,D_b]=0.
$$

例如作用在 $(\gamma,z)$ 上，两个交换子的向量部分分别是
$B_D(y,z)x-B_D(x,z)y$ 与其相反数。$D$ 还是 $\circ$ 的导子。这说明同一三维片中，对称比较的非交换与有向响应的非交换恰好抵消。

### 7.2 复单位是三方向的乘积

### 定义 7.1（最小结合闭包）

取由 $W$ 生成的实含幺结合代数，关系为

$$
xy+yx=2B_D(x,y)1,
$$

并令 $x^*=x$。这就是 $\operatorname{Cl}_{3,0}$。它是一个明确的数学闭包定义；是否每个代数元素都有实际门实现，另须供应接口。

选 $B_D$ 正交单位 $e_1,e_2$，令 $e_3=D_{e_1}e_2$。这样取向由 $D$ 决定，即使辅助坐标中的尺度 $t<0$ 也不会漏号。定义

$$
\boxed{J=e_1e_2e_3.}
$$

生成关系给

$$
J^2=-1,\qquad J^*=-J,\qquad Jx=xJ,
\qquad xy=B_D(x,y)1+J D_xy.
$$

故 $\mathbb C_J=\{a+bJ:a,b\in\mathbb R\}$ 是内部中心复数。选不同的同向正交基不改变 $J$。

### 定理 7.2（二元块的复 Hilbert 表示）

上述实代数同构于 $M_2(\mathbb C_J)$。其最小左理想给出二维复 Hilbert 空间，$W$ 对应无迹 Hermitian 矩阵。

**证明。**
反交换关系把任意词约到

$$
1,e_1,e_2,e_3,e_1e_2,e_2e_3,e_3e_1,J
$$

这八个词的实线性组合。令三生成元分别作用为

$$
\sigma_1=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
\sigma_2=\begin{pmatrix}0&-J\\J&0\end{pmatrix},\quad
\sigma_3=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
$$

它们满足定义关系，八个像实线性独立并张成 $M_2(\mathbb C_J)$，故同构。这里矩阵是推导后的表示，不是三维证明的前件。

置 $p=(1+e_3)/2$。左理想 $\mathcal H=\mathcal A p$ 以 $p,e_1p$ 为复基。由
$\xi^*\eta=\langle \xi,\eta\rangle p$ 定义内积，其范数平方为 $|z_1|^2+|z_2|^2$。所以得到 $\mathcal H\cong\mathbb C_J^2$。

<a id="section-8"></a>

## 8. 几何与原概率：球面、相位圈和 Born 规则

<a id="sec-born"></a>

### 定理 8.1（选定原轨道的最小概率完成）

令 $R=\lVert x_\epsilon-c\rVert_{B_D}$。非平凡性给 $R>0$。选定原准备轨道的闭凸包为

$$
S_{\min}=c+\{w:\lVert w\rVert_{B_D}\le R\}.
$$

它的正锥为 $\{tc+w:t\ge0,\ \lVert w\rVert\le Rt\}$，即四维 Lorentz 锥。每个实际未来事件都有保持原概率的量子比特 Born 表示。

**证明。**
$G^\circ=SO(3)$ 将非零 $x_\epsilon-c$ 的轨道扫成半径 $R$ 的球面；原控制群在其闭包中稠密，故原轨道闭包就是该球面，闭凸包就是球。

设 $S(w)=\sum_i w_i\sigma_i$，使用 $B_D$ 正交坐标。对 $\lVert w\rVert\le R$ 定义

$$
\rho_w=\frac12\left(I+\frac{S(w)}R\right).
$$

因 $S(w)^2=\lVert w\rVert^2 I$，$\rho_w\ge0$、$\operatorname{Tr}\rho_w=1$。任一实际事件本来就是原行上的线性泛函，可唯一写成

$$
f(tc+w)=\alpha t+B_D(b,w).
$$

它在整个轨道取值于 $[0,1]$，连续性和凸性给

$$
R\lVert b\rVert\le\min(\alpha,1-\alpha).
$$

因此 $E_f=\alpha I+R S(b)$ 满足 $0\le E_f\le I$，而

$$
\boxed{f(c+w)=\operatorname{Tr}(\rho_w E_f).}
$$

原完整测试满足 $\sum_w E_w=I$，包括失败。没有给原概率换数值，也不需要先假定所有数学效果都实际存在。

**射线与相位圈。**

球面极点对应秩一 $\rho=\lvert \psi\rangle\langle \psi\rvert$，其中 $\lVert \psi\rVert=1$。同一投影的全部向量代表为 $e^{J\theta}\psi$。于是

$$
S^1\longrightarrow S^3\longrightarrow S^2\cong\mathbb{CP}^1.
$$

明确地，$(z_1,z_2)\in S^3$ 映到

$$
n=(2\operatorname{Re}(\overline z_1z_2),\ 2\operatorname{Im}(\overline z_1z_2),\ |z_1|^2-|z_2|^2).
$$

若 $P_n=(I+n\cdot\sigma)/2$，则

$$
\operatorname{Tr}(P_nP_m)=\frac{1+n\cdot m}{2}
=\cos^2\frac{\theta(n,m)}2
=|\langle \psi_n,\psi_m\rangle|^2.
$$

$U_n(\theta)=\exp(-J\theta S(n)/2)$ 的共轭作用给 $SO(3)$ 旋转，$U_n(2\pi)=-I$，$U_n(4\pi)=I$。这解释半角与相位结构。这里的三维是*可区分内容的维数*，不等于已经推导三维物理空间。

**完成与供应仍须分开。**

$S_{\min}$ 是所选原轨道的数学闭凸包；不能把整体中别的准备无条件装进同一个球。即使所有原效果只有
$E_{\pm,n}=(I\pm\eta n\cdot\sigma)/2$、$0<\eta<1$，仍有相同有限预测空间、相同旋转群和 $\Xi$，却没有原锐二结果读口。相容状态锥也可比所选轨道凸包更大。因此量子表示、全效果供应、精确端点和有限可达性是不同结论。

<a id="section-9"></a>

## 9. 从初等块发展完整有限维理论：逐项写明接口

<a id="sec-full"></a>

这里构造由上述初等块生成的有限理论。**新候选本身只选择初等块；复合、支撑和实际执行不能由命名推出。**下述接口沿用上一轮的层次，并分别说明它推出什么。常用有限量子记号与 Choi–Kraus 对应可参照 Watrous；以下给出所需证明。 [6](#ref-watrous)

### 9.1 复合：为什么是复张量积

### 命题 9.1（复合唯一性）

设两个已得到的简单块 $M_m(\mathbb C_J)$、$M_n(\mathbb C_J)$ 以同一个中心复数、保持单位及 $*$ 的方式嵌入非零联合结合代数 $\mathcal B$。若两像彼此可交换，并且它们的乘积张成 $\mathcal B$，则

$$
\mathcal B\cong M_m(\mathbb C_J)\otimes_{\mathbb C_J}M_n(\mathbb C_J)
\cong M_{mn}(\mathbb C_J).
$$

**证明。**
映射 $a\otimes b\mapsto\iota_A(a)\iota_B(b)$ 良定义且为满的含幺 $*$-同态。定义域 $M_{mn}(\mathbb C_J)$ 简单，其核只能是零或全体；含幺排除全体，故为同构。

共同复中心是实质接口。若只在实数上张量，两个 $J$ 的对齐可出现额外扇区；不能省略后仍宣称唯一复合。反复复合得 $M_{2^N}(\mathbb C_J)$。取数学秩 $d$ 投影 $p$，则角代数 $pM_{2^N}p\cong M_d$；有限直和加入经典标签。因此数学完成含全部

$$
\mathcal A=\bigoplus_j M_{d_j}(\mathbb C_J).
$$

要把某个角、标签或联合态当作实际对象，仍须对应的原附接、支撑返回与状态供应；数学角不是自动新增的实际器件。

### 9.2 状态、效果与测量

### 命题 9.2（全部正泛函的密度表示）

在上述有限矩阵代数的标准正锥上，每个归一正线性泛函唯一为

$$
\omega(a)=\sum_j\operatorname{Tr}(\rho_j a_j),\qquad
\rho_j\ge0,\quad \sum_j\operatorname{Tr}\rho_j=1.
$$

效果为 $0\le E\le I$，有限完整测量为 $\sum_k E_k=I$。

**证明。**
非退化迹配对先给唯一 Hermitian $\rho_j$。正性作用于每个秩一投影给
$\langle v\rvert\rho_j\lvert v\rangle\ge0$，故 $\rho_j\ge0$；单位取值给迹归一。反向直接成立。

简单块上的纯态为秩一投影，对应复射线；一般正元素的谱分解给混态。自伴可观测量 $A=\sum_k a_kP_k$ 的概率为 $\operatorname{Tr}(\rho P_k)$，期望为 $\operatorname{Tr}(\rho A)$。实际菜单可以是这些数学状态与效果的真子集；使用全正锥是本完整有限理论的完成选择，实际完备性须另证。

### 9.3 演化：参考扩张正性推出完全正性

### 定理 9.3（Choi 与 Kraus）

设原分支诱导复线性映射 $\mathcal E:M_d\to M_n$；原自伴部上的实线性映射按唯一复线性方式扩张。若存在原可附接参考的完整矩阵块 $M_r$、$r\ge d$，其联合完整正锥为标准矩阵正锥，并且同一个分支 $\mathcal E\otimes\operatorname{id}_r$ 保持该锥，则

$$
\mathcal E(\rho)=\sum_\mu K_\mu\rho K_\mu^*.
$$

分支不增加总概率等价于 $\sum_\mu K_\mu^*K_\mu\le I$，完整仪器所有标签一起求和为 $I$。

**证明。**
在参考块中取一个 $d$ 维数学子空间，令
$\lvert \Omega\rangle=\sum_{i=1}^d\lvert i\rangle\otimes\lvert i\rangle$。参考正性给

$$
C_{\mathcal E}=(\mathcal E\otimes\operatorname{id})(\lvert \Omega\rangle\langle \Omega\rvert)\ge0.
$$

谱分解 $C_{\mathcal E}=\sum_\mu\lvert v_\mu\rangle\langle v_\mu\rvert$，将每个 $v_\mu$ 重排成 $n\times d$ 矩阵 $K_\mu$。比较矩阵单位系数得到 Kraus 式。反向将每项写成 $(K_\mu\otimes I)Z(K_\mu^*\otimes I)$，便对任意参考保持正性。迹条件由对所有 $\rho\ge0$ 的迹不等式得到。

参考必须有足够大的完整矩阵块和足够联合正态；很多经典标签或只检查乘积态都不够。数学 Kraus 指标 $\mu$ 也不自动成为原器件可读的记录标签。实际记录仍按原仪器给定。

**此处才排除反射。**

Bloch 反射 $(r_x,r_y,r_z)\mapsto(r_x,-r_y,r_z)$ 对应转置 $T$。它正但非完全正，因为

$$
(T\otimes\operatorname{id})(\lvert \Phi^+\rangle\langle \Phi^+\rvert)
=\tfrac12\operatorname{Swap}
$$

在反对称向量上有特征值 $-1/2$。任何不正旋转都是旋转与此反射的复合。因此若同一原控制还满足完整参考正性，其中就不能存在反射型控制。若原菜单确已含反射，结论是这份实例不满足后续参考合同，不能删除原反射后仍称同一实例完成。局部 $\Xi$ 单独不排除它们；只供应可分联合态时，转置作用于一侧仍对全部这些输入保正，故完整联合正锥确为实质前件。

### 9.4 为什么理想投影更新是 Lüders 式

### 定理 9.4（理想分支的唯一更新）

在一个简单块上，设 CP 分支 $\mathcal E$ 的效果为投影 $P$，即
$\sum_\mu K_\mu^*K_\mu=P$。若它不扰动任何支撑于 $P$ 的输入态，则

$$
\mathcal E(\rho)=P\rho P.
$$

**证明。**
效果条件使每个 $K_\mu=K_\mu P$。对任意 $\psi\in P\mathcal H$，不扰动给
$\sum_\mu\lvert K_\mu\psi\rangle\langle K_\mu\psi\rvert=\lvert \psi\rangle\langle \psi\rvert$。正项之和秩一，故每个 $K_\mu\psi$ 与 $\psi$ 共线。对两个独立向量及其和使用线性，得 $K_\mu|_{P\mathcal H}=c_\mu I$；秩一情形直接成立。于是 $K_\mu=c_\mu P$、$\sum_\mu|c_\mu|^2=1$，所求式成立。$P=0$ 时分支为零。

归一后为 $P\rho P/\operatorname{Tr}(\rho P)$，仅在分母非零时定义。一般仪器不须理想，因此 Born 概率本身不固定后态。直和情形逐简单块应用，不使用不同中心块之间不存在的相干叠加。

### 9.5 连续可逆动力学与 Schrödinger 方程

### 定理 9.5（完整正可逆群）

若 $t\mapsto\mathcal E_t$ 为有限矩阵简单块上的连续 CPTP 单参数群，且负时间为同一原类中的 CP 逆，则存在 Hermitian $H$，使

$$
\mathcal E_t(\rho)=U_t\rho U_t^*,\qquad
U_t=e^{-JtH/\hbar}.
$$

所以

$$
J\hbar\dot\psi=H\psi,\qquad
\dot\rho=-\frac J\hbar[H,\rho].
$$

**证明。**
Heisenberg 对偶 $T_t$ 与逆 $T_{-t}$ 都保单位且 CP。Schwarz 不等式给
$T_t(a)^*T_t(a)\le T_t(a^*a)$；施逆并用逆的 Schwarz 不等式，两个方向相合，故取等号。极化给乘法保持，因此 $T_t$ 为 $*$-自同构。

$M_d$ 的 $*$-自同构把矩阵单位送到另一组矩阵单位；选择相应正交基和相位，得它由某个酉矩阵共轭实现。连续单参数自同构的 Lie 生成元是内导子，故可选择 $U_t=e^{-JtH/\hbar}$。整体标量相位不影响状态，$H$ 因而允许加标量。有限直和中连续群不能连续地置换离散中心，故逐块成立。

这一结论需要有一个实际或指定的连续时间群。$\Xi$ 的控制参数不会自动变成物理时钟；$\hbar$ 表示时间与能量单位的换算，本文没有算出其数值，也没有从几何选定某个具体 Hamiltonian。

### 9.6 理论的基本后果与适用范围

迹结构给无信号性：若 $\mathcal E_B$ 保迹，则
$\operatorname{Tr}_B[(\operatorname{id}\otimes\mathcal E_B)(\rho_{AB})]=\operatorname{Tr}_B\rho_{AB}$。两个数学块允许 Bell 态及纠缠；其实际制备仍依赖联合供应。

在任意态的半内积 $\langle X,Y\rangle_\rho=\operatorname{Tr}(\rho X^*Y)$ 中用 Cauchy–Schwarz，得

$$
\operatorname{Var}_\rho(A)\operatorname{Var}_\rho(B)
\ge\left|\frac1{2J}\operatorname{Tr}(\rho[A,B])\right|^2.
$$

这给通常不确定关系。概率的二次型还使固定线性路径振幅的三阶包含–排除干涉为零；若改变堵路过程或器件，本来就不是在比较同一组振幅。

因此本节已经给出有限维量子理论所需的状态、观测、复合、一般过程、理想更新与连续可逆演化。无限维正则表示、空间平移与正则对易关系、场、具体相互作用、引力、连续谱等并未由这个初等有限窗口推出。

<a id="section-10"></a>

## 10. 接上 C124：怎样获得实际有限平方根滤波

<a id="sec-supply"></a>

本节使用项目 C124 的完整原联合合同作*后续供应接口*。不能把它读成第 [4](#sec-axiom) 节的一个隐含推论，也不能据此说所有联合对象的独立 $D$ 已被本文消去。 [3](#ref-repo124)

### 命题 10.1（原子、必然、非中心端点）

在已经取得有限复矩阵直和的实际指针 $P$ 中，设原效果 $d$ 的非零射线为整个正锥的极射线，某个次归一原准备 $\alpha$ 满足 $\alpha(d)=1$，且 $d$ 非中心。则

$$
d=p,\qquad \rho_\alpha=p,
$$

其中 $p$ 是某个大小 $r\ge2$ 的简单块内的秩一投影。

**证明。**
有限矩阵正锥的极射线是单个块内的秩一正元：若秩至少二或横跨两个块，谱分解就将它分为不共线的正项。故 $d=cp$，其中 $0<c\le1$。于是

$$
1=\operatorname{Tr}(\rho_\alpha cp)
\le c\operatorname{Tr}\rho_\alpha\le c\le1.
$$

全部取等迫使 $c=1$、准备归一且支撑在 $p$ 上，即 $\rho_\alpha=p$。非中心排除大小一的经典块。这里 $\rho_\alpha$ 是迹表示的密度，不把原比较度量的 Riesz 向量误认作同一个对象。

取同一块内与 $p_0=p$ 正交的秩一 $p_1$，令 $v=\lvert 1\rangle\langle 0\rvert$。对任意效果 $0\le E\le I_A$，写 $a=\sqrt E$、$b=\sqrt{I-E}$，在整个原联合对象中构造

$$
U_E=a\otimes(p_0+p_1)+b\otimes(v-v^*)
+I_A\otimes(I_P-p_0-p_1).
$$

它在选定两方向上为
$\left(\begin{smallmatrix}a&-b\\b&a\end{smallmatrix}\right)$，在其余方向恒等。$a,b$ 可交换且 $a^2+b^2=I$，故 $U_E$ 酉。

C124 在这里还要先使用*联合对象自己的* P/G/D，证明该酉属于原指定比较群的单位稳定子，再用精确 $N_u$ 获得实际有限门。只凭局部酉存在不能跳过这一步。接原准备 $p_0$，再接同一个原破坏性读口，得到

$$
\rho\longmapsto \sqrt E\,\rho\,\sqrt E.
$$

效果有零特征值也成立，不依赖无限极限。两个数学方向没有被偷偷升格成新实际 qubit 对象。

**完整失败记录。**

原失败效果只保证 $\sum_\ell d_\ell=I_P-p_0$，在高维余补上不能宣称每个 $d_\ell$ 都是 $t_\ell(I-p_0)$。因 $0\le d_\ell\le I_P-p_0$，失败分支每个 Kraus 算子都满足 $K_{\ell j}p_0=0$，所以该分支消去 $p_0$ 的行列及其与 $p_1$ 的交叉项，剩下的指针输入只占据 $p_1$。若原失败映射为 $\Psi_\ell$，令

$$
\omega_\ell=\Psi_\ell(p_1),\qquad t_\ell=\operatorname{Tr}\omega_\ell,
\qquad \sum_\ell t_\ell=1.
$$

同记录联合执行给真实失败输出

$$
b\rho b\otimes\omega_\ell.
$$

在原实际丢弃输出对象后才是 $t_\ell b\rho b$；再将失败标签合并，才得到总失败支 $b\rho b$。丢弃量子输出与遗忘经典标签是不同操作。这样保存全部原标签与零概率记录，不把一般高维失败器件误说成测量后制备。

**为何端点可以更一般。**

项目给出的满足族包括

$$
P=\mathbb C\oplus M_3(\mathbb C),\qquad
\mathcal D_3=\left\{\bigoplus_jM_{3^{k_j}}(\mathbb C):k_j\ge0\right\}.
$$

它没有实际 $M_2$ 对象，却能利用完整指针及 $P^{\otimes k}$ 的大矩阵块提供有限滤波和参考。这个结果拓宽端点类型；它不证明整个合同更少，也不保证统一门字长、精确参数编码或任意 Kraus 分解的实际逐项读出。

<a id="section-11"></a>

## 11. 本轮的完整前提账本与内生性的精确定义

<a id="sec-ledger"></a>

| 层次 | 本轮使用的关系 | 得到的结论 |
|---|---|---|
| 原预测前端 | 全未来完整概率、未知有限容量、同菜单准确统计逆 | 原 $V,W,G,\mathfrak g$，紧性与辅助正定比较 |
| 本轮唯一新候选 | 原 $\Xi_{A,e}$ 同构 | $\dim W=\dim\mathfrak g=3$，恢复 $D$、面积和局部球面 |
| 最小数学结合闭包 | 三维比较的 Clifford 关系 | 内部 $J$、$M_2(\mathbb C_J)$、二维 Hilbert 空间 |
| 原线性读数 | 原事件在原球面上的 $[0,1]$ 界 | 不改变数值的 Born/POVM 表示 |
| 复合与支撑接口 | 同一复中心、可交换嵌入、乘积张成；数学角与直和 | 有限矩阵理论；实际对象仍需附接与返回 |
| 参考与过程接口 | 足够大完整矩阵参考；同一原分支在完整标准联合正锥上保正 | CP/Kraus；排除转置型反射 |
| 理想测量定义 | 效果为投影，且不扰动其支撑内所有态 | Lüders 更新 |
| 时间接口 | 连续 CPTP 群及 CP 逆 | 幺正群与 Schrödinger 形式 |
| 实际端点供应 | C124 完整原联合合同及 AC | 原有限平方根滤波词、完整成功与失败记录 |

与 $\Omega Q$-002 相比，$D$ 不再是外部提供的映射，自静止与连通协变也不再单独检查。它们由式 [(3)](#eq-phi) 恢复。其他层次没有伪装成已经消失。对连通 $G$，反向也成立：上一轮给出的三维模型取对齐 $e$ 与 $A=D_e$，就满足本轮 $\Xi$。因此这是一种**消去额外结构后的等价压缩**，不是模型类严格变大的“更弱公理”，也没有证明它是所有语言中的最短表达。

**公理怎样成为内生约束。**

内容由原读数定义，控制由原接续定义，交换子由原顺序定义，参照从原空间中选，恢复 $D$ 的公式也只消费这些内部对象。所谓“公理内生”，在这里的可核验含义是：*不再向 $\Omega$ 注入一套新的响应表，而是在 $\Omega$ 内部两种定义产物之间检查一一对应。*

这仍然是一项非平凡结构约束。第 [2](#sec-reverse) 节的全部原概率模型满足同样前端，却不满足 $\Xi$；故不能从“$\Omega$ 包含一切”单独推出该条件。把符合 $\Xi$ 的窗口定义成“初等量子块”当然可以，但还需要证明给定 $\Omega$ 中存在这样的块，以及原自然对象确实落在此类。只有未来找到更早的整体一致性原理，能独立排除那些反模型，$\Xi$ 才能从选择条件升级为更大理论的定理。

**与 $\zeta$ 或离线零点的关系。**

本轮证明没有用 $\zeta$ 零点，也不产生 RH 结论。若要建立关系，需要在同一个实际来源上明确构造：其全未来概率空间、准确逆、有限预测容量，以及通过 $\Xi$ 的原 $(A,e)$。随后还要有把离线零点变成上述原对象的破坏性证据的定理。项目 FIB 的条件秩二结果没有自动提供这条桥；“都出现谱、旋转或三维片”不足以建立等价。 [5](#ref-repofib)

整体里本来就有能被读出的差别，也有让这些差别转动的办法。先拿一个转向作参照，再拿一份原有差别当试针：把参照转向和另一转向换个先后次序，看试针多偏了多少。我们只要求，这种“换次序造成的偏动”，在除去参照自身后，既不会把两种不同的转向混成一种，也不会漏掉任何能读出的横向差别。这样，两方向一比较，就会长出第三个方向；如果还想多塞方向进来，三条回路就不能互相抵消，于是整体只留下一个三维旋转块。原来还要额外给的“每份内容对应什么响应”，现在可以从这个块里算出来。方向组成球面，三方向的乘积给出内部复数，相同方向上的振幅只差一个相位圈，原读数便写成 Born 概率。再把这些块按明确的复合和参考规则接起来，就得到有限维量子理论；实际能不能做出每个锐读口和每个联合门，继续由整体自己的原准备、原控制和原记录来兑现。

<a id="references"></a>

## 参考文献

<a id="ref-repohead"></a>

### [1]

 The Omega Institute, *trureturing*, 固定提交 `0d2719a1091903642f361f04994da098acd20e22`，2026-11-03 20:51:09 UTC。与上一轮比较：[https://github.com/the-omega-institute/trureturing/compare/8171c9756da2b5c654cba2eb1d04a4d93a9fadeb...0d2719a1091903642f361f04994da098acd20e22](https://github.com/the-omega-institute/trureturing/compare/8171c9756da2b5c654cba2eb1d04a4d93a9fadeb...0d2719a1091903642f361f04994da098acd20e22)。

<a id="ref-repo117"></a>

### [2]

 同仓库，*AURIC Common Source Self Reference and Observer Sequences C117*，尤其 §16。固定原文：[https://github.com/the-omega-institute/trureturing/blob/0d2719a1091903642f361f04994da098acd20e22/docs/develop/theory/AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md](https://github.com/the-omega-institute/trureturing/blob/0d2719a1091903642f361f04994da098acd20e22/docs/develop/theory/AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md)。

<a id="ref-repo124"></a>

### [3]

 同仓库，*AURIC Native Reciprocal Comparison and Finite Endpoint Quantum C123*，新增 C124 为 §§10–17。固定原文：[https://github.com/the-omega-institute/trureturing/blob/0d2719a1091903642f361f04994da098acd20e22/docs/develop/theory/AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md](https://github.com/the-omega-institute/trureturing/blob/0d2719a1091903642f361f04994da098acd20e22/docs/develop/theory/AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md)。

<a id="ref-repofour"></a>

### [4]

 同仓库，*Quantum Reality Four Path Full Record Recovery Bound Continuation II*，新 §43。[https://github.com/the-omega-institute/trureturing/blob/0d2719a1091903642f361f04994da098acd20e22/docs/develop/theory/QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_II.md](https://github.com/the-omega-institute/trureturing/blob/0d2719a1091903642f361f04994da098acd20e22/docs/develop/theory/QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_II.md)。

<a id="ref-repofib"></a>

### [5]

 同仓库，*FIB Atom Recursive Holographic Boundary Geometry Continuation III, Appendix III*，至 §141。[https://github.com/the-omega-institute/trureturing/blob/0d2719a1091903642f361f04994da098acd20e22/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_III.md](https://github.com/the-omega-institute/trureturing/blob/0d2719a1091903642f361f04994da098acd20e22/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_III.md)。

<a id="ref-watrous"></a>

### [6]

 John Watrous, *The Theory of Quantum Information*, 2018，作者公开稿，第 2 章，尤其定理 2.22。[https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)。
