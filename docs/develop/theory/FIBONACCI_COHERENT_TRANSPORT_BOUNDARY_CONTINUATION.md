# Fibonacci 相干运输边界续卷

## 42. 原生一次正向跨切口脉冲的实际事件张成

**定义 42.1（完整端点代数、指定脉冲与逐支调用预算）。** 路径空间
$H_m^c$、端点块代数 $\mathfrak A_m$ 和右追加包含 $j_m$ 严格取
[融合链卷 §12](FUSION_SPIN_CHAIN_QCA_CUT_OBSTRUCTIONS.md#12-从遗传树到有限融合空间对象与实际嵌入)
的定义 12.1、式（FT.2）–（FT.5）：初始标签为 $\mathbf1$，
每片叶的类型为 $\tau$，保留两个末端类型的全部合法路径，不作 End 筛选。
对整数 $L\ge1$，置 $n=3L+1$，并在同一环境代数中定义

$$
\begin{aligned}
X_L&=\mathfrak A_{n+3},\qquad
\iota=j_{n+2}\circ j_{n+1},\\
N_0&=j_n(\mathfrak A_n),\qquad B_0=\mathfrak A_{n+1},\\
N_L&=\iota(N_0),\qquad B_L=\iota(B_0)\subseteq X_L.
\end{aligned}
\tag{42.1}
$$

这里的包含均为实际路径基上的保单位星同态，不以相同维数替代。
[运输边界卷定义 41.1、定理 41.2](FIBONACCI_COHERENT_TRANSPORT_BOUNDARY.md#41-原生开放前缀三叶融合扩展与跨切口脉冲)
给原生开放前缀与这些融合路径的逐基对应。对固定的复数 $z$，
$|z|=1$、$z\ne1$，唯一脉冲原语为该卷定义 41.3 的正向门

$$
U_{L,z}=I+(z-1)P_n\in X_L.
\tag{42.2}
$$

$P_n$ 是融合卷 §14、式（FT.12）、（FT.14）的带权 TL 正交投影，
权重为 $d_{\mathbf1}=1,d_\tau=\varphi$，$\varphi^2=\varphi+1$、$\varphi>1$。
其酉性由融合卷命题 15.1 给出。

其余原语是任意有限仪器，其 Kraus 算子 $K_{y,r}$ 全部属于 $N_L$，且

$$
\sum_{y,r}K_{y,r}^*K_{y,r}=I_{X_L}.
\tag{42.3}
$$

保留结果 $y$；指标 $r$ 隐藏。同一 $y$ 的所有 Kraus 项必须使用同一续接。
有限自适应选择只依赖已保留结果和已声明控制。事件树、Boolean 接受或拒绝叶、
接受输出及其效果 $E_e$ 严格采用
[运输边界卷定理 39.1](FIBONACCI_COHERENT_TRANSPORT_BOUNDARY.md#39-任意固定酉与低层仪器的实际效果代数桥梁)
的递归，将其中低层 Kraus 替换为这里的 $K_{y,r}$，固定门替换为 $U_{L,z}$。
特别地，门节点拉回为 $`U_{L,z}^*E_eU_{L,z}`$，仪器节点拉回为
$`\sum_{y,r}K_{y,r}^*E_{e_y}K_{y,r}`$；中途接受表示接受该节点的全部后继叶。
对 $k=0,1$，令

$$
S_{L,z}^{(\le k)}
=\operatorname{span}_{\mathbb C}
\{E_e:\ e\text{ 为上述有限事件，每条根叶分支至多调用 }k\text{ 次脉冲}\}.
\tag{42.4}
$$

不同分支可以在不同位置调用门，但各自受同一预算限制。不授予逆脉冲、
其它相位、较细代数的仪器、隐藏指标读出或返回后再参与动作的环境。

**定理 42.2（原生一次正向事件的精确张成；repo-derived）。**
在定义 42.1 的完整操作合同下，对每个整数 $L\ge1$ 和每个
$z\in\mathbb C$、$|z|=1$、$z\ne1$，作为 $X_L$ 中的复线性空间，有

$$
S_{L,z}^{(\le1)}=B_L,
\qquad
S_{L,z}^{(\le0)}=N_L\subsetneq B_L.
\tag{42.5}
$$

等式包括 $B_0$ 的两个端点块中的每个矩阵单位在 $\iota$ 下的实际像；
不把同一矩阵单位的不同追加副本当作独立控制。所有参与张成的生成元都是
合法有限仪器与事件产生的正效果。结论是复线性张成的等式，并不声称
$B_L$ 中每个 $0\le G\le I$ 都单独由一次调用事件实现。

证明。（一）先在本证明内部使用定理 39.1 的过滤与极化步骤，保留调用次数。
令 $N$ 为任意有限维保单位复星子代数，$V$ 为固定酉，原语为 $N$ 中的
归一化有限仪器、正向 $V$ 和 Boolean 叶。记其至多零次、一次调用的
实际效果张成为 $S_N^{(\le0)}$、$S_{N,V}^{(\le1)}$。则

$$
\begin{aligned}
S_N^{(\le0)}&=N,\\
S_{N,V}^{(\le1)}&=M_{N,V},\\
M_{N,V}&=N+
\operatorname{span}_{\mathbb C}
\{A^*V^*XVB:\ A,B,X\in N\}.
\end{aligned}
\tag{42.6}
$$

为说明这里的下包含确实来自实际效果，先任取 $F\in N$、$0\le F\le I$。
以 $\sqrt F$、$\sqrt{I-F}$ 作两个保留结果的单 Kraus 仪器，只接受第一结果，
便零次调用实现效果 $F$。平方根属于 $N$，两项伴随平方之和为 $I$。
这些效果复线性张成 $N$：若 $X=X^*\in N$，取
$t\ge\max(1,\|X\|)$，则

$$
F=\frac{X+tI}{2t},\qquad 0\le F\le I,
\qquad X=2tF-tI.
\tag{42.7}
$$

任意 $X\in N$ 再分解为两个自伴元素的复线性组合。反向，零次调用树的
每次 Kraus 夹乘与求和都留在 $N$，由有限树归纳得到第一行等式。

对任意 $K\in N$，取 $\epsilon=(\|K\|+1)^{-1}>0$，使用两个保留结果

$$
K_{\mathrm{pass}}=\epsilon K,
\qquad K_{\mathrm{fail}}=\sqrt{I-\epsilon^2K^*K}.
\tag{42.8}
$$

它们都属于 $N$，且伴随平方之和为 $I$。第二结果立即拒绝；第一结果后
施加一次正向 $V$，再用上述零次调用仪器测试 $F$。接受效果恰为

$$
\epsilon^2K^*V^*FVK.
\tag{42.9}
$$

失败分支用零次门，成功分支用一次门。每个结果只有一个 Kraus 算子，
所以没有控制隐藏指标。利用（42.7）及复线性分解，对于任意 $X\in N$，
$Q_X(K)=K^*V^*XVK$ 属于实际一次调用效果的张成。极化恒等式为

$$
4A^*V^*XVB
=Q_X(A+B)-Q_X(A-B)-iQ_X(A+iB)+iQ_X(A-iB).
\tag{42.10}
$$

因此 $M_{N,V}\subseteq S_{N,V}^{(\le1)}$。这里只对不同合法事件的效果
取复线性组合，未把两个一次调用事件串接，也未把它们的效果相乘。

反向，$M_{N,V}$ 对 $N$ 的左右乘封闭，因

$$
C^*(A^*V^*XVB)D=(AC)^*V^*XV(BD)
\qquad(A,B,C,D,X\in N).
\tag{42.11}
$$

单位叶与零叶在 $N$ 中；仪器节点是这种夹乘的有限和。若根为门节点，
预算至多一次强制其整个续接为零次调用，故续接效果在 $N$，拉回在
$V^*NV\subseteq M_{N,V}$。若根为仪器节点，则对各保留结果的子树
归纳并求隐藏 Kraus 项之和。有限树归纳给上包含；这同时允许分支间
不同的门位置和保留结果自适应。至此证明（42.6），并得到该空间的
$N$ 双模封闭性。实际效果均自伴，所以其复线性张成还对伴随封闭。

（二）将环境 $X_L$ 中的实际操作精确降到 $B_0$ 内计算。
融合卷式（FT.5）对 $B_0$ 的任意矩阵单位给

$$
\iota(E^d_{p,q})
=\sum_{t\in\mathsf N(d,\tau)}
 \sum_{v\in\mathsf N(t,\tau)}
 E^v_{p t v,q t v}.
\tag{42.12}
$$

具体地，两个端点分别为

$$
\begin{aligned}
\iota(E^{\mathbf1}_{p,q})
&=E^{\mathbf1}_{p\tau\mathbf1,q\tau\mathbf1}
 +E^\tau_{p\tau\tau,q\tau\tau},\\
\iota(E^\tau_{p,q})
&=E^\tau_{p\mathbf1\tau,q\mathbf1\tau}
 +E^{\mathbf1}_{p\tau\mathbf1,q\tau\mathbf1}
 +E^\tau_{p\tau\tau,q\tau\tau}.
\end{aligned}
\tag{42.13}
$$

同一行中的 $p,q$ 具有该行指定的原端点；不同原端点的同形后缀不是
同一条完整路径。所有合法两步后缀都出现一次，没有端点筛选。

由融合卷 §14.2 的追加相容性，令
$V_z=I+(z-1)P_n\in B_0$，则

$$
U_{L,z}=\iota(V_z),\qquad N_L=\iota(N_0),\qquad B_L=\iota(B_0).
\tag{42.14}
$$

$\iota$ 保单位、单射且为星同态。因此 $N_0$ 中的合法仪器逐项送到
$N_L$ 中的合法仪器；反向，每个 $N_L$ 中的 Kraus 算子有唯一的
$N_0$ 原像，而归一化由单射性反映回来。平方根也与此有限维星同态相容。
把同一有限树的每个 Kraus 算子取原像，由叶向根归纳，效果递归满足

$$
E_e^{X_L}=\iota(E_e^{B_0}).
\tag{42.15}
$$

这个对应保持保留结果、隐藏指标的求和、控制选择和每条分支的调用次数。
每个环境事件都由此得到，且所有效果留在 $\iota(B_0)$。于是只须在
$B_0$ 内证明一次调用张成为 $B_0$、零次调用张成为 $N_0$；
（42.12）–（42.15）会把结论送到每枚实际嵌入矩阵单位，而不是单独的后缀副本。

（三）写出完整端点块。令

$$
E=H_n^{\mathbf1},\qquad F=H_n^\tau,\qquad
 a=\dim E=F_{n-1}>0,\qquad b=\dim F=F_n>0,
\tag{42.16}
$$

这里 Fibonacci 数取 $F_0=0,F_1=1$。在 $F$ 中，令 $D$ 为倒数第二个
标签是 $\tau$ 的路径所张空间。$E$ 中每条路径的倒数第二标签必为 $\tau$；
只将其最后标签由 $\mathbf1$ 改为 $\tau$，给出到 $D$ 的基等距同构
$T:E\to F$，记 $Q=TT^*$。补空间 $C=F\ominus D$ 恰由倒数第二标签
为 $\mathbf1$ 的路径组成，故 $\dim C=F_{n-2}$。

按新端点 $\mathbf1,\tau$ 排序，最后一步追加把 $H_{n+1}^{\mathbf1}$
识别为 $F$，把 $H_{n+1}^\tau$ 识别为 $E\oplus F$。式（FT.5）给

$$
\begin{aligned}
B_0&=\operatorname{End}(F)\oplus\operatorname{End}(E\oplus F),\\
N_0&=\{\nu(X,Y):X\in\operatorname{End}(E),\ Y\in\operatorname{End}(F)\},\\
\nu(X,Y)&=Y\oplus
 \begin{pmatrix}X&0\\0&Y\end{pmatrix}.
\end{aligned}
\tag{42.17}
$$

尤其 $Y$ 在两个新端点中重复，不能独立选择。置

$$
e=\nu(I_E,0)=0\oplus\begin{pmatrix}I_E&0\\0&0\end{pmatrix},
\qquad
f=\nu(0,I_F)=I_F\oplus\begin{pmatrix}0&0\\0&I_F\end{pmatrix}.
\tag{42.18}
$$

它们是 $N_0$ 中的互补正交投影，故测试 $e$ 或 $f$ 都是合法零次调用仪器。

（四）使用指定脉冲的全部块。置

$$
r=\varphi^{-1},\quad s=\sqrt r,\quad r^2+r=1,
\qquad \beta=(z-1)rs,\qquad a_0=1+(z-1)r^2.
\tag{42.19}
$$

在端点 $\mathbf1$，最后局部邻居相同为 $\mathbf1$ 时投影为 $1$，
不同时为 $0$；在端点 $\tau$，$E$ 与 $D$ 配对形成式（FT.14）的
二维块，$C$ 上投影为 $0$。因此没有丢弃任何路径的完整门为

$$
\begin{aligned}
(V_z)_{\mathbf1}&=Q+z(I_F-Q),\\
(V_z)_\tau&=
\begin{pmatrix}
a_0 I_E&\beta T^*\\
\beta T&I_F+(z-1)rQ
\end{pmatrix}.
\end{aligned}
\tag{42.20}
$$

记 $\alpha(X)=V_z^*XV_z$，$S=S_{N_0,V_z}^{(\le1)}$。
由（42.6）的双模封闭性，下面两个种子均在 $S$ 中：

$$
\begin{aligned}
R=e\alpha(f)f
 &=0\oplus\begin{pmatrix}0&cT^*\\0&0\end{pmatrix},
 &c&=\overline\beta(1-r+rz),\\
H=f\alpha(e)f
 &=0\oplus\begin{pmatrix}0&0\\0&|\beta|^2Q\end{pmatrix}.
\end{aligned}
\tag{42.21}
$$

这些等式由（42.20）逐块相乘得到，系数 $c$ 与运输边界卷式（41.8）相同。
$H$ 本身就是实际效果：先用 $(f,e)$ 测试 $f$，失败拒绝；成功后用一次
正向 $V_z$，再用 $(e,f)$ 测试 $e$，只接受成功。$R$ 则由（42.9）、
（42.10）保证在实际效果张成中；不需要将非自伴的 $R$ 当作单一效果。

对所有允许的相位，

$$
\beta\ne0,\qquad |\beta|^2=|z-1|^2r^3>0,
\qquad c\ne0.
\tag{42.22}
$$

最后一个断言因为 $1-r+rz=0$ 会强制
$z=-(1-r)/r=-r$，其模为 $r<1$。这与 $|z|=1$ 矛盾。
所以不存在需要另授相位或逆门才能避开的非平凡单位相位例外。

（五）用粗矩阵单位夹乘这两个种子，取得所有端点块。
固定 $E$ 中的一个路径基向量 $h$，记 $d=Th\in D$。
对 $p\in E$、$q\in F$ 的任意路径基向量，（42.17）给合法粗算子，且

$$
\nu(|p\rangle\langle h|,0)\,R\,
\nu(0,|d\rangle\langle q|)
=c\left[0\oplus
\begin{pmatrix}0&|p\rangle\langle q|\\0&0\end{pmatrix}\right].
\tag{42.23}
$$

双模封闭与 $c\ne0$ 给出端点 $\tau$ 的全部 $E\leftarrow F$ 矩阵单位。
伴随封闭再给全部 $F\leftarrow E$ 矩阵单位。这一步的伴随只是复线性
空间的运算，不是对脉冲原语取逆。

对 $p,q\in F$ 的任意路径基向量，同样有

$$
\nu(0,|p\rangle\langle d|)\,H\,
\nu(0,|d\rangle\langle q|)
=|\beta|^2\left[0\oplus
\begin{pmatrix}0&0\\0&|p\rangle\langle q|\end{pmatrix}\right].
\tag{42.24}
$$

于是端点 $\tau$ 内的全部 $F\leftarrow F$ 单位都在 $S$ 中，且它们的
端点 $\mathbf1$ 块为零。这也覆盖 $C$ 中的行列，因为粗 $Y$ 可在整个
$F$ 内任取矩阵单位，并非只在 $D$ 上行动。端点 $\tau$ 内的
$E\leftarrow E$ 单位已经属于 $\nu(\operatorname{End}(E),0)\subseteq N_0$。
因此端点 $\tau$ 的每个矩阵单位均属于 $S$。

最后，从 $N_0$ 中的重复单位减去刚取得的仅在端点 $\tau$ 非零的单位：

$$
\nu(0,|p\rangle\langle q|)
-\left[0\oplus\begin{pmatrix}0&0\\0&|p\rangle\langle q|\end{pmatrix}\right]
=|p\rangle\langle q|\oplus0.
\tag{42.25}
$$

这给端点 $\mathbf1$ 的每个矩阵单位。所有步骤仅为粗左右夹乘、伴随和
复线性组合，没有用一次调用效果之间的乘积来增加可达空间。
于是 $B_0\subseteq S$。反向，$N_0\subseteq B_0$、$V_z\in B_0$，
效果递归全在 $B_0$ 内，故 $S=B_0$。

零次调用由（42.6）恰张成 $N_0$。因 $a,b>0$，端点 $\tau$ 中任一非零
$E\leftarrow F$ 单位属于 $B_0$ 而不属于（42.17）的 $N_0$，故包含严格。
再由（42.12）–（42.15）的实际、单射运输得到（42.5）的全部等式与严格性。
例如 $L=1$ 时 $n=4$，$(a,b,\dim C)=(2,3,1)$，
$\dim B_0=b^2+(a+b)^2=34$、$\dim N_0=a^2+b^2=13$；
这些数直接来自合法路径递推，证明对所有 $L\ge1$ 使用的是上述统一块构造。
$\square$

定理 42.2 的过滤、极化和 Kraus 归一化是运输边界卷定理 39.1 的中间输入；
这里保留逐支一次预算，不调用该定理的无预算最小不变代数结论。
Fibonacci 路径 TL 矩阵是已有结构：Kauffman–Lomonaco，
[*The Fibonacci Model and the Temperley–Lieb Algebra*](https://arxiv.org/pdf/0804.4304v1)，
Theorem 2 给标准 Fibonacci 序列上的表示，其随后 Remark 明定两侧由 $P$ 夹住。
本节的初始 $\mathbf1$、完整双端点及实际追加约定则取融合卷 §12、§14，
不能用该文的端点约定直接替换。（42.21）–（42.25）把指定原生脉冲的
两个种子与重复端点副本分离相接，给这里的 repo-derived 有界事件张成结论；
不认领通用 TL 表示、过滤或极化的原创性，也不作世界范围的新颖性断言。

本节的线性事件空间与另行选择的正解码合同须分开。
Grigoletto–Ticozzi，[*Exact model reduction for discrete-time conditional quantum dynamics*](https://arxiv.org/html/2403.12575v2)，
Proposition 3 从 observation algebra 的条件期望及其 CPTP 分解构造条件模型；
它不提供这里的原生一次调用张成等式。Bluhm–Rauber–Wolf，
[*Quantum Compression Relative to a Set of Measurements*](https://arxiv.org/html/1708.04898v4)，
Corollary 8.5 讨论生成相同 C* 代数的效果集仍可具有不同压缩性质。
因此只认出生成 C* 代数不能替代（42.6）与实际效果的下包含。
运输边界卷定义 11.7、命题 11.8 的共同状态解码资源，以及 §35–§36 的
逐分支条件后继与可读记录假设，均是各自的附加合同，不扩充定义 42.1 的原语。

（42.5）确定全部允许一次调用事件统计所需的精确线性可观测空间；
它不提供每个正元素的单次实现、统计估计成本、$z\to1$ 时一致的条件数界、
记忆或压缩维数、返回环境的完备续接或物理实现结论。
特别地，（42.22）的非零系数允许在复线性张成中除法，
而 $|\beta|^2\to0$ 使这一代数步骤本身不构成一致稳定的取得过程。

## 追加锚（本行以下为增补区）
