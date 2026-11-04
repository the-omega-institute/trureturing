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

## 43. 完整原生一次脉冲事件的一阶下界与二次上界反例

**定义 43.1（实际事件偏差与正交态对的最坏偏差）。** 对每个整数
$L\ge1$ 和每个 $|z|=1$、$z\ne1$，严格采用定义 42.1 的初始标签 $\mathbf1$、全部合法路径、
$n=3L+1$ 及（42.16）–（42.20）的 $E,F,D,C,T,Q,B_0,N_0,V_z$。
以 $\mathcal F_{L,z}^{(\le1)}$ 表示定义 42.1 的有限事件树经
（42.14）–（42.15）取回 $B_0$ 后的实际接受效果集合；每条根叶分支
至多调用一次固定正向 $V_z$。仪器在 $N_0$ 中归一化，只保留结果 $y$，
同一结果的隐藏 Kraus 指标求和，叶值为 Boolean。两个端点块都保留，
不授予逆门、其它相位、较细仪器、参考寄存器或返回后续接的环境。

在 $B_0=\operatorname{End}(F)\oplus\operatorname{End}(E\oplus F)$ 上取
普通直和矩阵迹 $\operatorname{Tr}$，令 $\|\cdot\|$、$\|\cdot\|_1$、
$\|\cdot\|_{\mathrm{HS}}$ 分别为该表示的算子范数、迹范数与
Hilbert–Schmidt 范数。对任意 Hermitian 元素 $\Delta\in B_0$，定义

$$
\eta_{L,z}(\Delta)
=\sup_{G\in\mathcal F_{L,z}^{(\le1)}}
 \left|\operatorname{Tr}(\Delta G)\right|,
\qquad
\kappa_L(z)
=\inf_{\substack{\rho,\sigma\in B_0,\ \rho,\sigma\ge0\\
 \operatorname{Tr}\rho=\operatorname{Tr}\sigma=1,\ \rho\sigma=0}}
 \eta_{L,z}(\rho-\sigma).
\tag{43.1}
$$

此处态对遍历两个端点块的全部归一化正元素，没有选定支撑或删去路径。
事件集合本身只含实际正效果，不以其复线性张成或 $B_0$ 的全部正收缩替代。

**定理 43.2（完整 $L=1$ 载体的一阶事件界；repo-derived）。**
在定义 43.1 的合同下，对每个实数 $\theta$ 满足
$0<|\theta|\le1/288$，以及每个 Hermitian 元素 $\Delta\in B_0$，
完整的 $L=1$ 载体满足

$$
\eta_{1,e^{i\theta}}(\Delta)
\ge \frac{|\theta|}{8928}\|\Delta\|_1,
\qquad
\kappa_1(e^{i\theta})\ge\frac{|\theta|}{4464}.
\tag{43.2}
$$

特别地，对每个整数 $j\ge288$，令 $z_j=e^{i/j}$，则

$$
\frac{\kappa_1(z_j)}{|z_j-1|^2}\ge\frac{j}{4464}.
\tag{43.3}
$$

因此不存在有限常数 $C>0$，能使所有整数 $L\ge1$ 和所有
$|z|=1$、$z\ne1$ 同时满足 $\kappa_L(z)\le C|z-1|^2$。
从而不存在与 $L,z$ 无关的 $0<c\le C<\infty$，使
$c|z-1|^2\le\kappa_L(z)\le C|z-1|^2$ 在该全体参数上成立。
这里反驳的是其上界；结论不单独否定二次下界，也不确定一般 $L$ 的
相位阶、$\kappa_L$ 的精确值或匹配的一阶上界。

证明。（一）先固定 $L=1$、$t=|\theta|>0$，记
$\eta=\eta_{1,e^{i\theta}}(\Delta)$、$V=V_{e^{i\theta}}$。
由（42.16）–（42.20）及融合链卷定义 12.1 的合法路径递推，

$$
\dim E=2,\quad \dim F=3,\quad \dim D=2,\quad \dim C=1,
\qquad B_0\cong M_3(\mathbb C)\oplus M_5(\mathbb C).
\tag{43.4}
$$

这里 $F=D\oplus C$，$T:E\to D$ 是路径基等距同构，$Q=TT^*$。
令 $r=(\sqrt5-1)/2$、$k=r\sqrt r$。融合链卷（FT.14）及
（42.20）给完整脉冲生成投影

$$
P=(I_F-Q)\oplus
 \begin{pmatrix}r^2I_E&kT^*\\kT&rQ\end{pmatrix},
\qquad
V=I+(e^{i\theta}-1)P=e^{i\theta P}.
\tag{43.5}
$$

确实，$r^2+r=1$、$k^2=r^3$，故 $E\oplus D$ 的每个实对称
二维块有迹 $1$、行列式 $0$，是正交投影；端点 $\tau$ 的 $C$ 块为
$0$，端点 $\mathbf1$ 的块是 $I_F-Q$。这也直接确认 $P=P^*=P^2$、
$\|P\|=1$，并与融合链卷命题 15.1 的投影脉冲公式一致。

（二）定量使用（42.7）–（42.10）的实际过滤和极化。
每个 $H\in N_0$、$0\le H\le I$ 都是零次调用效果：两个保留结果
分别采用 $\sqrt H$、$\sqrt{I-H}$，只接受第一个结果。
它们属于 $N_0$，伴随平方之和为 $I$。特别地，$I$ 也是实际效果。
若 $S=S^*\in N_0$、$\|S\|\le1$，写 $S=2H-I$，其中
$H=(S+I)/2$，便有 $|\operatorname{Tr}(\Delta S)|\le3\eta$。
任意收缩 $X\in N_0$ 的实部和虚部均为自伴收缩，因此

$$
\left|\operatorname{Tr}(\Delta X)\right|\le6\eta
\qquad(X\in N_0,\ \|X\|\le1).
\tag{43.6}
$$

取收缩 $A,B,X\in N_0$。对
$K=A+B,A-B,A+iB,A-iB$ 中每一个，都有 $\|K\|\le2$。
令 $\epsilon=(\|K\|+1)^{-1}$，则 $\epsilon^{-2}\le9$。
（42.8）的 pass/fail 仪器在 fail 时立即拒绝，在 pass 后调用一次
正向 $V$，再作上述 $H$ 测试，只接受测试成功。于是
$`\epsilon^2K^*V^*HVK`$ 是实际接受效果，且

$$
\left|\operatorname{Tr}(\Delta K^*V^*HVK)\right|\le9\eta.
\tag{43.7}
$$

每个保留结果只有一个 Kraus 算子，伴随平方之和为 $I$；fail 分支零次调用，
pass 分支一次调用，没有读取隐藏指标。对自伴收缩 $S=2H-I$，将
（43.7）分别用于 $H$ 和 $I$，得到相应界 $27\eta$；再对
$X=\operatorname{Re}X+i\operatorname{Im}X$ 分解，得到

$$
\left|\operatorname{Tr}(\Delta K^*V^*XVK)\right|\le54\eta.
\tag{43.8}
$$

在（42.10）的极化恒等式中，四个系数的模均为 $1/4$，故
$`|\operatorname{Tr}(\Delta A^*V^*XVB)|\le54\eta`$。
另一方面 $`A^*XB`$ 是 $N_0$ 中的收缩，由（43.6）得

$$
\left|\operatorname{Tr}\bigl(\Delta A^*(V^*XV-X)B\bigr)\right|
\le60\eta.
\tag{43.9}
$$

所有有符号或复系数的组合只用于不同实际事件统计之间的三角不等式，
不被当作单一正效果，也没有将两个一次调用事件相乘或串接。

（三）对完整脉冲作一致的一阶展开。以 $[X,P]=XP-PX$ 记交换子，令
$\alpha_u(X)=e^{-iuP}Xe^{iuP}$。标准矩阵 Taylor 公式的积分余项给

$$
\alpha_\theta(X)=X+\theta i[X,P]+R_\theta(X),
\qquad \|R_\theta(X)\|\le2\theta^2\quad(\|X\|\le1).
\tag{43.10}
$$

因为一次交换子的范数至多 $2\|X\|$，二阶导数在每个实数 $u$ 处的
范数至多 $4\|X\|$；积分余项对 $\theta$ 的两个符号都给同一界。
由（43.9）、迹与算子范数的对偶不等式及 $\|A\|,\|B\|\le1$，
任意这样的收缩三元组满足

$$
\left|\operatorname{Tr}\bigl(\Delta A^*i[X,P]B\bigr)\right|
\le D_\theta,
\qquad
D_\theta=\frac{60\eta}{t}+2t\|\Delta\|_1.
\tag{43.11}
$$

$u$ 仅是解析展开的参数，操作上只使用固定相位 $\theta$；与 $X$ 的
比较是零次调用统计，没有增加另一种脉冲相位或逆脉冲。

（四）控制端点 $\tau$ 的全部 $E$–$F$ 矩阵元。记 $e=\nu(I_E,0)$，
由（43.5）有

$$
i[e,P]=0\oplus
 \begin{pmatrix}0&ikT^*\\-ikT&0\end{pmatrix}.
\tag{43.12}
$$

固定 $E$ 中的单位路径基向量 $h$，令 $d=Th\in D$。
对任意路径基向量 $p\in E$、$q\in F$，取
$`A^*=\nu(|p\rangle\langle h|,0)`$、
$B=\nu(0,|d\rangle\langle q|)$。这两个粗算子是收缩，且

$$
A^*i[e,P]B=ikE_{\tau,EF}(p,q),
\qquad
E_{\tau,EF}(p,q)=0\oplus
 \begin{pmatrix}0&|p\rangle\langle q|\\0&0\end{pmatrix}.
\tag{43.13}
$$

将（43.11）用于 $X=e$，得每个相应矩阵单位的迹配对模至多
$D_\theta/k$。由于 $\Delta$ 自伴，反向 $F$–$E$ 矩阵单位的配对
为其复共轭，满足同一界。全部 $E$–$E$ 单位已在
$\nu(\operatorname{End}(E),0)$ 中，由（43.6）其配对模至多 $6\eta$。

（五）在一阶分开重复的两个 $F$ 副本，并保留 $C$ 的全部行列。
取 $C$ 中的单位路径基向量 $c$，置 $Y=|d\rangle\langle c|$、
$X=\nu(0,Y)$。这是 $N_0$ 中的收缩，$YQ=0$、$QY=Y$。
由（43.5），$i[X,P]$ 的端点 $\mathbf1$ 块是 $iY$，端点 $\tau$
的 $F$–$F$ 块是 $-irY$。对整个 $F$ 中任意路径基向量 $p,q$，取
$`A^*=\nu(0,|p\rangle\langle d|)`$、
$B=\nu(0,|c\rangle\langle q|)$；它们是收缩，夹乘杀掉全部含 $E$
的块，给出

$$
\begin{aligned}
A^*i[X,P]B&=iW_{pq},\\
W_{pq}&=E_{\mathbf1}(p,q)-rE_{\tau,FF}(p,q),\\
E_{\mathbf1}(p,q)&=|p\rangle\langle q|\oplus0,\\
E_{\tau,FF}(p,q)&=0\oplus
 \begin{pmatrix}0&0\\0&|p\rangle\langle q|\end{pmatrix}.
\end{aligned}
\tag{43.14}
$$

故 $|\operatorname{Tr}(\Delta W_{pq})|\le D_\theta$。同时重复的粗单位

$$
Z_{pq}=\nu(0,|p\rangle\langle q|)
       =E_{\mathbf1}(p,q)+E_{\tau,FF}(p,q)
\tag{43.15}
$$

属于 $N_0$ 且范数为 $1$，其迹配对模至多 $6\eta$。精确解这两个
线性关系得到

$$
E_{\tau,FF}(p,q)=\frac{Z_{pq}-W_{pq}}{1+r},
\qquad
E_{\mathbf1}(p,q)=\frac{rZ_{pq}+W_{pq}}{1+r}.
\tag{43.16}
$$

因此两个端点中每个 $F$–$F$ 单位的迹配对模均至多
$6\eta+D_\theta$。这里 $p,q$ 遍历整个 $F=D\oplus C$，包含
$C$ 的全部行列；$X,A,B$ 中每个粗算子在两个端点都重复其自身的同一个
$F$ 分量，未引入独立端点控制。（43.16）只分离统计的线性组合，
没有把 $W_{pq}$ 或单个端点矩阵单位授为仪器原语。

（六）将全部矩阵元估计变成全体 Hermitian 元素的迹范数估计。
普通迹满足 $\operatorname{Tr}(\Delta E_{pq})=\Delta_{qp}$。
又因 $r>1/2$，有 $1/k<2\sqrt2<3$，所以（四）、（五）与（43.6）
控制完整块对角 $8\times8$ 矩阵的每个矩阵元：

$$
\max_{p,q}|\Delta_{pq}|\le6\eta+3D_\theta.
\tag{43.17}
$$

不同端点之间的矩阵元本来为零。标准奇异值 Cauchy–Schwarz 不等式及
逐项平方求和给

$$
\|\Delta\|_1
\le\sqrt8\|\Delta\|_{\mathrm{HS}}
\le8\sqrt8\max_{p,q}|\Delta_{pq}|
\le24\max_{p,q}|\Delta_{pq}|.
\tag{43.18}
$$

于是

$$
\begin{aligned}
\|\Delta\|_1
&\le144\eta+72D_\theta\\
&=\left(144+\frac{4320}{t}\right)\eta
  +144t\|\Delta\|_1.
\end{aligned}
\tag{43.19}
$$

当 $0<t\le1/288$ 时，$144t\le1/2$，吸收右端最后一项后，利用
$t\le1$ 得

$$
\|\Delta\|_1
\le\left(288+\frac{8640}{t}\right)\eta
\le\frac{8928}{t}\eta.
\tag{43.20}
$$

这证明（43.2）的第一式，对 $\Delta$ 没有无迹或特定态对的限制。
若 $\rho,\sigma\ge0$、普通迹均为 $1$ 且 $\rho\sigma=0$，则它们
支撑正交，$\|\rho-\sigma\|_1=\operatorname{Tr}\rho+
\operatorname{Tr}\sigma=2$。第一式对每一这样的态对同时给
$\eta_{1,e^{i\theta}}(\rho-\sigma)\ge t/4464$；对完整态对集合取
下确界，仍有（43.2）的第二式。这里没有用单个有利态对代替下确界。

（七）对整数 $j\ge288$，$z_j=e^{i/j}$ 是非平凡单位相位，并且

$$
\kappa_1(z_j)\ge\frac1{4464j},
\qquad
0<|z_j-1|^2=4\sin^2\!\left(\frac1{2j}\right)\le\frac1{j^2}.
\tag{43.21}
$$

相除得到（43.3）。对任意给定有限 $C>0$，取整数
$j>\max\{287,4464C\}$，则 $L=1$ 和 $z=z_j$ 已违反
$\kappa_L(z)\le C|z-1|^2$。同一个上界常数原须适用于所有 $L,z$，
故固定这一个合法 $L$ 的序列足以否定其全称命题，也否定相应双边比较。

本证明的实际效果供应取自定义 42.1、（42.7）–（42.10）和
（42.14）–（42.20）；路径、普通迹和投影脉冲分别沿用融合链卷
定义 12.1、（FT.2）–（FT.5）、（FT.14）–（FT.16）。极化、矩阵
Taylor 余项和上述范数不等式只作为推导中间步骤。定量结论来自
（43.14）–（43.16）的共享端点分离及（43.19）的全载体估计，
不从定理 42.2 的定性张成等式推断条件数。本结论限于所声明的有限维
仪器模型，不给出物理实现或样本取得成本。$\square$

## 追加锚（本行以下为增补区）

## 44. 完整原生一次正向脉冲事件的统一线性条件界

**定义 44.1（全长度、全相位的原生合同）。** 对每个整数 $L\ge1$，令
$n=3L+1$，严格取融合链卷定义 12.1 的初始标签 $\mathbf1$、全部合法路径空间
$E=H_n^{\mathbf1}$、$F=H_n^\tau$，不作端点或状态支撑筛选。沿用
（42.16）–（42.20）的实际路径等距映射 $T:E\to D\subset F$、
$Q=TT^*$、$F=D\oplus C$，以及

$$
\begin{aligned}
B_0&=\operatorname{End}(F)\oplus\operatorname{End}(E\oplus F),\\
N_0&=\{\nu(X,Y):X\in\operatorname{End}(E),\ Y\in\operatorname{End}(F)\},\\
\nu(X,Y)&=Y\oplus\operatorname{diag}(X,Y).
\end{aligned}
\tag{44.1}
$$

对每个 $z\in\mathbb C$、$|z|=1$、$z\ne1$，唯一门为（42.20）的
固定正向 $V_z$。实际接受效果集合 $\mathcal F_{L,z}^{(\le1)}$ 恰取
定义 42.1 的有限归一化仪器和 Boolean 事件树，经（42.14）–（42.15）
取回 $B_0$：Kraus 算子全在同一个共享 $Y$ 的 $N_0$ 中，保留结果 $y$，
隐藏指标求和且同一 $y$ 的隐藏项共用续接，每条根叶分支至多调用一次门。
允许保留结果上的有限自适应选择，不增加逆门、其它相位、较细仪器、
参考寄存器或返回后继续参与操作的环境。

取 $B_0$ 上的普通直和矩阵迹和相应迹范数 $\|\cdot\|_1$；
特别地，两个端点块各用其普通矩阵迹，不使用路径重数或融合维数加权。
沿用定义 43.1，明确写为

$$
\begin{aligned}
\eta_{L,z}(\Delta)
&=\sup_{G\in\mathcal F_{L,z}^{(\le1)}}
  |\operatorname{Tr}(\Delta G)|\qquad(\Delta=\Delta^*\in B_0),\\
\kappa_L(z)
&=\inf_{\substack{\rho,\sigma\in B_0,\ \rho,\sigma\ge0\\
 \operatorname{Tr}\rho=\operatorname{Tr}\sigma=1,\ \rho\sigma=0}}
 \eta_{L,z}(\rho-\sigma).
\end{aligned}
\tag{44.2}
$$

**定理 44.2（全载体、全非平凡单位相位的统一线性界；repo-derived）。**
在定义 44.1 的合同下，对每个整数 $L\ge1$、每个 $|z|=1$、$z\ne1$，
以及完整 $B_0$ 中的每个 Hermitian 元素 $\Delta$，有

$$
\eta_{L,z}(\Delta)\ge\frac{|z-1|}{512}\|\Delta\|_1.
\tag{44.3}
$$

因此，对两个完整端点块中全部普通迹为一的正交正态对取（44.2）的下确界，有

$$
\frac{|z-1|}{256}\le\kappa_L(z)\le4|z-1|.
\tag{44.4}
$$

常数不依赖 $L,z$ 或路径空间维数。这里比较的是实际接受事件的偏差，
没有将实际效果集合换成其线性张成或整个 $B_0$ 的正效果区间。

证明。（一）固定任意允许的 $L,z$，记

$$
\delta=|z-1|,\qquad r=\varphi^{-1}=\frac{\sqrt5-1}{2},\qquad s=\sqrt r,
\qquad r^2+r=1,\quad 1-r=r^2,\quad \frac12<r<1.
\tag{44.5}
$$

由（42.16）的实际路径构造，$\dim E=F_{n-1}\ge2$、
$\dim C=F_{n-2}\ge1$，所以 $D$、$C$ 均非零。记 $e=\nu(I_E,0)$，
$V=V_z$。融合链卷 §12 的路径包含与 §14 的带权 TL 投影给（42.20），即

$$
\begin{aligned}
V_{\mathbf1}&=Q+z(I_F-Q),\\
V_\tau&=\begin{pmatrix}a_0I_E&\beta T^*\\\beta T&U\end{pmatrix},\\
a_0&=r+r^2z,\qquad \beta=(z-1)r^{3/2},\qquad
U=I_F+(z-1)rQ.
\end{aligned}
\tag{44.6}
$$

这保留全部路径及两个端点块。任意 Hermitian $\Delta$ 唯一写成

$$
\Delta=A\oplus\begin{pmatrix}H&B\\B^*&J\end{pmatrix},
\qquad S=A+J,\qquad \eta=\eta_{L,z}(\Delta),
\tag{44.7}
$$

其中 $A,J$ 作用于整个 $F$，$H$ 作用于整个 $E$，$B:F\to E$。

（二）定量复用（42.7）–（42.10）的过滤与极化。每个 $R\in N_0$、
$0\le R\le I$ 都是实际零次调用效果：取两个保留结果的 Kraus 算子
$\sqrt R$、$\sqrt{I-R}$，只接受第一结果。它们属于 $N_0$ 且归一化。
分别测试 $H$ 的正、负谱投影所对应的 $\nu(X,0)$，以及 $S$ 的正、负
谱投影所对应的 $\nu(0,Y)$，得到

$$
\|H\|_1\le2\eta,\qquad \|S\|_1\le2\eta.
\tag{44.8}
$$

对任意收缩 $M,N\in N_0$ 和 $R\in N_0$、$0\le R\le I$，还有

$$
|\operatorname{Tr}(\Delta M^*V^*RVN)|\le9\eta.
\tag{44.9}
$$

确实，对 $K=M+N,M-N,M+iN,M-iN$ 分别有 $\|K\|\le2$。
取 $\epsilon=(\|K\|+1)^{-1}$，pass/fail 仪器的 Kraus 算子为

$$
\epsilon K,\qquad \sqrt{I-\epsilon^2K^*K}.
\tag{44.10}
$$

fail 立即拒绝；pass 后用一次固定正向 $V$，再作零次调用的 $R$ 测试。
接受效果为 $`\epsilon^2K^*V^*RVK`$，故未缩放配对的模至多
$\epsilon^{-2}\eta\le9\eta$。（42.10）的极化恒等式有四个模为
$1/4$ 的系数，三角不等式给（44.9）。复系数只用于不同实际事件统计的
比较，不把所得双线性表达式授为正效果，也不串接两个一次调用事件。

（三）不逐个估计矩阵元，而控制全部矩形相干。对任意收缩 $W:F\to E$，
在（44.9）取 $M=e$、$N=\nu(0,TW)$、$R=e$。因为 $T^*T=I_E$，
$\|TW\|\le1$，逐块乘法给

$$
M^*V^*eVN
=0\oplus\begin{pmatrix}0&\overline{a_0}\beta W\\0&0\end{pmatrix}.
\tag{44.11}
$$

其与 $\Delta$ 的配对为 $\overline{a_0}\beta\operatorname{Tr}(B^*W)$。
矩形矩阵的迹范数对偶公式
$\|B\|_1=\sup_{\|W\|\le1}|\operatorname{Tr}(B^*W)|$
于是给

$$
\|B\|_1\le\frac{9\eta}{|a_0\beta|}
\le\frac{9\eta}{\delta r^{9/2}},
\tag{44.12}
$$

其中用了 $|a_0|\ge r-r^2=r^3$、$|\beta|=\delta r^{3/2}$。
该对偶公式也可直接由奇异值分解取得：极分解的部分等距因子达到上确界，
任意收缩的配对至多为奇异值之和。因此没有引入矩阵维数因子。
$W$ 遍历整个 $F\to E$ 的收缩，未限制其在 $F$ 中的输入支撑。

（四）用两条路径的输出测试分开共享端点副本。在 $D,C$ 中分别取单位路径
向量 $d,c$，令

$$
\psi=\frac{d+c}{\sqrt2},\qquad
u_0=1-r+rz,\qquad
 t=\overline z-u_0=-(z-1)(\overline z+r).
\tag{44.13}
$$

这里 $u_0$ 是标量，不是（44.1）的嵌入符号 $\nu$。
$|u_0|\le1$，且 $|t|\ge\delta(1-r)=\delta r^2>0$。
由（44.6），$V_{\mathbf1}\psi=(d+zc)/\sqrt2$、
$U\psi=(u_0d+c)/\sqrt2$，所以两份 $F$ 输出矩阵的差在基 $d,c$ 上为

$$
Z=|V_{\mathbf1}\psi\rangle\langle V_{\mathbf1}\psi|
  -|U\psi\rangle\langle U\psi|
=\frac12\begin{pmatrix}1-|u_0|^2&t\\\overline t&0\end{pmatrix},
\tag{44.14}
$$

其余方向为零。置 $\lambda=\overline t/|t|$、
$w=(d+\lambda c)/\sqrt2$，并在整个 $F$ 上取 $Y=|w\rangle\langle w|$。
定义

$$
\begin{aligned}
p_1&=\langle V_{\mathbf1}\psi,YV_{\mathbf1}\psi\rangle,\qquad
p_2=\langle U\psi,YU\psi\rangle,\\
h&=p_1-p_2=\langle w,Zw\rangle
 =\frac{1-|u_0|^2}{4}+\frac{|t|}{2}
 \ge\frac{\delta r^2}{2}.
\end{aligned}
\tag{44.15}
$$

$V_{\mathbf1}$ 酉，$U$ 是酉 $V_\tau$ 的压缩，故 $0\le p_1,p_2\le1$。
末端测试 $\nu(0,Y)$ 是实际粗效果，其 $E$ 分量为零。
$\lambda$ 只选择合同已允许的粗仪器，不是另一次门相位。

（五）对每个正输入收缩构造归一化的制备事件。有限维的
trace-and-prepare 与重置取运输边界卷 §24 的低层重置构造及命题 33.2
的有限 CP 制备步骤为既有输入；通用 Holevo 测量后制备形式及秩一 Kraus
表示见 Horodecki–Shor–Ruskai，
[*Entanglement Breaking Channels*, quant-ph/0302031v2](https://arxiv.org/html/quant-ph/0302031v2)，
Theorems 2、4（尤其 4(A)、4(D) 及保迹归一化条件）。这里采用该版本正文
标题；其 arXiv 摘要元数据题为 *General Entanglement Breaking Channels*。
这些通用构造是已知中间工具；此处须在共享 $Y$ 的实际仪器中验证它们的嵌入。

任取 $0\le R\le I_F$，令 $(v_j)_{j=1}^{\dim F}$ 为整个 $F$ 的正交归一基。
只保留 pass、fail 两个结果；pass 有隐藏 Kraus 项，fail 有一个项，分别为

$$
\begin{aligned}
K_j&=\nu(0,|\psi\rangle\langle v_j|\sqrt R),\\
K_{\mathrm{fail}}&=\nu(I_E,\sqrt{I_F-R}),\\
\sum_jK_j^*K_j+K_{\mathrm{fail}}^*K_{\mathrm{fail}}
&=\nu(0,R)+\nu(I_E,I_F-R)=I_{B_0}.
\end{aligned}
\tag{44.16}
$$

所有项在同一个 $N_0$ 中，每个 $F$ 分量都在两个端点相同地重复。
fail 拒绝；pass 后，不论隐藏 $j$ 为何，都用同一个固定正向 $V$，
再测试同一个 $\nu(0,Y)$，只接受测试成功。因此没有保留或控制 $j$。
对这些隐藏项直接求和，实际接受效果恰为

$$
G_R=p_1R\oplus\begin{pmatrix}0&0\\0&p_2R\end{pmatrix}.
\tag{44.17}
$$

具体地，pass 夹乘中的 $E$ 分量为零，故所有 $E$–$F$ 角消失；
在两份 $F$ 上分别用
$\sum_j\sqrt R|v_j\rangle\langle\psi|Z_0|\psi\rangle\langle v_j|\sqrt R
=\langle\psi,Z_0\psi\rangle R$
得到系数 $p_1,p_2$。这同时证明（44.17）的正性及实际可达性。
零次调用的 $\nu(0,R)$ 与 $\Delta$ 的配对是 $\operatorname{Tr}(SR)$，故

$$
\begin{aligned}
h\operatorname{Tr}(AR)
 &=\operatorname{Tr}(\Delta G_R)-p_2\operatorname{Tr}(SR),\\
|h\operatorname{Tr}(AR)|&\le2\eta.
\end{aligned}
\tag{44.18}
$$

分别取 $A$ 的正、负谱投影为 $R$，由（44.15）得

$$
\|A\|_1\le\frac{4\eta}{h}\le\frac{8\eta}{\delta r^2},
\qquad
\|J\|_1\le\|S\|_1+\|A\|_1
\le2\eta+\frac{8\eta}{\delta r^2}.
\tag{44.19}
$$

$R$ 和 $(v_j)$ 都遍历整个 $F$，所以两个完整 $F$ 副本中包括全部 $C$
行列的任意算子都受此估计控制。

（六）拼合全体 Hermitian 元素的界。奇异值分解给精确等式

$$
\left\|\begin{pmatrix}0&B\\B^*&0\end{pmatrix}\right\|_1=2\|B\|_1.
\tag{44.20}
$$

将（44.8）、（44.12）、（44.19）代入迹范数三角不等式，得到

$$
\begin{aligned}
\|\Delta\|_1
&\le\|A\|_1+\|H\|_1+\|J\|_1+2\|B\|_1\\
&\le\left(4\delta+\frac{16}{r^2}+\frac{18}{r^{9/2}}\right)
 \frac{\eta}{\delta}.
\end{aligned}
\tag{44.21}
$$

由于 $0<\delta\le2$、$r>1/2$ 以及
$r^{-9/2}<16\sqrt2<24$，括号内小于
$8+64+432=504<512$，这就证明（44.3）。
若 $\rho,\sigma$ 是（44.2）中的任意态对，正性及 $\rho\sigma=0$
使支撑正交，故 $\|\rho-\sigma\|_1=2$。将（44.3）用于每一这样的态对，
再对完整集合取下确界，得 $\kappa_L(z)\ge\delta/256$；
没有用一个有利态对替换最坏态对的下确界。

（七）对整个自适应事件族证明上界。任取整个 $F$ 中的单位向量 $v$，令

$$
\rho=|v\rangle\langle v|\oplus0,\qquad
\sigma=0\oplus\operatorname{diag}(0,|v\rangle\langle v|).
\tag{44.22}
$$

两态均正、普通迹为一且支撑正交；它们对每个 $\nu(X,Y)\in N_0$ 的
配对相同。任给一个合法有限事件树，其接受效果记为 $G$，将所有脉冲节点
改成恒等操作，得到零次调用效果 $G_0\in N_0$。因为每条根叶分支至多
有一个脉冲，原树中的脉冲节点构成反链，即任意两个之间没有祖先关系。

对任意归一化正输入 $\omega\in B_0$，记这些节点前的未归一化正态为
$\omega_j$，其中隐藏 Kraus 指标已求和。在原树及替换后的树中，这些
$\omega_j$ 相同，因为各节点前都没有脉冲。逐个使用仪器归一化，互不为
祖先的节点所承载的概率质量之和不超过根的质量，故
$\sum_j\operatorname{Tr}\omega_j\le1$。每个脉冲后的续接都零次调用，
有接受效果 $H_j\in N_0$、$0\le H_j\le I$。于是

$$
\operatorname{Tr}(\omega(G-G_0))
=\sum_j\operatorname{Tr}\bigl(\omega_j(V^*H_jV-H_j)\bigr).
\tag{44.23}
$$

这允许不同保留结果在不同深度调用门，也允许从未到达任何脉冲的分支。
由 $V=I+(z-1)P$、$P=P^*=P^2$（融合链卷命题 15.1 及（42.14）），
$\|V-I\|\le\delta$。利用 $V$ 酉及 $H_j$ 为正收缩，有

$$
\begin{aligned}
\|V^*H_jV-H_j\|
&\le\|(V^*-I)H_jV\|+\|H_j(V-I)\|\le2\delta,\\
|\operatorname{Tr}(\omega(G-G_0))|
&\le2\delta\sum_j\operatorname{Tr}\omega_j\le2\delta.
\end{aligned}
\tag{44.24}
$$

分别用于（44.22）的 $\rho,\sigma$，再用
$\operatorname{Tr}((\rho-\sigma)G_0)=0$，得到

$$
|\operatorname{Tr}((\rho-\sigma)G)|\le4\delta
\qquad(G\in\mathcal F_{L,z}^{(\le1)}).
\tag{44.25}
$$

先取整个实际事件族的上确界，再将这一合法态对代入（44.2）的下确界，
即得 $\kappa_L(z)\le4\delta$。

（八）操作桥梁与适用范围。（二）至（五）使用的都是有限、归一化的
$N_0$ 仪器和 Boolean 叶，分支上只有零次或一次固定正向门；唯一具有
多个隐藏 Kraus 项的 pass 结果在全部隐藏项上共用续接。所有有符号或
复系数组合只出现在实际事件统计之间的不等式中。（七）涵盖任意有限
自适应树、保留结果、隐藏项求和及依分支而变的门位置。
（42.14）–（42.15）的单射保单位星同态逐项保持这些仪器、效果递归和
逐支调用数；普通迹及态域则明确取其约化代数 $B_0$ 中的（44.2），
不把环境表示的重复副本迹当作该普通迹。$E$、两个完整 $F$ 副本及全部
合法路径在估计中始终保留。

受限测量偏差与正交态最坏区分的标准背景见 Lancien–Winter，
[*Distinguishing multi-partite states by local measurements*, arXiv:1206.2884v2](https://arxiv.org/html/1206.2884v2)，
§I 及 §IV 的式 (4)、Proposition 8、Theorems 9–10；其中局域、LOCC、PPT
等测量族不被认同为此处共享 $Y$ 的事件族。通道距离的单次操作解释和
实现连续性背景见 Kretschmann–Schlingemann–Werner，
[*The Information-Disturbance Tradeoff and the Continuity of Stinespring's Representation*, quant-ph/0605009v1](https://arxiv.org/html/quant-ph/0605009v1)，
§II.2 式 (5)–(9) 及 §III.3 Theorem 1、式 (18)。本证明只在（44.24）
使用初等投影脉冲估计，没有因此取得一般通道测试器或参考系统权限。

路径与运输的输入仍归融合链卷 §12、§14 和本卷 §42；过滤、极化、
有限制备及范数对偶是上述既有工具。（44.15）–（44.19）的归一化共享副本
分离、（44.12）与（44.21）的无维数损失拼合，以及（44.23）的逐支反链
归约构成本节的原生定量综合推导，不从定理 42.2 的线性张成推出条件界。
结论覆盖定理 43.2 之外的全部允许长度和全部非平凡单位相位，但不声称
常数最优、物理可用性、样本复杂度或世界范围原创性。$\square$

## 追加锚（本行以下为增补区）
