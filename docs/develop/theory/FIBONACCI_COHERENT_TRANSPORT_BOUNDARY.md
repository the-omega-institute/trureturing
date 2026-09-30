# Fibonacci 相干运输：进位、续接边界与区域容量

## 1. 有限组成模型与带操作的边界

**定义 1.1（组成标签与有限提升）。** 固定整数 $d,e\ge2$，置

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
A=(\mathbb Z/d\mathbb Z)^2,\qquad
H=(\mathbb Z/e\mathbb Z)^2.
$$

模 $r$ 的向量 $[x]_r$ 一律取坐标位于 $\{0,\ldots,r-1\}$ 的代表。有限 Hilbert 空间记为 $\mathcal H_A=\mathbb C^A$、$\mathcal H_H=\mathbb C^H$；$\mathcal B(\mathcal H)$ 表示其全部线性算子，$E_{aa'}=|a\rangle\langle a'|$。对任意 $r\ge2$ 定义置换酉

$$
U_r|x\rangle=|[Mx]_r\rangle.
$$

因 $\det M=-1$，此定义在每个模数上都可逆。由 [FIB 第 25 节的数字分解](https://github.com/the-omega-institute/trureturing/blob/64b78db1ad18a8a90b42e13a412dfc281d5c0922/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#L1760)，逐坐标写 $x=a+dh$，将模 $de$ 的组成空间识别为 $\mathcal H_A\otimes\mathcal H_H$；$U$ 表示 $U_{de}$ 在这一指定识别下的算子。

这里的标签是组成余数。[FIB 第 3.3 节](https://github.com/the-omega-institute/trureturing/blob/64b78db1ad18a8a90b42e13a412dfc281d5c0922/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#L67)中的有序二叉树到组成向量的映射忘记叶序和括号，再取模又忘记整数提升。上述 Hilbert 空间没有把被忘记的树结构补回；第 9 节的区域字标签另行定义。

**定义 1.2（进位与平移）。** 对 $a=(a_0,a_1)\in A$ 定义

$$
f(a)=[Ma]_d,\qquad
k(a)=\left\lfloor\frac{a_0+a_1}{d}\right\rfloor\in\{0,1\},\qquad
c(a)=(0,k(a))\in H.
$$

对 $v\in H$ 令 $T_v|h\rangle=|h+v\rangle$，并记 $R=T_{(1,0)}$。本卷的层间运输由

$$
U|a,h\rangle=|f(a),Mh+c(a)\rangle
$$

给定。这里高层运算模 $e$，低层运算模 $d$。这是 [FIB 第 26 节](https://github.com/the-omega-institute/trureturing/blob/64b78db1ad18a8a90b42e13a412dfc281d5c0922/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#L1836)操作进位律的 Fibonacci 实例。

**定义 1.3（仪器分支与条件充分性）。** 在指定输入、输出空间上，一次仪器由有限族完全正映射

$$
\mathcal I_y(\rho)=\sum_\mu K_{y\mu}\rho K_{y\mu}^\dagger,
\qquad \sum_{y,\mu}K_{y\mu}^\dagger K_{y\mu}=I
$$

组成。记录 $y$ 的概率为 $p_y=\operatorname{Tr}\mathcal I_y(\rho)$；仅在 $p_y>0$ 时定义条件态 $\mathcal I_y(\rho)/p_y$。效果 $E_y=\sum_\mu K_{y\mu}^\dagger K_{y\mu}$ 只规定概率，不替代整个分支。采用此标准仪器约定以及半迹距离 $D(\rho,\sigma)=\frac12\|\rho-\sigma\|_1$，参见 Watrous, [*The Theory of Quantum Information*，第 2、3 章](https://cs.uwaterloo.ca/~watrous/TQI/)。

一个操作合同 $\mathscr A$ 指定空间类型、允许通道与仪器、可读记录和动作选择规则。有限自适应协议是在每条已有记录路径上选择下一项允许操作的有限树；选择器只使用已经保留的记录及声明的控制数据。边界映射 $q$ 对 $\mathscr A$ 条件充分，指相同 $q(\rho)$ 的输入给出相同的整条记录分布，且每条正概率路径的后继边界相同；动作合法域及选择器也必须能由同一边界和记录决定。零概率路径没有条件态义务。

这采用 [FIB 第 55 节](https://github.com/the-omega-institute/trureturing/blob/64b78db1ad18a8a90b42e13a412dfc281d5c0922/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#L3261)及[动态边界卷第 1、2 节](https://github.com/the-omega-institute/trureturing/blob/64b78db1ad18a8a90b42e13a412dfc281d5c0922/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md#L15)的合法性、读数和后继同时下降要求。以下每个充分性结论均另给操作合同；不把当前约化态相等定义成未来等价。

## 2. 采样纤维、来源坐标与实际时钟

**定义 2.1（同一来源的采样仪器）。** 固定 $n\ge2$、$m\ge2$ 和整数 $0\le t_0<\cdots<t_{m-1}$。本节空间为 $\mathcal K_n=\mathbb C^{(\mathbb Z/n\mathbb Z)^2}$，不预设 $n=d$ 或 $n=de$。置 $F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$，并令

$$
r_t(x)=(M^t x)_1=F_t x_0+F_{t+1}x_1\pmod n,\qquad
O_{\mathcal T}(x)=(r_{t_0}(x),\ldots,r_{t_{m-1}}(x)),
$$

$$
g=\gcd(t_1-t_0,\ldots,t_{m-1}-t_0),\qquad
Q_z=\sum_{x:x_1=z}|x\rangle\langle x|.
$$

对实际可达的 $y=(y_0,\ldots,y_{m-1})\in\operatorname{im}O_{\mathcal T}$，来源坐标投影为

$$
P_y=\sum_{x:O_{\mathcal T}(x)=y}|x\rangle\langle x|
=\prod_{i=0}^{m-1}U_n^{-t_i}Q_{y_i}U_n^{t_i}.
$$

乘积中的投影在来源计算基上均对角，因而交换。来源坐标 Lüders 分支是 $\rho\mapsto P_y\rho P_y$；实际时钟次序在命题 2.2 中显式给出。采样核公式使用 [FIB 第 44.2 节](https://github.com/the-omega-institute/trureturing/blob/64b78db1ad18a8a90b42e13a412dfc281d5c0922/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#L2782)。

**命题 2.2（纤维维数与末钟条件态）。** 对定义 2.1 的每个实际可达 $y$，有

$$
\operatorname{rank}P_y=\gcd(n,F_g).
$$

若从时钟 $0$ 的密度算子 $\rho$ 出发，在相邻采样时刻间施加 $U_n$，在每个 $t_i$ 执行 $\{Q_z\}$ 的 Lüders 仪器，则整条记录 $y$ 的 Kraus 算子、概率与末钟条件态分别为

$$
\begin{aligned}
K_y&=Q_{y_{m-1}}U_n^{t_{m-1}-t_{m-2}}\cdots
Q_{y_1}U_n^{t_1-t_0}Q_{y_0}U_n^{t_0}
=U_n^{t_{m-1}}P_y,\\
p_y&=\operatorname{Tr}(P_y\rho),\\
\rho_{y,\mathrm{last}}&=
\frac{U_n^{t_{m-1}}P_y\rho P_yU_n^{-t_{m-1}}}{p_y}\qquad(p_y>0).
\end{aligned}
$$

证明。采样映射是有限加法群同态，每个非空纤维是其核的陪集。FIB 第 44.2 节的 Smith 因子 $1,F_g$ 给出核大小 $\gcd(n,F_g)$，这就是投影的维数。将每个 $Q_{y_i}$ 拉回来源时钟并消去相邻酉，得到 $K_y=U_n^{t_{m-1}}P_y$。于是 $K_y^\dagger K_y=P_y$，取迹和正概率归一化得到其余公式。若输入为纯态且 $p_y>0$，条件态是一个归一化向量的投影，其秩为 $1$；$\operatorname{rank}P_y$ 是容许纤维的维数，不是该条件纯态的秩。$\square$

**命题 2.3（声明的采样操作不读相位）。** 在 $\mathcal K_n$ 上，允许的操作为计算基置换与计算基对角 Kraus 仪器，最后仍用同类仪器读出。对任意有限自适应协议，两个具有相同计算基对角元的密度算子给出相同记录概率；每条正概率路径的后继对角元也相同。因此对任意不同标签 $x,x'$，态 $(|x\rangle+|x'\rangle)/\sqrt2$ 与 $(|x\rangle-|x'\rangle)/\sqrt2$ 在此合同下不可区分。定义 2.1 的采样协议属于这个合同。

证明。若 $K_{y\mu}|x\rangle=k_{y\mu}(x)|x\rangle$，则

$$
\bigl[\mathcal I_y(\rho)\bigr]_{xx}
=\sum_\mu|k_{y\mu}(x)|^2\rho_{xx}.
$$

置换仅重排这些对角元。因此一条分支的概率及未归一化后继对角元只依赖输入对角元。沿有限协议树归纳：同一已有记录使选择器取同一操作，新记录概率相同；当累计概率为正时，以同一正数归一化，后继对角元继续相同。两给定纯态有相同对角元，故结论成立。

仅要求效果对角不足以得到此结论。在 $\operatorname{span}\{|x\rangle,|x'\rangle\}$ 上取把两种相位态分别送到 $|x\rangle,|x'\rangle$ 的酉，并在正交补上取恒等。其单分支效果为 $I$，但随后计算基测量完全区分两输入。故此处约束的是实际 Kraus 分支，不能扩大到任意具有对角效果的仪器，也不能包含第 8 节的 $W(t)$。$\square$

**定义 2.4（采样合同的时钟与切口）。** 采样记录同时包含 $n,\mathcal T,y$ 和所用仪器。[FIB 第 45 节](https://github.com/the-omega-institute/trureturing/blob/64b78db1ad18a8a90b42e13a412dfc281d5c0922/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#L2854)给出的粗步长 $g$ 上闭合与细步长 $1$ 上不闭合，适用于其声明的经典来源读数；它不把 $P_y$ 自动变为任意相干操作的充分态。类似地，[FIB 第 46 节](https://github.com/the-omega-institute/trureturing/blob/64b78db1ad18a8a90b42e13a412dfc281d5c0922/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#L2880)的四端口 Schmidt 谱属于联合单射的模组成采样态。第 9 节使用另一种区域字空间，其切口不由四个时刻端口替代。

## 3. 进位相干与单步最大输出代数

**定义 3.1（进位扇区）。** 记

$$
A_i=\{a\in A:k(a)=i\},\qquad
\mathcal H_i=\operatorname{span}\{|a\rangle:a\in A_i\},\qquad
P_i=\sum_{a\in A_i}E_{aa}\quad(i=0,1).
$$

$P_0+P_1=I_A$。本节的 $P_i$ 是进位扇区投影，与第 2 节带采样记录下标的 $P_y$ 分属不同定义。令 $\Delta_A$ 为计算基对角代数，$\alpha(B)=U_d^\dagger B U_d$。

**定理 3.2（单步低层可观测量的精确代数）。** 对任意 $d,e\ge2$，定义

$$
\mathcal D_{\mathrm{out}}
=\{B\in\mathcal B(\mathcal H_A):
U^\dagger(B\otimes I_H)U\in\mathcal B(\mathcal H_A)\otimes I_H\}.
$$

则

$$
\boxed{\mathcal D_{\mathrm{out}}
=U_d\bigl(\mathcal B(\mathcal H_0)\oplus\mathcal B(\mathcal H_1)\bigr)U_d^\dagger.}
$$

对其中的 $B$，有 $U^\dagger(B\otimes I_H)U=\alpha(B)\otimes I_H$；对不在其中的 $B$，其单步输出期望不能对全部联合输入仅由低层约化态决定。扇区和代数维数为

$$
\dim\mathcal H_0=\frac{d(d+1)}2,\qquad
\dim\mathcal H_1=\frac{d(d-1)}2,\qquad
\dim_{\mathbb C}\mathcal D_{\mathrm{out}}
=\dim_{\mathbb R}(\mathcal D_{\mathrm{out}})_{\mathrm{sa}}
=\frac{d^2(d^2+1)}2.
$$

证明。令 $V_a=T_{c(a)}U_e$。因 $M(1,0)=(0,1)$，有

$$
V_a=U_eR^{k(a)},\qquad
U=\sum_a|f(a)\rangle\langle a|\otimes V_a.
$$

逐个矩阵单位展开得到

$$
U^\dagger(B\otimes I_H)U
=\sum_{a,a'}B_{f(a),f(a')}E_{aa'}\otimes R^{k(a')-k(a)}.
$$

由于 $e\ge2$，$R$ 与 $R^{-1}$ 都不是标量恒等算子。各 $E_{aa'}$ 线性独立，所以此算子属于 $\mathcal B(\mathcal H_A)\otimes I_H$，当且仅当 $k(a)\ne k(a')$ 时 $B_{f(a),f(a')}=0$。这正是 $\alpha(B)$ 在两进位扇区间无交叉块的条件。保留的项中高层因子全为 $I_H$，给出所述拉回公式。

若某输出期望对所有联合密度算子都只依赖偏迹，则其线性泛函消灭偏迹核；有限维对偶性给出对应算子必须属于 $\mathcal B(\mathcal H_A)\otimes I_H$。对自伴算子也可直接用满秩密度算子加减足够小的自伴偏迹零扰动得到同一结论。因此上述代数确实最大。计数 $a_0+a_1<d$ 得 $1+2+\cdots+d=d(d+1)/2$；余下标签数为 $d(d-1)/2$。两个全矩阵块的复维数是两扇区维数的平方和；自伴部分的实维数相同。

一般“半因果酉必为张量积”的结论见 Beckman–Gottesman–Nielsen–Preskill, [*Causal and localizable quantum operations*，定理 7](https://arxiv.org/abs/quant-ph/0102043)。这里的结论是给定进位运输的最大可保留子代数，由上面的矩阵单位计算确定。$\square$

**命题 3.3（单步最大性不等于同一边界闭合）。** 当 $d=2$ 时，置

$$
B=|00\rangle\langle01|+|01\rangle\langle00|.
$$

则 $B\in\mathcal D_{\mathrm{out}}$，但

$$
\alpha(B)=|00\rangle\langle10|+|10\rangle\langle00|
\notin\mathcal D_{\mathrm{out}}.
$$

证明。模 $2$ 的低层置换有 $00\mapsto00$ 和 $10\mapsto01\mapsto11\mapsto10$。输入的唯一进位 $1$ 标签是 $11$，故输出单独成块的标签是 $10$。$B$ 的两个标签均在另一个输出块中，而 $\alpha(B)$ 跨过该分块，定理 3.2 给出结论。$\square$

## 4. 全前缀、单终点与固定自主代数

**定义 4.1（累计进位与移动观测量）。** 对整数 $t\ge0$，令

$$
c_t(a)=\frac{M^ta-f^t(a)}d\pmod e,
\qquad c_0(a)=0.
$$

分子用整数代表计算，逐坐标可被 $d$ 整除。对固定的低层算子 $B$，其移动观测量定义为

$$
B_t=U_d^t B U_d^{-t}.
$$

给定 $N\ge1$，前缀进位签名为

$$
s_N(a)=\bigl(k(a),k(f(a)),\ldots,k(f^{N-1}(a))\bigr).
$$

**定理 4.2（每个移动时刻的共同相干块）。** 固定 $N\ge1$。对 $B\in\mathcal B(\mathcal H_A)$，以下条件等价：对每个 $t=1,\ldots,N$，均有

$$
(U^t)^\dagger(B_t\otimes I_H)U^t
\in\mathcal B(\mathcal H_A)\otimes I_H;
$$

以及 $B_{aa'}=0$ 对一切 $s_N(a)\ne s_N(a')$ 成立。因此全部满足条件的 $B$ 构成

$$
\mathcal S_N=
\bigoplus_{s\in\operatorname{im}s_N}
\mathcal B\bigl(\operatorname{span}\{|a\rangle:s_N(a)=s\}\bigr).
$$

若 $n_s=|s_N^{-1}(s)|$，则 $\dim_{\mathbb C}\mathcal S_N=\sum_s n_s^2$。在这些条件下，每个上述拉回实际上等于 $B\otimes I_H$。这里同时要求所有 $1\le t\le N$，且观测量随时刻移动。

证明。累计进位满足

$$
c_{t+1}(a)=M c_t(a)+c(f^t(a)),\qquad
U^t=\sum_a|f^t(a)\rangle\langle a|\otimes T_{c_t(a)}U_e^t.
$$

前式由整数恒等式或 FIB 第 26.2 节得到，后式对 $t$ 归纳。故

$$
(U^t)^\dagger(B_t\otimes I_H)U^t
=\sum_{a,a'}B_{aa'}E_{aa'}\otimes
T_{M^{-t}(c_t(a')-c_t(a))}.
$$

在正则平移表示中，$T_v$ 为标量恒等算子当且仅当 $v=0$：作用到 $|0\rangle$ 即可判定。又 $M$ 在模 $e$ 上可逆，所以第 $t$ 个条件等价于非零 $B_{aa'}$ 只连接 $c_t(a)=c_t(a')$ 的标签。对所有 $t=1,\ldots,N$ 同时相等，结合 $c_0=0$ 和递推式，等价于

$$
c(f^j(a))=c(f^j(a'))\pmod e\quad(0\le j<N).
$$

因 $k$ 只有 $0,1$ 两值且 $e\ge2$，模 $e$ 相等就是进位相等。反方向由同一递推逐步成立，给出等价性和全部拉回公式。$\square$

**定理 4.3（完整进位签名分离组成标签）。** 对任意 $a,a'\in A$，若

$$
k(f^j(a))=k(f^j(a'))\qquad\text{对每个 }j\ge0,
$$

则 $a=a'$。因此 $\mathcal S_N$ 随 $N$ 增大而递减，且其全体交为 $\Delta_A$。若 $P\ge1$ 是有限置换 $f$ 的周期，即 $f^P=\mathrm{id}$，则已经有 $\mathcal S_P=\Delta_A$。

进一步，令 $\varphi=(1+\sqrt5)/2$、$D=d-1$。对任意 $N\ge1$，若 $a\ne a'$ 而 $s_N(a)=s_N(a')$，则

$$
\varphi^N\le\varphi^3(d-1)^2.
$$

因此 $N>3+2\log_\varphi(d-1)$ 保证 $s_N$ 单射。特别地，取

$$
N_d=\left\lfloor3+2\log_\varphi(d-1)\right\rfloor+1,
$$

则每个 $N\ge N_d$ 均有 $\mathcal S_N=\Delta_A$；$d=2$ 时此充分界为 $N_d=4$。该界独立于 $e\ge2$，不主张最优，也不推断每个更短前缀都保留非对角相干。它只适用于全前缀代数 $\mathcal S_N$，不适用于定理 4.5 的单终点代数。

证明。把 $a,a'$ 和全部 $f^j(a),f^j(a')$ 取为整数代表。由

$$
f^{j+1}(a)=M f^j(a)-d(0,k(f^j(a)))
$$

及相同的进位，归纳得 $f^j(a)-f^j(a')=M^j(a-a')$。取 $j=P$，有 $(M^P-I)(a-a')=0$。$M$ 的两个实特征值为 $\varphi=(1+\sqrt5)/2$ 与 $-\varphi^{-1}$；对任何 $P\ge1$，两者的 $P$ 次幂均不为 $1$，故 $M^P-I$ 可逆，得到 $a=a'$。若只给前 $P$ 个进位相等，上述归纳仍足以到达 $j=P$，所以这个有限前缀已经分离全部标签。全体交与 $\mathcal S_P$ 的结论由定理 4.2 的块描述立即得到。

对于显式界，设 $z=a-a'\ne0$ 且 $s_N(a)=s_N(a')$。同一整数递推给出 $M^Nz=f^N(a)-f^N(a')$，故 $z$ 与 $M^Nz$ 的坐标绝对值均不超过 $D$。沿用 [FIB 第 18.1 节的两个实嵌入](https://github.com/the-omega-institute/trureturing/blob/64b78db1ad18a8a90b42e13a412dfc281d5c0922/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#L1020)，置 $\psi=(1-\sqrt5)/2$、$\sigma_+(z)=z_0+\varphi z_1$、$\sigma_-(z)=z_0+\psi z_1$。两根的无理性保证两个嵌入对非零整数向量均非零，故 $Q(z)=\sigma_+(z)\sigma_-(z)=z_0^2+z_0z_1-z_1^2$ 是非零整数，$|Q(z)|\ge1$。又 $|\sigma_-(z)|\le(1+|\psi|)D=\varphi D$、$|\sigma_+(M^Nz)|\le(1+\varphi)D=\varphi^2D$，且 $\sigma_+(M^Nz)=\varphi^N\sigma_+(z)$，从而 $1\le|Q(z)|=\varphi^{-N}|\sigma_+(M^Nz)|\,|\sigma_-(z)|\le\varphi^{3-N}D^2$，得到所述界。取逆否命题及整数阈值，再用定理 4.2 即得 $\mathcal S_N=\Delta_A$。此推导使用整数进位相等，没有使用累计进位模 $e$ 的相消。$\square$

**定理 4.4（同一自主低层代数的最大值）。** 在全部满足

$$
\mathcal N\subseteq\mathcal D_{\mathrm{out}},\qquad
\alpha(\mathcal N)\subseteq\mathcal N
$$

的含幺 $C^*$ 子代数中，按包含关系最大的代数恰为 $\Delta_A$。这一结论针对每一步使用同一边界的未修正 $U$。

证明。有限维性和 $\alpha$ 的可逆性给出 $\dim\alpha(\mathcal N)=\dim\mathcal N$，因此包含关系必为相等。于是 $B\in\mathcal N$ 的全部正、负整数次 $\alpha$ 共轭仍在 $\mathcal N$ 中。对每个 $j\ge0$，将定理 3.2 用于 $\alpha^{-j-1}(B)\in\mathcal N$，可知 $\alpha^{-j}(B)=U_d^jBU_d^{-j}$ 在 $k$ 的扇区上成块。若 $B_{aa'}\ne0$，后者在 $(f^j(a),f^j(a'))$ 的矩阵元也非零，故 $k(f^j(a))=k(f^j(a'))$。定理 4.3 迫使 $a=a'$，所以 $\mathcal N\subseteq\Delta_A$。反之，$U_d$ 是置换，故 $\alpha(\Delta_A)=\Delta_A$，且 $\Delta_A\subseteq\mathcal D_{\mathrm{out}}$。$\square$

**定理 4.5（只看终点的代数与整周期回归）。** 固定单个整数 $m\ge1$，定义

$$
\mathcal D_m=\{B:(U^m)^\dagger(B\otimes I_H)U^m
\in\mathcal B(\mathcal H_A)\otimes I_H\}.
$$

则

$$
\mathcal D_m=U_d^m\left(
\bigoplus_{\gamma\in\operatorname{im}c_m}
\mathcal B\bigl(\operatorname{span}\{|a\rangle:c_m(a)=\gamma\}\bigr)
\right)U_d^{-m}.
$$

这族单终点代数不随 $m$ 单调递减。具体地，若 $M^m=I\pmod{de}$，则 $U^m=I$、$\mathcal D_m=\mathcal B(\mathcal H_A)$；这样的正整数 $m$ 总存在。

证明。将定理 4.2 的展开中的 $B_{aa'}$ 换成 $B_{f^m(a),f^m(a')}$，仅检查这个时刻，平移为标量的判据恰为 $c_m(a)=c_m(a')$，得到公式。模 $de$ 上的 $M$ 属于有限群 $\mathrm{GL}_2(\mathbb Z/de\mathbb Z)$，所以有有限阶。其整周期上的组成置换和提升 $U$ 都是恒等，因而全部低层算子可拉回。由于 $d,e\ge2$ 时定理 3.2 的 $\mathcal D_1$ 严格小于全代数，这族代数不可能递减。终点累计进位模 $e$ 的相消可恢复相干；它不满足定理 4.2 的每个中间时刻条件，也不扩大定理 4.4 的固定自主代数。$\square$

## 5. 单轮低层预测的锐界与环境相位

**定理 5.1（全部联合输入上的极小极大误差）。** 对任意 $d,e\ge2$，令 $\Phi$ 遍历低层到低层的全部完全正保迹映射。上确界遍历 $\mathcal H_A\otimes\mathcal H_H$ 上的全部密度算子，允许任意层间关联。则

$$
\boxed{
\inf_{\Phi\ \mathrm{CPTP}}\ \sup_{\rho_{AH}}
D\left(\operatorname{Tr}_H(U\rho_{AH}U^\dagger),
\Phi(\operatorname{Tr}_H\rho_{AH})\right)=\frac12.}
$$

达到上界的映射为

$$
\Phi_0(X)=U_d(P_0XP_0+P_1XP_1)U_d^\dagger.
$$

此极小极大式没有额外参考系统。

证明。先给上界。记 $\eta=\operatorname{Tr}_H(U\rho_{AH}U^\dagger)$ 和 $\widetilde P_i=U_dP_iU_d^\dagger$。同扇区的高层算子相同，偏迹消去其共轭，故

$$
\Phi_0(\operatorname{Tr}_H\rho_{AH})
=\widetilde P_0\eta\widetilde P_0+\widetilde P_1\eta\widetilde P_1
=\frac{\eta+Z\eta Z}{2},\qquad
Z=\widetilde P_0-\widetilde P_1.
$$

$Z$ 是酉，两个密度算子的迹范数差不超过 $2$，因此

$$
D\left(\eta,\frac{\eta+Z\eta Z}{2}\right)
=\frac14\|\eta-Z\eta Z\|_1\le\frac12.
$$

再给下界。取任意 $a\in A_0,b\in A_1$；这两集合均非空，例如可取 $a=(0,0),b=(d-1,1)$。令 $\xi=(|a\rangle+|b\rangle)/\sqrt2$、$\omega=\exp(2\pi i/e)$。对每个 $j=0,\ldots,e-1$，归一化高层向量 $|r_j\rangle=\frac1{\sqrt e}\sum_{h_0=0}^{e-1}\omega^{-jh_0}|h_0,0\rangle$ 满足 $R|r_j\rangle=\omega^j|r_j\rangle$。输入 $|\xi\rangle\langle\xi|\otimes|r_j\rangle\langle r_j|$ 的低层边缘均相同，输出低层却分别是

$$
|\psi_j\rangle=
\frac{|f(a)\rangle+\omega^j|f(b)\rangle}{\sqrt2}.
$$

任何给定 $\Phi$ 对这些输入都预测同一密度算子 $\sigma$。由单位根和为零，

$$
\frac1e\sum_j|\psi_j\rangle\langle\psi_j|
=\frac12\left(|f(a)\rangle\langle f(a)|+|f(b)\rangle\langle f(b)|\right)=\frac P2.
$$

因此至少一个 $j$ 满足 $\langle\psi_j|\sigma|\psi_j\rangle\le\operatorname{Tr}(P\sigma)/2\le1/2$。半迹距离对效果的标准变分界给出

$$
D(|\psi_j\rangle\langle\psi_j|,\sigma)
\ge1-\langle\psi_j|\sigma|\psi_j\rangle\ge\frac12.
$$

这个下界对每个 $\Phi$ 成立，且前面已经构造达到它的 CPTP 映射。所用迹范数与效果不等式见 Watrous 上引书第 3 章。$\square$

**定理 5.2（固定乘积环境的一轮相干因子）。** 设单轮输入限定为 $\rho_A\otimes\tau_H$，其中 $\tau_H$ 固定，置

$$
z=\operatorname{Tr}(R\tau_H).
$$

则该轮低层通道为

$$
\Lambda_\tau(\rho_A)=U_d\left(
P_0\rho_AP_0+P_1\rho_AP_1
+\overline z P_0\rho_AP_1+zP_1\rho_AP_0
\right)U_d^\dagger.
$$

$z$ 的全体可达值为 $\operatorname{conv}\{1,\omega,\ldots,\omega^{e-1}\}$；当 $e=2$ 时是线段 $[-1,1]$。此通道为酉通道，当且仅当 $|z|=1$，等价于 $\tau_H$ 的支撑包含在 $R$ 的一个本征空间内。

证明。$E_{aa'}$ 的系数乘上

$$
\operatorname{Tr}(V_a\tau_HV_{a'}^\dagger)
=\operatorname{Tr}(R^{k(a)-k(a')}\tau_H),
$$

得到所述交叉块的符号。设 $R=\sum_j\omega^j\Pi_j$，则 $z=\sum_j\omega^j\operatorname{Tr}(\Pi_j\tau_H)$，其中权重非负且和为 $1$。任意这样的权重均可用各本征空间中纯态的混合实现，所以值域正是所述凸包。单位圆上不同点的非平凡凸组合模长严格小于 $1$；故 $|z|=1$ 当且仅当全部权重落在一个本征值上。密度算子的正性进一步保证其支撑落在该本征空间。

若 $z=\omega^j$，括号内映射是 $D_j\rho_AD_j^\dagger$，其中 $D_j=P_0+\omega^jP_1$，所以通道酉。若 $|z|<1$，对任意跨两扇区的等权纯态，输出在两维支撑上的本征值为 $(1\pm|z|)/2$，是混态，因而通道不可能酉。这只刻画一轮乘积输入；若每轮重新制备同一 $\tau_H$，才可按该重置合同反复使用同一低层通道。未重置的 $U$ 会保留并更新环境及关联，不能套用此结论。$\square$

**定义 5.3（关联输入的完整算子块）。** 对任意联合态写

$$
\rho_{AH}=\sum_{a,a'}E_{aa'}\otimes\rho_{aa'},
\qquad
\operatorname{Tr}_H(U\rho_{AH}U^\dagger)
=\sum_{a,a'}|f(a)\rangle\langle f(a')|
\operatorname{Tr}\left(R^{k(a)-k(a')}\rho_{aa'}\right).
$$

这里 $\rho_{aa'}$ 为高层算子，不假设相同，也不假设非对角块单独为正。该恒等式由 $V_a=U_eR^{k(a)}$ 和迹的循环性得到；低层边缘只给出 $\operatorname{Tr}\rho_{aa'}$，高层边缘只给出 $\sum_a\rho_{aa}$，一般都不决定右侧。第 7 节给出既保持两边缘相同又改变下一低层输出的具体联合态。

## 6. 主动联合修正与可重复的精确下降

**定义 6.1（按输出标签控制的进位修正）。** 定义联合置换

$$
D_{\mathrm{car}}|b,h\rangle
=|b,h-c(f^{-1}(b))\rangle.
$$

该操作需要访问低层标签与高层平移接口。它是在已选定张量分解中实际施加的受控酉操作。

**定理 6.2（精确消去本轮进位耦合）。** 对所有 $d,e\ge2$，有

$$
\boxed{D_{\mathrm{car}}U=U_d\otimes U_e.}
$$

因此对任意有限维旁观参考系统 $\mathcal H_{\mathrm{ref}}$ 和任意密度算子 $\rho_{AH\mathrm{ref}}$，包括层间及参考关联，均有

$$
\operatorname{Tr}_H\left[
(D_{\mathrm{car}}U\otimes I_{\mathrm{ref}})\rho
(D_{\mathrm{car}}U\otimes I_{\mathrm{ref}})^\dagger\right]
=(U_d\otimes I_{\mathrm{ref}})
\operatorname{Tr}_H\rho
(U_d^\dagger\otimes I_{\mathrm{ref}}).
$$

证明。在 $|a,h\rangle$ 上先施加 $U$ 得 $|f(a),Mh+c(a)\rangle$，再施加 $D_{\mathrm{car}}$，减去的正是 $c(a)$，得到 $|f(a),Mh\rangle$。由基向量上的相等得到算子恒等式。旁观参考上张量恒等，利用高层酉共轭不改变偏迹，得到第二式。此等式不要求输入为乘积态，也不消除原有纠缠：$U_d\otimes U_e$ 及其逆都是局部酉，保持两层之间原有的可分性或纠缠性。它不是只改符号的被动粗化。

[FIB 第 28 节](https://github.com/the-omega-institute/trureturing/blob/64b78db1ad18a8a90b42e13a412dfc281d5c0922/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#L1944)讨论均匀相容态的受控纤维分解；这里的恒等式针对动态 $U$ 的全部输入。[FIB 第 31 节](https://github.com/the-omega-institute/trureturing/blob/64b78db1ad18a8a90b42e13a412dfc281d5c0922/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#L2128)所要求的粗化交换式，在本条由加入实际修正后的乘积酉实现。$\square$

**命题 6.3（修正合同下的全部有限续接）。** 允许操作为完整修正轮 $D_{\mathrm{car}}U$ 与任意作用在 $A$ 上的通道、仪器；所有低层读出均可保留，参考系统只旁观。则 $q_{\mathrm{car}}(\rho)=\operatorname{Tr}_H\rho$ 对这一操作合同条件充分，包括任意有限自适应序列的概率和正概率条件态。

证明。定理 6.2 给出每个完整修正轮在 $q_{\mathrm{car}}$ 上的共轭更新。每个低层分支 $\mathcal I_y\otimes\mathrm{id}_H$ 与偏迹交换，其概率由 $\operatorname{Tr}\mathcal I_y(q_{\mathrm{car}}(\rho))$ 给出。因此沿有限协议树归纳，同记录选择同操作，未归一化后继边缘相同、概率相同；当概率为正时归一化仍相同。对参考系统只需把所有低层映射张量 $\mathrm{id}_{\mathrm{ref}}$。此合同将 $D_{\mathrm{car}}U$ 视为完整动作；若允许在 $U$ 后而修正前另行读出，须另用相应未修正边界。$\square$

## 7. 离散续接的最小联合代数与条件态关联

**定理 7.1（包含全部低层算子的最小联合不变代数）。** 令

$$
\mathcal T_H=\operatorname{span}_{\mathbb C}\{T_v:v\in H\}.
$$

在包含 $\mathcal B(\mathcal H_A)\otimes I_H$ 且满足 $U^\dagger\mathcal A U\subseteq\mathcal A$ 的含幺 $C^*$ 子代数中，唯一按包含关系最小者为

$$
\boxed{\mathcal A_{\min}=\mathcal B(\mathcal H_A)\otimes\mathcal T_H.}
$$

不要求 $d,e$ 互素。这里的最小性是在联合算子代数中包含全部低层算子的最小性；与定理 4.4 在纯低层范围内求最大自主代数属于不同问题。

证明。任取符合条件的 $\mathcal A$。取 $a\in A_0,a'\in A_1$，定理 3.2 给出

$$
U^\dagger(E_{f(a),f(a')}\otimes I_H)U=E_{aa'}\otimes R\in\mathcal A.
$$

对任意 $b\in A$，左右乘已有的 $E_{ba}\otimes I_H$ 与 $E_{a'b}\otimes I_H$ 得 $E_{bb}\otimes R$；求和得 $I_A\otimes R\in\mathcal A$。因高层平移交换，再次拉回有

$$
U^\dagger(I_A\otimes T_v)U=I_A\otimes T_{M^{-1}v}.
$$

特别地 $I_A\otimes T_{(-1,1)}\in\mathcal A$，因为 $M^{-1}(1,0)=(-1,1)$。向量 $(1,0)$ 与 $(-1,1)$ 在每个模 $e$ 上生成 $H$：两者之和为 $(0,1)$。用乘积和伴随遂得到所有 $I_A\otimes T_v$，再与低层矩阵单位相乘，证明 $\mathcal A_{\min}\subseteq\mathcal A$。

反过来，$\mathcal T_H$ 因 $T_vT_w=T_{v+w}$、$T_v^\dagger=T_{-v}$ 构成含幺 $C^*$ 代数。直接计算

$$
U^\dagger(E_{f(a),f(a')}\otimes T_v)U
=E_{aa'}\otimes T_{M^{-1}(v+c(a')-c(a))},
$$

所以 $\mathcal A_{\min}$ 在拉回下稳定，满足所有条件。有限维性还使该包含成为相等。$\square$

**定义 7.2（统一 Fourier 符号与条件矩阵）。** 令 $\widehat H=(\mathbb Z/e\mathbb Z)^2$ 为有限群 $H$ 的对偶标签集，$\omega=\exp(2\pi i/e)$。始终采用

$$
|p\rangle=\frac1e\sum_{h\in H}\omega^{-p\cdot h}|h\rangle,
\qquad p\in\widehat H.
$$

这里的 $p$ 是代数特征标标签，不附加物理动量解释。此约定给出

$$
T_v|p\rangle=\omega^{p\cdot v}|p\rangle,\qquad
U_e|p\rangle=|g(p)\rangle,\qquad
g(p)=M^{-\mathsf T}p=(-p_0+p_1,p_0).
$$

对任意联合密度算子 $\rho$，定义未归一化的正低层矩阵

$$
\sigma_p=(I_A\otimes\langle p|)\rho(I_A\otimes|p\rangle),
\qquad \sum_p\operatorname{Tr}\sigma_p=1.
$$

若 $w_p=\operatorname{Tr}\sigma_p>0$，才定义该标签下条件态 $\sigma_p/w_p$。保留全部 $\sigma_p$ 同时保留权重与关联，而非只保留 $\sum_p\sigma_p$ 和 $\{w_p\}$。

**定理 7.3（Fourier 条件矩阵的精确更新）。** 定义

$$
D_p=P_0+\omega^{p_0}P_1,\qquad W_p=U_dD_p.
$$

对任意初始联合态，未修正的一步 $U$ 使

$$
\boxed{\sigma'_{g(p)}=W_p\sigma_pW_p^\dagger.}
$$

此外

$$
\mathcal A_{\min}\cong\bigoplus_{p\in\widehat H}\mathcal B(\mathcal H_A),
\qquad \dim_{\mathbb C}\mathcal A_{\min}=d^4e^2.
$$

证明。将定义 7.2 的 Fourier 向量代入置换，令 $h'=Mh$，其指数变成 $-(M^{-\mathsf T}p)\cdot h'$，得到 $U_e|p\rangle=|g(p)\rangle$；平移的相位为正号 $\omega^{p\cdot v}$。又 $V_a=U_eR^{k(a)}$，故

$$
U(|a\rangle\otimes|p\rangle)
=\omega^{p_0k(a)}|f(a)\rangle\otimes|g(p)\rangle.
$$

因为 $g$ 是双射，输出的 $g(p)$ 对角块只能来自输入的 $p$ 对角块；即便输入含任意不同 $p,p'$ 间相干，仍给出所述更新。字符正交性又给出

$$
|p\rangle\langle p|=\frac1{e^2}\sum_{v\in H}\omega^{-p\cdot v}T_v.
$$

因此 $\mathcal T_H$ 正好是 Fourier 基中的全部对角算子，直和分解成立。每个低层全矩阵块维数为 $(d^2)^2=d^4$，共 $e^2$ 块，得到维数。这里 $e^2$ 是经典标签数，每个标签仍配有 $d^2$ 维低层空间上的任意正矩阵；标签计数不能替代这些量子矩阵。代数包含意义的最小性不宣称任何存储或电路复杂度的全局最优值。$W_p$ 只是条件低层酉的记号，不是第 8 节的连续行走 $W(t)$。$\square$

**定理 7.4（离散运输与任意低层仪器的条件充分边界）。** 允许操作字母表 $\mathscr A_{\mathrm{disc}}$ 由未修正的 $U$ 和任意作用于 $A$ 的有限结果仪器组成，包含任意低层通道作为单结果仪器。选择器只依赖已保留的记录与控制数据，所有读出均在低层。则

$$
q_{\mathrm{disc}}(\rho)=(\sigma_p)_{p\in\widehat H}
$$

对所有初始联合态及所有有限自适应协议条件充分。若仪器分支为 $\mathcal I_y(X)=\sum_\mu K_{y\mu}XK_{y\mu}^\dagger$，其保留块、概率和归一化更新为

$$
\widetilde\sigma_{p,y}=\sum_\mu K_{y\mu}\sigma_pK_{y\mu}^\dagger,
\qquad
p_y=\sum_p\operatorname{Tr}\widetilde\sigma_{p,y},
\qquad
\sigma_{p\mid y}=\frac{\widetilde\sigma_{p,y}}{p_y}\quad(p_y>0).
$$

结论也适用于任意有限维旁观参考：此时将每个 $\sigma_p$ 取为 $A\otimes\mathrm{ref}$ 上的算子，所有作用于低层的算子张量 $I_{\mathrm{ref}}$。

证明。定义高层 Fourier 去相干映射

$$
\mathcal E(\rho)=\sum_p(I_A\otimes|p\rangle\langle p|)\rho
(I_A\otimes|p\rangle\langle p|)
=\sum_p\sigma_p\otimes|p\rangle\langle p|.
$$

定理 7.3 表明 $U$ 将高层标签按 $g$ 双射重排，故

$$
\mathcal E\circ\operatorname{Ad}_U
=\operatorname{Ad}_U\circ\mathcal E.
$$

每个低层 Kraus 算子与高层投影交换，所以 $\mathcal E$ 也与每个低层仪器分支交换；并且 $\operatorname{Tr}_H\mathcal E(\rho)=\operatorname{Tr}_H\rho$。由此在任何固定记录分支上，先去相干与沿分支操作再去相干的结果完全相同，且分支迹相同。

更具体地，定理 7.3 给出运输更新，本定理显示公式给出每个仪器分支更新。沿协议树的深度归纳，拥有相同保留块的两输入在同记录节点选择相同操作，并产生相同的子分支概率和未归一化保留块。每条正概率路径用共同的正概率归一化，条件保留块仍相同。有限深度给出全部记录分布及后继边界相同；参考扩张的证明逐式不变。此结论比较的是保留边界和低层条件态，不声称被舍弃的高层非对角块也相同。$\square$

**命题 7.5（两份边缘不能替代条件关联）。** 对任意 $d,e\ge2$，选 $a\in A_0,b\in A_1$，定义

$$
|\xi_\pm\rangle=\frac{|a\rangle\pm|b\rangle}{\sqrt2},\qquad
p_j=(j,0),\qquad D_j=P_0+\omega^jP_1,
$$

$$
\rho_\pm=\frac1e\sum_{j=0}^{e-1}
D_j^\dagger|\xi_\pm\rangle\langle\xi_\pm|D_j
\otimes|p_j\rangle\langle p_j|.
$$

它们具有完全相同的低层边缘和高层边缘，但一步 $U$ 后的低层态正交。

证明。每个求和项是正的秩一乘积投影，总迹为 $1$，所以两者都是合法联合态。由 $\sum_{j=0}^{e-1}\omega^j=0$，交叉项平均消失，从而

$$
\operatorname{Tr}_H\rho_+=\operatorname{Tr}_H\rho_-
=\frac{|a\rangle\langle a|+|b\rangle\langle b|}{2},
\qquad
\operatorname{Tr}_A\rho_+=\operatorname{Tr}_A\rho_-
=\frac1e\sum_j|p_j\rangle\langle p_j|.
$$

对标签 $p_j$，定理 7.3 的低层酉是 $U_dD_j$，恰好消去输入条件态中的 $D_j^\dagger$，于是

$$
\operatorname{Tr}_H(U\rho_\pm U^\dagger)
=U_d|\xi_\pm\rangle\langle\xi_\pm|U_d^\dagger.
$$

$\langle\xi_+|\xi_-\rangle=0$，故两输出正交。这个差异来自标签 $p_j$ 与对应条件低层态的配对；只知道两边缘，即使都精确知道，也没有保留该配对。$\square$

**命题 7.6（高层位置测量不属于此边界的合同）。** 固定任意低层密度算子 $\rho_A$。联合态 $\rho_A\otimes|0,0\rangle\langle0,0|$ 与 $\rho_A\otimes|1,0\rangle\langle1,0|$ 有相同的 $q_{\mathrm{disc}}$，但高层计算基测量完全区分它们。

证明。每个高层计算基向量在 Fourier 基上的概率均为 $1/e^2$，所以两者对所有 $p$ 都给出 $\sigma_p=\rho_A/e^2$。高层位置投影则在两个不同标签上分别概率为 $1$。因此定理 7.4 不能添加任意高层操作或测量。$\square$

## 8. 连续相干行走的障碍与轨道块修复

**定义 8.1（在给定运输上另选的行走）。** 在同一联合空间上选择

$$
L=2I-U-U^\dagger=(I-U)^\dagger(I-U),\qquad
W(t)=\exp(-itL),\qquad t\in\mathbb R.
$$

$L$ 自伴且半正定，$W(t)$ 为酉。用有限图上的自伴生成元定义连续时间相干行走是标准构造，参见 Farhi–Gutmann, [*Quantum Computation and Decision Trees*](https://arxiv.org/abs/quant-ph/9706062)。这里具体选定的是由进位置换 $U$ 形成的 $L$；实参数 $t$ 与第 4 节的整数轮数分别属于不同操作。这个选择是模型的附加结构，不由组成递推单独指定。

**命题 8.2（模二三循环的精确振幅与回归）。** 取 $d=e=2$，用定义 7.2 的 Fourier 约定，置

$$
u=|10\rangle\otimes|p_{10}\rangle,\qquad
v=|01\rangle\otimes|p_{11}\rangle,\qquad
w=|11\rangle\otimes|p_{01}\rangle,
$$

其中 $p_{ij}=(i,j)$。则 $Uu=v,Uv=w,Uw=u$，三个相位均为 $+1$。在 $\mathcal V=\operatorname{span}\{u,v,w\}$ 上，令 $J_3$ 表示此有序基中的全 $1$ 矩阵，则

$$
L|_{\mathcal V}=3I-J_3,\qquad
W(t)|_{\mathcal V}=\frac{J_3}{3}
+\exp(-3it)\left(I-\frac{J_3}{3}\right).
$$

从 $u$ 出发，在低层计算基 $10,01,11$ 上的概率依次为

$$
\left(\frac{5+4\cos3t}{9},\quad
\frac{2-2\cos3t}{9},\quad
\frac{2-2\cos3t}{9}\right).
$$

尤其 $W(2\pi/3)$ 在 $\mathcal V$ 上为恒等。

证明。三个低层标签满足 $10\mapsto01\mapsto11\mapsto10$，三个高层对偶标签满足 $10\mapsto11\mapsto01\mapsto10$。前两个低层标签的进位为 $0$，第三个进位虽为 $1$，但对应高层标签 $01$ 的 $p_0=0$，故定理 7.3 的相位在三步均为 $1$。在三循环上 $U+U^\dagger=J_3-I$，所以得到 $L$ 的表达。$J_3/3$ 是均匀向量方向上的投影，其补空间的 $L$ 本征值为 $3$，指数公式随即成立。写 $r=\exp(-3it)$，从 $u$ 到自身的振幅为 $(1+2r)/3$，到另两基向量的振幅均为 $(1-r)/3$。各低层标签互异，偏迹后计算基概率就是这三个振幅的模平方，得到显示公式及回归。$\square$

**定理 8.3（逐 Fourier 标签边界对 $W(t)$ 不充分）。** 在命题 8.2 的空间中，令

$$
|\psi_\pm\rangle=\frac{u\pm iv}{\sqrt2},\qquad
\rho_\pm=|\psi_\pm\rangle\langle\psi_\pm|.
$$

两输入的全部 $\sigma_p$ 相同，但施加 $W(t)$ 后，低层结果 $01$ 的概率分别为

$$
p_\pm(01;t)=\frac{7+2\cos3t}{18}\pm\frac13\sin3t.
$$

因此 $p_+(01;t)-p_-(01;t)=\frac23\sin3t$；在 $t=\pi/6$ 时，两概率精确为 $13/18$ 与 $1/18$。

证明。$u$ 与 $v$ 的高层 Fourier 标签不同，所以两态的高层对角块均只有

$$
\sigma_{10}=\frac12|10\rangle\langle10|,
\qquad
\sigma_{11}=\frac12|01\rangle\langle01|,
$$

其余块为零。相对相位仅位于被 $q_{\mathrm{disc}}$ 舍去的跨标签块中。令 $a_t=(1+2\exp(-3it))/3$、$b_t=(1-\exp(-3it))/3$。命题 8.2 给出 $v$ 的输出振幅为 $(b_t\pm ia_t)/\sqrt2$，而 $\mathcal V$ 中只有 $v$ 的低层标签为 $01$，故

$$
p_\pm(01;t)=\frac12|b_t\pm ia_t|^2
=\frac{7+2\cos3t}{18}\pm\frac13\sin3t.
$$

代入 $3t=\pi/2$ 得两精确数值。于是即使最终只测低层，加入 $W(t)$ 也会使原先舍弃的高层标签相干产生可读差异。$\square$

**定义 8.4（对偶轨道内完整块）。** 令 $\mathfrak O$ 为 $g=M^{-\mathsf T}$ 在 $\widehat H$ 上的轨道分割，置

$$
Q_O=\sum_{p\in O}|p\rangle\langle p|,
\qquad
\tau_O=(I_A\otimes Q_O)\rho(I_A\otimes Q_O),
\qquad
\mathcal E_{\mathrm{orb}}(\rho)=\sum_{O\in\mathfrak O}\tau_O.
$$

边界 $q_{\mathrm{orb}}(\rho)=(\tau_O)_O$ 在每个轨道中保留全部 Fourier 非对角块，只去掉不同轨道之间的相干。各块未归一化，$\sum_O\operatorname{Tr}\tau_O=1$。

**定理 8.5（轨道块的条件充分性与包含意义下的最小性）。** 对任意 $d,e\ge2$，允许字母表 $\mathscr A_{\mathrm{orb}}$ 由 $U$、所有实参数 $t\in\mathbb R$ 的 $W(t)$，以及任意低层有限结果仪器组成。所有选择器只依赖已保留记录与控制数据。则对任意初始联合态，$q_{\mathrm{orb}}$ 保留全部有限自适应协议的概率和每条正概率路径的条件边界。结论在任意有限维旁观参考扩张下仍成立。其保留算子代数及复维数为

$$
\mathcal A_{\mathrm{orb}}
=\mathcal B(\mathcal H_A)\otimes
\bigoplus_{O\in\mathfrak O}\mathcal B(\mathbb C^O),
\qquad
\dim_{\mathbb C}\mathcal A_{\mathrm{orb}}
=d^4\sum_{O\in\mathfrak O}|O|^2.
$$

当 $e=2$ 时，轨道为 $\{00\}$ 和 $\{10,11,01\}$，所以维数为 $10d^4$。进一步，在所有满足

$$
\mathcal B(\mathcal H_A)\otimes I_H\subseteq\mathcal N
\subseteq\mathcal B(\mathcal H_A\otimes\mathcal H_H),\qquad
U^\dagger\mathcal N U\subseteq\mathcal N,\qquad
W(t)^\dagger\mathcal N W(t)\subseteq\mathcal N
\quad\text{对每个 }t\in\mathbb R
$$

的 $C^*$ 子代数中，$\mathcal A_{\mathrm{orb}}$ 是唯一按包含关系最小者。有限维性使这些共轭包含均为相等，因而也等价于正向共轭不变。任意低层仪器的每个完全正分支及其伴随映射也保持该代数。此最小性限于所声明操作下的联合 $C^*$ 子代数，不是任意编码、存储量或计算资源的最优性。

证明。定理 7.3 表明 $U$ 在每个轨道对应的 $\mathcal H_A\otimes\mathbb C^O$ 内作用，所以 $I_A\otimes Q_O$ 与 $U,U^\dagger$ 交换，进而与 $L$ 和 $W(t)$ 交换。它也与每个低层 Kraus 算子交换。因此 $\mathcal E_{\mathrm{orb}}$ 与每项允许酉通道和每个允许仪器分支交换，并保持低层偏迹。

具体地，若 $V=U$ 或 $V=W(t)$，则 $\tau'_O=V\tau_OV^\dagger$；低层仪器分支给出

$$
\widetilde\tau_{O,y}=\sum_\mu(K_{y\mu}\otimes I_H)\tau_O
(K_{y\mu}^\dagger\otimes I_H),\qquad
p_y=\sum_O\operatorname{Tr}\widetilde\tau_{O,y}.
$$

仅在 $p_y>0$ 时以 $p_y$ 除各块。沿有限自适应协议树逐层归纳，已有记录相同使下一操作及其 $t$ 参数相同；上述逐分支恒等式使新记录概率和保留块相同。共同正概率归一化后，条件边界继续相同。旁观参考上张量恒等即可。块矩阵代数的维数为各全矩阵块维数之和，得到公式；模 $2$ 的两个轨道由直接施加 $g$ 得到。

再证最小性。任取上述 $\mathcal N$。由定理 7.1 及定理 7.3 的 Fourier 投影公式，$\mathcal B(\mathcal H_A)\otimes\mathcal T_H\subseteq\mathcal N$，特别地

$$
\Pi_p=I_A\otimes|p\rangle\langle p|\in\mathcal N
\qquad(p\in\widehat H).
$$

因 $M^{\mathsf T}=M$ 且 $M^2=M+I$，有 $g=M^{-1}=M-I$、$g^2+g=I$，以及

$$
g-I=\begin{pmatrix}-2&1\\1&-1\end{pmatrix},\qquad
\det(g-I)=1.
$$

故在任意模 $e$ 上，$gp=p$ 迫使 $p=0$；若 $g^2p=p$，则由 $g^2+g=I$ 得 $gp=0$，再由 $g$ 可逆得 $p=0$。因此每个非零 $p$ 都满足 $gp\ne p$ 和 $g^2p\ne p$。

沿用定理 7.3 的 $W_p=U_d(P_0+\omega^{p_0}P_1)$，有

$$
U=\sum_{p\in\widehat H}W_p\otimes|gp\rangle\langle p|.
$$

对每个 $X\in\mathcal N$，所有 $t$ 的共轭不变性与有限维范数闭性给出

$$
i[L,X]=\left.\frac{d}{dt}\bigl(W(t)^\dagger XW(t)\bigr)\right|_{t=0}
\in\mathcal N.
$$

于是 $[L,X]\in\mathcal N$。取非零 $p$ 并令 $q=gp$，用 $q\ne p$ 及 $gq\ne p$ 得

$$
\Pi_q[L,\Pi_p]\Pi_p
=\Pi_q L\Pi_p
=-W_p\otimes|q\rangle\langle p|\in\mathcal N.
$$

这里 $2I$ 项因 $q\ne p$ 消失，$U^\dagger$ 项只有在 $gq=p$ 时才可能贡献，故也消失。左乘 $W_p^\dagger\otimes I_H\in\mathcal N$ 并取负，得到 $I_A\otimes|gp\rangle\langle p|\in\mathcal N$。沿轨道取乘积及伴随，得到同一非零轨道内的全部矩阵单位；零轨道是单点，所需投影 $\Pi_0$ 已在 $\mathcal N$ 中。再乘低层矩阵单位，便有 $\mathcal A_{\mathrm{orb}}\subseteq\mathcal N$。反方向由前面 $I_A\otimes Q_O$ 与 $U,W(t)$ 及全部低层算子交换可知：每个轨道块在这些共轭下稳定，低层仪器分支及其伴随也逐块作用。因此 $\mathcal A_{\mathrm{orb}}$ 本身满足全部条件，完成最小性证明。

上述导数步骤使用全部实时间的 $W(t)$。若只允许某些离散采样时刻，则不能直接沿用此最小性结论，除非另证足以恢复该导数的稠密性或闭包性质；此前逐块更新的充分性仍适用于这个更小的操作集合。

本合同仍排除任意高层操作。例如，取高层向量 $(|p_{00}\rangle\pm|p_{10}\rangle)/\sqrt2$ 并与同一低层态相乘，两者有相同轨道块，但高层位置结果 $h=(0,0)$ 的概率分别为 $1/2$ 与 $0$。因为 $e=2$ 时两个 Fourier 向量在此位置振幅均为 $1/2$，相加和相减给出所述概率。故跨轨道相干也不能在扩大的高层位置测量合同中任意舍弃。$\square$

## 9. 区域合法字、两态接缝与精确 Schmidt 容量

**定义 9.1（区域字空间及其切口）。** 对整数 $L\ge0$，令

$$
\mathcal W_L=\{w\in\{0,1\}^L:w_iw_{i+1}=0\text{ 对所有相邻位置成立}\},
\qquad
\mathcal R_L=\operatorname{span}\{|w\rangle:w\in\mathcal W_L\}
\subseteq(\mathbb C^2)^{\otimes L}.
$$

$\mathcal W_0$ 含唯一空字。给定 $L=\ell+r$ 的位置切口，张量分解是前 $\ell$ 位与后 $r$ 位；拼接 $uv$ 合法恰当且仅当两侧内部均合法且接缝不为 $11$。这是区域位字的合法关系，不是 $A\times H$ 的低高模数组成标签分解，也不预设两者之间有任何同构。

纯态的 Schmidt 秩等于其在左右正交基中的系数矩阵秩；熵取 $S=-\operatorname{Tr}(\rho_L\log\rho_L)$，本节 $\log$ 为自然对数。所用 Schmidt 分解和精确矩阵乘积态的键维数工具，见 Schollwöck, [*The density-matrix renormalization group in the age of matrix product states*，第 4.1.1 节](https://arxiv.org/abs/1008.3477)。以下计算针对此指定合法字支撑。

**定理 9.2（均匀区域态的至多二阶接缝）。** 有 $|\mathcal W_L|=F_{L+2}$。当 $\ell,r\ge1$ 时，等振幅合法态

$$
|\Omega_{\ell+r}\rangle
=\frac1{\sqrt{F_{\ell+r+2}}}\sum_{w\in\mathcal W_{\ell+r}}|w\rangle
$$

在 $\ell|r$ 切口上的 Schmidt 秩至多为 $2$，因而熵不超过 $\log2$。

证明。记 $N_L=|\mathcal W_L|$。初值为 $N_0=1,N_1=2$；对 $L\ge2$，合法字以 $0$ 开头时余下任意合法长 $L-1$ 字，以 $1$ 开头时下一位必须为 $0$、余下任意合法长 $L-2$ 字，故 $N_L=N_{L-1}+N_{L-2}$，得到 $N_L=F_{L+2}$。

令 $|l_i\rangle$ 为所有以 $i$ 结尾的左侧合法字之未归一化和，$|r_j\rangle$ 为所有以 $j$ 开头的右侧合法字之未归一化和。唯一被禁止的接缝是 $11$，所以

$$
|\Omega_{\ell+r}\rangle
=\frac{|l_0\rangle\otimes(|r_0\rangle+|r_1\rangle)
+|l_1\rangle\otimes|r_0\rangle}{\sqrt{F_{\ell+r+2}}}.
$$

这是两个乘积向量之和，因此系数矩阵秩至多为 $2$。Schmidt 分解及概率熵的标准秩界给出 $S\le\log2$。这利用了所有合法字振幅相同这一具体条件。$\square$

**定理 9.3（固定 $00$ 接缝仍可有 Fibonacci 秩）。** 对每个 $m\ge1$，定义长 $2m$ 的合法纯态

$$
|\Gamma_m\rangle=
\frac1{\sqrt{F_{m+1}}}
\sum_{u\in\mathcal W_{m-1}}|u0\rangle\otimes|0u\rangle.
$$

其接缝恒为 $00$，但在 $m|m$ 切口的 Schmidt 秩为 $F_{m+1}$，非零 Schmidt 系数均为 $F_{m+1}^{-1/2}$，熵为 $\log F_{m+1}$。这也是所有固定 $00$ 接缝合法纯态的最大 Schmidt 秩和最大熵。

证明。每个 $u$ 内部无相邻 $1$，两侧添 $0$ 以及中间 $00$ 都保持合法。不同 $u$ 对应不同的左右计算基向量，所以显示的和已经是 Schmidt 分解。由定理 9.2 的计数，求和项数为 $|\mathcal W_{m-1}|=F_{m+1}$，归一化及谱随即成立。

所有以 $0$ 结尾的合法长 $m$ 左字恰为 $u0$，所有以 $0$ 开头的合法长 $m$ 右字恰为 $0v$，左右维数均为 $F_{m+1}$，故任何固定 $00$ 接缝态的秩都不超过该值，熵不超过其对数；$\Gamma_m$ 同时达到两界。当 $m=1$ 时 $u$ 为空字，态为 $|0\rangle\otimes|0\rangle$，秩 $F_2=1$，同样满足结论。$\square$

**定理 9.4（全部合法态的精确最大区域容量）。** 对每个 $m\ge1$，在全部支撑于 $\mathcal R_{2m}$ 的归一化纯态中，$m|m$ 切口的最大 Schmidt 秩和最大熵分别为

$$
\boxed{R_{\max}(m)=F_{m+2},\qquad S_{\max}(m)=\log F_{m+2}.}
$$

证明。左右局部合法字空间维数同为 $N=F_{m+2}$，所以秩至多为 $N$，熵至多为 $\log N$。要同时达到上界，须构造只使用合法接缝的完美匹配。

按末位分左字集为 $L_0,L_1$，按首位分右字集为 $R_0,R_1$。对 $m\ge1$，有

$$
|L_0|=|R_0|=a=F_{m+1},\qquad
|L_1|=|R_1|=b=F_m,\qquad b\le a.
$$

末位或首位为 $0$ 的计数由去掉该位得到；当 $m\ge2$ 时，末位或首位为 $1$ 强迫邻位为 $0$，留下 $m-2$ 位，计数为 $F_m$；$m=1$ 时各集合都只有一个字，公式仍成立。

选 $S_0\subseteq R_0$、$T_0\subseteq L_0$，均含 $b$ 个元素。任选双射把 $L_1$ 配到 $S_0$、把 $T_0$ 配到 $R_1$，再把 $L_0\setminus T_0$ 配到 $R_0\setminus S_0$。最后两集合大小同为 $a-b$，所以这给出覆盖全部 $N=a+b$ 个左右标签的双射 $\pi$。其接缝只出现 $10,01,00$，没有 $11$；因此

$$
|\Lambda_m\rangle=\frac1{\sqrt N}\sum_{u\in\mathcal W_m}|u\rangle\otimes|\pi(u)\rangle
$$

是合法纯态。双射保证左右向量各自正交，故其 Schmidt 系数全为 $1/\sqrt N$，同时达到秩与熵上界。这一显式匹配也包括 $m=1$、$a=b=1$ 的边界情况。

由标准 Schmidt/MPS 工具，精确表示 $\Gamma_m$ 的该切口键维数至少为 $F_{m+1}$，精确表示 $\Lambda_m$ 至少为 $F_{m+2}$；均匀态在任意位置切口则可使用至多 $2$ 的 Schmidt 支撑。两状态的经典接缝自动机只检查末位 $0/1$ 与下一位是否相容，不决定系数矩阵的秩。因此经典合法性记忆为两态，不蕴含任意合法相干态都只需二维量子键。这里的键维数结论属于所声明的精确张量表示资源，不等同于任意编码、近似精度或访问合同下的全局存储最优值。$\square$

## 10. 事件、精度与区域的可继续接口

**定义 10.1（带类型的三类运输合同）。** 一个有限接口同时指定来源空间、张量分解、当前时钟、允许操作字母表、实际仪器分支、保留边界和已读记录。精度分解采用定义 1.1 的 $x=a+dh$；区域分解采用定义 9.1 的位字切口；事件分支采用定义 1.3。连接两个接口必须给出这些空间和操作之间的实际映射，不能只凭维数或 Fibonacci 计数相同识别它们。

对进位运输，以下三种合同分别选择不同的后继任务：第一种只保留固定低层自主代数 $\Delta_A$，并只允许保持它的额外仪器；第二种保留全部低层相干和未修正 $U$，使用定义 7.2 的条件矩阵边界；第三种允许实际联合修正 $D_{\mathrm{car}}$，把完整修正轮作为动作，并保留完整低层态。加入 $W(t)$ 是对第二种合同的扩充，采用定义 8.4 的轨道内完整块。任何合同都将选择器限制为由当前保留的控制数据及记录决定。

**定理 10.2（固定对角边界的逐分支闭合）。** 令

$$
q_\Delta(\rho)=\bigl(\langle a|\operatorname{Tr}_H\rho|a\rangle\bigr)_{a\in A}.
$$

允许字母表由未修正 $U$ 与满足

$$
\mathcal I_y^\dagger(\Delta_A)\subseteq\Delta_A
\quad\text{对每个结果 }y
$$

的低层仪器组成；读出和选择器也遵守同一合同。则 $q_\Delta$ 对任意初始联合态及任意有限自适应序列条件充分。任意低层酉门不自动属于此字母表。

证明。定理 3.2 对每个对角算子 $B$ 给出 $U^\dagger(B\otimes I_H)U=\alpha(B)\otimes I_H$，且 $\alpha(B)$ 仍对角，所以运输只将分布按 $f$ 重排。对于额外仪器，分支后第 $b$ 个对角元为

$$
\operatorname{Tr}\bigl[\rho\bigl(\mathcal I_y^\dagger(E_{bb})\otimes I_H\bigr)\bigr].
$$

显示假设使该表达只依赖 $q_\Delta(\rho)$。因 $I_A\in\Delta_A$，分支概率也由同一边界决定。等价地，存在非负的次随机核

$$
S_y(b\mid a)=\sum_\mu|\langle b|K_{y\mu}|a\rangle|^2,
\qquad
\widetilde q_y(b)=\sum_aS_y(b\mid a)q_\Delta(\rho)(a).
$$

取 $p_y=\sum_b\widetilde q_y(b)$，正概率时以后者归一化。逐层归纳证明所有有限自适应分支的概率和条件对角边界一致。一般低层相干门的共轭会把某个 $E_{bb}$ 变成非对角算子，如命题 2.3 证明中的两标签酉，所以它不满足假设；要允许任意低层仪器，可用定理 7.4 的更丰富边界，或定理 6.3 的完整修正轮。$\square$

**定义 10.3（区域接口的合法操作域）。** 在区域字模型中，若一次操作 $K:\mathcal R_L\to\mathcal R_{L'}$ 被宣称保持合法字支撑，其矩阵必须满足输入支撑和输出支撑条件，而不能只要求所测效果读出接缝。对两个区域的拼接，允许的基对为 $uv\in\mathcal W_{\ell+r}$；量子输入还包含这些基对的完整系数或密度矩阵。若目标是精确保存任意合法纯态在该切口的相干关联，其接口必须能表达定理 9.4 的完整匹配态。两态接缝验证器本身没有规定这种态的取得、更新或读出过程。

**假设 10.4（指定的持续单激发子空间）。** 若要把某个有限模式空间解释为“一个持续存在的激发”，额外指定

$$
\mathcal H_{\mathrm{ext}}=\mathbb C|\mathrm{vac}\rangle\oplus\mathcal H_{\mathrm{exc}}
$$

和初始态支撑 $\operatorname{supp}\rho\subseteq\mathcal H_{\mathrm{exc}}$。所选运输酉、行走和修正轮在 $\mathcal H_{\mathrm{exc}}$ 上实现相应已声明的模型，并满足 $V\mathcal H_{\mathrm{exc}}=\mathcal H_{\mathrm{exc}}$；允许仪器的每个 Kraus 算子均满足 $K_{y\mu}\mathcal H_{\mathrm{exc}}\subseteq\mathcal H_{\mathrm{exc}}$。若接口同时保留高低层结构，$\mathcal H_{\mathrm{exc}}$ 还须附带定义 1.1 的张量识别，仪器须遵守所选的第 6、7、8 或 10.2 节合同。这些是额外的子空间和仪器假设，有限组成递推本身未指定它们；$\mathcal H_{\mathrm{exc}}$ 不与进位扇区 $\mathcal H_1$ 混同。

**命题 10.5（持续性与正概率续接的共同条件）。** 在假设 10.4 下，任意有限自适应允许序列的每个正概率后继态仍支撑于 $\mathcal H_{\mathrm{exc}}$。若使用其中某一已声明的充分边界，则相应的记录概率及条件边界结论同时适用。仅指定点击效果和概率，不能替代假设 10.4 的逐分支支撑要求。

证明。每个酉保持 $\mathcal H_{\mathrm{exc}}$；每个 Kraus 算子把该子空间映入自身，所以对支撑于 $\mathcal H_{\mathrm{exc}}$ 的正算子，各分支和仍为支撑于 $\mathcal H_{\mathrm{exc}}$ 的正算子。对正迹分支除以迹不会改变支撑。沿有限协议树归纳即得持续性；同一路径上的记录和条件边界则分别由命题 6.3、定理 7.4、定理 8.5 或定理 10.2 的逐分支归纳给出。

若去掉仪器支撑条件，同一效果可能来自保留模式分支，也可能来自把模式送到 $|\mathrm{vac}\rangle$ 的吸收分支；具体的相同点击概率、不同后继构造见[波粒事件卷命题 4.3](https://github.com/the-omega-institute/trureturing/blob/64b78db1ad18a8a90b42e13a412dfc281d5c0922/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_WAVE_PARTICLE_EVENTS.md#L132)。因此概率记录不单独确定吸收或存活，只有指定实际操作才确定下一合法动作。这也符合[动态边界卷第 19 节](https://github.com/the-omega-institute/trureturing/blob/64b78db1ad18a8a90b42e13a412dfc281d5c0922/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md#L1562)将未来响应和选择器纳入边界的要求。$\square$

## 追加锚（本行以下为增补区）

## 11. 实际有限事件的效果张成、固定时钟与相干端口

**定义 11.1（联合历史效果与四种 FIB 操作字母表）。** 沿用定义 1.1、1.2、7.2、8.1，输入遍历 $\mathcal H=\mathcal H_A\otimes\mathcal H_H$ 上的全部密度算子，允许任意层间关联。每项低层仪器均为定义 1.3 的任意有限结果仪器，其 Kraus 算子在联合空间上为 $K_{y\mu}\otimes I_H$。协议是有限自适应树；同一已有记录及同一声明的经典控制数据决定下一动作，所有终端读出也只在低层。对固定完整历史 $h$，令 $\mathcal J_h$ 为该路径上未归一化的完全正分支之复合。其实际事件效果及联合概率为

$$
E_h=\mathcal J_h^\dagger(I),\qquad
\Pr_\rho(h)=\operatorname{Tr}\mathcal J_h(\rho)
=\operatorname{Tr}(E_h\rho).
$$

对同一协议中若干互斥完整历史组成的事件 $B$，置 $E_B=\sum_{h\in B}E_h$；中途事件可对其全部后继历史求和。所有这些效果满足 $0\le E_B\le I$。对于给定字母表 $\Sigma$，记实际事件效果集合为 $\mathscr F_\Sigma$，并置

$$
S_\Sigma=\operatorname{span}_{\mathbb C}\mathscr F_\Sigma.
$$

联合事件的未归一化概率是输入的线性函数；正概率条件事件的比值另行计算，不作为上述线性效果。此用法与 Grigoletto–Ticozzi, [*Exact model reduction for discrete-time conditional quantum dynamics*，§II.A–B、定义 1 与问题 1](https://arxiv.org/pdf/2403.12575v2)的未归一化历史及条件精确约化约定一致。

以下四种字母表均包含上述全部低层仪器，区别只在联合演化原语：$\Sigma_{\mathrm{dis}}$ 允许正向 $U$，即定理 7.4 的合同；$\Sigma_{\mathrm{orb}}$ 允许 $U$ 及所有实时间的 $W(t)$，即定理 8.5 的合同；$\Sigma_W$ 仅允许所有 $t\ge0$ 的 $W(t)$；对固定 $\Delta>0$，$\Sigma_\Delta$ 仅允许一个 $W(\Delta)$ 及其有限次重复。后两者都不以 $U$ 为原语。记

$$
\mathcal A_{\mathrm{dis}}:=\mathcal A_{\min}
=\mathcal B(\mathcal H_A)\otimes\mathcal T_H,
\qquad
\mathcal A_{\mathrm{orb}}
=\mathcal B(\mathcal H_A)\otimes
\bigoplus_{O\in\widehat H/\langle g\rangle}\mathcal B(\mathbb C^O).
$$

**定理 11.2（离散与连续 FIB 的实际统计边界）。** 对所有 $d,e\ge2$，有

$$
S_{\mathrm{dis}}=\mathcal A_{\mathrm{dis}},\qquad
S_{\mathrm{orb}}=\mathcal A_{\mathrm{orb}}.
$$

因而两个任意联合输入在 $\Sigma_{\mathrm{dis}}$ 的全部有限协议中具有相同事件概率，当且仅当定义 7.2 的每个 $\sigma_p$ 相同；在 $\Sigma_{\mathrm{orb}}$ 中具有相同的全部事件概率，当且仅当定义 8.4 的每个完整块 $\tau_O$ 相同。

证明。对本定理任一字母表，先由实际仪器构造一个可应用既有最小性结果的代数。暂记 $S=S_\Sigma$；全部效果自伴且全事件效果为 $I$，故 $S^\dagger=S$ 且 $I\in S$。给定任意低层矩阵 $K$，取 $\epsilon>0$ 使 $\epsilon\|K\|\le1$。前置 Kraus 算子为

$$
\epsilon K,\qquad (I_A-\epsilon^2K^\dagger K)^{1/2}
$$

的低层二结果仪器，记录第一结果后继续产生效果 $E$ 的协议。这个联合事件的效果是 $\epsilon^2(K^\dagger\otimes I_H)E(K\otimes I_H)$。除去非零标量，再线性延拓，得到该夹乘对每个 $E\in S$ 都属于 $S$。省略高层恒等因子，极化给出

$$
A^\dagger EB=\frac14\sum_{r=0}^3i^{-r}
(A+i^rB)^\dagger E(A+i^rB)\in S.
$$

取其中一个低层矩阵为恒等，即知 $S$ 是低层全矩阵代数的左右双模。所有低层终端效果也已张成 $\mathcal B(\mathcal H_A)\otimes I_H$。

在此实际效果空间上定义乘子代数

$$
\mathfrak D(S)=\{X\in\mathcal B(\mathcal H):XS\subseteq S,
\ SX\subseteq S\}.
$$

它对线性组合及乘积封闭，含 $I$。若 $X\in\mathfrak D(S)$，利用 $S^\dagger=S$，有 $X^\dagger E=(E^\dagger X)^\dagger\in S$ 及 $EX^\dagger=(XE^\dagger)^\dagger\in S$，故也对伴随封闭。它是有限维含幺 $C^*$ 代数；由 $I\in S$ 及低层双模性质，

$$
\mathcal B(\mathcal H_A)\otimes I_H
\subseteq\mathfrak D(S)\subseteq S.
$$

若 $V$ 是任一允许酉，前置 $V$ 给出 $\alpha_V(S)\subseteq S$，其中 $\alpha_V(X)=V^\dagger XV$。有限维单射性使该包含成为相等。于是 $\alpha_V$ 也将 $\mathfrak D(S)$ 映到自身，且是满射：例如 $\alpha_V(X)E=\alpha_V(X\alpha_V^{-1}(E))\in S$，右乘情形相同，逆向包含同理。这只是在有限维空间中使用逆映射，没有增加物理逆门许可。

对离散合同，定理 7.1 因而给出 $\mathcal A_{\mathrm{dis}}\subseteq\mathfrak D(S_{\mathrm{dis}})\subseteq S_{\mathrm{dis}}$。对原连续合同，定理 8.5 同样给出 $\mathcal A_{\mathrm{orb}}\subseteq\mathfrak D(S_{\mathrm{orb}})\subseteq S_{\mathrm{orb}}$。反过来，这两个既有代数分别在其允许酉拉回及每个低层完全正分支的伴随作用下不变，并包含低层终端效果。从终端沿每条有限历史反向归纳，再对事件求和，得到 $S_{\mathrm{dis}}\subseteq\mathcal A_{\mathrm{dis}}$ 和 $S_{\mathrm{orb}}\subseteq\mathcal A_{\mathrm{orb}}$，完成两项等式。

实际效果的线性张成相等后，有限维迹配对表明：所有事件概率相同，恰好等价于两态在相应代数上的全部线性泛函相同。Fourier 单点块或轨道完整块正是这些泛函的密度矩阵表示。若某个保留块不同，存在代数中的自伴算子区分它们；将该算子展开成有限个实际效果的线性组合，至少一个实际事件就有不同概率。

以观测线性空间刻画不可区分性的标准方法见 D’Alessandro, [*On Quantum State Observability and Measurement*，定理 5 及 §3 的式 (53)–(56)](https://arxiv.org/pdf/quant-ph/0307127v1)。本处从有限低层过滤、极化到 $\mathfrak D(S)$ 的推导承担具体 FIB 效果张成等于上述代数的桥梁。效果的线性组合不必本身是一个可执行效果；结论不授予高层投影仪器，不断言每个代数正元素均可由单一事件实现，也不提供单次未知态恢复或高效层析。统计等价的输入域是 $AH$；不能据此推出只读低层时对额外不可读参考关联的必要性结论。定理 7.4、8.5 的旁观参考逐分支充分性仍按各自的条件成立。$\square$

**定理 11.3（仅非负时间行走已生成全部轨道响应）。** 对定义 11.1 中没有离散 $U$ 原语的 $\Sigma_W$，任意 $d,e\ge2$ 都有

$$
S_W=\mathcal A_{\mathrm{orb}}.
$$

因此其全部允许历史统计相同，当且仅当全部 $\tau_O$ 相同；加入离散 $U$ 不增加效果空间的方向。

证明。将定理 11.2 的过滤、极化及乘子构造用于 $S_W$，记所得代数为 $\mathfrak D_W$。它包含低层全矩阵代数，满足 $\mathfrak D_W\subseteq S_W$，并被每个非负时间拉回

$$
\alpha_t(X)=W(t)^\dagger XW(t)
$$

规范化。以下交换子也可由有限个非负时间精确取得。令 $\Lambda=\operatorname{spec}L$、$\Omega=\Lambda-\Lambda$、$s=|\Omega|$。由于 $\Lambda\subseteq[0,4]$，不同 $\nu\in\Omega$ 的数 $z_\nu=\exp(i\pi\nu/8)$ 两两不同。Vandermonde 矩阵可逆，故存在 $b_0,\ldots,b_{s-1}\in\mathbb C$ 满足 $\sum_k b_kz_\nu^k=i\nu$。在 $L$ 的各谱角上比较，得到对所有 $X$ 的恒等式

$$
i[L,X]=\sum_{k=0}^{s-1}b_k\alpha_{k\pi/8}(X).
$$

于是 $[L,X]\in\mathfrak D_W$ 对每个 $X\in\mathfrak D_W$ 成立，没有使用无限协议或近似闭包。

记高层置换 $V=U_e$，则 $U=\sum_aE_{f(a),a}\otimes T_{c(a)}V$。矩阵恒等式

$$
M-I=M^{-1},\qquad M^2-I=M
$$

使两者在模 $d$ 上都可逆。因此对任何 $a\ne0$，有 $f(a)\ne a$、$f^2(a)\ne a$。置 $P_a=E_{aa}\otimes I_H$、$b=f(a)$，得到

$$
P_b[L,P_a]P_a=P_bLP_a
=-E_{ba}\otimes T_{c(a)}V\in\mathfrak D_W.
$$

这个低层非对角角中的 $2I$ 项为零；$U^\dagger$ 项要求 $f(b)=a$，已被排除。用低层矩阵单位左右夹乘并对低层对角求和，便有 $I_A\otimes T_{c(a)}V\in\mathfrak D_W$。

特别取两个明确的非零低层标签

$$
a^{(0)}=(1,0),\qquad a^{(1)}=(d-1,1).
$$

它们在所有 $d\ge2$ 时有效，包括 $d=2$，且进位分别为 $0$ 与 $(0,1)$。所以 $I_A\otimes V$、$I_A\otimes T_{(0,1)}V$ 都是乘子。在已经成立的乘子代数内取乘积和伴随，得到

$$
I_A\otimes T_{(0,1)}\in\mathfrak D_W,\qquad
I_A\otimes V^\dagger T_{(0,1)}V
=I_A\otimes T_{(1,0)}\in\mathfrak D_W.
$$

这两个方向生成全部高层平移。Fourier 反演给出

$$
\Pi_p:=I_A\otimes|p\rangle\langle p|
=\frac1{e^2}\sum_{v\in H}\omega^{-p\cdot v}(I_A\otimes T_v)
\in\mathfrak D_W,
\qquad
\Pi_{gp}(I_A\otimes V)\Pi_p
=I_A\otimes|gp\rangle\langle p|\in\mathfrak D_W.
$$

沿每条 $g$ 轨道相乘并取伴随，得到轨道内的全部矩阵单位；零轨道所需的对角投影也已在其中。再乘低层矩阵，得到 $\mathcal A_{\mathrm{orb}}\subseteq\mathfrak D_W\subseteq S_W$。这些乘积是乘子代数中的运算，不是把高层算子提升为可执行原语。

反向包含由定理 8.5 的逐块不变性得到：每个 $W(t)$ 和低层 Kraus 算子都保持 $g$ 轨道块，故全部实际历史效果属于 $\mathcal A_{\mathrm{orb}}$。最后使用定理 11.2 的迹配对论证即得统计等价。$\square$

**定理 11.4（固定采样门的全局谱差判据）。** 对定义 11.1 的 $\Sigma_\Delta$，令 $\Lambda=\operatorname{spec}L$ 为整个 $AH$ 空间上的谱，$\Omega=\Lambda-\Lambda$ 是所有不同全局谱差的集合。若

$$
\nu,\mu\in\Omega,\quad
e^{i\Delta\nu}=e^{i\Delta\mu}\quad\Longrightarrow\quad\nu=\mu,
\tag{11.1}
$$

则 $S_\Delta=\mathcal A_{\mathrm{orb}}$，全部历史统计等价于相同的轨道完整块。对于所有 $d,e\ge2$，每个固定的 $0<\Delta<\pi/4$ 都满足此充分条件，特别包括 $\Delta=\pi/8$。

证明。写 $L=\sum_{\lambda\in\Lambda}\lambda R_\lambda$，则

$$
\alpha_t(X)=\sum_{\lambda,\kappa\in\Lambda}
e^{it(\lambda-\kappa)}R_\lambda XR_\kappa.
$$

令 $s=|\Omega|$。条件 (11.1) 使 $z_\nu=e^{i\Delta\nu}$ 两两不同，故对任意 $t\ge0$ 有唯一的次数小于 $s$ 的插值多项式，其系数 $c_k(t)$ 满足

$$
\sum_{k=0}^{s-1}c_k(t)z_\nu^k=e^{it\nu}
\quad(\nu\in\Omega).
$$

因此在整个算子空间上有精确恒等式

$$
\alpha_t=\sum_{k=0}^{s-1}c_k(t)\alpha_{k\Delta}.
$$

右侧第 $k$ 项由前置 $k$ 次固定门 $W(\Delta)$ 给出，$k=0$ 是不施加演化。故 $S_\Delta$ 在全部 $\alpha_t$ 下保持，且原本就在低层分支伴随映射下保持。从任意 $\Sigma_W$ 协议的终端反向展开，每个等待步骤只替换为上述有限线性组合；有限树、有限 Kraus 和与事件求和仍给有限个合法采样协议效果的线性组合。于是 $S_W\subseteq S_\Delta$。采样门又属于 $\Sigma_W$，所以 $S_\Delta\subseteq S_W$，定理 11.3 给出等式。

由于 $\Omega\subseteq[-4,4]$，当 $0<\Delta<\pi/4$ 且 $\nu\ne\mu$ 时有 $0<|\Delta(\nu-\mu)|<2\pi$，故不可能等于 $2\pi$ 的整数倍。这证明统一充分界。若 $r=|\Lambda|$，则 $s\le r(r-1)+1$；每个等待步骤的插值只用非负幂 $0,\ldots,s-1$。这是效果空间中的有限精确展开，系数不是概率，不表示用一次采样门物理实现任意 $W(t)$，也不提供整个协议展开或统计估计的效率保证。$\square$

**命题 11.5（采样端点与一个确切失效时钟）。** 对所有 $d,e\ge2$，$\Delta=\pi/4$ 都不满足 (11.1)。当 $d=e=2$、$\Delta=2\pi$ 时，则有真正严格的效果空间包含

$$
S_{2\pi}=\mathcal B(\mathbb C^4)\otimes I_4
\subsetneq\mathcal A_{\mathrm{orb}},\qquad
\dim_{\mathbb C}S_{2\pi}=16,\quad
\dim_{\mathbb C}\mathcal A_{\mathrm{orb}}=160.
$$

证明。令 $n=de\ge4$。$U$ 与 $M$ 在 $(\mathbb Z/n\mathbb Z)^2$ 上的置换仅相差 digits 重标记。若 $M$ 的模 $n$ 阶为奇数，取行列式会得到 $-1=1\pmod n$，矛盾。这个线性作用忠实，故其置换阶也为偶数；置换阶是各循环长度的最小公倍数，所以至少有一个偶长循环，其循环移位具有特征值 $-1$。又零标签固定，$U$ 有特征值 $1$。于是 $0,4\in\Lambda$，$-4,4\in\Omega$。在 $\Delta=\pi/4$ 处，两者相位均为 $-1$，判据失效。

对于 $d=e=2$，全局模数为 $4$，且

$$
M^3=\begin{pmatrix}1&2\\2&3\end{pmatrix},\qquad
M^6=\begin{pmatrix}5&8\\8&13\end{pmatrix}\equiv I\pmod4.
$$

全局置换包含六循环

$$
(1,0)\to(0,1)\to(1,1)\to(1,2)
\to(2,3)\to(3,1)\to(1,0).
$$

因 $U^6=I$ 且这条六循环给出全部六次单位根，得到 $\operatorname{spec}L=\{0,1,3,4\}$，故 $W(2\pi)=I$。此固定采样合同中的全部操作都只作用低层，效果张成恰为 $\mathcal B(\mathbb C^4)\otimes I_4$。高层模 $2$ 的 $g$ 轨道大小为 $1,3$，定理 8.5 给出轨道代数维数 $16(1+9)=160$。

命题 8.2 的三循环限制谱不能代替这里的全局谱。$\Delta=\pi/4$ 的结论仅是充分判据失效，未判定该端点是否仍有 $S_\Delta=\mathcal A_{\mathrm{orb}}$；$\Delta=2\pi$ 的严格失败由上面的恒等门计算单独证明。所有可行采样时钟的必要充分分类仍未给出。$\square$

**命题 11.6（相同响应空间不使连续等待成为离散运输）。** 对任意 $d,e\ge2$、任意实数 $t$ 及任意 $|\zeta|=1$，均有 $W(t)\ne\zeta U$。未插入低层控制的有限个 $W(t)$ 的乘积也不能等于 $\zeta U$。

证明。由 $M-I=M^{-1}$ 与 $M^2-I=M$ 在模 $de$ 上可逆，$M$ 的每条非零循环长度 $\ell$ 都至少为 $3$。任选这样一条循环，$U$ 在其上有不同的特征值 $\lambda=e^{2\pi i/\ell}$ 和 $\lambda^{-1}$。两者在 $L$ 上具有同一能量 $2-\lambda-\lambda^{-1}$，所以 $W(t)$ 在这两个本征向量上给出相同相位；$\zeta U$ 则给出不同的 $\zeta\lambda$ 与 $\zeta\lambda^{-1}$，矛盾。有限个等待门的乘积是 $W(\sum t)$，故结论相同。这一论证只比较固定的 $U=U_M$ 与未插入控制的等待，不判定任意低层控制交错后的精确门合成。$\square$

**定义 11.7（FIB 历史的共同 CPTP 状态解码资源）。** 选取定理 11.2–11.4 中一个已确定实际效果张成的 FIB 字母表 $\Sigma$，并取相应 Fourier 分割 $\mathcal P$：离散合同使用全部单点，轨道合同使用 $\langle g\rangle$ 轨道。置

$$
\mathcal H_O=\mathcal H_A\otimes\mathbb C^O,\qquad
P_O=I_A\otimes Q_O,\qquad
\mathcal E_{\mathcal P}(\rho)=\sum_{O\in\mathcal P}P_O\rho P_O.
$$

编码 $\mathrm{Enc}$ 与同一个状态解码 $\mathrm{Dec}$ 均为 CPTP；它们固定且不随随后选择的协议改变。只给一份未知的 $AH$ 输入，解码返回同一 $\mathcal H$ 上的状态。中间资源有两种计费合同：其一是普通有限 Hilbert 空间 $\mathcal K$，全部 $\dim\mathcal K$ 计费；其二是任意有限的免费经典 flag 集 $F$ 及公共 $q$ 维量子端口，中间态代数为 $\bigoplus_{f\in F}\mathcal B(\mathbb C^q)$，只计 $q$。后一合同允许一般编码分支 $\mathrm{Enc}_f$，各分支完全正、总和保迹，概率和量子态均可依赖整个输入；不预设 $f$ 是原块标签。解码写为 $\mathrm{Dec}(\bigoplus_f\sigma_f)=\sum_f\mathrm{Dec}_f(\sigma_f)$，每个 $\mathrm{Dec}_f$ 为 CPTP。

中间传递资源恰为以上所列空间，没有隐藏量子旁路或预共享纠缠。允许固定局部辅助态并将其丢弃，均吸收入 CPTP 映射；经典 flag 是有限字母，不承载未知态的无限精度经典描述。统计任务要求 $T=\mathrm{Dec}\circ\mathrm{Enc}$ 对全部输入及全部实际历史效果满足

$$
\operatorname{Tr}(E T(\rho))=\operatorname{Tr}(E\rho)
\quad(E\in\mathscr F_\Sigma).
$$

对应的精确块恢复任务要求 $T=\mathcal E_{\mathcal P}$。密度算子复线性张成全部算子，故对全部输入态的精确恢复也是线性映射恒等式，张量任意参考系统的恒等映射后仍成立。这是在 FIB 操作合同之外另行指定的编解码资源合同；不要求编码中的高层操作属于原有低层协议字母表。共同 CPTP 编解码及免费有限经典寄存器采用 Bluhm–Rauber–Wolf, [*Quantum Compression Relative to a Set of Measurements*，定义 4.1](https://arxiv.org/pdf/1708.04898v4)的约定。

**命题 11.8（FIB 操作改变所需相干端口）。** 在定义 11.7 的单份精确共同解码合同下，离散 $\Sigma_{\mathrm{dis}}$ 的最小免费 flag 量子端口为 $d^2$；原连续 $\Sigma_{\mathrm{orb}}$、仅非负等待的 $\Sigma_W$，以及满足 (11.1) 的固定采样 $\Sigma_\Delta$，其最小端口均为 $d^2\max_{O\in\widehat H/\langle g\rangle}|O|$。这些合同的最小全计费 Hilbert 记忆维数均为 $d^2e^2$。特别地，当 $e=2$ 时，FIB 字母表所决定的响应块及两种精确成本为

$$
\begin{aligned}
\Sigma_{\mathrm{dis}}:&\quad
(d^2,d^2,d^2,d^2),\qquad
q_{\min}=d^2,\qquad (\dim\mathcal K)_{\min}=4d^2,\\
\Sigma_{\mathrm{orb}},\ \Sigma_W,\ \Sigma_\Delta\text{ 满足 (11.1)}:&\quad
(d^2,3d^2),\qquad
q_{\min}=3d^2,\qquad (\dim\mathcal K)_{\min}=4d^2.
\end{aligned}
$$

其中每个 $0<\Delta<\pi/4$ 都适用。这些最优值对共同解码保持全部实际历史统计和精确恢复 $\mathcal E_{\mathcal P}$ 两项任务相同；两项任务要求的通道等式并不相同。

证明。先把具体 FIB 效果识别接到共同解码要求。定理 11.2–11.4 给出

$$
\operatorname{span}_{\mathbb C}\mathscr F_\Sigma
=\mathcal A_{\mathcal P}
=\bigoplus_{O\in\mathcal P}\mathcal B(\mathcal H_O).
$$

所以统计保持等价于 $T^\dagger$ 在 $\mathcal A_{\mathcal P}$ 上逐点恒等。Pinching 关于迹配对自伴，像空间恰为 $\mathcal A_{\mathcal P}$，故对所有 $X$ 与 $\rho$，

$$
\operatorname{Tr}\bigl[X\mathcal E_{\mathcal P}(T(\rho)-\rho)\bigr]
=\operatorname{Tr}\bigl[\mathcal E_{\mathcal P}(X)(T(\rho)-\rho)\bigr]=0.
$$

由迹配对非退化性得到准确的通道条件

$$
\mathcal E_{\mathcal P}\circ T=\mathcal E_{\mathcal P}.
$$

后置 $\mathcal E_{\mathcal P}$，将解码换为 $\mathrm{Dec}'=\mathcal E_{\mathcal P}\circ\mathrm{Dec}$，不改变中间资源，即取得 $\mathrm{Dec}'\circ\mathrm{Enc}=\mathcal E_{\mathcal P}$。反之，精确 pinching 固定每个实际效果的期望，自然保持全部历史统计。故两任务的可行记忆维数相同。这里没有从统计保持推出原来的 $T$ 就等于 pinching，例如恒等通道也保持统计。

下面在这些已识别的 FIB 块上使用已知的精确块压缩工具。Bluhm–Rauber–Wolf 上引文定理 7.1 给出最大矩阵块维数的上界构造，定理 9.2 给出精确态族恢复的相应最优值；应用的态族是 $\{\mathcal E_{\mathcal P}(\rho):\rho\text{ 为密度算子}\}$，其生成代数正是 $\bigoplus_O\mathcal B(\mathcal H_O)$。固定这一态族与恢复全部输入的 pinching 有相同成本：后者固定该态族，前者只需在编码前再施加 pinching。为明确一般输入相关 flag 和全域 CPTP 解码的条件，将这些标准工具在本处的秩论证写出。

令 $n_O=\dim\mathcal H_O=d^2|O|$，$J_O:\mathcal H_O\to\mathcal H$ 为自然包含。全记忆计费时，取全部块内正交基，合计 $\sum_On_O=d^2e^2$ 个向量 $u_j$。每个基态都被 pinching 固定。若 $\sigma_j=\mathrm{Enc}(|u_j\rangle\langle u_j|)$，则解码拉回的 POVM $Q_j=\mathrm{Dec}^\dagger(|u_j\rangle\langle u_j|)$ 满足 $\operatorname{Tr}(Q_j\sigma_k)=\delta_{jk}$。$\sigma_j$ 的支撑位于 $Q_j$ 的特征值 $1$ 子空间，而其余 $\sigma_k$ 的支撑位于其核。因此这些非零支撑两两正交，$\dim\mathcal K\ge\sum_On_O$。取 $\mathcal K=\mathcal H$、编码为 pinching、解码为恒等，达到此界。

免费 flag 时，固定一个最大块 $O$，令编码分支 Kraus 算子为 $B_{f\alpha}:\mathcal H\to\mathbb C^q$，解码分支 Kraus 算子为 $A_{f\beta}:\mathbb C^q\to\mathcal H$。限制输入到该块后，复合 Kraus 算子为 $C_{f\alpha\beta}=A_{f\beta}B_{f\alpha}J_O$，每个秩至多为 $q$；这种经过公共量子端口的 Kraus 秩界也见 Bluhm–Rauber–Wolf 上引文引理 5.2 的证明。块恢复要求它们给出的通道恰为 $X\mapsto J_OXJ_O^\dagger$。其 Choi 算子是秩一的；用归一化最大纠缠向量 $|\Omega_O\rangle$ 表示，就是

$$
\sum_{f,\alpha,\beta}
|(I\otimes C_{f\alpha\beta})\Omega_O\rangle
\langle(I\otimes C_{f\alpha\beta})\Omega_O|
=|(I\otimes J_O)\Omega_O\rangle
\langle(I\otimes J_O)\Omega_O|.
$$

正算子之和为秩一时，每个非零求和向量都与目标向量共线：对目标的任意正交向量取二次型，各非负项只能全为零。向量化单射遂给出每个非零 $C_{f\alpha\beta}=\alpha_{f\alpha\beta}J_O$，其秩为 $n_O$。至少一个非零项存在，因而 $q\ge n_O$。这是 Nayak–Sen, [*Invertible Quantum Operations and Perfect Encryption of Quantum States*，定理 2.1 证明中的 $B_jA_i=\alpha_{ji}I$](https://arxiv.org/pdf/quant-ph/0605041v4)所用可逆 Kraus 秩论证在该 FIB 块上的应用；参考系统只用于通道等式的数学检验，不是额外传递或读出资源。下界没有限制 flag 怎样依赖输入。

为达到上界，取 $q=\max_On_O$，为每块选等距映射 $V_O:\mathcal H_O\to\mathbb C^q$，将块标签作为一种可行的有限 flag，置

$$
\begin{aligned}
\mathrm{Enc}_O(\rho)&=V_OJ_O^\dagger\rho J_OV_O^\dagger,\\
\mathrm{Dec}_O(\sigma)&=J_OV_O^\dagger\sigma V_OJ_O^\dagger
+\operatorname{Tr}\bigl[(I_q-V_OV_O^\dagger)\sigma\bigr]\tau_*,
\end{aligned}
$$

其中 $\tau_*$ 为固定的 $\mathcal H$ 上密度算子。各编码分支完全正且总迹守恒；解码的两项均完全正，迹之和为 $\operatorname{Tr}\sigma$，所以在端口全部状态上均为 CPTP。编码输出落在 $V_O$ 的像中，第二项为零，复合恰为 $\sum_OP_O\rho P_O$。由此在本 FIB 分割上得到 $q_{\min}=\max_On_O=d^2\max_O|O|$ 及全记忆值 $\sum_On_O=d^2e^2$。

离散分割的 $e^2$ 个块均为单点。$e=2$ 时，$g$ 的轨道是 $\{00\}$ 与 $\{10,11,01\}$，故连续或满足判据的采样操作需要 $d^2$ 与 $3d^2$ 两个块，得到所述操作依赖的端口变化。

这里必须使用实际效果的线性张成以及同一个 CPTP 状态解码器。仅有 $C^*(\mathscr F_\Sigma)=\mathcal A_{\mathcal P}$ 不足以推出上述下界，参见 Bluhm–Rauber–Wolf 上引文推论 8.5。逐测量另选读出、受限效果集、近似或渐近资源不由本命题判定。第 9 节合法字的区域 Schmidt 切口也不是本节的低高模数分解，其容量不能直接代入此编解码合同。$\square$

## 12. 离散几何、连续几何与正规轨道边界

**定义 12.1（无附加相位的混合几何合同）。** 在同一 digits 分解 $x=a+dh$ 上，固定整数矩阵

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}1&1\\0&-1\end{pmatrix},\qquad
C=MJ=\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
$$

对这些矩阵及其乘积 $G$，标准提升始终是不另加相位的置换 $|x\rangle\mapsto|[Gx]_{de}\rangle$。在低高分解中记为 $U_G$，并定义

$$
f_G(a)=[Ga]_d,\qquad
c_G(a)=\frac{Ga-f_G(a)}d\pmod e,\qquad
\gamma_G=G^{-\mathsf T}.
$$

分子用整数代表计算，允许负进位。于是

$$
U_G|a,h\rangle=|f_G(a),Gh+c_G(a)\rangle,
\qquad U_GU_{G'}=U_{GG'}.
$$

沿用定义 7.2 的 Fourier 约定，写为

$$
\begin{aligned}
U_G&=\sum_{p\in\widehat H}F_{G,p}\otimes|\gamma_Gp\rangle\langle p|,\\
F_{G,p}|a\rangle&=\omega^{(\gamma_Gp)\cdot c_G(a)}|f_G(a)\rangle.
\end{aligned}
$$

每个 $F_{G,p}$ 都是低层酉，且 $F_{G,p}|0\rangle=|0\rangle$。记 $g=M^{-\mathsf T}$、$j=J^{-\mathsf T}$，在 $\widehat H$ 上置

$$
\Gamma=\langle g,j\rangle,\qquad N=\langle g,-I\rangle,
\qquad L_G=2I-U_G-U_G^\dagger,\quad W_G(t)=e^{-itL_G}.
$$

混合字母表 $\Sigma_{\mathrm{mix}}$ 允许离散 $U_M,U_J,U_C$、所有 $t\ge0$ 的 $W_M(t)$，以及定义 11.1 的任意低层有限仪器和有限自适应选择；全部读出在低层。它不含 $W_J$ 或 $W_C$。这里 $U_M=U$、$W_M(t)=W(t)$，且 $U_C=U_MU_J$。对 $K=N$ 或 $\Gamma$，记其 Fourier 轨道分割为 $\mathcal P_K=\widehat H/K$，并置

$$
\mathcal A_K=\mathcal B(\mathcal H_A)\otimes
\bigoplus_{O\in\mathcal P_K}\mathcal B(\mathbb C^O),\qquad
\mathcal E_K(\rho)=\sum_{O\in\mathcal P_K}(I_A\otimes Q_O)\rho(I_A\otimes Q_O).
$$

**定理 12.2（仅连续 $M$ 的混合合同保留正规闭包块）。** $N$ 恰是 $\langle g\rangle$ 在 $\Gamma$ 中的正规闭包。对全部 $d,e\ge2$，混合合同的实际事件效果张成、代数维数及条件充分边界为

$$
S_{\mathrm{mix}}=\mathcal A_N,\qquad
\dim_{\mathbb C}\mathcal A_N=d^4\sum_{O\in\mathcal P_N}|O|^2,
\qquad \rho\longmapsto\mathcal E_N(\rho).
$$

这里 pinching 保留每条正概率路径的后继块及整条记录分布。任意两联合输入的全部允许历史统计相同，当且仅当其全部 $N$ 轨道完整块相同。$\mathcal A_N$ 也恰为包含全部低层算子、在这些允许酉拉回下不变的最小含幺 $C^*$ 代数。

进一步，每条 $\Gamma$ 轨道由一条或两条 $N$ 轨道组成，且

$$
\mathcal A_N=\mathcal A_\Gamma
\quad\Longleftrightarrow\quad
jp\in Np\quad\text{对所有 }p\in\widehat H.
$$

证明。直接乘矩阵得

$$
j^2=I,\qquad jgj=-g^{-1},\qquad C^{-\mathsf T}=gj.
$$

正规闭包包含 $g$ 及 $jgj=-g^{-1}$，因而包含它们的乘积 $-I$；反之，$N=\langle g,-I\rangle$ 被 $g$ 与 $j$ 的共轭保持。因此它正是所述正规闭包，且 $\Gamma=N\cup Nj$，其中两个陪集允许相同。由于正规性，$j(Np)=N(jp)$，故 $\Gamma p=Np\cup N(jp)$，两个轨道或者相等或者不交。各分割的块矩阵描述立即给出代数相等的判据。

先证所有实际效果的上包含及逐分支充分性。定义 12.1 的展开表明离散 $U_G$ 对 $G=M,J,C$ 将 $\mathcal H_A\otimes\mathbb C^O$ 送到 $\mathcal H_A\otimes\mathbb C^{\gamma_GO}$。正规性保证 $\gamma_GO$ 仍是一条 $N$ 轨道。因此这些离散酉可以置换完整块，并规范化 $\mathcal A_N$。因为 $g\in N$，$U_M$ 保持每一条 $N$ 轨道，故 $L_M,W_M(t)$ 也逐块作用；低层 Kraus 算子与全部 $I_A\otimes Q_O$ 交换。

于是 $\mathcal E_N$ 与每个允许离散酉通道、连续酉通道及低层仪器分支交换，且保持低层偏迹。固定分支的未归一化块可以先 pinching 再更新，或先更新再 pinching，结果相同；分支迹相同。沿有限自适应树归纳，得到全部记录概率相同，正概率时用共同的概率归一化后，后继块仍相同。这里 $U_J$ 可以置换块，充分性不要求每个块投影分别与 $U_J$ 交换。从终端效果反向归纳，同时得到 $S_{\mathrm{mix}}\subseteq\mathcal A_N$。

为证明实际效果的下包含，把定理 11.2 的乘子构造用于此合同，记 $\mathfrak D_{\mathrm{mix}}=\mathfrak D(S_{\mathrm{mix}})$。它含全部低层矩阵，被每个允许酉共轭规范化，且包含于 $S_{\mathrm{mix}}$。将定理 11.3 的两低层 carry 角、非负时间有限插值及 Fourier 反演的论证直接用于 $\mathfrak D_{\mathrm{mix}}$，得到

$$
\Pi_p\in\mathfrak D_{\mathrm{mix}},\qquad
I_A\otimes|gp\rangle\langle p|\in\mathfrak D_{\mathrm{mix}}
\quad(p\in\widehat H).
$$

再作已允许的离散 $U_J$ 正向共轭，得到

$$
U_J(I_A\otimes|gp\rangle\langle p|)U_J^\dagger
=F_{J,gp}F_{J,p}^\dagger\otimes|jgp\rangle\langle jp|
\in\mathfrak D_{\mathrm{mix}}.
$$

低层系数是酉，可乘其伴随消去。令 $r=jp$，所得边为 $r\to jgjr=-g^{-1}r$。已有的 $g$ 边与这些 $-g^{-1}$ 边生成 $N=\langle g,-I\rangle$；沿有限轨道路径相乘并取伴随，就得到每条 $N$ 轨道内的全部矩阵单位。结合低层矩阵，有

$$
\mathcal A_N\subseteq\mathfrak D_{\mathrm{mix}}
\subseteq S_{\mathrm{mix}}\subseteq\mathcal A_N.
$$

这证明实际张成等式。任何包含低层全矩阵且在允许拉回下不变的含幺 $C^*$ 代数，也在低层 Kraus 夹乘下保持，所以包含每个实际事件效果；因而包含 $S_{\mathrm{mix}}=\mathcal A_N$，得到所述最小性。有限维迹配对给出统计等价的必要性，块维数相加给出维数公式。

有限等价关系的每个等价类产生全矩阵块，是 Sims, [*Étale groupoids and their C*-algebras*，例 3.3.7](https://arxiv.org/pdf/1710.10897v2)中离散等价关系紧算子块的有限情形。这里用的是 $N$ 轨道等价关系及其矩阵单位；所述代数不认同于另一个保留稳定子资料的变换群胚 crossed product。具体是哪一个等价关系，由上面的允许操作与正规闭包计算决定。$\square$

**定理 12.3（再允许一种连续几何就保留整个 $\Gamma$ 块）。** 在 $\Sigma_{\mathrm{mix}}$ 上，任选 $G=J$ 或 $G=C$，额外允许所有 $t\ge0$ 的 $W_G(t)$，记新字母表为 $\Sigma_{\mathrm{mix}+G}$。对定义 12.1 的标准无附加相位提升，有

$$
S_{\mathrm{mix}+G}=\mathcal A_\Gamma.
$$

相应的 $\Gamma$ 块 pinching 条件充分；全部实际历史统计相同，当且仅当全部 $\Gamma$ 轨道完整块相同。

证明。对新合同再次使用实际效果的乘子代数 $\mathfrak D_G$。定理 12.2 中提取 $N$ 轨道矩阵单位的论证对它仍成立，故 $\mathcal A_N\subseteq\mathfrak D_G$，特别包含全部 $\Pi_p$。由于 $\operatorname{spec}L_G\subseteq[0,4]$，定理 11.3 在步长 $\pi/8$ 上的有限插值同样给出 $[L_G,X]\in\mathfrak D_G$；这里全部非负 $W_G(t)$ 均已明确许可。

若 $q=\gamma_Gp\ne p$，在高层 Fourier 角上计算有

$$
\Pi_q[L_G,\Pi_p]\Pi_p
=-\left(F_{G,p}
+\mathbf1_{\{\gamma_Gq=p\}}F_{G,q}^\dagger\right)
\otimes|q\rangle\langle p|\in\mathfrak D_G.
$$

第一项来自 $U_G$，第二项只在有反向边时来自 $U_G^\dagger$。即使两项之和不是可逆矩阵，也可取低层零角：由 $F_{G,p}|0\rangle=|0\rangle$，括号中算子的 $00$ 矩阵元为 $1+\mathbf1_{\{\gamma_Gq=p\}}$，只能是 $1$ 或 $2$。左右乘 $E_{00}\otimes I_H$ 后，该非零系数可除去；再用 $E_{a0}$、$E_{0a}$ 左右夹乘并对 $a$ 求和，得到

$$
I_A\otimes|\gamma_Gp\rangle\langle p|\in\mathfrak D_G.
$$

固定点的对角矩阵单位本已存在。因此所有 $\gamma_G$ 邻边都取得了。$\gamma_J=j$ 与 $\gamma_C=gj$ 分别同 $N$ 生成 $\Gamma$，故与已有 $N$ 边组合，得到全部 $\Gamma$ 轨道内的矩阵单位。这证明 $\mathcal A_\Gamma\subseteq\mathfrak D_G\subseteq S_{\mathrm{mix}+G}$。

反过来，所有离散几何及两种获准连续演化均保持每个 $\Gamma$ 轨道子空间，低层分支也逐块作用。因此实际效果都在 $\mathcal A_\Gamma$ 内，且 $\mathcal E_\Gamma$ 与每条分支交换。结合迹配对及逐分支归纳，得到等式、统计必要充分性和条件充分性。乘子中的高层投影仍不是额外获准的高层仪器；新增的是指定的连续 $W_G$ 族。$\square$

**命题 12.4（模十一的两条特征线与低层完美区分）。** 取 $e=11$、任意 $d\ge2$，在 $\widehat H=\mathbb F_{11}^2$ 中置

$$
p=(1,4),\qquad q=(1,8),\qquad
O_4=\mathbb F_{11}^{\times}p,\quad
O_8=\mathbb F_{11}^{\times}q.
$$

$O_4,O_8$ 是两条互不相交、各有十点的 $N$ 轨道，$\Gamma$ 将它们合为一条二十点轨道。令

$$
\begin{aligned}
a&=(0,1),\qquad b=(1,d-1),\qquad\omega=e^{2\pi i/11},\\
u&=|a\rangle\otimes|p\rangle,\qquad
v=U_Ju=\omega^3|b\rangle\otimes|q\rangle,\\
|\psi_\pm\rangle&=\frac{u\pm iv}{\sqrt2},\qquad
\rho_\pm=|\psi_\pm\rangle\langle\psi_\pm|.
\end{aligned}
$$

两输入有相同 $N$ 边界，因而在 $\Sigma_{\mathrm{mix}}$ 的所有允许有限历史中不可区分。若增加 $W_J$ 的许可，施加一次 $W_J(t)$ 后仅测低层 $b$，则

$$
\Pr_\pm(b;t)=\frac{1\pm\sin4t}{2}.
$$

特别在 $t=\pi/8$，两概率分别为 $1$ 与 $0$。

证明。矩阵作用给出

$$
gp=3p,\qquad gq=7q,\qquad jp=q,\qquad jq=p.
$$

模 $11$ 的 $3$ 次幂为 $3,9,5,4,1$，阶为 $5$；$7^2=5$、$7^5=-1$ 且 $7\ne-1$，故 $7$ 阶为 $10$。于是 $\langle3,-1\rangle=\langle7,-1\rangle=\mathbb F_{11}^{\times}$。两向量不是标量倍数，给出不交的两条十点 $N$ 轨道；$j$ 交换它们，定理 12.2 给出所述二十点 $\Gamma$ 轨道。这只描述两条特征线上的非零标签，不穷尽全部 $121$ 个 Fourier 标签。

对低层 $a=(0,1)$，有 $Ja=(1,-1)$，故 $f_J(a)=b$、$c_J(a)=(0,-1)$。Fourier 运输相位是 $\omega^{q\cdot c_J(a)}=\omega^{-8}=\omega^3$，得到显示的 $v$。标准提升满足 $U_J^2=I$，所以 $U_Jv=u$。因为 $p,q$ 属于不同 $N$ 轨道，

$$
\mathcal E_N(\rho_+)=\mathcal E_N(\rho_-)
=\frac12\bigl(|u\rangle\langle u|+|v\rangle\langle v|\bigr).
$$

定理 12.2 因而保证原混合合同的全部事件概率相同。在 $\operatorname{span}\{u,v\}$ 上，$U_J$ 交换 $u,v$，且

$$
W_J(t)=e^{-2it}\bigl(\cos(2t)I+i\sin(2t)U_J\bigr).
$$

写 $c=\cos(2t)$、$s=\sin(2t)$，得到

$$
W_J(t)|\psi_\pm\rangle
=\frac{e^{-2it}}{\sqrt2}
\bigl((c\mp s)u+i(s\pm c)v\bigr).
$$

$a\ne b$，且此不变子空间中只有 $v$ 带低层标签 $b$，故概率为 $(s\pm c)^2/2=(1\pm\sin4t)/2$。该事件只用 $E_{bb}\otimes I_H$，没有高层或联合读出。新增连续许可确实读取原 $N$ pinching 舍去的相干；在 $t=\pi/4$ 则 $W_J(\pi/4)=U_J$，那个已有的离散时刻本身不给出此严格区分。$\square$

**命题 12.5（连续几何必须指定提升的相位）。** 定义 12.1 的 $U_J$ 与 $\widetilde U_J=iU_J$ 给出同一个离散酉通道，但按 $2I-V-V^\dagger$ 规则生成的连续行走不同；后者的生成元为 $2I$，行走仅为标量相位。因此只给离散通道不足以指定定理 12.3 的连续几何。

证明。标准 $J$ 满足 $J^2=I$，故 $U_J^2=I$ 且 $U_J^\dagger=U_J$。标量相位在共轭中消失，所以 $\widetilde U_J\rho\widetilde U_J^\dagger=U_J\rho U_J^\dagger$。但

$$
2I-\widetilde U_J-\widetilde U_J^\dagger
=2I-iU_J+iU_J=2I,
\qquad \widetilde W_J(t)=e^{-2it}I.
$$

因而在混合合同上只加入 $\widetilde W_J$ 不增加任何实际效果方向，仍为 $\mathcal A_N$；模十一的命题 12.4 则证明加入标准 $W_J$ 可以严格增加它。定理 12.3 的低层零角为 $1$ 或 $2$，用到了无附加相位的标准提升；将提升换成 $iU_J$ 时正反项相消。两种连续模型具有相同离散通道，并不构成矛盾，而是连续生成元的额外相位选择不能从该离散通道恢复。$\square$

## 追加锚（本行以下为增补区）

## 13. 闭半圆端点的实际效果空间

**定理 13.1（所有低高模数的端点采样）。** 对每个整数 $d,e\ge2$，采用定义 1.1、1.2、8.1 的标准提升，令 $L=2I-U-U^\dagger$。唯一联合演化原语为 $W=W_M(\pi/4)$；其余许可恰为定义 11.1 的任意低层有限仪器、低层终端读出及有限自适应历史，初始输入遍历全部联合密度算子。则

$$
S_{\pi/4}=\mathcal A_{\mathrm{orb}}.
$$

两个输入的全部实际历史统计相同，当且仅当每个 $g=M^{-\mathsf T}$ 轨道完整块相同；相应 pinching 也保留每条正概率路径的条件边界。

证明。对实际效果复线性空间 $S=S_{\pi/4}$，直接采用[定理 11.2 的低层 Kraus 缩放、极化与乘子构造](https://github.com/the-omega-institute/trureturing/blob/fecb0ec51a883ebb079d477888ecfdc4d27a97eb/docs/develop/theory/FIBONACCI_COHERENT_TRANSPORT_BOUNDARY.md#L935)：

$$
\mathfrak D=\{X:XS\subseteq S, SX\subseteq S\},\qquad
\mathcal B(\mathcal H_A)\otimes I_H\subseteq\mathfrak D\subseteq S.
$$

$\mathfrak D$ 是有限维含幺 $*$ 代数。前置一次获准的 $W$ 给 $W^\dagger SW\subseteq S$，有限维单射性使之为等号，从而 $W^\dagger\mathfrak DW=\mathfrak D$。逆共轭在此只是线性空间等式，不是新增的物理逆门。

由 $\operatorname{spec}L\subseteq[0,4]$，算子

$$
B=\frac{W^\dagger-W}{2i}=\sin(\pi L/4)
$$

半正定。谱定理给出全空间中的精确核等式

$$
\ker B=\ker(W^2-I)=\ker(U^2-I)
=\ker L\oplus\ker(L-4I).
\tag{13.1}
$$

前两个核在 $L$ 谱上都只取端点 $0,4$；这两个能量分别对应 $U$ 的特征值 $1,-1$。若 $P$ 是 $\mathfrak D$ 的任意非零中心投影，它与全部低层矩阵交换，故 $P=I_A\otimes Q$，其中 $Q\ne0$。取 $0\ne\eta\in\operatorname{ran}Q$。从低层 $(1,0)$ 出发的前两步均无进位，因而

$$
U^2(|1,0\rangle\otimes\eta)
=|1,1\rangle\otimes V^2\eta,
\qquad V=U_e.
$$

$d\ge2$ 保证两个低层标签不同，故此向量不等于原向量。因此任何非零中心块都不能包含于 (13.1) 的核。

$W$ 正规化 $\mathfrak D$，所以置换其最小非零中心投影。若 $P'=WPW^\dagger\ne P$，则 $PP'=0$，从而 $PWP=PP'W=0$，亦有 $PW^\dagger P=0$。于是 $PBP=0$。正性给出

$$
0=PBP=(B^{1/2}P)^\dagger(B^{1/2}P),
$$

故 $BP=0$，与上一段矛盾。于是 $W$ 固定每个最小中心块。函数 $\lambda\mapsto e^{-i\pi\lambda/4}$ 在 $[0,4]$ 上单射，所以 $L$ 是 $W$ 的有限谱函数，也逐块保持。

固定一个最小中心块。有限维矩阵代数的结构给出坐标

$$
P\mathcal H\simeq\mathcal K\otimes\mathcal R,
\qquad P\mathfrak DP\simeq\mathcal B(\mathcal K)\otimes I_{\mathcal R}.
$$

矩阵代数的 $*$ 自同构为内自同构；从 $W|_P$ 消去实现该自同构的第一因子酉后，余下酉属于交换子代数。因此 $W|_P=A_0\otimes R_0$。这只是代数坐标分解。取两因子的酉特征值 $a_i,r_j$，其乘积都在闭下半圆，有唯一 $\theta_{ij}\in[0,\pi]$ 满足 $a_ir_j=e^{-i\theta_{ij}}$。每个相位矩形满足

$$
\theta_{ij}+\theta_{k\ell}-\theta_{i\ell}-\theta_{kj}
\in2\pi\mathbb Z\cap[-2\pi,2\pi].
$$

若此差非零，交换指标后可令其为 $2\pi$；四角只能交错取 $\pi,0,0,\pi$。故 $a_k=-a_i$、$r_\ell=-r_j$。任意两个互为相反数且同在闭下半圆的单位复数只能为 $1,-1$。对任意行 $s$，$a_sr_j$ 与 $a_sr_\ell$ 因而都为 $\pm1$；对任意列 $t$，$a_ir_t$ 与 $a_kr_t$ 也都为 $\pm1$。于是整个乘积谱满足

$$
a_sr_t=\frac{(a_sr_j)(a_ir_t)}{a_ir_j}\in\{1,-1\}
\quad\text{对所有 }s,t.
$$

这使 $W^2P=P$，并由 (13.1) 使整个非零中心块落入 $\ker(U^2-I)$，矛盾。故所有相位矩形都为零。固定 $i_0,j_0$ 后，

$$
\theta_{ij}=\theta_{ij_0}+\theta_{i_0j}-\theta_{i_0j_0}.
$$

在相应特征基中分别取 Hermitian 算子 $A',R'$，特征值为 $4\theta_{ij_0}/\pi$ 与 $4(\theta_{i_0j}-\theta_{i_0j_0})/\pi$，便有

$$
L|_P=A'\otimes I+I\otimes R',
\qquad [L,P\mathfrak DP]\subseteq P\mathfrak DP.
$$

合并全部中心块得 $[L,\mathfrak D]\subseteq\mathfrak D$。

现在接入[定理 11.3 的两个非零进位角](https://github.com/the-omega-institute/trureturing/blob/fecb0ec51a883ebb079d477888ecfdc4d27a97eb/docs/develop/theory/FIBONACCI_COHERENT_TRANSPORT_BOUNDARY.md#L981)。恒等式 $M-I=M^{-1}$、$M^2-I=M$ 排除模 $d$ 的非零不动点和二周期。对 $a\ne0$、$b=f(a)$、$P_a=E_{aa}\otimes I_H$，有

$$
P_b[L,P_a]P_a=-E_{ba}\otimes T_{c(a)}V\in\mathfrak D.
$$

$U^\dagger$ 不贡献此角，否则 $f^2(a)=a$。低层矩阵夹乘并求和给 $I_A\otimes T_{c(a)}V\in\mathfrak D$。分别取 $a=(1,0)$ 与 $(d-1,1)$，得到 $I_A\otimes V$ 与 $I_A\otimes T_{(0,1)}V$。乘积、伴随以及 $V^\dagger T_{(0,1)}V=T_{(1,0)}$ 给出全部高层平移。按定义 7.2 的 Fourier 约定，

$$
\Pi_p=I_A\otimes|p\rangle\langle p|
=\frac1{e^2}\sum_{v\in H}\omega^{-p\cdot v}(I_A\otimes T_v)
\in\mathfrak D,
\qquad
\Pi_{gp}(I_A\otimes V)\Pi_p
=I_A\otimes|gp\rangle\langle p|\in\mathfrak D.
$$

沿每条有限 $g$ 轨道相乘并取伴随，得到全部轨道矩阵单位，故 $\mathcal A_{\mathrm{orb}}\subseteq\mathfrak D\subseteq S$。反向，每个轨道投影与 $U,L,W$ 及低层 Kraus 算子交换；从终端低层效果逐历史拉回，仍在 $\mathcal A_{\mathrm{orb}}$ 中。有限自适应分支与事件求和保持此性质，故 $S\subseteq\mathcal A_{\mathrm{orb}}$。迹配对给统计等价，pinching 与每个实际分支交换给正概率条件边界。$\square$

**推论 13.2（统一充分区间及其资源合同）。** 对所有 $d,e\ge2$，每个固定 $0<\Delta\le\pi/4$ 都有 $S_\Delta=\mathcal A_{\mathrm{orb}}$。在定义 11.7 的共同 CPTP 状态编解码合同下，最小免费有限经典 flag 量子端口仍为 $d^2\max_O|O|$，全计费 Hilbert 记忆为 $d^2e^2$。

证明。开区间由定理 11.4，端点由定理 13.1；对已确定的实际效果线性张成，直接应用命题 11.8。命题 11.5 所述 $\pm4$ 全局谱差在端点混叠仍然成立，故原充分判据仍然失效；本定理使用低层控制及 FIB 两步低层运动补足端点。这里没有增加逆门或其他等待时间，也没有断言所有更大时钟失败或该区间为最大区间。效果线性张成不表示每个高层投影本身是一项许可测量。$\square$

## 14. 模四提升的全部固定时钟与精确记忆

**定理 14.1（$d=e=2$ 的固定时钟三分）。** 固定 $d=e=2$，采用同一标准提升与定义 11.1 的 $\Sigma_\Delta$，其中任意 $\Delta>0$ 均只许可正向重复 $W=W(\Delta)$、任意低层有限仪器及低层读出。输入为全部联合态，历史有限且可自适应。置 $x=e^{-i\Delta}$、$V=U_{M,2}$，令 $\mathcal D_F$ 为四个完整高层 Fourier 标签的对角代数，则

$$
S_\Delta=
\begin{cases}
\mathcal B(\mathbb C^4)\otimes I_4,&x=1,\\
\mathcal B(\mathbb C^4)\otimes\mathcal D_F,&x^3=1, x\ne1,\\
\mathcal B(\mathbb C^4)\otimes
\bigl(\mathbb C\oplus\mathcal B(\mathbb C^3)\bigr)
=\mathcal A_{\mathrm{orb}},&x^3\ne1.
\end{cases}
\tag{14.1}
$$

三者复维数依次为 $16,64,160$。因此模 $2\pi$ 的时钟类 $0$、$\{2\pi/3,4\pi/3\}$ 和其余类恰对应这三种边界。两联合输入的全部实际事件概率相同，当且仅当按三行分别有相同的低层偏迹、相同的全部 Fourier 对角条件矩阵、相同的全部 $g$ 轨道完整块。

证明。整数恒等式 $M^3=I+2M$ 与 $M^6\equiv I\pmod4$ 给 $U^6=I$。令

$$
P_\pm=\frac{I\pm U^3}{2},\qquad
A=\frac{1+2x^3}{3},\quad
B=\frac{x(2+x^3)}3,\quad C=\frac{1-x^3}{3}.
$$

在 $P_+$ 上，$U$ 的谱属于三次单位根，$L$ 取值 $0,3$；在 $P_-$ 上，$U=-1$ 对应 $L=4$，另两枚六次单位根对应 $L=1$。对这些谱点求值，得到精确恒等式

$$
W=(AP_++BP_-)
+C\,U(P_++xP_-)+C\,U^2(P_+-xP_-).
\tag{14.2}
$$

例如 $P_+$ 上的表达为 $AI+C(U+U^2)$；$P_-$ 上为 $BI+xC(U-U^2)$，在 $U=-1$ 处等于 $x^4$，在另外两点等于 $x$。此外

$$
|A|^2=|B|^2=\frac{5+4\operatorname{Re}(x^3)}9\ge\frac19,
\qquad A-B=-\frac{(x-1)^3(x+1)}3.
\tag{14.3}
$$

因此 $|A|=|B|\ge1/3$，而 $A=B$ 恰在 $x=1,-1$。

标准 digits $a+2h$ 中，$M^3(a+2h)\equiv a+2(h+Ma)\pmod4$，所以

$$
U^3=\sum_{a\in(\mathbb Z/2)^2}E_{aa}\otimes T_{Ma}.
\tag{14.4}
$$

低层非零三点按 $10\to01\to11\to10$ 循环，故 (14.2) 的 $U,U^2$ 项不贡献其低层对角角。将 $W$ 写成低层分块 $W_{ba}$，对每个 $a\ne0$ 有

$$
D_a:=W_{aa}=A\frac{I+T_{Ma}}2+B\frac{I-T_{Ma}}2.
\tag{14.5}
$$

仍以定理 11.2 从实际效果构造 $\mathfrak D=\mathfrak D(S_\Delta)$，于是低层全矩阵包含于 $\mathfrak D\subseteq S_\Delta$，且 $W^\dagger\mathfrak DW=\mathfrak D$。对任意低层指标 $a,b,c,d$，$W^\dagger(E_{cd}\otimes I)W$ 的 $a,b$ 角为 $W_{ca}^\dagger W_{db}$。用低层矩阵单位夹取并复制到全部低层对角，得

$$
I_A\otimes W_{ca}^\dagger W_{db}\in\mathfrak D.
\tag{14.6}
$$

后续乘法都在此乘子代数中进行。

先设 $A\ne B$。三个非零 $Ma$ 遍历高层的三个非零平移方向；适当排列三个 $D_a$ 后，四个 Fourier 标签上的数值轮廓为

$$
p_0:(A,A,A),\quad p_1:(A,B,B),\quad
p_2:(B,A,B),\quad p_3:(B,B,A).
$$

置 $\kappa=|A|^2>0$、$z_0=B/A$，则 $|z_0|=1$、$z_0\ne1$。两个已由 (14.6) 取得的归一化乘子 $\kappa^{-1}D_{a_1}^\dagger D_{a_2}$、$\kappa^{-1}D_{a_1}^\dagger D_{a_3}$ 的联合特征值依次为

$$
(1,1),\quad(z_0,z_0),\quad(\overline z_0,1),\quad(1,\overline z_0).
$$

这四对两两不同，包括 $z_0=-1$。为取得目标标签 $p$ 的投影，对每个 $q\ne p$ 选一个在 $p,q$ 处数值不同的乘子 $R_q$，将三个因子

$$
\frac{R_q-R_q(q)I}{R_q(p)-R_q(q)}
$$

相乘，即在 $p$ 上取值 $1$，在其余三点取值 $0$。因此全部 $\Pi_p=I_A\otimes|p\rangle\langle p|$ 属于 $\mathfrak D$。

若 $x^3\ne1$ 且 $x\ne-1$，则 $C\ne0$、$A\ne B$。低层 $10\to01$ 的 $U$ 步无进位，$U^2$ 则到 $11$，所以

$$
W_{01,10}=C\,V\left(\frac{I+T_{(0,1)}}2
+x\frac{I-T_{(0,1)}}2\right).
\tag{14.7}
$$

在每个 Fourier 标签 $p$ 上，这个角都是振幅为 $C$ 或 $xC$ 的非零 $p\to gp$ 单项。任取 $a_*\ne0$，(14.6) 给 $I_A\otimes D_{a_*}^\dagger W_{01,10}\in\mathfrak D$；$D_{a_*}$ 在每个标签上的值是非零的 $A$ 或 $B$。用 $\Pi_{gp},\Pi_p$ 夹取便取得每条 $g$ 邻边的矩阵单位。沿轨道相乘并取伴随，得 $\mathcal A_{\mathrm{orb}}\subseteq\mathfrak D\subseteq S_\Delta$。轨道投影与 $W$ 及全部低层分支交换，给反向包含。

剩余 $x=-1$ 时，(14.2) 化为

$$
W=-\frac13I+\frac23(U^2+U^4).
$$

每个非零低层对角角是 $-I_H/3$；在 (14.6) 中固定这个标量角，便将所有 $W_{db}$ 放入高层乘子部分。两步进位直接给

$$
W_{11,10}=\frac23V^2,\qquad
W_{10,01}=\frac23T_{(0,1)}V^2.
$$

第一条的两步均无进位；第二条仅 $11\to10$ 有进位。$U^4$ 的低层位移是 $f$，不贡献这两个 $f^2$ 角。由 $V^3=I$，$(V^2)^2=V$；再以乘积取得 $T_{(0,1)}$，用 $V^\dagger T_{(0,1)}V=T_{(1,0)}$ 得全部平移。Fourier 反演及 $V$ 邻边遂给全部轨道矩阵单位，仍有 $S_\Delta=\mathcal A_{\mathrm{orb}}$。

若 $x^3=1$、$x\ne1$，则 $C=0,A=1,B=x$，故

$$
W=P_++xP_-=\frac{1+x}{2}I+\frac{1-x}{2}U^3.
$$

由 (14.4)，这是按低层控制的 Fourier 对角门。每个高层单点投影均与它及所有低层分支交换，故 $S_\Delta\subseteq\mathcal B(\mathbb C^4)\otimes\mathcal D_F$；$A\ne B$ 时已证明的标签分离给反向包含。最后 $x=1$ 时 (14.2) 给 $W=I$，只有低层操作，张成恰为 $\mathcal B(\mathbb C^4)\otimes I_4$。$L$ 谱包含于 $\{0,1,3,4\}$，$W$ 以 $2\pi$ 为周期，上述互斥情形穷尽全部正时钟。模 $2$ 的 $g$ 轨道大小为 $1,3$，故三种维数分别为 $16$、$16\cdot4$、$16(1+9)$。在各已证明的实际效果线性空间上使用非退化迹配对，即得所列统计等价条件。$\square$

**推论 14.2（共振时钟舍去同轨道相位）。** 对两个不同的非零高层 Fourier 标签 $p,q$ 及任意低层密度算子 $\tau$，置

$$
|\psi_\pm\rangle=\frac{|p\rangle\pm|q\rangle}{\sqrt2},\qquad
\rho_\pm=\tau\otimes|\psi_\pm\rangle\langle\psi_\pm|.
$$

在 $\Delta\equiv2\pi/3,4\pi/3\pmod{2\pi}$ 的全部允许有限协议中，两输入的所有事件概率相同；在 (14.1) 第三种合同中则存在实际有限事件区分它们。

证明。两态的每个 Fourier 对角低层条件矩阵相同，所以对第二种实际效果线性空间给出相同迹配对。两个标签属于同一非零三周期，而轨道内算子 $I_A\otimes(|p\rangle\langle q|+|q\rangle\langle p|)$ 的期望分别为 $1,-1$。第三种合同的实际效果张成包含该算子，若所有实际事件概率相同，就会与这两个期望矛盾。这只证明区分事件存在，不将该算子或某个高层投影宣告为一项可直接执行的测量，也不提供最少调用数。三分结论限于 $d=e=2$。$\square$

**命题 14.3（固定时钟的共同状态解码成本）。** 在[定义 11.7 的单份、精确、共同 CPTP 编解码合同](https://github.com/the-omega-institute/trureturing/blob/fecb0ec51a883ebb079d477888ecfdc4d27a97eb/docs/develop/theory/FIBONACCI_COHERENT_TRANSPORT_BOUNDARY.md#L1114)下，要求保持定理 14.1 的全部实际历史统计。免费经典 flag 为任意有限集合，其概率可依赖输入，编码与同一个状态解码均固定，无隐藏量子旁路或预共享纠缠。则成本为

| 固定时钟条件 | 最小公共量子端口 $q$，有限经典 flag 免费 | 最小全计费 Hilbert 维数 |
| --- | ---: | ---: |
| $x=1$ | $4$ | $4$ |
| $x^3=1, x\ne1$ | $4$ | $16$ |
| $x^3\ne1$ | $12$ | $16$ |

证明。第一行的高层是不可读重数因子。令 $T=\mathrm{Dec}\circ\mathrm{Enc}$；效果线性张成给出的准确要求为

$$
\operatorname{Tr}_H\circ T=\operatorname{Tr}_H.
$$

取 $\mathrm{Enc}=\operatorname{Tr}_H$，$\mathrm{Dec}(\sigma)=\sigma\otimes\eta_H$，其中 $\eta_H$ 为固定密度算子，即用四维记忆达到上界。下界须单独处理：将输入高层固定为 $\eta_H$，解码后取低层偏迹，便得到通过同一存储资源实现的四维恒等通道。若量子端口为 $q$ 维，每个 flag 分支的复合 Kraus 算子秩至多为 $q$。恒等通道的 Choi 算子秩一，正算子之和等于此 Choi 算子迫使每个非零复合 Kraus 算子都是 $I_4$ 的标量倍数，故 $q\ge4$，即使 flag 的分布任意依赖输入仍成立。全计费时，四个低层正交基态必须仍可完美区分，编码支撑两两正交，故记忆维数至少为 $4$。此行不要求恢复原来的完整 $AH$ 态。

第二行有四个可读的四维 Fourier 块，第三行有四维与十二维两个可读轨道块。实际效果张成的等号给 $\mathcal E_{\mathcal P}\circ T=\mathcal E_{\mathcal P}$；在解码后加同一 pinching 不增加资源，便转为精确块恢复。因此可直接应用[命题 11.8 的块编码及 Choi 下界](https://github.com/the-omega-institute/trureturing/blob/fecb0ec51a883ebb079d477888ecfdc4d27a97eb/docs/develop/theory/FIBONACCI_COHERENT_TRANSPORT_BOUNDARY.md#L1133)，得到最大块维数 $4,12$。块标签可作免费有限 flag，各块等距嵌入公共端口达到上界。全计费时，两者均有十六个块内正交基态；拉回这些基投影得到完美区分编码态的 POVM，故十六个非零编码支撑两两正交，下界为 $16$。直接保存 pinching 的十六维输出达到它。此处使用实际效果线性张成与共同状态解码，而不只使用生成的 $C^*$ 代数；压缩工具的文献合同同命题 11.8 所引 Bluhm–Rauber–Wolf 与 Nayak–Sen。$\square$

## 15. 最长轨道、Pisano 周期与负单位同步

**定义 15.1（完整向量轨道的算术量）。** 对每个整数 $e\ge2$，所有作用均在完整 Fourier 标签集 $(\mathbb Z/e\mathbb Z)^2$ 上，置

$$
g=\begin{pmatrix}-1&1\\1&0\end{pmatrix},\qquad
j=\begin{pmatrix}1&0\\1&-1\end{pmatrix},\qquad
N_e=\langle g,-I\rangle,\qquad\Gamma_e=\langle g,j\rangle,
$$

$$
T_e=\operatorname{ord}_e(g),\qquad
h_e=|N_e|,\qquad b_e=\max_v|\Gamma_ev|,
\qquad
\pi(e)=\min\{k\ge1:(F_k,F_{k+1})\equiv(0,1)\pmod e\}.
$$

$\pi(e)$ 是矩阵／Pisano 周期；最小正零指标另在第 19 节记为 $r(e)$，两者不混同。

**定理 15.2（同一个标签达到循环群和正规群的阶）。** 对每个 $e\ge2$，包括合数，有

$$
\max_v|\langle g\rangle v|=T_e=\pi(e),\qquad
\max_v|N_ev|=h_e=
\begin{cases}
T_e,&-I\in\langle g\rangle,\\
2T_e,&-I\notin\langle g\rangle.
\end{cases}
\tag{15.1}
$$

两种最大值均由 $\alpha=(1,0)^{\mathsf T}$ 达到。若 $e=\prod_i p_i^{a_i}$，则 $T_e=\operatorname{lcm}_iT_{p_i^{a_i}}$。

证明。$\alpha,g\alpha$ 的列矩阵为 $\left(\begin{smallmatrix}1&-1\\0&1\end{smallmatrix}\right)$，行列式为 $1$，所以在每个剩余环上均为一组基。任何与 $g$ 交换且固定 $\alpha$ 的矩阵也固定 $g\alpha$，因而为恒等。将此用于 $\langle g\rangle$ 与 $N_e$，两个稳定子均平凡，轨道大小分别达到相应群阶。$N_e$ 中元素形如 $\varepsilon g^k$，$\varepsilon\in\{1,-1\}$，故其阶为 $T_e$ 或 $2T_e$。

对 $k\ge1$，Fibonacci 矩阵式

$$
M^k=\begin{pmatrix}F_{k-1}&F_k\\F_k&F_{k+1}\end{pmatrix}
$$

表明 $M^k=I$ 恰当 $F_k=0,F_{k+1}=1$ 模 $e$。转置与取逆保持矩阵阶，故 $T_e=\pi(e)$。CRT 下 $g_e^k=I$ 恰当同一个 $k$ 被每个局部矩阵阶整除，遂得最小公倍数。此处使用 Robinson, [*The Fibonacci Matrix Modulo m*，第 30–33 页，性质 (iii)、(iv) 及矩阵周期解释](https://www.fq.math.ca/Scanned/1-2/robinson.pdf)中的经典矩阵阶与最小公倍数工具；原文第 30、33 页的符号排印以[更正页](https://www.fq.math.ca/Scanned/2-1/corrections6.pdf)为准。上述基向量证明把这些周期工具具体接到本卷的完整 Fourier 轨道。$\square$

**引理 15.3（奇素数幂的局部负单位条件）。** 对奇素数 $p$ 与每个 $a\ge1$，

$$
-I\in\langle g\rangle\pmod{p^a}
\quad\Longleftrightarrow\quad4\mid T_{p^a},
\qquad
\nu_2(T_{p^a})=\nu_2(T_p).
\tag{15.2}
$$

证明。$\det g=-1$ 使 $T=T_{p^a}$ 为偶数。若 $-I$ 属于该循环群，它必须是唯一的非平凡二阶元素 $g^{T/2}$；比较行列式得 $T/2$ 为偶数。反向设 $4\mid T$，令 $B=g^{T/2}$，则 $B^2=I$、$B\ne I$、$\det B=1$。约化到 $\mathbb F_p$，其最小多项式整除 $(X-1)(X+1)$，故可对角化；二维、行列式为 $1$ 的对合只能为 $I$ 或 $-I$。若 $B\equiv I\pmod p$，则 $B+I$ 在 $\mathbb Z/p^a\mathbb Z$ 上可逆，由 $(B-I)(B+I)=0$ 得 $B=I$，矛盾。于是 $B\equiv-I\pmod p$，$B-I$ 可逆，得 $B=-I$。

约化 $\operatorname{GL}_2(\mathbb Z/p^a\mathbb Z)\to\operatorname{GL}_2(\mathbb F_p)$ 的核有过滤 $I+p^sX$，相邻商嵌入模 $p$ 的矩阵加法群，故为有限 $p$ 群。因此 $T_{p^a}/T_p$ 是 $p$ 的幂，$p$ 为奇数给第二式。这是 Robinson 上引性质 (iv) 所容许的周期平台与奇素数提升的直接群论后果，并未假设每一层都增长 $p$ 倍。$\square$

**定理 15.4（负单位的全局半周期同步）。** $e=2$ 时 $-I\in\langle g\rangle$；$4\mid e$ 时不属于。其余模数写成

$$
e=2^\epsilon\prod_{i=1}^r p_i^{a_i},\qquad
\epsilon\in\{0,1\},\quad r\ge1,
$$

其中 $p_i$ 为不同奇素数，则

$$
-I\in\langle g\rangle\pmod e
\quad\Longleftrightarrow\quad
\nu_2(\pi(p_1))=\cdots=\nu_2(\pi(p_r))=s\ge2.
\tag{15.3}
$$

证明。模 $2$ 时 $-I=I$。模 $4$ 时 $M^3=I+2M\ne I,-I$，$M^2=\left(\begin{smallmatrix}1&1\\1&2\end{smallmatrix}\right)\ne I$，而 $M^6\equiv I$；其阶为 $6$，唯一非平凡二阶元素是 $M^3$，所以 $-I$ 不属于循环群。取逆转置保留此成员关系，约化即排除所有 $4\mid e$。

令 $T_i=T_{p_i^{a_i}}$。引理 15.3 说明每个奇局部分量首先须有 $4\mid T_i$，然后实现 $-I$ 的指数恰为

$$
k\equiv T_i/2\pmod{T_i}.
\tag{15.4}
$$

若 $\nu_2(T_i)<\nu_2(T_j)$，前一半周期模 $2^{\nu_2(T_i)}$ 非零，后一半周期则为零，故没有同一个 $k$。反之，若所有赋值为同一个 $s\ge2$，置 $L=\operatorname{lcm}_iT_i$；每个 $L/T_i$ 为奇数，故 $k=L/2$ 满足全部 (15.4)。若还有模 $2$ 分量，其周期为 $3$、所需指数类为 $0$；改取 $L'=\operatorname{lcm}(L,3)$、$k=L'/2$ 即同时满足它，而 $L'/T_i$ 仍为奇数。最后用引理 15.3 将 $\nu_2(T_i)$ 换成 $\nu_2(\pi(p_i))$，得 (15.3)。这要求一个共同半周期指数，不是分别存在局部指数。

例如 $M^4\equiv-I\pmod3$ 给 $\pi(3)=8$；$M^5\equiv3I\pmod5$、$M^{10}\equiv-I\pmod5$，而 $M^4\not\equiv I\pmod5$，给 $\pi(5)=20$。模 $15$ 的两项半周期要求为 $k\equiv4\pmod8$、$k\equiv10\pmod{20}$，在模 $4$ 上冲突。所以 $T_{15}=40$、$h_{15}=80$，尽管两个局部循环群都含负单位。$\square$

**推论 15.5（算术量代入已声明的相干端口）。** 对所有 $d,e\ge2$，沿用定义 11.7 的全部输入、单份精确、共同 CPTP 状态编解码、免费有限经典 flag 与公共量子端口合同，三个已确定实际效果空间的最优值为

$$
q_g(d,e)=d^2T_e,\qquad
q_N(d,e)=d^2h_e,\qquad
q_\Gamma(d,e)=d^2b_e.
\tag{15.5}
$$

$g$ 项用于 $\Sigma_{\mathrm{orb}}$、$\Sigma_W$ 及已证明 $S_\Delta=\mathcal A_{\mathrm{orb}}$ 的固定时钟，特别是所有 $0<\Delta\le\pi/4$；$N$ 项用于定义 12.1 的混合合同；$\Gamma$ 项用于定理 12.3 加入标准 $W_J$ 或 $W_C$ 的合同。三者的最小全计费 Hilbert 记忆均为 $d^2e^2$。

证明。实际效果线性张成分别由第 11、13、14 节及[定理 12.2](https://github.com/the-omega-institute/trureturing/blob/fecb0ec51a883ebb079d477888ecfdc4d27a97eb/docs/develop/theory/FIBONACCI_COHERENT_TRANSPORT_BOUNDARY.md#L1252)、[定理 12.3](https://github.com/the-omega-institute/trureturing/blob/fecb0ec51a883ebb079d477888ecfdc4d27a97eb/docs/develop/theory/FIBONACCI_COHERENT_TRANSPORT_BOUNDARY.md#L1309)给出。各轨道块维数为 $d^2|O|$，命题 11.8 的统计到 pinching 桥梁及最大块结论可直接应用；代入定理 15.2 与 $b_e$ 的定义即得 (15.5)。全计费值为全部块维数之和 $d^2e^2$。此推论不改变许可字母表，也不将无共同状态解码的逐测量访问归入同一资源问题。$\square$

## 16. 对偶二次环、稳定子与同一全局作用

**定义 16.1（物理标签的统一对偶环坐标）。** 记基环 $B_e=\mathbb Z/e\mathbb Z$，二次环及其共轭为

$$
R_e=B_e[z]/(z^2+z-1),\qquad
\overline z=-1-z=-z^{-1},\qquad
\Phi(x,y)=y+xz,\qquad\operatorname{Nm}(f)=f\bar f,
\qquad H_e=\langle z,-1\rangle\le R_e^\times.
$$

$\Phi$ 是从完整物理 Fourier 标签到二次环元素的 $B_e$ 模同构，不是 Hilbert 态的整体相位识别。对标签 $v=(x,y)$，称其本原，指 $B_ex+B_ey=B_e$；称其循环，指 $v,gv$ 构成 $B_e^2$ 的基；称其 $N_e$ 自由，指稳定子只含恒等群元素。

**命题 16.2（负共轭与三种向量条件）。** 对每个 $e\ge2$，

$$
\Phi(gv)=z\Phi(v),\qquad
\Phi(jv)=-\overline{\Phi(v)},
$$

$$
D(x,y):=\det[v,gv]=x^2+xy-y^2
=-\operatorname{Nm}(\Phi(v)).
\tag{16.1}
$$

$\Phi(v)$ 是环单位，当且仅当 $v$ 循环。循环向量必本原且 $N_e$ 自由；本原、循环与 $N_e$ 自由并非同一个条件。

证明。由 $z^2=1-z$，$z(y+xz)=x+(y-x)z=\Phi(gv)$；而 $\overline{y+xz}=y-x-xz=-\Phi(jv)$。范数展开为 $y^2-xy-x^2$，给 (16.1)。乘以 $y+xz$ 在基 $(1,z)$ 中的矩阵是 $\left(\begin{smallmatrix}y&x\\x&y-x\end{smallmatrix}\right)$；它可逆恰当范数为基环单位，亦可由 $f^{-1}=\bar f/\operatorname{Nm}(f)$ 得充分性。因此环单位恰对应 $D(x,y)$ 为单位，亦即 $v,gv$ 成基。成基蕴含坐标生成单位理想；若 $af=f$ 且 $f$ 为单位，则 $a=1$，给 $N_e$ 自由。第 17 节的分裂素数幂向量 $(1,p)$（在特征基中）及第 18 节的实际标签给出本原且 $N_e$ 自由、但不循环的实例；模 $11$ 特征线上的非零向量本原但有非平凡 $N_{11}$ 稳定子。$\square$

**定理 16.3（包括非单位与零标签的精确轨道判据）。** 对任意 $f\in R_e$，定义

$$
S(f)=\{a\in H_e:(a-1)f=0\},\qquad
E(f)=\{a\in H_e:\bar f=af\}.
$$

在 $\Phi$ 坐标中有

$$
|\Gamma_e f|=
\begin{cases}
h_e/|S(f)|,&E(f)\ne\varnothing,\\
2h_e/|S(f)|,&E(f)=\varnothing.
\end{cases}
\tag{16.2}
$$

此外 $|\Gamma_e|=2h_e$，且

$$
b_e\in\{h_e,2h_e\},\qquad
b_e=2h_e\quad\Longleftrightarrow\quad
\exists f\in R_e:\ S(f)=\{1\}, E(f)=\varnothing.
\tag{16.3}
$$

证明。$N_e$ 忠实对应 $H_e$ 的乘法作用。$S(f)$ 是稳定子，$E(f)$ 非空时是它的一个陪集。共轭保持 $H_e$，因为 $\bar z=-z^{-1}$，故 $f$ 与 $\bar f$ 的稳定子阶相同。矩阵关系 $j^2=I$、$jgj=-g^{-1}$ 给 $N_e\triangleleft\Gamma_e$，且 $\Gamma_e=N_e\cup N_ej$。$N_e$ 的每个元素与 $g$ 交换，但

$$
jg-gj=\begin{pmatrix}-1&2\\-3&1\end{pmatrix}
$$

在任何模 $e\ge2$ 下非零，所以 $j\notin N_e$，群阶为 $2h_e$。两条 $N_e$ 轨道 $H_ef,H_e\bar f$ 大小相同，或者相等或者不交；$j$ 的负号由 $-1\in H_e$ 吸收，故轨道稳定子公式给 (16.2)。零标签有 $S(0)=E(0)=H_e$，也被该式包含。

若 $|S(f)|\ge2$，其 $\Gamma_e$ 轨道至多有 $h_e$ 点；若 $S(f)=\{1\}$，轨道只能有 $h_e$ 或 $2h_e$ 点。定理 15.2 的 $\alpha$ 至少达到 $h_e$，所以最大值与达到条件恰为 (16.3)。对单位可将反射条件写成 $\bar f/f\in H_e$，但非单位必须保留 $S,E$ 原式。此为全部标签的精确判据，不是仅由合数的素因子清单给出的 $b_e$ 闭式。$\square$

**命题 16.4（CRT 中的真实向量周期与共同指数）。** 写 $e=\prod_i e_i$ 为两两互素素数幂，固定一个实际全局标签 $v$，其分量为 $v_i$。令

$$
s_i=|\langle g_i\rangle v_i|,
\qquad K_i(\varepsilon)=
\{k\bmod s_i:j_iv_i=\varepsilon g_i^kv_i\},
\quad\varepsilon\in\{1,-1\}.
$$

每个 $K_i(\varepsilon)$ 或为空，或为单个剩余类 $k_i(\varepsilon)$。于是 $jv\in N_ev$ 当且仅当存在同一个 $\varepsilon$，使全部 $K_i(\varepsilon)$ 非空且

$$
k_i(\varepsilon)\equiv k_j(\varepsilon)
\pmod{\gcd(s_i,s_j)}\quad\text{对所有 }i,j.
\tag{16.4}
$$

证明。两个指数作用在同一 $v_i$ 上结果相同，恰当其差为该向量返回周期 $s_i$ 的倍数，故局部解至多一个剩余类。先固定共同符号 $\varepsilon$，广义 CRT 说明这些指数同余有一个共同整数解 $k$ 恰当 (16.4)；其解给实际全局元素 $\varepsilon g^k$，反向亦然。零分量有 $s_i=1$，不添约束。

系数 CRT 将 $R_e$ 识别为 $\prod_iR_{e_i}$，任意一组局部向量均给唯一全局向量；群元素却只能取同一 $\varepsilon,k$ 的 $(\varepsilon z_i^k)_i$。因此 $S(f)$ 也要求同一个全局元素同时满足全部局部固定式，不能分别优化局部轨道后拼接最大值。不同符号—指数参数可能表示同一个群元素；稳定子计数按群元素进行，尤其在 $-I\in\langle g\rangle$ 或 $e=2$ 时不能重复计数。矩阵周期仅在向量确有满周期时可代替这里的 $s_i$。$\square$

## 17. 所有素数幂的最大几何轨道

**定理 17.1（素数幂分类）。** 对任意素数 $p$、整数 $a\ge1$，令 $e=p^a$，沿用 $T=T_e,h=h_e,b=b_e$。奇素数 $p\ne5$ 时记 $\chi=(5/p)$。则完整标签集上的最大轨道由下表给出；表中非分裂情形的 $t=p^{a-1}(p+1)$。

| 模数情形 | $h$ | $b$ |
| --- | --- | --- |
| $e=2$ | $3$ | $3$ |
| $e=2^a, a\ge2$ | $3\cdot2^a$ | $h$ |
| $e=5^a$ | $4\cdot5^a$ | $h$ |
| 奇 $p\ne5, \chi=-1$ | $T$ | $h$ 若 $h=2t$，否则 $2h$ |
| 奇 $p\ne5, \chi=1, a=1$ | $T$ 若 $4\mid T$，否则 $2T$ | $h$ 若 $h=2(p-1)$，否则 $2h$ |
| 奇 $p\ne5, \chi=1, a\ge2$ | $T$ 若 $4\mid T$，否则 $2T$ | $2h$ |

在 $2^a$、$5^a$ 以及奇非分裂且 $h=2t$ 的情形，每条 $\Gamma_e$ 轨道已经是一条 $N_e$ 轨道。分裂素数 $a=1,h=2(p-1)$ 时，两条特征轴仍会合并，最大值却不增长。分裂 $a\ge2$ 的 $2h$ 由本原、非循环且 $N_e$ 自由的向量达到。

证明。先在本题矩阵上确定 $2,5$ 的周期提升。若 $p$ 奇、$X=I+p^sB$、$s\ge1$ 且 $B$ 至少一项非零模 $p$，二项展开给

$$
X^p\equiv I+p^{s+1}B\pmod{p^{s+2}},
$$

所以矩阵 $X^p-I$ 的最小项赋值恰为 $s+1$。$p=2$ 时此结论在 $s\ge2$ 成立，因为

$$
(I+2^sB)^2=I+2^{s+1}B+2^{2s}B^2.
$$

结合引理 15.3 证明中的约化核为 $p$ 群，这些赋值决定下列实际阶；这正是 Robinson [第 32–33 页的二项式周期提升方法](https://www.fq.math.ca/Scanned/1-2/robinson.pdf)，这里分别计算两个特殊素数的起始层。

模 $2$ 的 $M$ 阶为 $3$，而整数恒等式

$$
M^3=I+2M,\qquad M^6=I+4M^3
$$

给模 $4$ 阶为 $6$，且 $\nu_2(M^6-I)=2$。逐层平方得到

$$
T_{2^a}=3\cdot2^{a-1}\quad(a\ge1).
\tag{17.1}
$$

模 $2$ 负单位为恒等；更高次幂的负单位由模 $4$ 障碍排除。因此 $h_2=3$，$a\ge2$ 时 $h_{2^a}=3\cdot2^a$。

模 $5$ 令 $B=(g-2I)/2$，则 $B\ne0,B^2=0$。由 $g^k=2^k(I+kB)$，$g^k=I$ 要求标量 $2^k=1$ 及 $k=0\pmod5$：非零幂零矩阵 $B$ 与 $I$ 线性无关。故 $T_5=20$。再由整数恒等式 $M^5=3I+5M$，

$$
M^{20}\equiv6I+15M\pmod{25},\qquad
M^{20}-I\equiv5(I+3M)\pmod{25},
$$

其赋值恰为 $1$。上述奇素数提升给

$$
T_{5^a}=20\cdot5^{a-1}=4\cdot5^a.
\tag{17.2}
$$

引理 15.3 给 $h_{5^a}=T_{5^a}$。其余奇素数的 $h$ 同样由该引理决定，未要求 $T_{p^a}=p^{a-1}T_p$。

其次处理非分裂二次环，包括 $p=2$。当 $p$ 奇且 $\chi=-1$，或 $p=2$ 时，$X^2+X-1$ 模 $p$ 不可约且可分。令 $R=R_{p^a}$、$B_0=\mathbb Z/p^a\mathbb Z$。$R$ 的剩余域为 $\mathbb F_{p^2}$；元素是单位恰当两项系数不同时被 $p$ 整除。确实，剩余域中的非零像可逆，将逆提升后误差在幂零理想 $pR$ 内，可用有限几何级数消去。每个非零元素因此可写成 $p^r u$，$0\le r<a$，其中 $u$ 为单位。计数给

$$
|R^\times|=p^{2a-2}(p^2-1),\qquad
|B_0^\times|=p^{a-1}(p-1).
$$

范数 $\operatorname{Nm}:R^\times\to B_0^\times$ 满射。剩余域单位群循环，范数为 $u\mapsto u^{p+1}$，其像有 $p-1$ 点，故第一层满射。若已匹配某目标范数至模 $p^k$，$1\le k<a$，乘以 $1+p^kv$ 会使下一位范数改变为

$$
\operatorname{Nm}(1+p^kv)
\equiv1+p^k\operatorname{Tr}(v)\pmod{p^{k+1}}.
$$

剩余域中 $\operatorname{Tr}(z)=-1$，故迹满射；逐层修正即可达到目标。于是范数核 $K$ 有

$$
|K|=t=p^{a-1}(p+1).
$$

共轭比值 $u\mapsto\bar u/u$ 也满射到 $K$。其核是固定单位；若 $x+yz$ 被共轭固定，则 $y(2z+1)=0$。因 $(2z+1)^2=5$ 在此环可逆，必有 $y=0$，故核恰为 $B_0^\times$。其像已有 $|R^\times|/|B_0^\times|=t$ 点，且范数为 $1$，正好等于 $K$。

对奇非分裂 $p$，剩余域中共轭是 Frobenius，$z^{p+1}=\operatorname{Nm}(z)=-1$。故 $T_p\mid2(p+1)$ 但 $T_p\nmid p+1$，从而 $\nu_2(T_p)=\nu_2(2(p+1))\ge2$。引理 15.3 给 $h=T$。$H=\langle z,-1\rangle$ 的范数像为 $\{1,-1\}$，所以 $|H\cap K|=h/2$，并且 $h\le2t$。若 $h<2t$，选 $k\in K\setminus H$，由比值满射选一个单位 $u$ 使 $\bar u/u=k$。同一个 $u$ 既有平凡稳定子，又满足 $E(u)=\varnothing$，故定理 16.3 给 $2h$。若 $h=2t$，$H$ 恰是范数为 $\pm1$ 的全部单位。对任意非零标签 $f=p^ru$，

$$
\bar f=(\bar u/u)f,\qquad \bar u/u\in K\subseteq H.
$$

因此连非单位标签的轨道也没有合并；零点固定，单位达到 $h$。这证明表中的奇非分裂行。

$p=2,a\ge2$ 时，$1\ne-1$ 在基环成立，已知 $h=3\cdot2^a=2t$。同一范数计数说明 $H$ 为范数 $\pm1$ 的全部逆像，故对所有 $f=2^ru$ 使用上一式，得到 $b=h$ 及全部轨道不合并。$a=1$ 时 $R=\mathbb F_4$，$H=\mathbb F_4^\times$ 已包含所有三个非零元素，故 $b=h=3$。

再处理奇分裂素数 $p\ne5$。两个模 $p$ 根不同，导数可逆；若 $\lambda_k$ 已是模 $p^k$ 的根，将其改为 $\lambda_k+p^ku$，下一位误差为原误差加 $p^ku(2\lambda_k+1)$，唯一选择 $u\pmod p$ 即消去误差。逐层得到 $B_0$ 中两个根 $\lambda,\mu$，满足

$$
\lambda+\mu=-1,\qquad\lambda\mu=-1,
\qquad\lambda-\mu\in B_0^\times.
$$

特征向量 $e_\lambda=(1,\lambda+1)$、$e_\mu=(1,\mu+1)$ 成基。在这个特征基中

$$
g=\operatorname{diag}(\lambda,\mu),\qquad j(X,Y)=(Y,X).
\tag{17.3}
$$

这些是物理向量的特征坐标，不能将其直接当作 $\Phi(x,y)=y+xz$ 的系数。

当 $a\ge2$，在 (17.3) 中取同一个标签 $v=(1,p)$。若 $\varepsilon\operatorname{diag}(\lambda^k,\mu^k)$ 固定它，第一坐标给 $\varepsilon\lambda^k=1$，第二乘数因此为 $\varepsilon\mu^k=(-1)^k$。固定第二坐标要求

$$
p\bigl((-1)^k-1\bigr)=0\pmod{p^a}.
$$

$p$ 奇且 $a\ge2$ 排除奇 $k$；偶 $k$ 时两个乘数都为 $1$，所讨论的群元素即为恒等。这证明稳定子平凡，不要求其符号—指数表达唯一。另一方面 $jv=(p,1)$，而 $N_e$ 的两个对角乘数均为单位，分别保持两坐标的 $p$ 进赋值，不能把 $(0,1)$ 的赋值对变为 $(1,0)$。故 $jv\notin N_ev$，定理 16.3 给 $b=2h$。$v$ 本原，但 $v,gv$ 的行列式在该基中为 $p(\mu-\lambda)$，不是单位，故不循环。

当 $a=1$，置 $K_0=\langle\lambda^2,-1\rangle\le\mathbb F_p^\times$。$N_p$ 的行列式像为 $\{1,-1\}$，核恰为

$$
\{\operatorname{diag}(u,u^{-1}):u\in K_0\},\qquad h=2|K_0|.
$$

对 $X,Y\ne0$，稳定子平凡；将 $(X,Y)$ 送至 $(Y,X)$ 的唯一对角矩阵为 $\operatorname{diag}(Y/X,X/Y)$，故 $jv\in N_pv$ 恰当 $Y/X\in K_0$。若 $h<2(p-1)$，取比值在 $K_0$ 外，便达到 $2h$。若 $h=2(p-1)$，所有两坐标非零的标签轨道不合并，大小为 $h$；还须检查非单位标签。此时 $\langle\lambda,-1\rangle$ 包含 $K_0=\mathbb F_p^\times$，每条非零特征轴是一条 $p-1$ 点 $N_p$ 轨道，$j$ 交换两轴，合并后恰为 $2(p-1)=h$ 点。零点固定，所以最大值仍为 $h$。

最后处理分歧素数 $5$。在 $B_0=\mathbb Z/5^a\mathbb Z$ 中令 $w=2z+1$，则

$$
R_{5^a}\simeq B_0[w]/(w^2-5),\qquad \bar w=-w.
$$

单位 $x+yw$ 恰当 $x\not\equiv0\pmod5$，其范数是 $x^2-5y^2$。每个非零元素可写为 $w^ru$，$0\le r<2a$，$u$ 为单位：将零系数赋值记为 $a$，比较不同奇偶性的 $2\nu_5(x)$ 与 $2\nu_5(y)+1$。若 $\nu_5(x)\le\nu_5(y)$，提出 $w^{2\nu_5(x)}=5^{\nu_5(x)}$ 后常数项为单位；若 $\nu_5(x)>\nu_5(y)=s$，则

$$
x+yw=w^{2s+1}
\left(\frac{y}{5^s}+\frac{x}{5^{s+1}}w\right),
$$

括号的常数项为单位。式中的商用系数的整数提升求出，所得等式在商环中成立，故覆盖全部非零非单位。

单位数为 $4\cdot5^{2a-1}$。范数像恰为模 $5$ 是非零平方的基环单位：必要性由范数模 $5$ 等于 $x^2$；反向，对这种基环单位，其模 $5$ 平方根的导数 $2x$ 可逆，逐层提升出标量平方根，它的范数就是目标。范数像有 $2\cdot5^{a-1}$ 点，核有 $2\cdot5^a$ 点。已知 $h=4\cdot5^a$，而 $H$ 的范数像是 $\{1,-1\}$；两者确在上述像内，故 $H$ 恰为范数 $\pm1$ 的全部逆像，包含整个范数核。对任意 $f=w^ru$，

$$
\bar f=(-1)^r\frac{\bar u}{u}f.
$$

该乘数的范数为 $1$，所以属于 $H$。零点亦固定，故全部 $\Gamma_e$ 轨道已是 $N_e$ 轨道；单位达到 $h$。这完成所有素数幂及所有标签的证明。$\square$

**推论 17.2（模十一与模四十七的端口对照）。** 对任意 $d\ge2$，模 $11$ 有 $T_{11}=10,h_{11}=b_{11}=20$；模 $47$ 有 $T_{47}=h_{47}=32,b_{47}=64$。在推论 15.5 的合同中，相应 $(q_N,q_\Gamma)$ 为 $(20d^2,20d^2)$ 与 $(32d^2,64d^2)$。

证明。模 $11$ 的两根为 $3,7$。$3^5=1$ 且 $3\ne1$，故 $3$ 阶为 $5$；$7^2=5$、$7^5=-1$ 且 $7\ne-1$，故 $7$ 阶为 $10$。于是 $T_{11}=10$，负单位不在循环群内，$h_{11}=20=2(11-1)$。定理 17.1 给 $b_{11}=20$。[命题 12.4 的两条非零特征线](https://github.com/the-omega-institute/trureturing/blob/fecb0ec51a883ebb079d477888ecfdc4d27a97eb/docs/develop/theory/FIBONACCI_COHERENT_TRANSPORT_BOUNDARY.md#L1338)各有十点，确被 $j$ 合为二十点轨道；但两特征坐标均非零的标签原本已有二十点轨道。因此可观测代数严格增加，不必增加最大端口。

模 $47$ 时二次互反给 $(5/47)=-1$。由 $F_{15}=610,F_{16}=987,F_{17}=1597$，Fibonacci 矩阵式给 $M^{16}\equiv-I\pmod{47}$。其阶整除 $32$ 且不整除 $16$，所以 $T_{47}=32$，负单位已在循环群内。由于 $h_{47}=32<2(47+1)=96$，非分裂行给 $b_{47}=64$。最后代入 (15.5)。$\square$

## 18. 非循环标签共同达到合数与提升后的最大值

**命题 18.1（模三十三：单位测试遗漏最大轨道）。** 模 $33$ 有

$$
T_{33}=40,\qquad h_{33}=80,\qquad b_{33}=160.
$$

同一个物理 Fourier 标签 $v=(12,4)\pmod{33}$ 本原且 $N_{33}$ 自由，但不循环，并满足 $|\Gamma_{33}v|=160$。相反，每个 $f\in R_{33}^\times$ 的 $\Gamma_{33}$ 轨道都恰有 $80$ 点。

证明。已知 $T_3=8,T_{11}=10$，CRT 给 $T_{33}=40$。模 $11$ 的 $-I$ 不在循环群内，所以全局也不在，$h_{33}=80$。模 $11$ 取

$$
a=(1,4),\qquad b=(1,8),\qquad
ga=3a,\quad gb=7b,\quad ja=b,\quad jb=a.
$$

实际全局标签 $v$ 的模 $11$ 分量为 $a$，模 $3$ 分量为 $\beta=(0,1)$。若一个全局群元素 $\varepsilon g^k$ 固定 $v$，模 $11$ 上要求 $\varepsilon3^k=1$。$3$ 阶为 $5$，其子群不含 $-1$，故强制 $\varepsilon=1$ 与 $5\mid k$。模 $3$ 上，$\beta,g\beta=(1,0)$ 成基，所以固定 $\beta$ 强制 $8\mid k$。两条件在同一个 $k$ 上给 $40\mid k$，即全局恒等元素，稳定子平凡。

$j$ 把 $v$ 的模 $11$ 分量送到另一条特征线，而每个 $N_{11}$ 元素分别保持两线，故 $jv\notin N_{33}v$。由定理 16.3，$|\Gamma_{33}v|=2h_{33}=160$，也达到群阶上界。$4$ 在模 $33$ 是单位，故 $v$ 本原；但

$$
D(12,4)=144+48-16=176\equiv11\pmod{33}
$$

不是单位，所以它不循环。

为完整排除单位标签达到 $160$，使用同一个环的完整范数核。$R_3\simeq\mathbb F_9$，单位范数核阶为 $4$；$R_{11}\simeq\mathbb F_{11}\times\mathbb F_{11}$，共轭交换两坐标，单位范数是乘积，其核阶为 $10$。故 $R_{33}^\times$ 的完整范数一群 $K_{33}$ 有 $40$ 个元素。$H_{33}$ 的范数像只有同一个全局 $\{1,-1\}$，因为 $\operatorname{Nm}(z)=-1$、$\operatorname{Nm}(-1)=1$，所以

$$
|H_{33}\cap K_{33}|=80/2=40=|K_{33}|.
$$

于是 $K_{33}\subseteq H_{33}$。任意单位 $f$ 的比值 $\bar f/f$ 都在 $K_{33}$，因而在 $H_{33}$；其稳定子又平凡，由 (16.2) 得轨道恰有 $80$ 点。这是对全体单位的排除，不只是某个单位候选失败。局部虽有 $b_3=h_3=8$、$b_{11}=h_{11}=20$，同一个全局非循环标签却使 $b_{33}=2h_{33}$。$\square$

**命题 18.2（模一百二十一：同一整数标签的提升）。** 模 $121$ 有

$$
T_{121}=110,\qquad h_{121}=220,\qquad b_{121}=440.
$$

同一个整数标签 $v=(12,4)\pmod{121}$ 本原、非循环且 $N_{121}$ 自由，满足 $|\Gamma_{121}v|=440$；所有环单位标签的 $\Gamma_{121}$ 轨道恰为 $220$ 点。

证明。整数矩阵恒等式为

$$
M^{10}=\begin{pmatrix}34&55\\55&89\end{pmatrix}
=I+11A,
\qquad A=\begin{pmatrix}3&5\\5&8\end{pmatrix}.
$$

若 $M^k=I\pmod{121}$，模 $11$ 强制 $k=10t$，而

$$
(I+11A)^t\equiv I+11tA\pmod{121}.
$$

$A$ 的非对角元 $5$ 为模 $11$ 单位，故此式等于 $I$ 恰当 $11\mid t$。于是 $T_{121}=110$；模 $11$ 的负单位障碍仍在，故 $h_{121}=220$。

多项式 $X^2+X-1$ 模 $121$ 的两根为 $\lambda=36,\mu=84$：它们的和为 $-1$、积为 $-1$，差是单位。因此

$$
a=(1,37),\qquad b=(1,85)
$$

构成 $g$ 特征基，特征值为 $\lambda,\mu$，且 $ja=b,jb=a$。标签 $v$ 在此基中的坐标是 $(1,11)$，因为

$$
a+11b=(12,972)\equiv(12,4)\pmod{121}.
$$

若 $\varepsilon g^k$ 固定它，第一特征坐标给 $\varepsilon\lambda^k=1$，第二乘数由 $\mu=-\lambda^{-1}$ 变为 $(-1)^k$。固定第二坐标要求 $11((-1)^k-1)=0\pmod{121}$；奇 $k$ 给 $-22\ne0$，故 $k$ 偶。此时两个乘数都为 $1$，所以稳定子平凡。$j$ 将 $(1,11)$ 送到 $(11,1)$，而 $N_{121}$ 的单位对角乘数分别保持两坐标的 $11$ 进赋值，不能实现此交换。因此 (16.2) 给 $440$ 点，达到上界。$12$ 为模 $121$ 单位，故标签本原；$D(12,4)\equiv55\pmod{121}$ 非单位，故不循环。

最后 $R_{121}\simeq(\mathbb Z/121\mathbb Z)\times(\mathbb Z/121\mathbb Z)$，单位范数一群有 $\varphi(121)=110$ 点；$H_{121}$ 的范数核也有 $220/2=110$ 点，故包含完整范数一群。单位的共轭比值全部属于 $H_{121}$，给所有单位轨道恰为 $220$。这里特征基中的 $j$ 交换两坐标与 $\Phi$ 中的负共轭相容：按两根求值，$\Phi(a)=(\lambda-\mu,0)$、$\Phi(b)=(0,\mu-\lambda)$，两种坐标的归一化因子符号相反。$\square$

**推论 18.3（不可由局部最大值直接合成的端口）。** 对所有 $d\ge2$，在推论 15.5 的 $\Gamma$ 合同下，

$$
q_\Gamma(d,33)=160d^2=4d^2\pi(33),\qquad
q_\Gamma(d,121)=440d^2=4d^2\pi(121).
$$

证明。将两项已由同一个实际标签达到的 $b_e$ 代入 (15.5)。它们排除普遍公式 $q_\Gamma=2d^2\pi(e)$。模 $11$ 到模 $121$ 的最大轨道增长，以及模 $3,11$ 到模 $33$ 的共同实现，分别表明单素数结论不能不检查标签稳定子就提升或合成；完整 CRT 条件仍由命题 16.4 给出。$\square$

## 19. 射影聚合删除的可读标量索引

**命题 19.1（零指标、标量返回与完整周期）。** 对每个 $e\ge2$，令

$$
r(e)=\min\{r\ge1:F_r\equiv0\pmod e\},\qquad
c_e=F_{r(e)-1}\pmod e,\qquad
\omega_e=\operatorname{ord}_{B_e^\times}(c_e).
$$

则

$$
M^{r(e)}=c_eI,\qquad c_e^2=(-1)^{r(e)},\qquad
\pi(e)=r(e)\omega_e,\qquad\omega_e\in\{1,2,4\},
\qquad g^{r(e)}=c_e^{-1}I.
\tag{19.1}
$$

若 $r(e)$ 偶，则 $\omega_e\in\{1,2\}$；若 $r(e)$ 奇且 $e>2$，则 $\omega_e=4$。特征二例外为 $r(2)=3,c_2=1,\omega_2=1,\pi(2)=3$。对 $\alpha=(1,0)$，按共同单位倍数取商后的轨道长为 $r(e)$，完整向量轨道长为 $\pi(e)$，每个射影纤维有 $\omega_e$ 个实际轨道标签。

证明。这里的 $r(e)$ 对应母卷[命题 105.2](https://github.com/the-omega-institute/trureturing/blob/fecb0ec51a883ebb079d477888ecfdc4d27a97eb/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#L7125)中的 $\rho(e)$；[推论 105.3](https://github.com/the-omega-institute/trureturing/blob/fecb0ec51a883ebb079d477888ecfdc4d27a97eb/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#L7177)给出标量返回子群和零指标整除性质。[定理 120.3](https://github.com/the-omega-institute/trureturing/blob/fecb0ec51a883ebb079d477888ecfdc4d27a97eb/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#L10571)在素数幂本原射影标签上明确区分此返回阶与矩阵／Pisano 周期。以下只把这些既有关系接到完整 Fourier 标签；经典标量乘数公式亦见 Robinson [第 31–32 页](https://www.fq.math.ca/Scanned/1-2/robinson.pdf)。

$M$ 在有限环上可逆，故有正有限阶，$r(e)$ 存在。矩阵式

$$
M^n=F_{n-1}I+F_nM
$$

表明 $M^n$ 为标量恰当 $F_n=0$。标量幂在循环群中构成子群，其在整数指数中的原像为 $r(e)\mathbb Z$；因此全部零指标恰是 $r(e)$ 的倍数。在最小返回处得到 $M^{r(e)}=c_eI$；它可逆，$c_e$ 是单位。取行列式得 $c_e^2=(-1)^{r(e)}$，所以 $c_e^4=1$。完整返回 $M^n=I$ 必先有 $n=r(e)t$，此时恰要求 $c_e^t=1$，得到 $\pi(e)=r(e)\omega_e$ 及所列奇偶情形。$e=2$ 的数值由 $F_1=F_2=1,F_3=2$ 给出。一个周期内的零指标为 $0,r(e),\ldots,(\omega_e-1)r(e)$，故 $\omega_e$ 也等于每周期零点数。

取逆转置给 $g^{r(e)}=c_e^{-1}I$。若 $g^k\alpha=u\alpha$，其中 $u\in B_e^\times$，交换性使 $g^k(g\alpha)=u(g\alpha)$；$\alpha,g\alpha$ 成基，故 $g^k=uI$。因此该标签的射影返回恰在标量返回指数发生，轨道长为 $r(e)$；完整轨道长为 $\pi(e)$，每个纤维就是 $\langle c_e\rangle$ 的 $\omega_e$ 个倍数。$\square$

**定理 19.2（聚合射影条件矩阵不足以保留实际统计）。** 固定任意 $d,e\ge2$。高层本原向量的有限环射影等价关系是 $p\sim up$，$u\in B_e^\times$；一般合数上的本原意为两坐标生成单位理想，不要求其中某一个坐标本身为单位。取本原 $p$ 使 $c_ep\ne p$，并取任意低层密度算子 $\tau$。定义

$$
\rho^{(p)}=\tau\otimes|p\rangle\langle p|,\qquad
\rho^{(c_ep)}=\tau\otimes|c_ep\rangle\langle c_ep|.
$$

若边界只保留射影聚合条件矩阵

$$
\overline\sigma_{[v]}(\rho)=\sum_{u\in[v]}\sigma_u(\rho),\qquad
\sigma_u(\rho)=(I_A\otimes\langle u|)\rho(I_A\otimes|u\rangle),
\tag{19.2}
$$

则两态的记录完全相同；这里对类中不同向量各求和一次。可将同样的单位倍数关系用于非本原标签，或另外保留其记录，两种做法对本例均无影响。但在任何已证明实际效果线性张成包含 $\mathcal A_{\mathrm{orb}}$ 的本卷合同中，存在实际有限低层事件区分它们，特别包括全部 $0<\Delta\le\pi/4$ 的固定采样合同。

证明。两态的非零条件矩阵分别只在标签 $p$ 与 $c_ep$ 处等于 $\tau$，而二者属于同一射影类。因此 (19.2) 在该类上均为 $\tau$，其余为零。由 (19.1)，$c_ep=g^{-r(e)}p$，它们甚至属于同一个完整 $g$ 轨道。算子

$$
\Pi_p=I_A\otimes|p\rangle\langle p|
\in\mathcal A_{\mathrm{orb}}
$$

对两态的期望分别为 $1,0$。由于它属于实际事件效果的复线性张成，若每个实际有限事件都给两态相同概率，则每个有限线性组合也给相同值，与这两个期望矛盾。故存在所述实际事件。这里不把 $\Pi_p$ 本身加入许可仪器，也不从线性张成推出完美单次区分。

$|c_ep\rangle$ 是另一个完整 Fourier 标签的正交基态，不是给 $|p\rangle$ 乘一个复数整体相位。失败的边界明确删除了单位倍数索引；若某个块仅名为“射影块”，却仍保留全部向量索引与所需相干，就没有实施 (19.2) 的有损聚合，本反例不针对这种命名。$\square$

**命题 19.3（模五的四个标签与两种四阶操作）。** 模 $5$ 有 $r(5)=5,c_5=3,\pi(5)=20$。同一射影点上的四个标签

$$
(1,0),\quad(3,0),\quad(4,0),\quad(2,0)
$$

对应四个两两正交的 Fourier 基态。配同一个任意低层态后，它们的射影聚合记录相同，但在定理 19.2 的合同下任意两者都可由某个实际有限低层事件区分。标量矩阵 $c_5I=3I$ 与定义 12.1 的 $C=MJ$ 都有阶 $4$，却是不同且在 $\operatorname{GL}_2(\mathbb F_5)$ 内不共轭的操作。

证明。$F_1,F_2,F_3,F_4,F_5\equiv1,1,2,3,0\pmod5$，所以 $r(5)=5,c_5=3$；$3^2=-1$ 给乘数阶 $4$，由 (19.1) 得周期 $20$。四个倍数互异；$g^5=2I$，所以沿正向五步依次为 $p,2p,4p,3p$，再回到 $p$。同一完整轨道有二十个标签，射影轨道只有五个，聚合删除的每纤维四倍数索引正是 $\omega_5=4$。任意两态的单点 Fourier 投影期望不同，定理 19.2 的线性张成论证给所述区分。

另一方面

$$
C=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\quad C^2=-I,
\qquad\det(3I)=4=-1,\quad\det C=1\pmod5.
$$

行列式在模线性共轭下不变，而且标量矩阵被所有此类共轭固定，故两者在 $\operatorname{GL}_2(\mathbb F_5)$ 中不共轭。此断言仅限二元模坐标的线性换基，不扩展为相应二十五维置换酉在任意 Hilbert 酉换基下不共轭。共同阶数也不授权在操作合同中交换二者。完整 $g$ 边界在推论 15.5 的资源合同下仍需 $20d^2$ 维公共量子端口，不能将射影长度 $5$ 直接代入该完整统计任务。$\square$

## 追加锚（本行以下为增补区）

## 20. 复合模数的最大相干块

沿用第 16 节的记号

$$
R_e=(\mathbb Z/e\mathbb Z)[z]/(z^2+z-1),\qquad
\bar z=-1-z,\qquad H_e=\langle z,-1\rangle\le R_e^\times,
$$

并令 $h(e)=|H_e|$、$b(e)=\max_{f\in R_e}|\Gamma_e f|$。定义单位比值群

$$
\mathcal B_e=\{\bar u/u:u\in R_e^\times\},\qquad C_e=|\mathcal B_e|,
$$

以及

$$
\iota_e=\begin{cases}1,&e=2,\\4,&5\mid e,\\2,&\text{otherwise}.\end{cases}
$$

对互素素数幂作乘法定义 $C_e$；局部因子为

$$
C_{2^a}=3\cdot2^{a-1},\qquad C_{5^a}=5^a,
$$

$$
C_{p^a}=p^{a-1}(p-1)\quad\text{若 }p\ne2,5\text{ 且 }(5/p)=1,
$$

$$
C_{p^a}=p^{a-1}(p+1)\quad\text{若 }p\ne2,5\text{ 且 }(5/p)=-1.
$$

**定理 20.1（全部模数的最大轨道）。** 令 $E(e)$ 表示下列条件：$e$ 没有奇分裂素因子，或 $e=p$、$e=2p$，其中 $p$ 是一个奇分裂素数。则对每个 $e\ge2$ 有

$$
\boxed{
 b(e)=h(e)\iff h(e)=\iota_eC_e\text{ 且 }E(e),
}\qquad
\boxed{
 b(e)=2h(e)\text{ 在其余情形}.}
\tag{20.1}
$$

**证明。** 用 $\Psi(x,y)=y+xz$ 识别 $(\mathbb Z/e\mathbb Z)^2$ 与 $R_e$。直接计算得

$$
\Psi(g(x,y))=z\Psi(x,y),\qquad \Psi(j(x,y))=-\overline{\Psi(x,y)}.
\tag{20.2}
$$

因此 $N_e$ 是 $H_e$ 的乘法作用。共轭正规化 $H_e$，而共轭不是乘法作用：它固定 $1$ 却不固定 $z$；即使 $e$ 为偶数，$2z+1$ 的常数项仍为 $1$，所以这一步不需要除以 $2$。于是 $\Gamma_e$ 在 $f$ 上的轨道是 $H_ef$ 与 $H_e\bar f$ 的并。令

$$
S(f)=\{a\in H_e:(a-1)f=0\}.
$$

若 $S(f)$ 的阶为 $s$，则 $|H_ef|=h(e)/s$；两个 $H_e$ 轨道或者相等或者不交。故每条轨道大小为 $h(e)/s$ 或 $2h(e)/s$，并且

$$
 b(e)=2h(e)\quad\Longleftrightarrow\quad
\exists f\;[S(f)=\{1\},\ \bar f\notin H_ef].
\tag{20.3}
$$

单位环元的稳定子总是平凡；非单位不作此假设。单位 $1$ 的轨道恰有 $h(e)$ 个元素，而 $s\ge2$ 的标签轨道至多有 $h(e)$ 个元素，所以最大值只可能是 $h(e)$ 或 $2h(e)$。

考虑同态 $u\mapsto\bar u/u$。若 $u=a+bz$ 且 $\bar u=u$，比较常数系数即得 $b=0$，故其核恰为标量单位群 $(\mathbb Z/e\mathbb Z)^\times$，包括 $2$ 的幂。CRT 同时分解单位群与共轭，因此 $\mathcal B_e$ 是局部比值群的直积。局部单位数为

$$
|R_{2^a}^\times|=3\cdot2^{2a-2},\quad
|R_{5^a}^\times|=4\cdot5^{2a-1},
$$

$$
|R_{p^a}^\times|=
\begin{cases}
p^{2a-2}(p-1)^2,&(5/p)=1,\\
p^{2a-2}(p^2-1),&(5/p)=-1,
\end{cases}
$$

这些计数来自模 $p$ 的环分别为 $\mathbb F_p\times\mathbb F_p$、$\mathbb F_{p^2}$、$\mathbb F_4$ 和 $\mathbb F_5[w]/(w^2)$。模 $p$ 的每个单位有 $p^{2a-2}$ 个提升且全部可逆，因为 $pR_{p^a}$ 是幂零理想；模 $p$ 非单位的提升仍非单位。分别除以标量单位数 $\varphi(p^a)$ 即得所列 $C_e$。

在商群 $R_e^\times/\mathcal B_e$ 中，

$$
\bar z/z=-z^{-2}\in\mathcal B_e,
$$

所以 $[z]^2=[-1]$，商中 $[z]$ 的阶至多为 $4$。若 $5\mid e$，令 $w=2z+1$，则 $w^2=5$，模 $5$ 共轭在 $R_5/(w)=\mathbb F_5$ 上为恒等，而任意单位比值约化为 $1$；$-1$ 约化为 $4$，故 $[-1]\ne1$，从而 $[z]$ 的阶恰为 $4$。若 $5\nmid e$，则 $w=2z+1$ 的范数为 $-5$，故 $w$ 可逆，且 $\bar w/w=-1$，所以 $[-1]=1$。若另有 $e>2$，$\operatorname N(z)=-1\ne1$，而 $\operatorname N(\mathcal B_e)=1$，故 $[z]\ne1$，其阶恰为 $2$。当 $e=2$ 时 $R_2=\mathbb F_4$，标量单位群 $\mathbb F_2^\times$ 是平凡群，故比值同态像有三个元素，$\mathcal B_2=R_2^\times$，商中 $[z]$ 的阶为 $1$。于是

$$
|H_e\cap\mathcal B_e|=h(e)/\iota_e,\qquad h(e)\le\iota_eC_e,\qquad
\mathcal B_e\subseteq H_e\iff h(e)=\iota_eC_e.
\tag{20.4}
$$

若 $h(e)<\iota_eC_e$，取 $c=\bar u/u\in\mathcal B_e\setminus H_e$。单位 $u$ 的 $H_e$ 稳定子平凡，且 $\bar u\notin H_eu$，所以 $|\Gamma_eu|=2h(e)$。以下设饱和条件 $\mathcal B_e\subseteq H_e$ 成立。

设 $p^a\parallel e$ 是奇分裂素因子。在局部坐标 $R_{p^a}\simeq(\mathbb Z/p^a)^2$ 中，$z=(\lambda,\mu)$、$\lambda\mu=-1$，共轭交换两坐标。这是实际环同构：模 $p$ 的两根简单，若 $\lambda$ 已是模 $p^k$ 的根，$\lambda+p^kt$ 是模 $p^{k+1}$ 的根等价于一个系数 $2\lambda+1\ne0\pmod p$ 的线性方程，故两根逐层唯一提升且根差为单位。每个所选局部有序对遂对应唯一的原二坐标标签。

若 $a\ge2$，取该分量为 $(1,p)$，其余 CRT 分量为单位 $1$。若同一个 $\varepsilon z^k$ 固定该标签，第一坐标给出乘子为 $1$；两坐标乘积为 $\operatorname N(\varepsilon z^k)=(-1)^k$，第二坐标条件为 $p((-1)^k-1)=0\pmod {p^a}$，故 $k$ 为偶数，随后两坐标乘子均为 $1$。其余分量为 $1$ 又迫使全局元素为恒等。共轭把 $(1,p)$ 变成 $(p,1)$，单位乘法不能交换一个单位坐标与一个非单位坐标，因此 $\bar f\notin H_ef$。

若 $a=1$ 且 $m=e/p>2$，取 $p$ 分量 $(1,0)$，其余 $m$ 分量为单位 $1$。固定条件先在 $R_m$ 中给出 $\operatorname N(\varepsilon z^k)=1$；由于 $m>2$，$k$ 为偶数，且 $p$ 分量两坐标乘子均为 $1$。同样得到平凡稳定子和共轭后的另一坐标轴。这里的符号 $\varepsilon$ 与指数 $k$ 是全局共同的。

这些构造穷尽“有奇分裂因子而非 $p,2p$”的情形。剩下没有奇分裂因子的情形。惰性局部（包括 $2$）约化为域，所以非单位恰为 $pR_{p^a}$。对惰性 $p^a$，若 $a\ge2$，令 $u=1+p^{a-1}z$，则

$$
\frac{\bar u}{u}=1-p^{a-1}(2z+1)\ne1,
\tag{20.5}
$$

因为 $p^{2a-2}=0\pmod {p^a}$，而右端与 $1$ 的差的常数系数非零。它固定全部被 $p$ 除的非单位。若 $a=1$，唯一非单位为零，取任意非平凡的局部比值元即可。对 $5^a$，令 $w=2z+1$，则 $R_{5^a}=(\mathbb Z/5^a)[w]/(w^2-5)$。元素 $a+bw$ 可逆恰当 $5\nmid a$；若 $5\mid a$，写成 $w(b+(a/5)w)$，故非单位均被 $w$ 除。取 $n=w^{2a-1}=5^{a-1}w$；则 $n\ne0$、$n^2=0$、$\bar n=-n$，并且

$$
\frac{\overline{1-n/2}}{1-n/2}=1+n\ne1,
\tag{20.6}
$$

它固定全部被 $w$ 除的非单位，因为 $nw=w^{2a}=5^a=0$。先在对应局部分量构造 (20.5) 或 (20.6) 的比值元，再在其他分量放置 $1$，得到 $\mathcal B_e$ 中的全局支撑元；只有在此之后才用 $\mathcal B_e\subseteq H_e$ 把它视为同一个全局 $H_e$ 元素。因此任何非单位标签都有非平凡稳定子，而单位标签的共轭比值属于 $H_e$，故其轨道不翻倍。

最后处理 $e=p$ 与 $e=2p$。分裂局部的 $\mathcal B_p$ 是整个范数一群 $(t,t^{-1})$：取单位 $(1,t)$ 即得比值 $(t,t^{-1})$。饱和条件经投影给 $\mathcal B_p\subseteq H_p$，而 $z\mathcal B_p$ 是所有范数 $-1$ 的乘子对；因此轴稳定子 $(1,-1)$、$(-1,1)$ 都来自 $H_p$。当 $e=p$ 时，这两个乘子分别固定两条坐标轴，零标签也有非平凡稳定子。当 $e=2p$ 时，若 $2$ 分量为零，用非平凡的 $\mathcal B_2=\mathbb F_4^\times$ 元支撑即可；若 $2$ 分量非零而 $p$ 分量在坐标轴上（包括零），先取 $p$ 分量的非恒等轴稳定子。约化 $H_e\to H_p$ 满射，因为两群均由 $z,-1$ 生成；取其全局提升 $t$，再利用 $\mathcal B_e\subseteq H_e$ 中支持于 $2$ 分量的元素校正其 $\mathbb F_4^\times$ 分量为 $1$。若两分量均为非单位，任一支撑元同样适用。故这两个例外中所有非单位都有非平凡稳定子，单位仍不翻倍。

于是，饱和且满足 $E(e)$ 时 $b(e)=h(e)$；饱和而不满足 $E(e)$ 时分裂构造给 $b(e)=2h(e)$；不饱和时单位比值构造给 $b(e)=2h(e)$。这完成 (20.1)。在推论 15.5 的实际效果张成与共同 CPTP 精确解码合同下，最大相干块及最小免费 flag 量子端口因而为

$$
q_\Gamma(d,e)=
\begin{cases}
d^2h(e),&h(e)=\iota_eC_e\ \text{且 }E(e),\\
2d^2h(e),&\text{其余情形}.
\end{cases}
$$

这一步只把全部标签的最大轨道代入已有资源定理，不扩大许可仪器。$\square$

在因子分解和各局部精确周期已给定时，由第 15 节的负单位同步条件计算 $h(e)$，再以 (20.1) 决定最大轨道；不需要枚举向量或求离散对数。这不把因子分解或周期取得称为免费，也不给出按位复杂度的效率保证；奇素数的周期提升允许任意初始平台。周期的 CRT 与平台提升背景见 Baake--Neumärker--Roberts, [arXiv:1205.1003v1, Eq. (7), p. 4; Proposition 1, p. 5; Appendix A.2, pp. 26–27](https://arxiv.org/abs/1205.1003v1)。文中的 Fibonacci 矩阵与本卷 $M$ 置换共轭，其普通 reversing 结果不证明这里的带符号关系 $jgj=-g^{-1}$ 所产生的 $\Gamma_e$ 结论。局部单位计数亦见 Lombardo--Perucca, [arXiv:1612.02845v2, Lemma 13, p. 6](https://arxiv.org/abs/1612.02845v2)；计数不把特定有限子群 $H_e$ 识别为全部 Cartan 单位群。

## 21. 全局容量上界与可实现下界

沿用第 15 节，$T(e)=\operatorname{ord}_e(g)=\pi(e)$ 是同一 Fibonacci 矩阵的 Pisano 周期。另令

$$
\eta=-z^2,\qquad L(e)=\operatorname{ord}_{R_e^\times}(\eta).
$$

在 $H_e/\langle\eta\rangle$ 中 $[-1]=[z]^{-2}$，所以此商由 $[z]$ 生成且 $[z]^4=1$，有

$$
 h(e)\le4L(e),\qquad b(e)\le8L(e),
\tag{21.1}
$$

而显然 $h(e)\le2T(e)$、$b(e)\le4T(e)$。CRT 对同一全局元素给出

$$
T(e)=\operatorname{lcm}_{p^a\parallel e}T(p^a),\qquad
L(e)=\operatorname{lcm}_{p^a\parallel e}L(p^a).
\tag{21.2}
$$

对奇素数 $p\ne5$，局部周期满足

$$
T(p^a)\mid
\begin{cases}
p^{a-1}(p-1),&(5/p)=1,\\
2p^{a-1}(p+1),&(5/p)=-1.
\end{cases}
\tag{21.3}
$$

证明这些界时，分裂域中 $z$ 的两个坐标属于 $\mathbb F_p^\times$；惰性域中 Frobenius 为共轭，故 $z^{p+1}=-1$。于是 $T(p)\mid2(p+1)$ 却不整除 $p+1$，所以 $v_2(T(p))=v_2(p+1)+1$。约化使 $T(p)\mid T(p^a)$，二项式展开使 $T(p^a)\mid p^{a-1}T(p)$；因此商是 $p$ 的幂且可能小于 $p^{a-1}$，特别允许所有奇素数的提升平台。惰性情形的 $2$-进赋值在提升中不变。

惰性局部令 $T=T(p^a)$。模 $p$ 有 $z^{T/2}=-1$，因为有限域乘法群中唯一非平凡二阶元为 $-1$，而 $T/T(p)$ 为奇数。令 $A=z^{T/2}$，则 $A^2=1$ 且 $A-1$ 为单位，故 $(A-1)(A+1)=0$ 强制 $A=-1$。所以

$$
L(p^a)=\frac{T}{\gcd(T,T/2+2)}.
$$

写 $T=4t$、$t$ 奇时，分母为 $4$；写 $T=2^st$、$s\ge3$、$t$ 奇时，分母为 $2$。结合 $T$ 的 $2$-进赋值，得

$$
\begin{array}{c|c}
p\equiv1\pmod4,\ (5/p)=-1&
L(p^a)=T(p^a)/4\mid p^{a-1}(p+1)/2\\
p\equiv3\pmod4,\ (5/p)=-1&
L(p^a)=T(p^a)/2\mid p^{a-1}(p+1),\quad4\mid L(p^a).
\end{array}
\tag{21.3a}
$$

在 $5$ 处，

$$
T(5^a)=4\cdot5^a,\qquad L(5^a)=5^a.
\tag{21.4}
$$

确实模 $5$ 有 $g=2(I+B)$、$B^2=0$、$B\ne0$。$g^k=2^k(I+kB)$ 等于恒等时，非标量项迫使 $5\mid k$，标量项迫使 $4\mid k$，所以 $T(5)=20$。又

$$
M^5=3I+5M,\qquad M^{20}-I\equiv5(I+3M)\not\equiv0\pmod{25}.
$$

若 $X=I+5^sB$ 且 $B\not\equiv0\pmod5$，则 $X^5\equiv I+5^{s+1}B\pmod{5^{s+2}}$。约化核为 $5$ 群，故周期逐层恰乘 $5$。$z^{T/2}\equiv-1\pmod5$ 且平方为 $1$，前述单位因子论证给 $z^{T/2}=-1$；$T/4=5^a$ 为奇数，故同一最大公因子计算给 $L=T/4$。

在 $2$ 处，

$$
T(2^a)=3\cdot2^{a-1},\qquad
L(2)=3,\quad L(4)=6,\quad
L(2^a)=3\cdot2^{a-2}\quad(a\ge3).
\tag{21.5}
$$

模 $2$ 的 $M$ 阶为 $3$，$M^3=I+2M$ 给 $T(4)=6$，并且 $M^6=I+4(I+2M)$。当 $s\ge2$ 时，对 $I+2^sB$ 逐次平方使矩阵差的最小 $2$-进赋值恰增一，故得到 $T(2^a)$。模 $4$ 的六阶循环群唯一二阶元 $g^3$ 非标量，故 $-1\notin\langle z\rangle$ 模 $4$ 及其所有提升。当 $a\ge2$，$\eta^k=1$ 因而等价于 $k$ 偶且 $T(2^a)\mid2k$；否则奇 $k$ 会给出 $z^{2k}=-1$。最小这样的 $k$ 就是 (21.5) 所列值；$a=1$ 则 $\eta=z^2$ 阶为 $3$。

**命题 21.1。** 对所有 $e\ge2$，$T(e)\le6e$。

**证明。** 把因子分为 $2$、$5$、奇分裂素数和奇惰性素数。添加一个分裂素数幂 $q^b$ 时，(21.3) 使 $T/e$ 至多乘以 $(q-1)/q<1$。若含 $5^c$，先取 $2^s5^c$；由 (21.2)、(21.4)、(21.5) 取最小公倍数，其 $T/e$ 依 $s=0,1,2,\ge3$ 分别为 $4,6,3,3/2$。已有周期被 $4$ 整除时，加入奇惰性 $p^a$ 的倍率至多

$$
\frac{2p^{a-1}(p+1)}{4p^a}=\frac{p+1}{2p}\le\frac23.
$$

若不含 $5$ 且含奇惰性因子，先加入一个 $p^a$；其周期被 $4$ 整除，与 $2^s$ 周期的公因子依 $s=0,1,2,\ge3$ 至少为 $1,1,2,4$（空基底周期记为 $1$）。由 $2(p+1)/p\le8/3$，合并后的 $T/e$ 上界依次为 $8/3,4,2,1$，之后每个惰性因子仍按上式加入，最后加入分裂因子只会降低比值。若没有奇惰性因子，只有 $2^s$，比值为 $1$ 或 $3/2$。因此全部情形中最大值为 $6$。证毕。

含分裂因子时，写 $e=p^am$。若 $m>2$，$T(p^a)$ 与 $T(m)$ 都为偶数，因为 $\det g=-1$，在模数大于 $2$ 时恒等幂的指数不能为奇数。故同一个 CRT 阶满足

$$
T(e)\le\frac{T(p^a)T(m)}2
\le3e\left(1-\frac1p\right),\qquad b(e)<12e.
$$

$m=1$ 时 $b(e)\le4p^{a-1}(p-1)<4e$；$m=2$ 时 $T(2)=3$ 给 $b(e)<6e$。

无奇分裂因子时，用 (21.1) 及 (21.3)--(21.5) 分组。写 $e=2^s5^c\prod_{i=1}^u p_i^{a_i}\prod_{j=1}^v q_j^{b_j}$，其中 $p_i\equiv1\pmod4$、$q_j\equiv3\pmod4$ 都是奇惰性素数，$s,c\ge0$；缺失的因子取 $1$。由 (21.3a) 把惰性素数分成这两类。若 $u$ 个第一类因子、$v$ 个第二类因子，则加入第一类的 $L/e$ 倍率至多 $(p+1)/(2p)\le3/5$，因为此类 $p\ge5$；第一个第二类因子的倍率至多 $(q+1)/q\le4/3$，其后因子与已有周期共享 $4$，故各至多 $(q+1)/(4q)\le1/3$。于是

$$
\frac{L(e)}e\le
\begin{cases}
 r_s(3/5)^u,&v=0,\\
 (3/2)(3/5)(4/3)(1/3)^{v-1},&u,v\ge1,\\
 (3/2)(4/3)(1/3)^{v-1},&u=0, v\ge2,
\end{cases}
$$

其中 $r_s=1,3/2,3/2,3/4$ 对应 $s=0,1,2,\ge3$，是 $2^s5^c$ 基底的 $L/e$ 上界，包括 $c=0$。上表三行依次至多为 $3/2,6/5,2/3$。剩余 $u=0,v=1$ 时逐项为

$$
\begin{array}{c|cccc}
s&0&1&2&\ge3\\ \hline
L(e)/e&\le4/3&\le2&\le1&\le1 .
\end{array}
$$

$s=2$ 使用 $L(4)=6$ 与 $4\mid L(q^b)$ 的公因子至少为 $2$，所以未经约分的 $(3/2)(4/3)=2$ 再除以 $2$；$s\ge3$ 则 $(3/4)(4/3)\le1$ 已足够。因此只有 $s=1$ 一格可能使 $L(e)>3e/2$，即

$$
 e=2\cdot5^c p^a,\qquad p\equiv3\pmod4,\quad (5/p)=-1.
\tag{21.6}
$$

在 (21.6) 且 $L(e)>3e/2$ 的情形，局部界给

$$
L(e)\mid U:=3\cdot5^c p^{a-1}(p+1)=C_e,\qquad U/e=\frac32(1+1/p)\le2.
$$

若 $L(e)$ 是 $U$ 的真因子，则 $L(e)\le U/2\le e$，和 $L(e)>3e/2$ 矛盾；故 $L(e)=U=C_e$。又 $\eta=\overline{z^{-1}}/z^{-1}\in\mathcal B_e$，两者同阶，故 $\langle\eta\rangle=\mathcal B_e\subseteq H_e$。由定理 20.1 的无分裂稳定子构造，$b(e)=h(e)\le4L(e)\le8e$。其余情形由 $b(e)\le8L(e)\le12e$ 得到结论。

综上

$$
\boxed{b(e)\le12e\quad(e\ge2).}
\tag{21.7}
$$

在已有精确解码合同 $q_\Gamma(d,e)=d^2b(e)$ 下，立即有

$$
q_\Gamma(d,e)\le12d^2e.
\tag{21.8}
$$

这只是普通算术上界，不是 $12$ 的最优性结论。

**命题 21.2（同一标签达到的下界族）。** 对任意 $a\ge1$，取 $e=118\cdot5^a=2\cdot59\cdot5^a$。其周期、群阶和最大轨道满足

$$
T_e=348\cdot5^a,\qquad h_e=696\cdot5^a,\qquad b_e=1392\cdot5^a=\frac{696}{59}e.
\tag{21.9}
$$

证明。取实际标签 $v_a=(1,y)$，其中

$$
 y\equiv0\pmod{2\cdot5^a},\qquad y\equiv26\pmod{59}.
$$

模 $59$ 的两个根为 $25,33$，其和、积均为 $-1$。由 Fermat 定理，$25^{29}=5^{58}=1$；$29$ 是素数且 $25\ne1$，故其阶恰为 $29$。$33=-25^{-1}$ 的两个因子阶互素，故阶为 $58$。特征向量 $(1,26),(1,34)$ 的行列式为 $8\ne0\pmod{59}$，给出特征基，故 $T(59)=58$；$25$ 的奇阶同时排除 $-I\in\langle g\rangle$ 模 $59$，也排除全局包含。因此 $h_e=2T_e$，而 (21.2) 给 $T_e=\operatorname{lcm}(3,4\cdot5^a,58)=348\cdot5^a$。特征轴由 $(1,26)$、$(1,34)$ 给出，且 $j$ 交换两轴。若同一个 $\varepsilon g^k$ 固定 $v_a$，模 $59$ 先强制 $\varepsilon=1$、$29\mid k$；模 $2$ 与模 $5^a$ 的标签均为 $(1,0)$，而 $\det[(1,0),g(1,0)]=1$，两者是基；$g^k$ 固定第一向量且与 $g$ 交换，便同时固定第二向量，故分别强制 $3\mid k$、$4\cdot5^a\mid k$。于是 $N_e$ 稳定子平凡，且 $jv_a\notin N_ev_a$，从而 $|\Gamma_ev_a|=2h_e$。同一符号、同一指数完成 CRT 共同实现。$\square$

$a=1$ 时可取 $e=590$、$v=(1,380)$；此时 $b(590)=6960$，而 $8e=4720$。标签虽本原，

$$
\det[v,gv]=1+380-380^2\equiv-59\pmod{590}
$$

不是单位，故它不是 cyclic 标签；这说明非循环标签也能达到全局最大轨道。由此

$$
\boxed{\frac{696}{59}\le\sup_{e\ge2}\frac{b(e)}e\le12.}
\tag{21.10}
$$

对受限族 $e=6\cdot5^a$，$M^4=-I\pmod3$ 给 $T(3)=8$，所以 $T(e)=24\cdot5^a$。若全局 $g^k=-I$，模 $3$ 要求 $k\equiv4\pmod8$，模 $5^a$ 要求 $k\equiv2\cdot5^a\pmod{4\cdot5^a}$，两者的模 $4$ 条件冲突。于是 $h(e)=2T(e)=48\cdot5^a$，而 $C_e=3\cdot4\cdot5^a$、$\iota_e=4$ 且无分裂因子；(20.1) 给 $b(e)=h(e)=8e$。这只是受限族，(21.9) 已排除统一 $8e$ 上界。(21.10) 不证明上确界为 $12$，也不使用无界的最大周期素数供应假设。

## 22. 有限调用的实际效果张成

固定 $d=e=2$。令 $S_N$ 为每条分支至多调用 $N$ 次固定 $W=W(\Delta)$、允许任意有限低层仪器、有限经典记录和自适应控制所得实际事件效果的复线性张成，令 $S_\infty=\bigcup_{N\ge0}S_N$。把低层端的免费操作写成 $K$，并令

$$
T_N=\{X\in\mathcal B(H):I_A\otimes X\in S_N\},\qquad T_\infty=\bigcup_{N\ge0}T_N.
$$

**命题 22.1（实际效果的有限饱和）。** 对实际事件效果 $E$ 及任意低层矩阵 $K$，选 $\varepsilon>0$ 使 $\varepsilon K$ 为收缩；前置 Kraus 分支 $\varepsilon K$、$\sqrt{I-\varepsilon^2K^\dagger K}$ 并记录第一分支，得到实际联合事件效果 $\varepsilon^2K^\dagger EK$，调用预算不变。对 $E$ 的有限复线性组合延拓，故 $K^\dagger EK\in S_N$。极化恒等式

$$
A^\dagger EB=\frac14\sum_{r=0}^3i^{-r}(A+i^rB)^\dagger E(A+i^rB)
$$

给出任意左右低层矩阵作用。若 $E_{ab}$ 是 $E\in S_N$ 的高层矩阵角，用低层矩阵单位夹取并复制到所有低层对角，

$$
\sum_r(|r\rangle\langle a|\otimes I)E(|b\rangle\langle r|\otimes I)
=I_A\otimes E_{ab}\in S_N.
$$

反之，对 $I_A\otimes X$ 左乘矩阵单位得每个 $|a\rangle\langle b|\otimes X$。零调用协议仅作用于 $A$，任意低层终端效果又张成全矩阵空间。因此

$$
S_N=\mathcal B(\mathbb C^4)\otimes T_N,\qquad T_0=\operatorname{span}\{I_H\},\qquad\dim T_0=1.
\tag{22.1}
$$

将一个至多 $N+1$ 次调用的有限协议树在第一次 $W$ 调用处切开。每个经典前缀的低层完全正映射有有限 Kraus 和 $\sum_rK_r(\cdot)K_r^\dagger$；第一次调用后的尾协议效果属于 $S_N$。因而精确递推为

$$
\boxed{
S_{N+1}=\operatorname{span}\left(S_N\cup
\{K^\dagger W^\dagger EWK:E\in S_N,\ K\in\mathcal B(A)\}\right).}
\tag{22.2}
$$

反向包含由“先执行一个缩放的 $K$ 分支、调用一次 $W$、再执行尾协议”实现；正向包含由第一次调用前的所有有限前缀 Kraus 和得到。停止分支已包含在 $S_0$ 中；整个证明只使用经典 continue/stopped 记录，不引入相干控制。

尚未调用就停止的前缀只贡献低层效果；未被记录的 Kraus 指标只用于计算有限完全正和，不被当作可访问记录。若 $S_N=S_{N+1}$，递推立即给出 $S_{N+2}=S_{N+1}$，所以平台永久保持。每个有限协议有有限最坏调用数，而 $S_N$ 递增，故其并为最终线性空间 $S_\infty$。若 $r=\dim_\mathbb C T_\infty<\infty$，每次尚未达到 $T_\infty$ 的递推都至少增加一维；从一维出发，$r-1$ 次增长必已达到最终维数，故

$$
\boxed{S_{r-1}=S_\infty.}
\tag{22.3}
$$

定理 14.1 的实际效果分类给出

$$
\dim T_\infty=\begin{cases}
1,&\Delta\equiv0\pmod{2\pi},\\
4,&\Delta\equiv\pm2\pi/3\pmod{2\pi},\\
10,&\text{其余 }\Delta.
\end{cases}
$$

因此 $0,3,9$ 分别是达到最终实际效果空间的充分调用上界，而非最优性断言。其相应的高层上界必须分别由三件不同事实给出：$W=I$ 时整个高层保持恒等；在 $\pm2\pi/3$ 共振时每个 Fourier 单点子空间不变，故效果为 Fourier 对角；非共振时完整的零轨道与三维非零轨道投影保持，故上界为

$$
\mathcal B(\mathbb C^4)\otimes(\mathbb C\oplus\mathcal B(\mathbb C^3)).
$$

不能仅以“轨道投影不变”替代中间共振的逐单点不变性。

若 $S_\infty$ 中两态效果不同，(22.3) 把相应效果写成有限个真实事件效果的复线性组合；若每个这些事件概率相同便矛盾，所以存在一个真实有限事件给出非零概率差。这个差没有正的统一下界，也不推出完美区分。调用数只计 $W$；仪器数、记录数、展开系数精度和控制参数精度不由此界控制。协议中的仪器和线性展开系数可以依赖已知的 $\Delta$；不要求统一一套控制序列和有界系数同时覆盖所有时钟。

对任意有限可访问辅助 $B$，允许仪器作用于 $AB$、时钟作用于 $AH\otimes I_B$。相同的缩放、极化和第一次调用切分给 $S_N^{AB}=\mathcal B(AB)\otimes T_N^{AB}$，且 $\dim T_0^{AB}=1$。三种上界分别由 $W=I$、Fourier 单点不变、轨道投影不变给出；原 $A$ 协议张量 $I_B$ 后，再用免费的 $AB$ 双模作用填满 $\mathcal B(AB)$，给最终空间的反向包含。因此 $\dim T_\infty^{AB}$ 仍分别为 $1,4,10$，同一递推证明 $0,3,9$ 的充分界与 $\dim B$ 无关。此处并不把 $S_N$ 假设成对一般乘法封闭的代数。

## 23. 有界调用的共振稳定性与四维端口

本节固定标准 $d=e=2$ 模型，$A,H$ 均为四维，$W_t=e^{-itL}$、$\operatorname{spec}L\subseteq\{0,1,3,4\}$。实际时钟始终为 $\Delta>0$；共振用模 $2\pi$ 的代表 $\Delta_*\in\{0,2\pi/3,-2\pi/3\}$ 表示，并写 $\Delta\equiv\Delta_*+\delta\pmod{2\pi}$。负代表不表示负时间原语。定义

$$
\eta(\delta)=
\begin{cases}
\sin(2|\delta|),&|\delta|\le\pi/4,\\
1,&|\delta|>\pi/4.
\end{cases}
$$

**定理 23.1（同一输入与共振不可分输入的界）。** 对任意参考扩张，单调用酉通道满足

$$
\frac12\|\mathsf W_\Delta-\mathsf W_{\Delta_*}\|_\diamond
\le\eta(\delta)\le\min\{1,2|\delta|\}.
\tag{23.1}
$$

固定任一有限自适应协议的全部控制规则，且每条分支的调用次数至多 $N$，则同一输入的实际与共振可访问输出之差至多 $\min\{1,N\eta(\delta)\}$。若两输入在共振版本下的可访问输出相同，则任一实际事件满足

$$
|p_+(E)-p_-(E)|\le\min\{1,2N\eta(\delta)\}
\le\min\{1,4N|\delta|\}.
\tag{23.2}
$$

证明。中心化 $K=L-2I$ 后 $\operatorname{spec}K\subseteq[-2,2]$。对任意纯态输入及参考，两个纯态输出重叠的模等于 $|\langle\xi|e^{-i\delta K}\otimes I|\xi\rangle|$；若 $|\delta|\le\pi/4$，其实部至少为 $\cos(2|\delta|)\ge0$，故纯态迹距离至多 $\sin(2|\delta|)$。纯化和偏迹收缩给任意混合态及参考的界，即 (23.1)；大角度用通用界 $1$，线性界用 $\sin u\le u$（或 $\|e^{-i\delta K}-I\|\le2|\delta|$）。

把经典记录全部保留，使仪器与控制规则成为 CPTP 中间映射。按调用槽逐个替换 $W_\Delta$ 为 $W_{\Delta_*}$，每个混合项的半 diamond 距离至多 $\eta$，合计至多 $N\eta$。早停用实际经典 continue/stopped 标志填满 $N$ 槽：继续的直和块调用时钟，停止的块作相同演化。对经典块对角输入，每槽仍至多 $\eta$；亦可先对标志退相干后定义整个 CPTP 槽。这不允许相干控制查询。最后丢弃 $H$、保留允许输出不会增距。两输入的共振输出相同，三角不等式的两条混合边给 (23.2)。控制规则可依赖已知 $\delta$，但在每次混合比较中固定。$\square$

例如采用标准 Fourier 基，取任意不同非零标签 $p,q$，令

$$
|\psi_\pm\rangle=\frac{|p\rangle\pm|q\rangle}{\sqrt2},\qquad
\rho_\pm=\tau_{ABR}\otimes|\psi_\pm\rangle\langle\psi_\pm|_H,
\tag{23.3}
$$

其中 $\tau_{ABR}$ 是任意共同态。$B$ 是有限可访问辅助，低层仪器可作用于 $AB$；$R$ 是从不触碰的外部参考。零共振只能读取共同的 $ABR$ 边缘，非零共振时所有分支按 Fourier 单点块对角，(23.3) 的对角条件矩阵相同，故所有共振输出相同。这里未允许给两输入另配能直接显示正负标签的不同参考扩张。

**定理 23.2（完全输出合同与四维重构）。** 对每个有限 $B$ 及每个上述至多 $N$ 调用协议 $P$，令 $\Phi_{\Delta,B}^P$ 是从 $AHB$ 到最终低层、保留的 $B$ 和全部经典记录的 CPTP 通道，输出丢弃 $H$。重构只作用于 $AH$，不接触受保护的 $B,R$。存在一个共同输入无关重构 $\mathcal R_*$，经 $q=4$ 量子端口和有限免费经典 flags 实现，使

$$
\frac12\left\|\Phi_{\Delta,B}^P-
\Phi_{\Delta,B}^P\circ(\mathcal R_*\otimes\operatorname{id}_B)\right\|_\diamond
\le\epsilon_N:=\min\{1,2N\eta(\delta)\}.
\tag{23.4}
$$

该式对所有 $AHBR$ 纠缠输入成立，且对全部 $\le N$ 历史使用同一个编解码器；$N=0$ 包含在内。

证明。非零共振取

$$
\mathcal R_*(\rho)=
\sum_{p\in\mathbb F_2^2}(I_A\otimes|p\rangle\langle p|)\rho
(I_A\otimes|p\rangle\langle p|);
$$

零共振取 $\mathcal R_*(\rho)=\operatorname{Tr}_H\rho\otimes|h_0\rangle\langle h_0|$，其中 $h_0$ 固定。在非零共振，每条完全正分支均按 $H$ 的 Fourier 单点块对角；演化后对 $H$ 取迹删除所有块间项，因此任意输入包括与 $BR$ 纠缠的输入只通过初始对角条件算子影响可访问输出。零共振没有 $AH$ 耦合，故只通过初始 $ABR$ 边缘影响输出。于是完整通道恒等式为

$$
\Phi_{\Delta_*,B}^P
=\Phi_{\Delta_*,B}^P\circ(\mathcal R_*\otimes\operatorname{id}_B).
\tag{23.5}
$$

用 (23.5) 插入 (23.4) 的两通道之间，两条混合边分别至多 $N\eta$；第二条还使用预合成 CPTP 重构的 diamond 收缩。这证明 (23.4)。它是丢弃 $H$ 的输出恒等式及近似，一般不是保留全 $AHBR$ 输出的等式。

非零共振的编码测出 Fourier 标签，把对应低层条件态存入四维量子端口，标签存入四值经典 flag；解码把低层态和该 Fourier 基态重新组合。其定义在全部带 flag 的量子记忆态上 CPTP。零共振仅存低层态并附回固定 $H$，不需要 flag。编解码器可为任意 CPTP 状态编码，不要求属于低层实验仪器；特别未将其 Fourier 测量增加为实验原语。所有量子信息只通过该端口，$B,R$ 不得由编解码器用作存储旁路。$\square$

**推论 23.3（事件参考态、条件精度与四维必要性）。** 对 (23.4) 比较中的事件，令 $\omega,\omega'$ 为保留下来的次归一化参考态，$p=\operatorname{Tr}\omega$、$p'=\operatorname{Tr}\omega'$。将失败输出替换为同一正交标志，迹距离收缩给

$$
\frac12\|\omega-\omega'\|_1+\frac12|p-p'|\le\epsilon_N.
\tag{23.6}
$$

若两成功概率均至少为 $s>0$，则

$$
\frac12\|\omega/p-\omega'/p'\|_1
\le\min\{1,\epsilon_N/s\}.
\tag{23.7}
$$

证明。成功与失败的输出态为 $\omega\oplus(1-p)|\mathrm f\rangle\langle\mathrm f|$ 及其带撇版本，迹范数在直和上相加即得 (23.6)。若 $p\ge p'>0$，三角不等式给归一化距离至多
$[\|\omega-\omega'\|_1/2+(p-p')/2]/p$；对换两者给分母 $\max(p,p')$。故 (23.7) 没有额外因子 $2$，且缺少成功概率下界时不保证条件态的统一精度。

进一步，采用同一个共同 CPTP 编解码器、有限免费 flags、无额外量子通信或预共享纠缠的参考保持合同。令受保护可访问 $B$ 为四维，取 $AB$ 的归一化 Bell 态及固定纯 $H$；零调用后联合测量 $AB$ 的 Bell 投影是允许的低层加辅助测试。先固定 $H$，再编解码并丢弃输出 $H$，得到 $A$ 上的通道。把带 flag 的编码 Kraus 与对应解码 Kraus 合成，所有 $K:\mathbb C^4\to\mathbb C^4$ 都满足 $\operatorname{rank}K\le q$，且 $\sum_K\operatorname{Tr}(K^\dagger K)=4$。于是重构后 Bell 投影概率

$$
F=\frac1{16}\sum_K|\operatorname{Tr}K|^2
\le\frac q{16}\sum_K\operatorname{Tr}(K^\dagger K)=\frac q4,
$$

其中 $|\operatorname{Tr}K|\le\|K\|_1\le\sqrt{\operatorname{rank}K}\|K\|_2$。原概率为 $1$，故对 $q\le4$，

$$
\epsilon\ge1-q/4.
\tag{23.8}
$$

任何包括零调用的统一误差合同若要求 $\epsilon<1/4$，必有整数 $q\ge4$。在 $\epsilon_N<1/4$ 的区域，定理 23.2 的四维方案因此达到量子端口维数最优；没有断言其误差本身最优。该下界要求受保护参考与允许的联合终端测试，不是未扩展输入统计的下界，也不是物理存储定律。$\square$

## 24. 一次调用的相干信号与已知失谐的固定信号

固定第 23 节的标准模四模型，令 $U=U_{M,4}$、$V=U_{M,2}$。本节 $V$ 只指高层置换。使用 canonical Fourier 基

$$
|p\rangle=\frac12\sum_{h\in\mathbb F_2^2}(-1)^{p\cdot h}|h\rangle,
\qquad V|p\rangle=|gp\rangle .
\tag{24.1}
$$

三个非零 Fourier 标签记作 $\alpha=10,\beta=11,\gamma=01$，$g$ 按 $\alpha\to\beta\to\gamma\to\alpha$ 循环。低层基用二进制串表示，不混用这些字母。输入为

$$
\rho_\pm=|10\rangle\langle10|_A\otimes
|\psi_\pm\rangle\langle\psi_\pm|,\qquad
|\psi_\pm\rangle=\frac{|p\rangle\pm|q\rangle}{\sqrt2}
$$

（任选不同非零 $p,q$）。定义标量函数，与子系统名称分开理解，

$$
x=e^{-it},\qquad A(t)=\frac{1+2x^3}{3},\quad
B(t)=\frac{x(2+x^3)}3,\quad C(t)=\frac{1-x^3}{3}.
\tag{24.2}
$$

下面公式省略这些标量的自变量。准备低层 $|10\rangle$，作一次 $W_t$，再测两结果低层投影，其中指定成功向量为

$$
|r_\phi\rangle=\frac{|10\rangle+e^{i\phi}|11\rangle}{\sqrt2}.
$$

**命题 24.1（两个固定相位的实际分布）。** 将无序对唯一定向为 $p=g^2q$，置 $d_\alpha=A$、$d_\beta=d_\gamma=B$，$f_\alpha=1$、$f_\beta=f_\gamma=-x$ 和 $Z=C\overline{d_p}f_q$。则

$$
p_{\pm,\phi}(t)=\frac{7+2\cos3t}{18}
\pm\frac12\operatorname{Re}(e^{-i\phi}Z),\qquad
D_\phi:=p_{+,\phi}-p_{-,\phi}=\operatorname{Re}(e^{-i\phi}Z).
\tag{24.3}
$$

证明。由 $M^3=I+2M$，$U^6=I$ 且 $U^3=\sum_a|a\rangle\langle a|\otimes T_{Ma}$。令全空间投影 $P_\pm=(I\pm U^3)/2$，在六次单位根上分别求值，或直接用 (14.2)，得

$$
W_t=(AP_++BP_-)+CU(P_++xP_-)+CU^2(P_+-xP_-).
\tag{24.4}
$$

$P_+$ 上的谱为 $L=0,3$，$P_-$ 上为 $L=1,4$，故此式是精确谱恒等式。低层从 $10$ 的前两次步进均无 carry，$M10=01$、$M^2 10=11$。令 $\Pi_\pm=(I\pm T_{01})/2$，则两个所需低层角为

$$
(W_t)_{10,10}=D_H:=A\Pi_++B\Pi_-,
\qquad
(W_t)_{11,10}=CV^2F_H,\quad F_H=\Pi_+-x\Pi_- .
$$

实际事件的高层 Kraus 为 $K_\phi=(D_H+e^{-i\phi}CV^2F_H)/\sqrt2$。在非零标签 $\alpha,\beta,\gamma$ 上，$T_{01}$ 的字符依次为 $+1,-1,-1$，即给所列 $d,f$；$V^2$ 无固定非零标签，且 $|A|^2=|B|^2=(5+4\cos3t)/9$、$|f_p|=1$。于是效果 $K_\phi^\dagger K_\phi$ 的三个对角元均为 $(|A|^2+|C|^2)/2=(7+2\cos3t)/18$，$(p,q)$ 非对角元为 $e^{-i\phi}C\overline{d_p}f_q/2$，给出 (24.3)。零 Fourier 标签不在这项对角元断言中。$\square$

三对的具体式为

$$
\begin{array}{c|c|c}
\{p,q\}&(p,q)&Z\\ \hline
\{\alpha,\gamma\}&(\gamma,\alpha)&
C\overline B=(x^{-1}+x^{-4}-2x^2)/9\\
\{\alpha,\beta\}&(\alpha,\beta)&
-xC\overline A=(x-2x^{-2}+x^4)/9\\
\{\beta,\gamma\}&(\beta,\gamma)&
-xC\overline B=(-1-x^{-3}+2x^3)/9 .
\end{array}
\tag{24.5}
$$

对实读出 $\phi=0$，前两对的差为 $(\cos t+\cos4t-2\cos2t)/9$，后一对为 $(\cos3t-1)/9$。前式令 $u=\cos t$ 后其九倍等于 $(u-1)(2u+1)(4u^2+2u-3)$，故另有非共振零点 $u=(\sqrt{13}-1)/4$；实读出单设置不足以普遍见证所有对和所有非共振时钟。

公平随机选 $\phi=0,\pi/2$ 并同时保留设置与二结果记录。每设置的两个联合概率差为 $D_\phi/2,-D_\phi/2$，所以联合分布的总变差精确为

$$
\operatorname{TV}(P_+,P_-)
=\frac{|\operatorname{Re}Z|+|\operatorname{Im}Z|}{2},\qquad
\frac{|Z|}{2}\le\operatorname{TV}\le\frac{|Z|}{\sqrt2}.
\tag{24.6}
$$

由 $|f_q|=1$、$|A|=|B|$，

$$
|Z|^2=\frac{(2-2\cos3t)(5+4\cos3t)}{81}.
\tag{24.7}
$$

第二因子至少为 $1$，故非共振时 $|Z|>0$。写 $t=\Delta_*+\delta$，则
$|Z|=(2/3)|\sin(3\delta/2)|\,|A|$，且 $1/3\le|A|\le1$。对 $|\delta|\le\pi/3$，用正弦弦界及 $|\sin y|\le|y|$ 得
$2|\delta|/(3\pi)\le|Z|\le|\delta|$，因而

$$
\frac{|\delta|}{3\pi}\le\operatorname{TV}\le\frac{|\delta|}{\sqrt2}.
\tag{24.8}
$$

这是本输入对的一次调用见证和一致的 $\Theta(|\delta|)$ 信号，不替代面对任意输入差的 $S_9$ 张成定理。TV 为非负分布距离；选出实现 TV 的单一联合事件需要依差值符号选择记录集合，不能把保留记录的 TV 当成丢弃设置后的无条件有符号差。重定 Fourier 基相位时必须同时运输物理输入系数；若重新用等实系数定义 $\psi_\pm$ 则一般改变了物理态。

**命题 24.2（$\pi$ 读出与固定差 $1/9$）。** 对同一输入对，已知失谐 $0<|\delta|\le1/54$ 时，达到事件差至少 $1/9$ 的最少最坏分支调用数 $Q_{\min}(\delta;p,q)$ 满足

$$
\frac1{36|\delta|}\le Q_{\min}(\delta;p,q)
\le n_\delta
:=3\left\lfloor\frac{\pi}{3|\delta|}+\frac12\right\rfloor
\le\frac\pi{|\delta|}+\frac32.
\tag{24.9}
$$

证明。在 $U$ 的六次单位根谱上逐点求值，得

$$
W_\pi=-I/3+2(U^2+U^4)/3.
$$

$U^2$ 的 $10\to11$ 路径无 carry，而 $U^4$ 的低层终点为 $01$，所以所需两个角恰为

$$
(W_\pi)_{10,10}=-I_H/3,\qquad
(W_\pi)_{11,10}=2V^2/3.
$$

取实读出 $r_0$，实际高层 Kraus 及效果为

$$
K_0=\frac{-I+2V^2}{3\sqrt2},\qquad
K_0^\dagger K_0=\frac{5I-2(V+V^2)}{18}.
$$

$V+V^2$ 在非零标签基上对角为零、全部非对角为 $1$，在 $\psi_\pm$ 上期望为 $\pm1$。因此实际未条件化概率为

$$
p_+(\pi)=1/6,\qquad p_-(\pi)=7/18,\qquad
p_-(\pi)-p_+(\pi)=2/9,
\tag{24.10}
$$

即约定 $D=p_+-p_-$ 下 $D(\pi)=-2/9$。

$n_\delta$ 为正的三倍整数，最近整数界给
$\bigl|n_\delta|\delta|-\pi\bigr|\le3|\delta|/2$。置
$h=\operatorname{sgn}(\delta)(n_\delta|\delta|-\pi)$，
则 $n_\delta\Delta_*\in2\pi\mathbb Z$ 且

$$
W_\Delta^{n_\delta}=W_{\pi+h},\qquad |h|\le3|\delta|/2.
$$

$\delta<0$ 时使用 $-\pi\equiv\pi\pmod{2\pi}$，仍只作正向原始调用。实际连续调用 $n_\delta$ 次，中间作恒等控制，再测 $r_0$。由中心化谱给每个输入的事件变化至多 $2|h|$，两输入的有符号差故至少
$2/9-4|h|\ge2/9-6|\delta|\ge1/9$。下界对任意允许自适应协议由 (23.2) 给 $1/9\le4N|\delta|$。$\square$

若初始低层为任意共同 $\tau$，可先用低层 CPTP 重置为 $|10\rangle$，不增加时钟调用；对 (23.3) 的共同辅助扩张同样适用。已知 $\delta$ 的固定差任务因此具有 $\Theta(1/|\delta|)$ 调用复杂度，一致于三个共振与全部不同非零标签对。这不计最优常数、重复 shot 数、参数取得及控制精度，也不表示完美区分。九次张成给每个非共振的非零见证，但 (23.2) 把其幅度压在 $36|\delta|$ 内；代数存在性与统一正信号是不同量词的结论。

## 25. 未知失谐的随机正调用读出

继续使用第 24 节的输入与 Fourier 约定，已知区间

$$
0<\delta_{\min}\le|\delta|\le\delta_{\max}\le1/54,\qquad
\Delta>0,\quad\Delta\equiv\Delta_*+\delta\pmod{2\pi}.
$$

实际 $\delta$、符号及共振代表均可未知。每次实验只使用一份输入，随机选择整数个正向 $W_\Delta$ 调用，并使用免费低层操作与有限经典记录。

**命题 25.1（对所有时间同号的匹配设置）。** 令 $f(a)=Ma\bmod2$，标准两步 carry 由 $M^2a=f^2(a)+2c_2(a)$ 定义。对已知的无序非零标签对，从下表取一行：用低层置换把初始 $10$ 送到 $a$，最终测量向量 $r_a=(|a\rangle+s|f^2(a)\rangle)/\sqrt2$。

$$
\begin{array}{c|c|c|c|c|c}
\{p,q\}&a&Ma\bmod2&f^2(a)&c_2(a)&s\\ \hline
\{01,11\}&10&01&11&00&+1\\
\{10,01\}&01&11&10&01&-1\\
\{10,11\}&11&10&01&11&-1
\end{array}
\tag{25.1}
$$

匹配事件对全部实数 $t$ 满足

$$
p_-(r_a;t)-p_+(r_a;t)=d(t):=\frac{1-\cos3t}{9}\ge0.
\tag{25.2}
$$

证明。由 (24.4)，记 $\Pi_{a,\pm}=(I\pm T_{Ma})/2$，实际矩阵角为

$$
D_a=(W_t)_{a,a}=A\Pi_{a,+}+B\Pi_{a,-},\qquad
(W_t)_{f^2(a),a}
=C\,T_{c_2(a)}V^2(\Pi_{a,+}-x\Pi_{a,-}).
\tag{25.3}
$$

每行所选两个标签均满足 $p\cdot Ma=q\cdot Ma=1$，所以对角值都为 $B$，最后括号的值都为 $-x$。把边定向为 $u\to v=g^2u$，其 carry 相位为 $\chi_v(c_2(a))=(-1)^{v\cdot c_2(a)}$；逐行正是 $s=+1,-1,-1$。实际 Kraus 为两角的 $(1,s)/\sqrt2$ 组合，其效果 $(v,u)$ 非对角元为 $-s\chi_v(c_2(a))xC\overline B/2$。$\rho_--\rho_+$ 的高层部分为 $-|u\rangle\langle v|-|v\rangle\langle u|$，故差为
$\operatorname{Re}(xC\overline B)=(1-\cos3t)/9$，其中
$xC\overline B=(1+x^{-3}-2x^3)/9$。$\square$

**定理 25.2（已知标签对、未知失谐）。** 以匹配设置取

$$
Q_0=\left\lceil\frac{2\pi}{3\delta_{\min}}\right\rceil,
$$

独立均匀抽取 $n\in\{1,\ldots,Q_0\}$，连续调用 $n$ 次 $W_\Delta$ 后作该低层测量。最终事件是对所有 $n$ 的成功读出取并，记录可以全部保留。则

$$
p_-(E)-p_+(E)\ge1/18,\qquad
N_{\max}=Q_0\le\frac{2\pi}{3\delta_{\min}}+1.
\tag{25.4}
$$

证明。$3\Delta_*\in2\pi\mathbb Z$，所以未条件化差为
$[1-Q_0^{-1}\sum_{n=1}^{Q_0}\cos(3n\delta)]/9$，每分支的差均非负。对 $J\ge1$、$\theta\notin2\pi\mathbb Z$，有限几何级数给

$$
\left|\frac1J\sum_{n=1}^Je^{in\theta}\right|
=\frac{|\sin(J\theta/2)|}{J|\sin(\theta/2)|}
\le\frac1{J|\sin(\theta/2)|}.
\tag{25.5}
$$

在此区间 $|\sin(3\delta/2)|\ge3|\delta|/\pi\ge3\delta_{\min}/\pi$，故平均余弦的绝对值至多 $\pi/(3Q_0\delta_{\min})\le1/2$，给 (25.4)。调度只用 $\delta_{\min}$，设置只用已知标签对。$\square$

**定理 25.3（标签对也未知）。** 独立均匀选 (25.1) 的一行，并均匀抽取 $m\in\{1,\ldots,Q\}$，其中

$$
Q=\left\lceil\frac{29\pi}{9\delta_{\min}}\right\rceil .
$$

连续调用 $n=3m$ 次，最后按该行读出，指定事件仍是各抽样分支的成功读出之并。则对全部不同非零标签对和全部允许失谐，

$$
p_-(E)-p_+(E)\ge1/54,\qquad
N_{\max}=3Q\le\frac{29\pi}{3\delta_{\min}}+3.
\tag{25.6}
$$

证明。令 $f_0(t)=(2\cos2t-\cos t-\cos4t)/9$，避免与低层置换 $f$ 混用。由 (25.3) 计算全部有符号差得

$$
\begin{array}{c|ccc}
\text{设置 }(a,s)&\{01,11\}&\{10,01\}&\{10,11\}\\ \hline
(10,+1)&d(t)&f_0(t)&f_0(t)\\
(01,-1)&f_0(t)&d(t)&-f_0(t)\\
(11,-1)&-f_0(t)&f_0(t)&d(t)
\end{array}
\tag{25.7}
$$

确实，对有向边 $u\to v=g^2u$，一般事件差为
$-s\chi_v(c_2(a))\operatorname{Re}(C\overline{d_v}f_u)$，其中 $d_v$ 是 $D_a$ 的值，$f_u$ 是 $\Pi_{a,+}-x\Pi_{a,-}$ 的值。若两字符均为负就得匹配项 (25.2)；若字符不同，则
$-\operatorname{Re}(C\overline B)=\operatorname{Re}(xC\overline A)=f_0(t)$，再乘该行的 $s\chi_v$ 即得全部六个不匹配项。这样每个负项的来源由实际 carry 与测量符号确定。

均匀混合设置后，第一和第三列为 $d(t)/3$；中间列为

$$
\frac{d(t)+2f_0(t)}3
=\frac{1-\cos3t+4\cos2t-2\cos t-2\cos4t}{27}.
\tag{25.8}
$$

$n=3m$ 使 $t=n\Delta\equiv3m\delta\pmod{2\pi}$，消去全部共振相位。对 $k=1,2,3,4$，$3k|\delta|/2\le1/9<\pi/2$；(25.5) 和正弦弦界给

$$
\left|\frac1Q\sum_{m=1}^Q\cos(3km\delta)\right|
\le\frac{\pi}{3Qk\delta_{\min}}.
$$

所以 (25.8) 的平均至少为

$$
\frac1{27}\left[
1-\frac{\pi}{3Q\delta_{\min}}
\left(\frac13+\frac42+\frac21+\frac24\right)\right]
=\frac1{27}\left(1-\frac{29\pi}{18Q\delta_{\min}}\right)
\ge\frac1{54}.
$$

另外两列的平均为 $[1-\operatorname{avg}\cos(9m\delta)]/27$，其余弦绝对值至多 $\pi/(9Q\delta_{\min})\le1/29<1/2$，也满足同一下界。这控制了不匹配分支的总抵消，而不是从某一好分支的存在推出混合结论。$\square$

两协议均不估计实际失谐，不调用逆时钟或测量高层；没有对抽样或成功分支作归一化后选择。对整个区间的统一固定差任务，(23.2) 在允许端点 $|\delta|=\delta_{\min}$ 分别给

$$
N\ge\frac1{72\delta_{\min}}\quad\text{及}\quad
N\ge\frac1{216\delta_{\min}}.
$$

结合 (25.4)、(25.6)，两个任务的最坏调用复杂度均为 $\Theta(1/\delta_{\min})$。达到的固定差分别为 $1/18$、$1/54$，不宣称未知失谐时的差 $1/9$、最佳常数、shot 或精度成本。若允许 $|\delta|$ 任意趋于零而没有正的 $\delta_{\min}$，(23.2) 使每个固定最坏调用预算的所有事件差趋于零，故不能保证统一正信号。

## 26. 逆失谐预算下的十二维端口下界

令 $X=A\otimes H$，$\dim A=\dim H=4$。本节改用 $V:\mathbb C^{12}\to X$ 表示非零 Fourier 轨道块的固定等距嵌入，不再指第 24 节的高层置换。令 $B\simeq\mathbb C^{12}$ 为受保护的可访问 Bell 伙伴：编解码器不接触它，低层协议期间它保持静止，最后允许测量它。若另取外部 diamond 参考 $R$，则 $R$ 始终不触碰。共同 CPTP 编码器、解码器经记忆代数 $\bigoplus_f\mathcal B(\mathbb C^q)$ 分解，$f$ 为任意有限免费经典 flag；没有额外量子通信、预共享纠缠或借 $B,R$ 绕过端口的存储。所有随机实验分支使用同一个编解码器，输出仅保留低层、$B$ 与记录并丢弃 $H$。

**定理 26.1（实际效果 frame 的统一端口约束）。** 存在有精确有限 frame 定义的常数 $c_0,\delta_0>0$，使对任一共振 $\Delta_*$、已知 $0<|\delta|\le\delta_0$ 和正物理时钟 $\Delta\equiv\Delta_*+\delta\pmod{2\pi}$，若上述共同编解码器对所有每分支至多

$$
N_\delta=9k,\qquad
k=3\operatorname{round}\!\left(\frac{\pi}{3|\delta|}\right),
\qquad
N_\delta\le9\left(\frac{\pi}{|\delta|}+\frac32\right)
\tag{26.1}
$$

次调用的允许实验具有统一误差 $\epsilon$，则

$$
\epsilon\ge c_0(1-q/12),\qquad1\le q\le12.
\tag{26.2}
$$

误差可为第 23 节的可访问输出半 diamond 距离，也可为包括全部 $XB$ 纠缠输入与终端 $B$ 测试的实际事件概率误差；后者已经足够。该断言不适用于未扩展输入的较弱统计。

证明。在 $t=\pi$，第 22 节给真实至多九次调用事件效果的复张成为

$$
S_9(\pi)=\mathcal A_{\mathrm{orb}}
=\mathcal B(\mathbb C^4)\oplus\mathcal B(\mathbb C^{12}).
$$

其 Hermitian 部分实维数为 $4^2+12^2=160$。因全部真实事件效果均为 Hermitian，从生成集中选出 $160$ 个复线性无关的正效果 $0\le F_j(\pi)\le I_X$；它们也是 Hermitian 部分的实基（对任意复展开取伴随，唯一性强制 Hermitian 元素的系数为实数）。每个 $F_j$ 配有一个实际有限协议，每分支至多九次正调用。固定这些协议的所有低层仪器、控制树和事件，只让时钟变化为 $W(t)$，得到 $F_j(t)$。

每条分支效果是有限 Kraus 与 $W(t)$ 的有限乘积之和，故 $F_j(t)$ 连续；每个轨道投影与所有低层分支及 $W(t)$ 交换，故对任意 $t$ 均有 $F_j(t)\in\mathcal A_{\mathrm{orb}}$。这正是 $\pi$ 邻域所需的上界，不用它推断较小共振代数。定义

$$
G_{j\ell}(t)=\operatorname{Tr}_X(F_j(t)F_\ell(t)),\qquad
\lambda_0=\lambda_{\min}G(\pi)>0.
$$

选择固定 $0<r<\pi/3$，使在闭区间 $|t-\pi|\le r$ 上
$\|G(t)-G(\pi)\|_{\mathrm{op}}\le\lambda_0/2$；连续性允许这样的正 $r$。于是 $\lambda_{\min}G(t)\ge\lambda_*:=\lambda_0/2>0$。令

$$
D_j(t)=\sum_\ell(G(t)^{-1})_{j\ell}F_\ell(t),
\qquad
\operatorname{Tr}_X(D_j(t)F_\ell(t))=\delta_{j\ell}.
$$

这些 Hermitian 对偶满足

$$
\|D_j(t)\|_{\mathrm{HS}}^2=(G(t)^{-1})_{jj}\le1/\lambda_*,
\qquad
\|V^\dagger D_j(t)V\|_{\mathrm{op}}\le1/\sqrt{\lambda_*}.
\tag{26.3}
$$

令 $|\Omega_V\rangle=12^{-1/2}\sum_{a=1}^{12}V|a\rangle\otimes|a\rangle_B$，$P_\Omega=|\Omega_V\rangle\langle\Omega_V|$。以固定 Bell 基取转置，定义

$$
C_j(t)=\frac{(V^\dagger D_j(t)V)^T}{12}.
$$

在整个 $X\otimes B$ 上，而不只在压缩后的轨道块上，有

$$
P_\Omega=\sum_{j=1}^{160}F_j(t)\otimes C_j(t).
\tag{26.4}
$$

确实每个 $V|a\rangle\langle b|V^\dagger$ 属于完整的 $\mathcal A_{\mathrm{orb}}$，其在 $F_j$ 基中的系数为
$\operatorname{Tr}(D_jV|a\rangle\langle b|V^\dagger)=\langle b|V^\dagger D_jV|a\rangle$。把这些展开代入
$P_\Omega=12^{-1}\sum_{a,b}V|a\rangle\langle b|V^\dagger\otimes|a\rangle\langle b|$
即得 (26.4)。完整 $160$ 维基保证另一四维块上的项正确相消为零；因此无需假设解码输出留在十二维输入块。

写 $C_j=C_j^+-C_j^-$，令
$a_j=\|C_j^+\|_{\mathrm{op}}$、$b_j=\|C_j^-\|_{\mathrm{op}}$。
对非零系数，$Q_j^+=C_j^+/a_j$、$Q_j^-=C_j^-/b_j$ 为 $B$ 上的实际二结果测量效果。先运行 $F_j$ 的低层协议，保持 $B$ 静止，再测试对应 $Q_j^\pm$，接受两事件的交，得到真实效果

$$
E_j^\pm=F_j(t)\otimes Q_j^\pm,\qquad
P_\Omega=\sum_j a_jE_j^+-\sum_j b_jE_j^- .
$$

这是真实正事件的有限带符号展开，总系数变差为

$$
0<\Gamma(t):=\sum_j(a_j+b_j)
\le\frac2{12}\sum_{j=1}^{160}\|V^\dagger D_j(t)V\|_{\mathrm{op}}
\le\frac{320}{12\sqrt{\lambda_0/2}}.
\tag{26.5}
$$

取 $\beta(t)=\sum_jb_j$。以概率 $a_j/\Gamma$ 运行 $E_j^+$ 并保留成功，以概率 $b_j/\Gamma$ 运行 $E_j^-$ 并保留其补事件，得到真正二元事件

$$
Z(t)=\frac{P_\Omega+\beta(t)I_{XB}}{\Gamma(t)}.
\tag{26.6}
$$

这些选择概率和为 $1$，故 $0\le Z(t)\le I$ 由实际凸混合直接保证。每个分支至多九次 $W(t)$ 调用，只测低层与终端 $B$，未授权任意 $AH$ Bell 测量。对任意两个归一化输入 $\rho,\sigma$，标量项严格消去，

$$
\Pr(Z(t)\mid\rho)-\Pr(Z(t)\mid\sigma)
=\operatorname{Tr}(P_\Omega(\rho-\sigma))/\Gamma(t).
\tag{26.7}
$$

设共同重构为 $\mathcal T=\mathrm{Dec}\circ\mathrm{Enc}$。编码的带 flag Kraus 为 $E_{f,\ell}:X\to\mathbb C^q$，解码为 $D_{f,j}:\mathbb C^q\to X$。作用于 Bell 输入块的复合算子
$K_{f,j,\ell}=D_{f,j}E_{f,\ell}V:\mathbb C^{12}\to X$
均秩至多 $q$，迹保持给 $\sum_K\operatorname{Tr}(K^\dagger K)=12$。重构 Bell 重叠为

$$
\begin{aligned}
F&=\operatorname{Tr}\!\left[
P_\Omega(\mathcal T\otimes\operatorname{id}_B)(P_\Omega)\right]\\
&=\frac1{12^2}\sum_K|\operatorname{Tr}(V^\dagger K)|^2
\le\frac q{12^2}\sum_K\|K\|_{\mathrm{HS}}^2
=\frac q{12}.
\end{aligned}
\tag{26.8}
$$

这里 $\operatorname{rank}(V^\dagger K)\le q$、$\|V^\dagger K\|_{\mathrm{HS}}\le\|K\|_{\mathrm{HS}}$，再用迹的核范数界。输出泄漏到另一块和任意有限 flags 都已经包含在这个计算中。原 Bell 输入重叠为 $1$，实际事件 (26.6) 的差为 $(1-F)/\Gamma(t)$，故在该 $\pi$ 邻域

$$
\epsilon\ge\frac{1-q/12}{\Gamma(t)}
\ge c_0(1-q/12),\qquad
c_0:=\frac{12\sqrt{\lambda_0/2}}{320}>0.
\tag{26.9}
$$

frame、随机分支及终端 $B$ 效果都与被检验的编解码器无关；编解码器必须对所有这些分支共同适用。

最后置 $\delta_0=\min\{\pi/3,2r/3\}$，取 (26.1) 的最近整数，平局任择一个。对 $0<|\delta|\le\delta_0$，所取整数为正，且

$$
\bigl|k|\delta|-\pi\bigr|\le3|\delta|/2,\qquad
h=\operatorname{sgn}(\delta)(k|\delta|-\pi).
$$

由于 $k$ 是 $3$ 的倍数，$k\Delta_*\in2\pi\mathbb Z$；$\delta<0$ 时 $-\pi\equiv\pi$，所以完全精确地有
$W_\Delta^k=W_{\pi+h}$，$|h|\le3|\delta|/2\le r$。把 (26.6) 协议中每一次有效时钟调用替换为 $k$ 次连续正向原始调用，即以最坏 $9k$ 次预算实现同一个实际事件。没有 inverse clock 或近似门合成。这证明 (26.1)、(26.2)；允许更大的预算当然仍含该事件。$\square$

$c_0,\delta_0$ 的定义取自固定有限实际 frame 的 $\lambda_0,r$，对三个共振一致，不含任何数值条件数或数值阈值断言。若容许误差 $\epsilon<c_0/12$，则每个整数 $q<12$ 均被排除。已有精确 $q=12$ 方案在相同扩张合同中仍充分：测出零/非零轨道的有限经典 flag，在最多十二维端口内保留该轨道的完整量子块，解码作对应嵌入；共同重构就是轨道 pinching。全部允许分支逐轨道作用，最终丢弃 $H$，所以该 pinching 保持可访问输出，包括与受保护 $B,R$ 的关联。编解码的这项状态任务不把轨道测量变成实验原语。

此处构造的是有非零统一对比度的实际随机 Bell 事件，没有构造从十二维块到可访问系统的完整量子态转移。第 23 节在小 $N|\delta|$ 时以 $q=4$ 给 $\epsilon_N\le4N|\delta|$；本节在逆失谐预算且精度 $\epsilon<c_0/12$ 时要求 $q\ge12$。调用与精度的量词决定这两个资源结论的适用区域，不给完整转变曲线、最优常数或 $q=5,\ldots,11$ 的中间分类。这些端口结论均限于所述共同 CPTP、参考保持及无额外量子通道合同，不是无条件的物理定律。

## 追加锚（本行以下为增补区）

## 27. 合法五窗字同时作为对象与单孔上下文

本节至 §38 连接三种已分别声明的结构：规范五窗来源、离散仿射操作、正的量子续接边界。首先保留来源类型，使同一个字确实具有对象解释和上下文解释；随后指定程序解释器，再将同终态地址对的相干细化接到逐分支条件充分性。沿用本卷定义 1.3 的仪器与正概率条件态，以及母卷定义 104.2、命题 149.4 的单位位、窗口方向、接缝和读出。以下有限路径不预先假定已经取得 End。

**定义 27.1（两态路径与单孔仿射解释）。** 置

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
S=M^3=\begin{pmatrix}1&2\\2&3\end{pmatrix},\qquad
F_\sigma=T_{d_\sigma}S,
$$

其中 $T_t(x)=x+t$，五窗表按低位到高位读取：

| 本章边型 | 窗口位 | $d_\sigma$ | 输入接缝 | 输出接缝 |
| --- | --- | --- | --- | --- |
| 27 · null | 000 | $(0,0)$ | 0 或 1 | 0 |
| 27 · 2 | 100 | $(1,0)$ | 0 | 0 |
| 27 · 3 | 010 | $(0,1)$ | 0 或 1 | 0 |
| 27 · 25 | 101 | $(2,1)$ | 0 | 1 |
| 27 · 5 | 001 | $(1,1)$ | 0 或 1 | 1 |

图 $Q$ 有对象 $0,1$ 和八条实际边；不同输入接缝上的同名边仍是不同边。其自由路径范畴中，$v\circ u$ 表示先读 $u$、后读 $v$，低到高串接记为 $uv$。空路径 $1_s$ 是恒等；$[\mathrm{null}]$ 是一条真实边。单位位 $\varepsilon=b_0$ 初始化 $s=\varepsilon$，不是窗口。

对 $w=\sigma_0\cdots\sigma_{n-1}:s\to t$ 定义

$$
D_w=\sum_{j=0}^{n-1}S^jd_{\sigma_j},\qquad
\Phi_w(x)=D_w+S^nx.
\tag{27.1}
$$

可以把 $x$ 视为有名字的第 $t$ 个格点副本 $V_t=\mathbb Z^2$ 中的孔；输出属于 $V_s$。同一字的对象解释为 $D_w=\Phi_w(0)$，完整来源数量为 $N=\varepsilon+(2,3)D_w$。上下文的孔接受完整的尾部组成向量，并非一个省略类型的“下一数字”。若使用非负来源，正向 $S,T_{d_\sigma}$ 都保持 $\mathbb N^2$；出现逆函数时载体另取整个有向格点或实平面。

**定理 27.2（串接、代入与读取方向）。** 对可串接路径 $u,v$，

$$
D_{uv}=D_u+S^{|u|}D_v,\qquad
\Phi_{uv}=\Phi_u\circ\Phi_v,
\qquad
D_{uv}=\Phi_u(D_v).
\tag{27.2}
$$

故路径的低到高串接与单孔上下文代入完全相容，但相对于 $v\circ u$ 的 chronological 组合约定，这是反变解释。真正低到高在线执行的协变累加器为

$$
(s,n,a)\xmapsto{\sigma}
(t,n+1,a+S^nd_\sigma),
\tag{27.3}
$$

其 guard 是表中的输入接缝要求。

证明。将 $uv$ 的求和在 $|u|$ 处切开即得第一式；把两仿射函数复合得到第二式，代入零得第三式。逐边应用 (27.3) 从 $(s,0,0)$ 得 $(t,|w|,D_w)$。通常函数复合最右边先执行，故 $\Phi_w=F_{\sigma_0}\circ\cdots\circ F_{\sigma_{n-1}}$ 的 Horner 执行顺序是高窗先做。保留 $V_t\to V_s$ 的方向，或使用目标范畴的对偶，即使反变性有正式类型；不能默默把输入字倒写而沿用原 seam 表。$\square$

例如单位位零的合法字 $89=[\mathrm{null}][\mathrm{null}][5]$ 满足

$$
D_w=S^2(1,1)=(13,21),\qquad
S^3=\begin{pmatrix}21&34\\34&55\end{pmatrix},
\qquad N=2\cdot13+3\cdot21=89.
$$

它同时给对象 $(13,21)$ 和上下文 $x\mapsto S^3x+(13,21)$。低位 null 保留位次；删去它们便只剩数量 $5$。

**命题 27.3（固定 Hom 内的忠实性）。** 裸合法路径的 $\Phi$ 在每个固定 $\operatorname{Hom}(s,t)$ 上单射。若给边增加参数而 $\Phi$ 忽略这些参数，该单射结论不再成立。

证明。$\Phi_u=\Phi_v$ 先给 $S^{|u|}=S^{|v|}$。$S$ 的特征值 $2+\sqrt5>1$ 使长度相等；代入零得到 $D_u=D_v$。两个内部合法字都可从单位位零起读，并补高位零成为有限支持的无相邻 1 序列。母卷的规范 Zeckendorf 唯一性使相同 $(2,3)D$ 的两串逐位相同；长度相等又排除了多保留整个零窗的区别。固定起态后标签逐步确定实际边，故路径相同。这也涵盖空路径和全零路径。若同一实际边带两个不同参数 $p,p'$ 而贡献仍为 $d_\sigma$，两条平行单边已具有相同仿射像，给出参数抹除的反例。$\square$

保留两个对象，以合法正路径的仿射像为全部箭头，并采用上述对偶方向，便得到与裸路径范畴同构的生成像范畴。它没有自动加入仿射逆。一般函子只保持源中已有的组合；把两个对象都送到一个几何对象后，原先不可组合的箭头也可具有可组合的像，这仍可以是函子。因此“不能反映接缝合法性”与“不是任何函子”是不同判断。要获得字面接缝的 typed equivalence，须另要求源靶对应反映原来的匹配，并核验 Hom 的满性与忠实性；一般范畴等价也不自动反映对象的字面相等。

**命题 27.4（最终仿射摘要与原始合法性分离）。** 恒等式

$$
F_5F_2=F_{\mathrm{null}}F_3,
\tag{27.4}
$$

是全孔输入上的局部归一化等式，但不能据此认证原始输入合法。

证明。两边线性部分都是 $S^2$，平移部分分别为

$$
d_5+Sd_2=(1,1)+(1,2)=(2,3)=Sd_3.
$$

低到高原字 $[5][2]$ 的 $001|100$ 接缝非法，$[\mathrm{null}][3]$ 合法。若忽略失败历史而机械更新，两字都具有单位位零、长度二、终接缝零、末整窗非零及同一完整 $\Phi$。这些终值的任何函数都不能区别该合法与非法输入。两个六位片段首位、末位都为零，所以把左片段换成右片段保持两侧外部 seam 条件，并消去其内部非法 seam；左右复合任意固定仿射上下文也保持 (27.4)。这是一条正确局部规则，没有由此得到全局归一化的终止性、完备性或唯一正常形。$\square$

方向错误还能合并两个合法规范来源。取 $u=[2][5][3]$、$v=[3][\mathrm{null}][3]$，均为 $0\to0$ 三窗字且末窗非零。正确值为

$$
D_u=(1,0)+S(1,1)+S^2(0,1)=(12,18),\quad N(u)=78,
$$

$$
D_v=(0,1)+S^2(0,1)=(8,14),\quad N(v)=58.
$$

误按输入次序连续施加 $F_\sigma$，即取 $\Psi_w=F_{\sigma_{n-1}}\cdots F_{\sigma_0}$，(27.4) 却给两者同为 $S^3x+(8,14)$。这不是合法路径之间正确 $\Phi$ 的碰撞，而是换了执行语义；合法性、终态和 End 资格都无法修复这个方向错误。

## 28. 递归签名、正面 reset 编码与原分支的操作边界

**定义 28.1（Stop、End 与有限递归类型）。** 正数 End 的独立资格位初始化为 $\chi=\varepsilon$，读窗后替换为 $\chi'=\mathbf1_{\{\sigma\ne\mathrm{null}\}}$，不取累计 OR。可达活动对为 $(s,\chi)\in\{(0,0),(0,1),(1,1)\}$；非法 seam 进入吸收错误态。正数 End 还须完整来源合同或证书保证未读高位全零；零另用全零的结构表示。单位一的空窗字可表示一并正数 End，单位零的空字不能作正数 End。语法 Stop 仅结束一个有限路径，不提供未知来源的高位证书。

若

$$
\mathrm{Geom}::=\mathrm{Self}\mid\mathrm{Mirror}(2)
\mid\mathrm{Translate}(3)\mid\mathrm{Rotate}(4)
\mid\mathrm{Scale}(\mathrm{Geom})
$$

中 $2,3,4$ 是有限叶参数集的基数，令 $C$ 为十个叶参数的互斥和，则其有限初始代数为 $\mu X.(C\sqcup X)$。按 §27 的真实窗图，允许 Stop 的有限路径类型和无 Stop 的无限流类型分别为

$$
X_0=1+3X_0+2X_1,\qquad X_1=1+2X_0+X_1,
\tag{28.1}
$$

$$
\Omega_0=3\Omega_0+2\Omega_1,\qquad
\Omega_1=2\Omega_0+\Omega_1.
\tag{28.2}
$$

前者取有限良基初始解，后者取所有合法无限展开的最大余代数解。

**命题 28.2（签名的实际内容）。** $\mu X.(10+X)\cong C\times\mathbb N$，每项唯一为 $\mathrm{Scale}^k(c)$；它不是五个递归子树的节点。式 (28.1)–(28.2) 则保留了窗图的实际一步展开。

证明。有限项外层不是 Scale 就是叶子；逐层剥除 Scale 必在有限深度遇到唯一叶子，给唯一 $(c,k)$，反向按 $k$ 次包裹构造。对 (28.1)，起态零有三条至零和两条至一的边，起态一有两条至零和一条至一的边，外加各自 Stop；头边与剩余路径唯一确定有限字。对 (28.2)，从任一两排序余代数中的点反复读取唯一声明的头边与后继，得到一条无限合法路径；任何余代数态射必须保留每个有限前缀，故这个展开态射唯一，证明终极性。所有窗口都推进，$[5]$ 留在状态一，只有三种下一窗；每个状态都能继续读 $[3]$。$\square$

若数字表示子项数，签名改成 $1+X^2+X^3+X^4+X$；若表示参数维数，参数集通常无限。单一构造子 $\mathrm{Node}(\mathrm{Ref},2,3,4,G)$ 的全部字段是积 $\mathrm{Ref}\times2\times3\times4\times G$；没有叶子时有限良基初始类型为空，而无限对象是另一流类型。这些解释不能由集合基数相近而识别。比如把 Scale 原样编成 $[5]$、Mirror 编成 $[2]$，嵌套串 $[5][2]$ 已非法。

**定理 28.3（十叶单链的合法程序数据编译）。** 选任意注入 $\beta:C\hookrightarrow\{[\mathrm{null}],[3]\}^4$，定义

$$
\operatorname{code}(\mathrm{Scale}^k c)
=([5][\mathrm{null}])^k\,\beta(c)\,[3].
\tag{28.3}
$$

此字从零接缝出发合法，长度 $2k+5$、终态零，且在单位位零及已知完整有限词的来源合同下编码为互不相同的实际正自然数。

证明。$[5][\mathrm{null}]$ 是 $0\to1\to0$ reset 宏；$[\mathrm{null}],[3]$ 是零态自环，所以所有拼接合法。先逐个解析初始 reset 宏取得 $k$，其后的四窗以 $\beta$ 恢复 $c$，再检查固定末窗 $[3]$；数据窗不含 $[5]$，所以宏区和叶区无歧义。末整窗非零，使不同完整词不能只差多保留的高零窗；规范 Zeckendorf 唯一性给整数单射。$\square$

这个递归宏的线性推进为 $S^2$，不是一窗 $S$；(28.3) 编的是程序数据。若规定解码后再按 $\mathrm{Scale}^k(c)$ 的另行给定语义求值，剥一层 Scale 对应剥一个 reset 宏，于是有限展开和解码相容。原算术窗口机对这个字计算其来源数值，不因此就执行了几何 Scale。这个受限十叶签名的码，与 §29 五个自由指令的四位最短码具有不同输入语言。

**定理 28.4（正长度原宏的有限阶障碍）。** 任意正长度 $l$ 的五仿射分支宏在 $\mathbb R^2$ 上为 $A(x)=S^lx+t$，有唯一周期点

$$
p=(I-S^l)^{-1}t,
$$

该点就是固定点。若 $X\subseteq\mathbb R^2$ 至少含两点、$A(X)\subseteq X$，则不存在注入 $h:X\to Y$ 与有限阶动作 $g^r=I_Y$ 满足 $hA=gh$。

证明。复合归纳给线性部分 $S^l$。$S$ 两特征值为 $2+\sqrt5$ 和 $2-\sqrt5$，其任意正次幂都不是一；故 $I-S^l$ 可逆。移心后 $A$ 为 $S^l$，$A^r(x)=x$ 迫使 $(S^{lr}-I)(x-p)=0$，即 $x=p$。若有上述 intertwiner，迭代与注入性使 $A^r=I_X$，每点都周期，矛盾。$\square$

因此在非退化、可重复的域上，原正宏不能被注入互绕成有限阶 Self、Mirror 或 Rotate。$[2][2]$ 是合法零态回路，但 $F_2^2(0)=(2,2)$；$[2\ 5]$ 则不能跟自己串接，把它忘类型地送到可自由重复的 quarter-turn 会丢失合法性反映，而不排除一般函子。局部三槽反转固定 null、$[3]$、$[2\ 5]$，交换 $[2]/[5]$；它把合法 $[2][5]$ 变成非法 $[5][2]$，并且不是下节的 $J$，因为 $Jd_2=d_2$。

**命题 28.5（原五分支的完整有向群）。** 在 $\mathbb Z^2$ 上另行允许逆分支，所生成的群恰为

$$
G_5=\{x\mapsto S^kx+t:k\in\mathbb Z,t\in\mathbb Z^2\}
\cong\mathbb Z^2\rtimes_S\mathbb Z,
$$

产品为 $(k,t)(k',t')=(k+k',t+S^kt')$，且无非平凡挠元。

证明。$S$ 整数幺模，显示集合是含全部分支的群。反向 $F_{\mathrm{null}}=S$、$F_2S^{-1}=T_{(1,0)}$、$F_3S^{-1}=T_{(0,1)}$ 给全部平移与整数幂。有限阶条件 $S^{kr}=I$ 强迫 $k=0$，再由 $rt=0$ 强迫 $t=0$。$\square$

逆分支增加了平移的可用性，但没有 $J,C$；它们的有限阶也不由原正来源许可。正宏在整实平面有固定点，非零平移没有，故整平面的任意集合共轭也不能把前者变成后者。若把 Scale 指普通 isotropic homothety，正宏的两个不同模特征值排除仿射共轭；其向固定点收敛的稳定集是一条真直线，而可逆标量缩放的稳定集是全平面、单点或有限阶情形，故整平面的拓扑共轭亦失败。零缩放不可逆。把 $S$ 称为“Scale”须明确它是双特征方向的黄金递归，而不是各向同性缩放。

原语义的正面修复是精确的 $F_\sigma=T_{d_\sigma}S$，两个 primitive 均保持 $\mathbb N^2$。另有 signed 分解 $F_\sigma=T_{d_\sigma}(CJ)^3$，$C=MJ$、$CJ=M$；chronological 次序为 $J,C,J,C,J,C,T_d$。$J(0,1)=(1,-1)$ 显示这个分解需要 signed 中间态；若只允许完整宏，读出也只能在声明的宏边界进行。

另一正面合同为每条实际边 $e:s\to t$ 选参数集 $P_e$，以 $(e,p)$、$p\in P_e$ 为参数化图的边；同一输入语言仍用有限可串接路径。另给配置集 $Z_s$、实际部分动作 $G_{e,p}:D_{e,p}\to Z_t$，其中 $D_{e,p}\subseteq Z_s$，把 membership in $D_{e,p}$ 作为额外 guard。保留 $(\varepsilon,s,\chi,n,a,w,z)$，其中 $z\in Z_s$；合法窗按 (27.3) 更新 $n,a$、替换 $s,\chi$、追加参数历史 $w$，并执行 $G_{e,p}(z)$。沿路径复合的定义域是所有中间 guards 都成立的初态；头边分解与函数结合律给唯一 compositional interpreter。若指令动作总定义，便是自由路径范畴到相应配置范畴的 functor；一般 partial maps 也按同一串接规则解释，但不能把某个 source 图路径的 seam 合法性当作其所有配置上均可执行。

独立的忠实历史模型取 $H_s$ 为所有结束于 $s$ 的有限参数化 histories，含空历史 $1_s$，边作用为追加 $(e,p)$。对平行路径作用在 $1_s$ 上即读回原路径，所以该历史解释忠实；具体几何投影可以识别 histories，例如两次镜像。轴、中心、平移量、角和比例是新增参数，五个裸名字不提供它们。

将五个打印标签重命名为五个 constructor tags，并保留实际边的源靶与参数，是合法的自由路径语法双射。名为 Self 的非空 constructor 仍不是空 identity path；几何评价消去它或消去两次 Mirror 时，只是该投影识别不同语法，并未否定语法双射。

## 29. 有向离散几何的正规形、探针与可执行数据码

本节把 §28 的额外几何合同写全，再给有限操作的 Fibonacci 对象码。它使用母卷命题 149.2 的矩阵恒等式，不把这个更大群认作 $G_5$。

**定理 29.1（扩大群的唯一正规形与产品）。** 在 signed lattice $\mathbb Z^2$ 上允许 $M,J,T_\alpha,T_\beta$ 及其逆，其中

$$
\alpha=(1,0),\quad\beta=(0,1),\quad
J=\begin{pmatrix}1&1\\0&-1\end{pmatrix},\quad C=MJ.
$$

群 $G=\langle M,J,T_\alpha,T_\beta\rangle$ 的每个元素唯一为

$$
g_{\epsilon,k,\delta,t}(x)=(-1)^\epsilon M^kJ^\delta x+t,
\quad \epsilon,\delta\in\{0,1\},\ k\in\mathbb Z,\ t\in\mathbb Z^2.
\tag{29.1}
$$

以右项先做的函数复合为产品，$g=(\epsilon,k,\delta,t)$、$h=(\epsilon',k',\delta',u)$ 有

$$
\begin{aligned}
\epsilon''&=\epsilon+\epsilon'+\delta k'\pmod2,\\
k''&=k+(-1)^\delta k',\\
\delta''&=\delta+\delta'\pmod2,\\
t''&=t+(-1)^\epsilon M^kJ^\delta u.
\end{aligned}
\tag{29.2}
$$

证明。$M^{-1}=M-I$、$J^2=I$、$JMJ=-M^{-1}$、$(MJ)^2=-I$；故 $-I$ 已生成，且对所有正负整数 $r$，$JM^rJ=(-1)^rM^{-r}$。移全部 $J$ 到右端得到线性正规形及符号 $\delta k'$；由 $AT_uA^{-1}=T_{Au}$ 移全部平移到左端。反向所列因子都在生成群中，给存在性。$M^r=\pm I$ 由扩张特征值 $\phi^r$ 强迫 $r=0$、正号。$J\ne\pm M^r$，否则 $J$ 与 $M$ 交换，与 $JMJ=-M^{-1}$ 合起来强迫 $M^2=-I$，矛盾。两线性正规形相等，先排除不同 $\delta$，再消去同一 $J^\delta$ 得相同 $k,\epsilon$。零点读出给唯一 $t$。$\square$

$J$ 是黄金共轭的整数线性作用；它的二阶不使它成为标准欧氏度量中的正交镜面反射。$C$ 则是该组成坐标的欧氏 quarter-turn。它们的 signed domains 与原 canonical 来源类型分别声明。

**命题 29.2（完整仿射有限阶分类）。** 写 $A=(-1)^\epsilon M^kJ^\delta$。全部情形如下：

| 本章线性型 | 平移条件 | $x\mapsto Ax+t$ 的阶 |
| --- | --- | --- |
| 29 · $A=I$ | $t=0$ | 1 |
| 29 · identity linear part | $t\ne0$ | 无限 |
| 29 · $A=-I$ | 任意 $t$ | 2 |
| 29 · $\delta=0,k\ne0$ | 任意 $t$ | 无限 |
| 29 · $\delta=1,k$ 奇 | 任意 $t$ | 4 |
| 29 · $\delta=1,k$ 偶 | $(I+A)t=0$ | 2 |
| 29 · even reflection with drift | $(I+A)t\ne0$ | 无限 |

证明。$g^r(x)=A^rx+\sum_{j=0}^{r-1}A^jt$。$\delta=0,k\ne0$ 的线性部分无限阶。$\delta=1$ 时 $A^2=(-1)^kI$，且正规形唯一性排除 $A=\pm I$。奇 $k$ 给 $I+A+A^2+A^3=0$，所以任意平移都恰为四阶；偶 $k$ 给 $g^2=T_{(I+A)t}$，非零整数平移无限阶。$A=I,-I$ 两行直接由同一公式得到。有限阶中心不必是整数点。对任意 $m\in\mathbb Z$，准确共轭为

$$
M^{2m}J=(-1)^mM^mJM^{-m}.
\tag{29.3}
$$

所以 $k=2m$ 时，反射平移条件还可写成 $t\in\mathbb ZM^m(1,-2)$（$\epsilon+m$ 偶）或 $t\in\mathbb ZM^m(1,0)$（$\epsilon+m$ 奇）；负 $m$ 同样成立。$\square$

**定理 29.3（成员承诺下恰需两个整数全向量探针）。** 任意仿射映射的 $f(0),f(\alpha),f(\beta)$ 给平移和两矩阵列；若已知 $f\in G$，只读 $f(0),f(3,1)$ 就单射识别 $f$，而一个整数输入不够。

证明。置 $Q(a,b)=a^2+ab-b^2$。代入给 $Q(Mw)=-Q(w)$、$Q(Jw)=Q(w)$，故对所有 $r\in\mathbb Z$ 有 $Q(M^rw)=(-1)^rQ(w)$。$v=(3,1)$ primitive 且 $Q(v)=11$。非恒等 $\pm M^k$ 没有非零固定向量：$k\ne0$ 时两个特征值的模都不为一，$k=0$ 的负号只固定零。若 $(-1)^\epsilon M^kJ$ 固定 $v$，奇 $k$ 因平方为 $-I$ 立即矛盾。偶 $k=2m$ 时 (29.3) 使 primitive 向量 $w=M^{-m}v$ 固定于 $(-1)^{\epsilon+m}J$。$J$ 的 primitive 正固定轴只有 $\pm(1,0)$，负固定轴只有 $\pm(1,-2)$，其 $|Q|$ 分别为一、五；但 $Q(w)=(-1)^m11$，矛盾。故 $v$ 的稳定子平凡。

$f(0)$ 固定 $t$，$f(v)-t=Av$ 固定 $A$，因为 $Av=Bv$ 使 $B^{-1}A$ 稳定 $v$。唯一正规形随后固定所有参数。对任意整数 probe $p$，identity 与 $x\mapsto-x+2p\in G$ 在 $p$ 上相同却为不同映射，证明一下界。$\square$

这只计独立的精确完整整数输出查询，并以成员承诺为前提；没有 scalar、模数、噪声、有限精度或高效 $k$ 解码结论，也没有从合法正窗域获得任意 probe 的权限。熟悉的 $0,\alpha$ 两点反而被 $J$ 同时固定。

**定理 29.4（五个自由标签的最短固定受限码）。** 对五个可任意串接的不同指令，要求等长、已知块对齐、码字内部和所有码字边界都没有 $11$。四位码

$$
\mathcal C=(0000,1000,0100,1010,0010)
\tag{29.4}
$$

满足合同，且三位或更短不可能。令程序 $P$ 有 $m\ge0$ 个标签，固定独立单位位 $\varepsilon_{\mathrm{code}}=0$，串接 $4m$ 个 data bits，再加最高标记一，在其上补零至三窗边界，并声明其余高位为零。所得实际正 canonical 来源记为 $\operatorname{Encode}(P)$。其成本恰为单位之后 $4m+1$ 个有效位置、包括单位 $4m+2$ 个位置，以及

$$
\left\lceil\frac{4m+1}{3}\right\rceil
\tag{29.5}
$$

个窗口。空程序编码为二。

证明。四位字都内部合法且末位零，任意边界合法。三位任意串接若同时有末一的字和首一的字就失败，故全部字必须首零或全部末零；内部合法的三位首零字只有 $000,001,010$，末零字只有 $000,010,100$。更短连五个二进制字都没有。对外包装，单位零守住第一边界，末码零守住 marker 边界，高零补齐不会制造 $11$；最高一所在的最后整窗非零，End 资格成立。它位于全位串位置 $4m+1$，所以成本如上；$m=0$ 时为单位零后 $100$，数量 $F_3=2$。最高一只能是 marker。解码验证单位零、最高位置 $h\equiv1\pmod4$，删该一及其上 padding，保留全部 $h-1$ 个 data positions，再按四位块取码字逆。故 $\operatorname{Decode}(\operatorname{Encode}(P))=P$。$\square$

解码使用完整 canonical 来源数、完整码或另行完整 End 证书；未知来源的任意有限 observation prefix 不能认证最高可见一是 marker。零和一不在本码像中。位数是解析开销，不是几何动作数；本下界也不适用于可变长码、state-dependent 码或已受限的指令语言。

**定义 29.5（有限程序的执行、组合与展开）。** 另行固定五个指令标签 $\Sigma=\{0,\ldots,4\}$、配置载体 $Z$、各指令的部分动作 $G_j$ 与 guard。所有所需有限参数须在合同中指定。按 chronological 顺序

$$
\operatorname{Eval}(j_1\cdots j_m,x)
=G_{j_m}\cdots G_{j_1}(x)
$$

仅在每一步 guard 成立时定义，空程序为 identity。$\operatorname{Exec}(n,x)$ 先完成来源解码，再按同一 guards 执行该词；marker 与 padding 没有指令动作。在码像上定义

$$
n\star n'=\operatorname{Encode}
\bigl(\operatorname{Decode}(n)\operatorname{Decode}(n')\bigr).
\tag{29.6}
$$

“展开”是解码后取空词或头标签与余词，然后将余词重新编码，和原有限指令词的头尾分解对应。

这里 $\star$ 是解码、指令串接、重新编码的 transported product，identity 为空程序码二；它不是原三位窗的裸串接，也不宣称 Encode 对原 $\Phi$ 仿射乘法是同态。这个明确的额外解释保留指令组合与逐步执行，原 FIB source arithmetic 则仍按 §27 求值。

以下 Python 3 程序在整数、有限列表、声明的 actions/guards 上实现这些定义；它是本节有限数学构造的代码表述。动作与权限由调用参数给出，来源的普通仿射求值不是 `execute` 的替代解释。

```python
CODES = ((0,0,0,0), (1,0,0,0), (0,1,0,0),
         (1,0,1,0), (0,0,1,0))
INVERSE = {c: j for j, c in enumerate(CODES)}

def encode(program):
    data = []
    for tag in program:
        if type(tag) is not int or not 0 <= tag < 5:
            raise ValueError("instruction tag")
        data.extend(CODES[tag])
    bits = [0] + data + [1]  # separate unit, data, highest marker
    a, b, value = 1, 2, 0
    for bit in bits:
        value += bit * a
        a, b = b, a + b
    return value

def canonical_bits(value):
    if type(value) is not int or value < 0:
        raise ValueError("natural source")
    if value == 0:
        return [0]
    weights = [1, 2]
    while weights[-1] <= value:
        weights.append(weights[-2] + weights[-1])
    bits = [0] * len(weights)
    remaining = value
    for j in range(len(weights)-1, -1, -1):
        if weights[j] <= remaining:
            bits[j] = 1
            remaining -= weights[j]
    while len(bits) > 1 and bits[-1] == 0:
        bits.pop()
    return bits

def decode(value):
    bits = canonical_bits(value)
    h = len(bits) - 1
    if bits[0] != 0 or h < 1 or h % 4 != 1:
        raise ValueError("program framing")
    program = []
    for j in range(1, h, 4):
        block = tuple(bits[j:j+4])
        if block not in INVERSE:
            raise ValueError("program data block")
        program.append(INVERSE[block])
    return program

def source_windows(value):
    bits = canonical_bits(value)
    unit, data = bits[0], bits[1:]
    data = data + [0] * ((-len(data)) % 3)
    return unit, [tuple(data[j:j+3]) for j in range(0, len(data), 3)]

def compose_codes(left, right):
    return encode(decode(left) + decode(right))

def unfold_code(value):
    program = decode(value)
    if not program:
        return None
    return program[0], encode(program[1:])

def execute(value, x, actions, guards):
    for tag in decode(value):
        if not guards[tag](x):
            raise ValueError("instruction domain")
        x = actions[tag](x)
    return x
```

例如在完整 signed carrier $Z=\mathbb Z^2$ 上，可具体取五个指令动作 $I,J,T_\alpha,C,M$，最后一个是黄金递归步而非 isotropic scale。对应调用参数可写为：

```python
SIGNED_ACTIONS = (
    lambda x: x,
    lambda x: (x[0] + x[1], -x[1]),
    lambda x: (x[0] + 1, x[1]),
    lambda x: (-x[1], x[0]),
    lambda x: (x[1], x[0] + x[1]),
)

def signed_domain(x):
    return (type(x) is tuple and len(x) == 2
            and all(type(a) is int for a in x))

SIGNED_GUARDS = (signed_domain,) * 5
```

每个动作保持此 signed domain，故 `execute` 以这组参数给明确的格点程序执行。改用正来源、受限支撑或其它五种几何动作时，必须换成相应 guards 与实际参数；不能把这组全格点权限沿用过去。

**定理 29.6（解析、执行、组合与展开交换）。** 对所有有限声明程序及逐步合法初态，

$$
\begin{aligned}
\operatorname{Decode}\operatorname{Encode}(P)&=P,\\
\operatorname{Encode}(PQ)&=\operatorname{Encode}(P)\star\operatorname{Encode}(Q),\\
\operatorname{Exec}(\operatorname{Encode}(P),x)&=\operatorname{Eval}(P,x),\\
\operatorname{Exec}(n\star n',x)
&=\operatorname{Exec}(n',\operatorname{Exec}(n,x)).
\end{aligned}
\tag{29.7}
$$

最后一式定义域恰为先执行 $n$、再执行 $n'$ 均合法的初态；`unfold_code` 同样与程序的空/头尾展开交换。

证明。定理 29.4 给解析逆与第二式。代码 `canonical_bits` 是规范贪心算法：选最大可用权重 $F_{j+2}$ 后，剩余量小于前一权重 $F_{j+1}$，故下一低位不能为一；向下继续使余量最终为零，得到无相邻一的表示，规范唯一性使其等于来源码。`encode` 的两个变量逐次为 $F_{j+2},F_{j+3}$，故返回定义的整数；`decode` 恢复 marker 以下全部块，包括最终零 data blocks。空词执行无动作；若前 $r$ 块已执行为 $\operatorname{Eval}(j_1\cdots j_r,x)$，第 $r+1$ 块解析为同一标签，并应用同一 guard 和动作，故归纳得第三式。指令词串接的逐步求值给第四式，其 guard 条件也逐步相同。解码逆同时使空/头尾两种展开逐项相同。$\square$

**命题 29.7（正规形整数记录的有限序列化）。** 正规形数据具有独立记录类型。取 zigzag 双射

$$
z(a)=\begin{cases}2a,&a\ge0,\\-2a-1,&a<0,\end{cases}
\quad
z^{-1}(2r)=r,\quad z^{-1}(2r+1)=-r-1.
$$

将 $(\epsilon_{\mathrm{nf}},k,\delta,t_0,t_1)$ 的五个整数都经 $z$ 变成 $n_1,\ldots,n_5$，序列化为

$$
1^{n_1}0\,1^{n_2}0\,1^{n_3}0\,1^{n_4}0\,1^{n_5}0.
\tag{29.8}
$$

用两个不同 data-symbol tags 承载零、一，再用 (29.4) 和正数外包装编码，即得该记录到实际 Fibonacci 正来源的单射。

证明。依次读到五个零，计数各自前的连续一，再逆 zigzag，即恢复五字段；零长度字段是一个零，连续零没有歧义。拒绝第五个零后的额外数据，检查 $\epsilon_{\mathrm{nf}},\delta\in\{0,1\}$，得到完整逆。两 data tags 与外包装各有左逆，复合仍单射。$\square$

解码记录后才应用 (29.1)，或把它编成已允许 primitive 的有限词；负 $k$ 仅在 inverse primitives 有权限时合法。承载 payload 的两 tags 此时只表示数据，不能未解码就执行其几何动作。程序码与记录码共用接口时须有类型标签或固定类型上下文。正规形保存动作参数，不能恢复被群关系识别掉的来源 instruction history、branching 或 self-reference；例如空词与 $JJ$ 同动作而不同历史。

最后，坐标变换也要运输整个合同。对 $h(x)=Bx+c$、可逆 $B$，动作 $Ax+t$ 的新参数为

$$
A'=BAB^{-1},\qquad t'=Bt+c-A'c.
\tag{29.9}
$$

定义域 $D$ 变成 $h(D)$，初态变成 $h(x)$，观察变成 $o\circ h^{-1}$。代入直接给动作与观察交换，有限合法组合逐步保持。非整数格自同构的 $B$ 改变载体为 $B\mathbb Z^2+c$；即便 $J,C$ 都不保持旧正锥，因为 $J\beta=(1,-1)$、$C\beta=(-1,0)$。seam、End、参数和权限须在 parser 类型中独立运输，不能从数值终点重新推断。

## 30. 另行可用的四阶标签旋转与真实相位载体

§29 在有向格点上提供 $C=MJ$。要连接本卷量子模型，仍须指定有限标签、线性提升和允许控制；整数坐标旋转本身不提供叠加制备。

**定义 30.1（标签置换的酉表示）。** 独立声明 $C(a,b)=(-b,a)$ 在 $X_n=(\mathbb Z/n\mathbb Z)^2$ 上可用，$n\ge1$，并在 $\mathcal H_n=\mathbb C^{X_n}$ 上取

$$
U_C|x\rangle=|Cx\rangle.
$$

这是基标签置换的线性提升，$U_C^4=I$；不是给原数字标签逐个任意指定 $i^j$ 相位。

**定理 30.2（完整四相重数与基）。** 令 $g=\gcd(2,n)$。有

$$
\operatorname{Tr}U_C=g,\quad
\operatorname{Tr}U_C^2=g^2,\quad
\operatorname{Tr}U_C^3=g.
$$

特征值 $1,-1,i,-i$ 的重数分别为

$$
\frac{n^2+2g+g^2}{4},\qquad
\frac{n^2-2g+g^2}{4},\qquad
\frac{n^2-g^2}{4},\qquad
\frac{n^2-g^2}{4}.
\tag{30.1}
$$

对应 character projectors 和每条四循环上的单位向量为

$$
P_j=\frac14\sum_{r=0}^3i^{-jr}U_C^r,\qquad
\chi_j=\frac12\sum_{r=0}^3i^{-jr}|C^rx_0\rangle,
\quad j=0,1,2,3.
\tag{30.2}
$$

证明。置换矩阵的迹数固定标签。$Cx=x$ 要求 $a=b$、$2a=0$，共 $g$ 个；$C^2x=x$ 要求 $2a=2b=0$，共 $g^2$ 个；$C^3$ 与 $C$ 固定点相同。有限几何级数给 $P_j^*=P_j$、$P_jP_k=\delta_{jk}P_j$、$\sum_jP_j=I$、$U_CP_j=i^jP_j$；取迹即得 (30.1)。直接循环计数也给 $g$ 条一循环、$(g^2-g)/2$ 条二循环、$(n^2-g^2)/4$ 条四循环；每条二循环贡献 $\pm1$，每条四循环贡献四根。在 (30.2) 中重标 $r+1$ 得 $U_C\chi_j=i^j\chi_j$，彼此正交且覆盖该四循环。$\square$

$n=1$ 时作用 trivial；$n=2$ 时是坐标交换，阶二且重数为 $3,1,0,0$。$n\ge3$ 时 $(1,0),(0,1),(-1,0),(0,-1)$ 四点不同，故所有四相出现，$U_C$ 及其密度共轭动作都有阶四。以下三个载体应保持分离：

| 本章动作载体 | amplitude unitary 阶 | density conjugation 阶 |
| --- | --- | --- |
| 30 · scalar $iI$ | 4 | 1 |
| 30 · literal $2\times2$ matrix $C$ on $\mathbb C^2$ | 4 | 2 |
| 30 · label permutation $U_C$, $n\ge3$ | 4 | 4 |

中行 $C^2=-I$ 是全局相位，且 $C$ 非标量；末行平方却把 $|x\rangle$ 送到 $|-x\rangle$，不是 $-|x\rangle$。沿四循环的基态投影在前三次作用后都不同，证明 density 阶确为四。模二末行退为阶二，模一为 identity。单个 eigenspace 中的相位是全局相位；只有跨 eigensector 的叠加及相应 recombination/readout 能读相对相位。这些制备和控制是额外权限：单凭基置换，从一个基态不能制备 (30.2) 的 Fourier 向量。

**命题 30.3（有限约化仍缺少旋转原语）。** 对每个 $n\ge2$，$C$ 不在 reduced 五仿射分支及其逆生成的群中。

证明。任何该群元素线性部分仍为 $S^k$，$k\in\mathbb Z$。$S$ 与其逆都对称，故所有幂对称；$n\ge3$ 时 $C$ 的非对角元 $-1,1$ 不相等，故不对称。$n=2$ 时 $S=I$ 而 $C\ne I$。若一个 affine 元素作为函数等于 $C$，代入零先迫使平移为零，再在两个坐标基上得到矩阵相等，已排除。这个有限模型证明没有把有向整数群的 torsion-free 性错误地搬到有限商群。$\square$

**命题 30.4（指定二模式相干的读取设置）。** 对可执行的二模式投影 $|r_\theta\rangle\langle r_\theta|$，其中 $r_\theta=(u+e^{i\theta}v)/\sqrt2$、$u,v$ 为正交单位向量，写 $s=\rho_{uu}+\rho_{vv}$、$z=\rho_{uv}$，则

$$
p_\theta=\frac s2+\operatorname{Re}(e^{i\theta}z).
$$

未知 $s$ 时三个设置 $0,\pi,\pi/2$ 已给

$$
s=p_0+p_\pi,\qquad
\operatorname{Re}z=(p_0-p_\pi)/2,\qquad
\operatorname{Im}z=(p_0+p_\pi)/2-p_{\pi/2}.
\tag{30.3}
$$

已知 $s$ 时两个设置 $0,\pi/2$ 足够。

证明。展开 $\langle r_\theta|\rho|r_\theta\rangle$ 得显示概率，代入三个角即得逆式。$\square$

四相成对差可方便消去背景，但不是此指定参数读取任务的必要最小设置数；本命题也不是高维全态层析或一次未知态恢复。五个打印标签乘四个 character 名称没有独立性的证明，更不能叫“二十个状态”：有限前缀、程序参数和量子态载体各有自己的类型。

**命题 30.5（扩大动力学改变 sector 权重）。** 对 $n\ge3$，axis-uniform 向量

$$
\chi_0=\tfrac12\bigl(|(1,0)\rangle+|(0,1)\rangle
+|(-1,0)\rangle+|(0,-1)\rangle\bigr)
$$

在 $C$ 的 $+1$ sector 中。若另行允许 $U_M|x\rangle=|Mx\rangle$，该 sector 的权重在 $v=U_M\chi_0$ 中恰为 $1/2$。

证明。$v$ 支撑于 $\{(0,1),(1,1),(0,-1),(-1,-1)\}$，$U_Cv$ 支撑于 $\{(-1,0),(-1,1),(1,0),(1,-1)\}$，对所有 $n\ge3$ 两组都不交。$U_C^2v=v$，故 $P_0v=(v+U_Cv)/2$，其平方范数为 $1/2$。$\square$

这说明稳定性依赖全部声明动力学；它不指定 sector 测量权限，也不推出物理粒子规律。

## 31. 新预测信息、相干响应与正的地址粗化

§27 的地址和 §30 的量子标签都是坐标选择；统计信息由实际操作和效果确定。复用定义 11.1，取实际 Hermitian 事件效果的实张成 $\mathcal O_\infty$，以及初始读出的子空间 $\mathcal O_0\subseteq\mathcal O_\infty$。商 $\mathcal O_\infty/\mathcal O_0$ 表示新增预测响应，定义没有规定新增方向必须是相干。

**命题 31.1（纯经典的新增 FIB 响应）。** 在 $\mathcal K_2=\mathbb C^{(\mathbb Z/2)^2}$ 上只允许等待整数次 $U|a,b\rangle=|b,a+b\rangle$ 后读第二坐标。令 $Z_a,Z_b$ 分别在该基取 $(-1)^a,(-1)^b$。则

$$
U^\dagger Z_bU=Z_aZ_b,\qquad
(U^2)^\dagger Z_bU^2=Z_a,\qquad U^3=I,
$$

$$
\mathcal O_0=\operatorname{span}_{\mathbb R}\{I,Z_b\},\qquad
\mathcal O_\infty=\operatorname{span}_{\mathbb R}\{I,Z_a,Z_b,Z_aZ_b\}.
\tag{31.1}
$$

新增两维全部计算基对角。

证明。迭代第二坐标依次为 $b,a+b,a$，二结果投影是相应 $Z$ 的 $(I\pm Z)/2$，所以效果恰张成 (31.1)。$|00\rangle,|10\rangle$ 初读相同，等待一步后分别读零、一，全程无需相干。$\square$

更强例属于本卷已有的标准 digits、完整低仪器合同。取 $d=e=2$、$\Delta=2\pi/3$、$x=e^{-2\pi i/3}$。定理 14.1 的已证公式为

$$
W=\frac{I+U^3}{2}+x\frac{I-U^3}{2},\qquad
U^3=\sum_aE_{aa}\otimes T_{Ma}.
$$

两输入都用低态 $s=(|00\rangle+|10\rangle)/\sqrt2$，高态分别为 Fourier 基 $p_{10},p_{01}$，都没有高 Fourier 非对角项。低 $00$ 控制 identity，低 $10$ 控制 $T_{01}$；它在两高标签上分别为 $+1,-1$。输出低向量分别为 $s$ 与 $(|00\rangle+x|10\rangle)/\sqrt2$，所以同一合法低事件 $|s\rangle\langle s|$ 的概率为

$$
1\quad\text{和}\quad |1+x|^2/4=1/4.
\tag{31.2}
$$

这个新预测信息来自高标签差异，不是新增高标签相干。定理 14.1 给该共振效果空间 Hermitian 维数 $64$，初始低读出维数 $16$；新增 $48$ 维全在高 Fourier 对角块中。

**定义 31.2（相对于声明 pinching 的相干响应）。** 先指定正交分块 $\{P_y\}$ 与自伴迹对偶 pinching $\mathcal D(X)=\sum_yP_yXP_y$。对实际 Hermitian 响应空间 $\mathcal O$，相干响应为

$$
\mathcal C_{\mathcal D}(\mathcal O)=(I-\mathcal D)\mathcal O
\cong\mathcal O/(\mathcal O\cap\operatorname{ran}\mathcal D).
\tag{31.3}
$$

新增相干响应可再取 $(I-\mathcal D)\mathcal O_\infty/(I-\mathcal D)\mathcal O_0$。

证明这个识别只需两事实：$\operatorname{Tr}[E(\rho-\mathcal D\rho)]=\operatorname{Tr}[(E-\mathcal DE)\rho]$，以及 $I-\mathcal D$ 限制到 $\mathcal O$ 的核为 $\mathcal O\cap\operatorname{ran}\mathcal D$。第一式由 pinching 自伴性，第二式由 $\mathcal D^2=\mathcal D$；线性第一同构定理给 (31.3)。这是带基准的线性商，不自动成为可执行效果空间或 quantum quotient。

在标准 $d=e=2$ 非共振合同中，沿用定理 14.1 的轨道代数，取完整高 Fourier pinching、保留所有低矩阵，则

$$
160=64+96,\qquad 160-16=48+96.
\tag{31.4}
$$

其中 $64=16\cdot4$ 是完整条件对角矩阵，$96=16(3^2-3)$ 是非零三标签轨道内的高相干；初始十六维包含在前者。共振处高相干部分为零。换成整个 $AH$ 计算基细 pinching 就是另一基准，不能沿用这个分解。

**命题 31.3（粗事件保留块内相干）。** 定义 2.1 的 Lüders 粗采样只删跨事件块相干，rank 大于一的块可保留量子相干。具体在模二时刻 $0,3$ 读第二坐标，可达记录为 $(z,z)$，

$$
P_z=|0,z\rangle\langle0,z|+|1,z\rangle\langle1,z|,
\qquad\operatorname{rank}P_z=2.
$$

两输入 $\chi_\pm=(|00\rangle\pm|10\rangle)/\sqrt2$ 都以概率一给 $(0,0)$，末钟条件态仍为 $|\chi_\pm\rangle\langle\chi_\pm|$。

证明。$U_2^3=I$，所以两个来源投影相同，且两向量都在 $P_0$ 的像内；命题 2.2 的 $U^3P_0$ 分支就是 $P_0$。块内矩阵元 $00,10$ 分别为 $\pm1/2$。一般 $P_y\rho P_y/p_y$ 仅在 $p_y>0$ 时定义，完全可能仍有内部非对角项。$\square$

经典记录不使条件态自动逐地址对角；相同效果也不规定相同更新。若要求细 dephasing 或 measure-and-prepare，须另行声明那个实际分支。

**命题 31.4（pair-address 正性与非单射求和障碍）。** 有限地址集 $X$ 的 density kernel 必须满足 $\rho\ge0$、$\rho=\rho^\dagger$、$\operatorname{Tr}\rho=1$。对非单射 $\kappa:X\to Y$，振幅求和 $A|x\rangle=|\kappa(x)\rangle$ 一般不给 TP 通道。

证明。取 $x\ne x'$、$\kappa(x)=\kappa(x')=y$。对 $\psi_\pm=(|x\rangle\pm|x'\rangle)/\sqrt2$，$A\psi_+=\sqrt2|y\rangle$、$A\psi_-=0$，故 $A\rho A^\dagger$ 的迹分别为二、零。事后归一化非线性，且第二态上无定义。$\square$

有效经典粗化可用 Kraus $|\kappa(x)\rangle\langle x|$：

$$
\mathcal Q_{\mathrm{mp}}(\rho)
=\sum_y\operatorname{Tr}(P_y\rho)|y\rangle\langle y|,
\qquad P_y=\sum_{\kappa(x)=y}|x\rangle\langle x|.
$$

Kraus 伴随乘积和为 $I_X$，所以 CPTP；它明确舍去纤维内部量子信息。若要保留内部相干，应改用块提取 $\rho\mapsto(P_y\rho P_y)_y$ 到 $\bigoplus_yB(P_y\mathcal H)$，或指定等距及重数系统和其处置。后者保留 rank-two 块而非单个 $|y\rangle$。§35 将证明这些正粗化何时还能保留所声明的全部条件续接。

## 32. 实际 operator system 与可观测稳定扇区

§31 讨论的是实际效果张成。定理 11.2 的特殊完整低仪器合同通过实际过滤、极化、左右双模及乘子代数 $\mathfrak D(S)$ 才证明它等于代数；不能从“事件效果”一词自动借入乘法。

**命题 32.1（同一 FIB 行走的四维效果、五维代数）。** 限制输入到命题 8.2 的三循环空间 $\mathcal V=\operatorname{span}\{u,v,w\}$，其中

$$
u=|10,p_{10}\rangle,\quad v=|01,p_{11}\rangle,\quad w=|11,p_{01}\rangle,
\qquad L|_{\mathcal V}=3I-J_3.
$$

合同仅允许一个不中断的任意非负等待区间，再做一次二结果低读出：选定结果为 $01$，另一结果为其补。没有中间仪器、额外低过滤或任意终端投影。定义正交基

$$
s=\frac{u+v+w}{\sqrt3},\qquad
r=\frac{-u+2v-w}{\sqrt6},\qquad d=\frac{u-w}{\sqrt2},
$$

以及

$$
A_0=\tfrac13|s\rangle\langle s|+\tfrac23|r\rangle\langle r|,
\quad X=|s\rangle\langle r|+|r\rangle\langle s|,
\quad Y=-i|s\rangle\langle r|+i|r\rangle\langle s|.
$$

实际响应空间为 $\mathcal O=\operatorname{span}_{\mathbb R}\{I,A_0,X,Y\}$，实维四，但

$$
C^*(\mathcal O)=B(\operatorname{span}\{s,r\})\oplus\mathbb C|d\rangle\langle d|
\tag{32.1}
$$

的 Hermitian 维数为五。

证明。$Ls=0,Lr=3r,Ld=3d$，且 $v=s/\sqrt3+\sqrt{2/3}\,r$。终端低结果压缩为 $|v\rangle\langle v|$，其 Heisenberg 效果为

$$
E_t=A_0+\frac{\sqrt2}{3}\bigl(\cos3t\,X+\sin3t\,Y\bigr).
$$

非负时间取到两个三角方向，补结果提供 $I$；四算子独立，所以恰维四。$X^2=P_s+P_r$ 不在其中：若为 $aI+bA_0$，在 $d$ 上给 $a=0$，在 $s,r$ 上又要求 $b/3=2b/3=1$，矛盾；$X,Y$ 的非对角项不能修复该对角等式。另一方面 $X^2$ 给两维支撑投影，$XY=i(P_s-P_r)$ 给其对角差，$X,Y$ 给两个角，$I-X^2=P_d$ 给余块，故恰生成 (32.1)。$\square$

实际不可区分态可以明确选为

$$
\rho_+=\tfrac12P_r+\tfrac12P_d,\qquad
\rho_-=\tfrac23P_s+\tfrac16P_r+\tfrac16P_d.
$$

它们对每个 $E_t$ 均给 $1/3$，却对 $X^2$ 分别给 $1/2,5/6$。将生成代数误作可读效果就在这个合同下虚增了可辨信息。一般实际效果的复化含 $I$、伴随封闭、带继承的矩阵正锥，因此首先是 operator system。普通商 $\mathcal O_\infty/\mathcal O_0$ 中 $\mathcal O_0$ 含单位，不能作为非零 CP map 的 operator-system kernel：正 map 若把单位送零，就把所有 $0\le A\le cI$ 送零，线性性使整 map 为零。标准 quotient operator system 还需要合法 kernel 与 Archimedean matrix cones，见 §38 的精确来源。

**命题 32.2（Hermitian 连续响应的生成元）。** 有限维 Hermitian 实空间中，对自伴 $H$，全部非负等待产生的线性响应等于

$$
\operatorname{span}_{\mathbb R}
\{e^{itH}Ae^{-itH}:t\ge0,A\in\mathcal O_0\}
=
\operatorname{span}_{\mathbb R}
\{(i\operatorname{ad}_H)^nA:n\ge0,A\in\mathcal O_0\}.
\tag{32.2}
$$

证明。导数为 $i[H,A]$，它 Hermitian，而 $[H,A]$ anti-Hermitian。左空间有限维闭，对时间的右导数及其迭代仍在其中；右空间对实线性算子 $i\operatorname{ad}_H$ 不变，其矩阵指数使所有时间轨道在其中，给反向包含。$\square$

固定离散时钟还需处理谱差混叠，不能用该导数代替；(32.2) 是响应张成规则，也没有授权直接测量每个交换子。

**命题 32.3（reducing、单向支持与中心的条件）。** 对全部声明 primitives 生成的含幺星代数 $\mathfrak A$，双向逐分支稳定投影属于 $\mathfrak A'$。对酉 $U$ 条件为 $[P,U]=0$，对全部时间 $e^{-itH}$ 为 $[P,H]=0$。对 Kraus $K_\mu$，仅从 $P$ 不泄漏的单向条件是 $(I-P)K_\mu P=0$；若 $P$ 与补空间都不混合，则为 $[P,K_\mu]=0$。若此外已证实际效果代数恰等于 $\mathfrak A$，可观测的 reducing 投影恰位于 $Z(\mathfrak A)=\mathfrak A\cap\mathfrak A'$。

证明。把 $K_\mu$ 写成 $P\mathcal H\oplus(I-P)\mathcal H$ 的四角，单向条件消一个角，reducing 消两个角，后者等价交换。与全部 generators 及其伴随交换等价于与生成星代数交换。可观测条件再取交即中心；未证明实际效果等于 primitive 代数时只能取实际效果空间与 commutant 的交，不能先宣称中心。$\square$

在标准 $d=e=2$ 固定时钟、完整低仪器合同中，全部低矩阵迫使 commutant 元素形如 $I_A\otimes Q$。定理 14.1 的实际效果代数也等于 primitive 星代数：实际历史效果在后者中，而每个 $W(\Delta)$ 和低 primitive 都在该定理列出的代数中，给两边包含。于是稳定高投影精确分类为：

| 本章时钟类，模 $2\pi$ | commutant 的高层部分 | 稳定 $Q$ |
| --- | --- | --- |
| 32 · $0$ | $B(\mathbb C^4)$ | 任意高层正交投影 |
| 32 · $\pm2\pi/3$ | 完整 Fourier 对角代数 $\mathcal D_F$ | 任意完整 Fourier 标签子集 |
| 32 · 其余 | $\mathbb CP_{00}\oplus\mathbb CI_{\mathrm{nonzero}}$ | 零标签与非零三标签这两个整块的任意并 |

这是对三种代数直接取 commutant：全低矩阵移除低层重数，$\mathcal D_F$ 在高层的 commutant 仍为 $\mathcal D_F$，$\mathbb C\oplus M_3$ 的 commutant 是两个标量块。

可观测 membership 不保证稳定。在 $\Delta=\pi$，$I_A\otimes P_{10}$ 属于轨道效果代数，但初态 $|10,p_{10}\rangle=u$ 在三循环上受 $W(\pi)=2J_3/3-I$ 作用，原标签幅为 $-1/3$，另两标签幅为 $2/3$，所以该 projection 权重从一降为 $1/9$。反向在 $\Delta=2\pi$，$W=I$，任意 $I_A\otimes Q$ 稳定，但非标量高投影不在 $B_4\otimes I_4$ 的效果空间中。稳定且不可读、可读且不稳定都存在；这些是操作合同的代数结论，不识别物理粒子。

## 33. 合法地址对的有限代数与声明的无限完成

§31 的有限 density kernel 可以取所有地址对；若要求沿合法递归保持矩阵单位乘法，哪些地址对能够共同延伸是另一个问题。本节固定单位位及初始接缝零，计数所有合法开放前缀，不按正数 End 筛选。

**定理 33.1（前缀数与同终态 AF 嵌入）。** 令 $W_{L,s}$ 为长度 $L$、终态 $s$ 的合法窗前缀，$p_{L,s}=|W_{L,s}|$。则

$$
(p_{L,0},p_{L,1})=(1,0)B^L
=(F_{3L+1},F_{3L}),\qquad
B=\begin{pmatrix}3&2\\2&1\end{pmatrix},
$$

$$
|W_L|=F_{3L+2},\qquad
A_L=M_{p_{L,0}}\oplus M_{p_{L,1}}.
\tag{33.1}
$$

零大小块略去，故 $A_0=\mathbb C$。对同终态 $u,v$，

$$
i_L(E_{uv})=\sum_{e:\operatorname{src}(e)=\operatorname{end}(u)}E_{ue,ve}
\tag{33.2}
$$

给保持单位的忠实星嵌入，包含重数矩阵为 $B$。

证明。§27 的边表给转移数 $3,2;2,1$。$B=K^3$，$K=\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$；由 Fibonacci 递推归纳 $K^n$ 的首行为 $(F_{n+1},F_n)$，给 (33.1)，$L=0$ 直接为 $(1,0)$。$B$ 是 seam 路径计数矩阵，不是组成坐标的 $S$。

矩阵单位相乘时，中间新前缀相等迫使旧前缀和实际末边都相等，故 (33.2) 保持 $E_{uv}E_{ab}=\delta_{va}E_{ub}$；伴随交换两指标，所以也保持伴随。每个旧块有后继，压缩到任一副本可读回原块，故单射。每个新前缀有唯一旧前缀与末边，所以旧总单位映成新总单位。目标终态 $t$ 中旧块 $s$ 出现 $B_{s,t}$ 份，维数恰为 $\sum_sp_{L,s}B_{s,t}=p_{L+1,t}$。$\square$

定义含幺 AF 极限 $A=\varinjlim(A_L,i_L)$，标准包含记为 $j_L$。这个模型保留合法前缀替换、共同边细化、乘法、伴随和矩阵正序；它没有授予每个抽象算子的实际控制权限。此具体构造属于 Bratteli 同终态矩阵单位框架，§38 的 Exel–Renault 来源给标准框架的精确范围。

**命题 33.2（全矩阵障碍仅限含幺星嵌入）。** 全前缀矩阵的第一非零层是 $M_5$，下一层为 $M_{21}$；不存在含幺星嵌入 $M_5\to M_{21}$。但可恢复 isometric CPTP 编码、固定 Hilbert 空间的 cylinder refinement、nonunital corner embedding 均可存在。

证明。含幺星同态 $M_n\to M_m$ 把 $n$ 个最小对角矩阵单位送到等秩、互相正交投影：等秩由两方向矩阵单位部分等距性得到；投影和为 $I_m$，故 $m=nr$。反向 $a\mapsto a\otimes I_r$ 给充分性。$5\nmid21$，所以该含幺嵌入不存在。直接共同延伸不同终态也失败：$[2]$ 的五后继与 $[5]$ 的三后继只共有 null、$[3]$、$[5]$；交叉矩阵单位沿这三标签延伸再乘回伴随，只恢复零态那边三个子投影，而不是全部五个。

任意等距 $V:\mathbb C^n\to\mathbb C^m$，$m\ge n$，仍给 CPTP 编码 $\rho\mapsto V\rho V^*$；固定 density $\tau$ 后，解码

$$
\sigma\mapsto V^*\sigma V+
\operatorname{Tr}[(I-VV^*)\sigma]\tau
$$

是 CP、TP，并在编码像上精确恢复。正交 complement 的 trace-and-prepare 与 compression 各为 CP，其迹和为原迹，证明不需 $n\mid m$。

在一个事先选择的来源 Hilbert 表示上，cylinder multiplication projections 直接满足 $P_u=\sum_eP_{ue}$。这是同一空间的正交分割，给 diagonal function algebra 的含幺细化，不是 $\mathbb C^{W_L}$ 与 $\mathbb C^{W_{L+1}}$ 的全矩阵含幺嵌入。$\square$

还可每次只选 null 后继，$V_L|u\rangle=|u[\mathrm{null}]\rangle$，得到全矩阵的忠实 corner maps $a\mapsto V_LaV_L^*$。旧单位只映到选定 null 子空间的投影，因此 nonunital。Hilbert 直极限有最终全 null 的合法无限地址为基，是可数的 separable 来源空间 $\mathcal H_{\mathrm{ev}}$。任意有限组这样的地址在某共同层出现，故角矩阵并包含所有有限支撑矩阵；它们的范数完成恰为 $\mathcal K(\mathcal H_{\mathrm{ev}})$。无限维 identity 不在其中。只加 $\mathbb CI$ 仍不能容纳一般无限秩且无限余秩的 cylinder projections：若投影 $P=K+cI$，其 Calkin 像是 scalar projection，$c$ 必为零或一，分别要求 $P$ 或 $I-P$ compact，从而有限秩。一般 cylinder projections 应放在 multiplier $B(\mathcal H_{\mathrm{ev}})$。这个 corner 完成与含幺同终态 AF 完成不同。

**定义 33.3（尾等价与全配对的分离）。** 令 $\Omega_0$ 为所有初态零的无限合法路径，带紧 cylinder 拓扑。AF 使用等深 tail equivalence

$$
R_{\mathrm{tail}}=
\{(x,y):\text{某共同深度之后的实际边尾部完全相同}\}.
$$

其组合为 $(x,y)(y,z)=(x,z)$，逆为 $(y,x)$；拓扑取有限深度尾关系的 inductive-limit topology。每类至多可数，因为只有有限前缀替换。全 null 与全 $[3]$ 流不尾等价，所以 $R_{\mathrm{tail}}\ne\Omega_0^2$。

若选择全 pair groupoid $\Omega_0^2$，解析结构必须另定。将 $\Omega_0$ 离散化，有限支撑核按计数卷积作用于 $\ell^2(\Omega_0)$，其范数完成是 $\mathcal K(\ell^2(\Omega_0))$；$\{\mathrm{null},3\}^{\mathbb N}\subseteq\Omega_0$ 已不可数，故这个 Hilbert 空间不可分。另一选择保留紧拓扑，并指定 full-support Radon 概率测度 $\mu$，例如各合法出边均有正概率的 Markov 测度。连续核按

$$
(f*g)(x,z)=\int f(x,y)g(y,z)\,d\mu(y),\qquad
f^*(x,y)=\overline{f(y,x)}
$$

作用于 $L^2(\Omega_0,\mu)$；它们是 Hilbert–Schmidt 从而 compact，continuous rank-one kernels 又因连续函数在 $L^2$ 稠密而范数稠密于全部 compacts，故完成为 $\mathcal K(L^2(\Omega_0,\mu))$。nonatomic 情形单点 delta 不给归一化 $L^2$ 向量；无限维 identity 也不属于这个 compact 范数完成。取强闭包会得到另一表示相关的 $B(\mathcal H)$。这些选择均不从地址集推断物理态或唯一测度；§37 只使用已声明的含幺 AF 极限。

## 34. 等深合法相干与相对格点操作的桥

§27 的对象/上下文解释保留尺度 $S^{|w|}$；§33 的共同尾细化恰好使一对地址的尺度相消。这是连接合法相干矩阵单位与几何操作的具体桥。

**定理 34.1（等深相对平移 cocycle）。** 对同长、同终态合法前缀 $u,v$，在 signed 格点上的可逆仿射函数有

$$
\Phi_u\Phi_v^{-1}=T_{D_u-D_v},\qquad
D_{ue}-D_{ve}=D_u-D_v.
\tag{34.1}
$$

对于 $x=uz,y=vz$，定义 $c(x,y)=D_u-D_v$，得到 $R_{\mathrm{tail}}$ 上良定义的连续 additive cocycle，且

$$
c(x,z)=c(x,y)+c(y,z),\qquad
c(x,y)=0\ \Longleftrightarrow\ x=y.
\tag{34.2}
$$

证明。写 $|u|=|v|=L$，直接消去 $S^L,S^{-L}$ 给第一式；共同追加边给两偏移都增加 $S^Ld_e$，得第二式。两个共同尾呈示可细化到同一更深切口，所以 $c$ 与呈示无关。三条尾等价路径也可取同一切口，偏移差相消给 additivity。每个前缀替换 cylinder 双截面上 $c$ 常值，故对标准 AF 拓扑连续。若 $c=0$，等长 $D_u=D_v$，命题 27.3 的证明给 $u=v$，继而 $x=y$。反向显然。$\square$

这里逆函数用于计算相对操作，不声称它保持旧非负域。cocycle 的零核只有 units，也不使其在全群胚上单射：例如固定 $u=[2],v=[3]$，取两个不同合法共同尾，两条不同 arrows 都给 $(1,-1)$。被偏移忽略的 instruction parameters 也会破坏零核结论，所以本节只用裸窗图。

**定理 34.2（任意格点酉表示给忠实兼容的相干解释）。** 选非零 Hilbert 空间 $K$ 和任意 unitary representation $U:\mathbb Z^2\to\mathcal U(K)$，令 $B_U=C^*(U(\mathbb Z^2))$。则

$$
\Theta_L(E_{uv})=E_{uv}\otimes U(D_u-D_v)
\tag{34.3}
$$

给 $A_L\to A_L\otimes B_U$ 的忠实含幺星同态，与 $i_L$ 相容，并延拓为 $\Theta:A\hookrightarrow A\otimes_{\min}B_U$。此忠实性不要求 $U$ 忠实。

证明。矩阵单位中间指标匹配时偏移差相消、$U$ 的乘法律给正确乘积；不匹配时两边都零。伴随改变差号，对角像为 $E_{uu}\otimes I$。更直接地

$$
V_L=\sum_{w\in W_L}E_{ww}\otimes U(D_w)
$$

是 finite diagonal unitary，$\Theta_L(a)=V_L(a\otimes I)V_L^*$。$K\ne0$ 使 $a\mapsto a\otimes I$ 等距单射，故忠实。由 (34.1) 逐矩阵单位得到

$$
(i_L\otimes\mathrm{id})\Theta_L=\Theta_{L+1}i_L.
$$

在有限层的稠密并上这些等距映射一致，故延拓为含幺等距星同态。没有要求 $V_L$ 在极限中收敛。即使 $U$ trivial，矩阵单位标签仍保留所有 $A$ 信息；是否几何动作也区分格点平移是 $U$ 自己的另一忠实性问题。$\square$

因此同终态相干 $E_{uv}$ 可以附带明确相对 lattice action，且共同尾细化、乘法、伴随和 positivity commute。若再选 faithful lattice translations，每个 nonunit tail arrow 附带非恒等平移。这个构造仍没有选择 density、preparation 或 measurement；也没有把任意具体响应块 $P_u\rho P_v$ 自动认作满足矩阵单位乘法的 abstract $E_{uv}$。

**命题 34.3（稳定坐标仅在尾类内注入）。** 置 $\phi=(1+\sqrt5)/2$、$q=2-\sqrt5$、$\ell(a,b)=a-\phi^{-1}b$。$\ell S=q\ell$、$|q|<1$，故无限合法地址有连续编码

$$
\pi(x)=\sum_{j\ge0}q^j\ell(d_{x_j}).
$$

同尾 $x=uz,y=vz$ 满足

$$
\pi(x)-\pi(y)=\ell(D_u-D_v)=\ell(c(x,y)),
$$

所以 $\pi$ 在每个尾等价类内单射。

证明。直接行向量乘法给 $\ell S=q\ell$；有限 digit 集与 $|q|<1$ 给一致收敛及连续性。共同尾以同一 $q^L$ 系数出现并相消。$\phi^{-1}$ 无理，使 $\ell$ 在 $\mathbb Z^2$ 上零核；再用 (34.2) 得单射。这个单射不能升级到全部无限地址：母卷 §§150–151 的同一收缩编码像为 $[-1,\phi]$，而 $\Omega_0$ 有非平凡 clopen cylinder，compact 且不连通。若连续 $\pi$ 全局单射，compact-to-Hausdorff 双射会给到该区间的 homeomorphism，与连通性矛盾。故全局碰撞存在，并由刚证结论必须跨尾类。$\square$

以上桥只处理 equal-depth extension。尺度差、unequal-depth graph-groupoid 和其 cocycle 不在本合同中；本节也不以稳定坐标完成来授予 $J,C$ 的全局连续执行权限。

## 35. 从闭合边界坐标到完全正的条件后继

本卷定理 7.4、10.2 已证明具体 pinching/对角合同的逐分支充分性；波粒事件卷定义 20.5、定理 20.6 已给最小动态效果闭包及其可实现坐标，定理 20.3 给下一效果空间的对偶下降判据。这些既有结果不承诺整个较小量子代数上的 CP 后继。本节只补该实现层，再于 §36 应用于真正的 legal-prefix 系统。

**定理 35.1（CP section 下的逐分支实现判据）。** $\mathcal X,\mathcal Y$ 是有限矩阵代数或有限直和矩阵代数，各用声明的普通矩阵迹之和。设 $E:\mathcal X\to\mathcal Y$ CPTP，存在 CP 线性 section $R:\mathcal Y\to\mathcal X$、$ER=\mathrm{id}_{\mathcal Y}$。则 $R$ 自动 TP。对有限 source instrument $\{J_e\}_e$，各分支 CP、总和 TP，下列逐分支条件等价：

$$
\begin{aligned}
&\text{存在 target instrument 满足 }EJ_e=J'_eE;\\
&EJ_e=EJ_eRE;\\
&\ker E\subseteq\ker(EJ_e);\\
&J_e^\dagger(\operatorname{ran}E^\dagger)
\subseteq\operatorname{ran}E^\dagger.
\end{aligned}
\tag{35.1}
$$

满足时 target branch 唯一，且

$$
J'_e=EJ_eR.
\tag{35.2}
$$

证明。$\operatorname{Tr}R(Y)=\operatorname{Tr}ER(Y)=\operatorname{Tr}Y$，所以 TP。若 intertwining 成立，右复合 $R$ 得 (35.2)，再右复合 $E$ 得第二条件。若第二条件成立，(35.2) 是 CP maps 的复合，且分支和 $E(\sum_eJ_e)R$ TP，故为整个 $\mathcal Y$ 上的合法 instrument，并满足 intertwining；CP 分支与总和 TP 也保证每支次保迹。

第二条件给核包含。反向 $X-REX\in\ker E$，故核包含使 $EJ_e(X-REX)=0$。有限维 Hilbert–Schmidt 迹配对下 $\operatorname{ran}E^\dagger=(\ker E)^\perp$。对全部 $X\in\ker E$、$Y\in\mathcal Y$，等式 $\langle Y,EJ_eX\rangle_{\mathrm{HS}}=\langle J_e^\dagger E^\dagger Y,X\rangle_{\mathrm{HS}}=0$ 恰要求最后的 range 包含。这证明全部等价与唯一性。$\square$

这里合法是 CP、总 TP 和空间类型合法。给定设备另有限制的 primitives、支撑、权限或成本时，仍需证明 (35.2) 可实施；有 CP 公式不自动成为已有 primitive 或廉价控制。

**推论 35.2（记录、参考与全部正概率条件续接）。** 固定允许的有限 instruments，所有动作在声明状态域上合法，选择器只读已保留记录与控制数据。若每支满足 (35.1)，则任意有限 adaptive history $h$ 有 $EJ_h=J'_hE$。对任意有限旁观参考 $B$、可纠缠输入 $\rho$，完整 history register $C$ 有

$$
\begin{aligned}
&\sum_h|h\rangle\langle h|_C\otimes
((EJ_h)\otimes\mathrm{id}_B)(\rho)\\
&\quad=\sum_h|h\rangle\langle h|_C\otimes
(J'_h\otimes\mathrm{id}_B)((E\otimes\mathrm{id}_B)(\rho)).
\end{aligned}
\tag{35.3}
$$

两边每支迹均为 $p_h=\operatorname{Tr}[(J_h\otimes\mathrm{id}_B)(\rho)]$；$p_h>0$ 时以同一概率除得到相同 boundary–reference 条件态。

证明。逐步代入 intertwining 给复合恒等；同一记录使下一选择同一动作。等式张量恒等仍成立，CP 保证任意参考输入的正性。$E$ TP 给每支原概率，正概率归一化给条件态；零概率支没有条件态义务。求 history 正交直和得到 (35.3)。若选择器还读被删 memory 或隐藏权限，则超出假设，须先把该数据并入边界。$\square$

**命题 35.3（pinching 的下降比交换弱）。** 令 $Q(X)=\sum_yP_yXP_y$，输出代数 $\mathcal N=\bigoplus_yB(P_y\mathcal H)$，$E$ 为 block extraction、$R$ 为自然 block inclusion。则 $ER=I_{\mathcal N}$、$RE=Q$，判据为

$$
QJ_e=QJ_eQ
\quad\Longleftrightarrow\quad
J_e^\dagger(\mathcal N)\subseteq\mathcal N.
\tag{35.4}
$$

$QJ_e=J_eQ$ 充分，但更强。

证明。将定理 35.1 的第二、第四条件嵌回原空间即得 (35.4)。固定准备 $J(X)=\operatorname{Tr}(X)\sigma$ 总有 $QJ(X)=\operatorname{Tr}(X)Q\sigma=QJQ(X)$；若 $\sigma$ 有块间相干，$JQ(X)=\operatorname{Tr}(X)\sigma$ 不等于 $QJ(X)$。$\square$

这也保留 §31 的高秩块，而不将其压成单模式。既有定理 7.4 的交换条件在其具体合同下更便于证明，但不是一般下降的必要形式。

**命题 35.4（section 是附加充分假设）。** 非平凡 qubit depolarizing channel $E_p(X)=pX+(1-p)\operatorname{Tr}(X)I/2$，$0<p<1$，没有正 section，但 random-unitary instruments 仍下降。

证明。$E_p$ 线性可逆，唯一右逆为 $Y/p-(1-p)\operatorname{Tr}(Y)I/(2p)$，在 $|0\rangle\langle0|$ 上特征值为 $(1+p)/(2p)$、$-(1-p)/(2p)$，所以不正。对 $J_e(X)=w_eU_eXU_e^\dagger$，$w_e\ge0,\sum_ew_e=1$，酉协变性给 $E_pJ_e=J_eE_p$，直接取 $J'_e=J_e$ 即为 target instrument。$\square$

仅保 branch probability 只检查 $J_e^\dagger I\in\operatorname{ran}E^\dagger$，没有检查全部 boundary effects。直接的 Hadamard 例说明差别：计算基 dephasing $Q$ 将 $|+\rangle\langle+|,|-\rangle\langle-|$ 都送到 $I/2$；单结果 Hadamard branch 的效果为 $I$，两输入事件概率都一，但 $Q\operatorname{Ad}_H$ 分别输出 $|0\rangle\langle0|,|1\rangle\langle1|$。所以这个原概率保留合同没有确定的条件后继。这里 $H|+\rangle=|0\rangle,H|-\rangle=|1\rangle$ 已直接证明反例，不需要外部归属。无 section 时可另找真正 CP $J'_e$ 并核验 intertwining；不能由线性效果闭包直接猜一个未构造的 quantum decoder。

## 36. 有限 legal-prefix AF 层的正边界与实际分支合同

§33 的嵌入保留 observables，§35 的定理保留 states 和 conditional continuations。两者在这里通过普通迹对偶连接，而不是凭相同维数识别两个来源。这里的“细层”是合法窗口长度 $L+1$；它不等于定义 1.1 digits 分解中的高层 $H$。

**定理 36.1（AF 嵌入的 CPTP 边界及所选 section）。** 令 $\mathcal H_{L,s}=\mathbb C^{W_{L,s}}$。每条实际边 $e:s\to t$ 给等距

$$
V_e:\mathcal H_{L,s}\to\mathcal H_{L+1,t},\qquad V_e|u\rangle=|ue\rangle.
$$

固定细终态 $t$ 后，incoming-copy 分解为

$$
\mathcal H_{L+1,t}=\bigoplus_{s,e:s\to t}V_e\mathcal H_{L,s},
\qquad\sum_{s,e:s\to t}V_eV_e^*=I_t.
\tag{36.1}
$$

各层用普通 block trace $\operatorname{Tr}_L=\sum_s\operatorname{Tr}_{\mathcal H_{L,s}}$。则 $i_L$ 的唯一迹对偶为

$$
(E_L\sigma)_s=\sum_{t,e:s\to t}V_e^*\sigma_tV_e,
\qquad E_L^\dagger=i_L,
\tag{36.2}
$$

它 CPTP。另选每个非零源块的出边权重

$$
w_{s,e}\ge0,\qquad\sum_{e:\operatorname{src}(e)=s}w_{s,e}=1,
$$

便有 CPTP section

$$
(R_L\rho)_t=\sum_{s,e:s\to t}w_{s,e}V_e\rho_sV_e^*,
\qquad E_LR_L=\mathrm{id}_{A_L}.
\tag{36.3}
$$

证明。每个新路径唯一给旧前缀和末边，故 (36.1) 是正交铺满分解。由 §33 的嵌入 $i_L(a)_t=\sum_{s,e}V_ea_sV_e^*$，迹循环性给 $\operatorname{Tr}_L[aE_L\sigma]=\operatorname{Tr}_{L+1}[i_L(a)\sigma]$，非退化迹配对给唯一性。式 (36.2) 是 CP compression 之和，(36.1) 使其总迹为 $\sum_t\operatorname{Tr}\sigma_t$，所以 CPTP。式 (36.3) 的 Kraus 为 $\sqrt{w_{s,e}}V_e$，源权重归一化给 TP；压缩到一条 incoming copy 时其它正交副本消失，故 $(E_LR_L\rho)_s=\sum_ew_{s,e}\rho_s=\rho_s$。所有证明张量有限参考恒等仍成立；零维旧块直接略去，$L=0$ 时 $E_0$ 是 $M_3\oplus M_2$ 两迹之和。$\square$

$E_L$ 求同 extension 的 diagonal copies 之和，完整保留同一旧终态前缀之间的矩阵元，删掉不同末边或不同旧终态的 incoming-copy 角。没有除以出度：$E_L(I_{L+1})_s=d_sI_s$，$d_0=5,d_1=3$。若额外平均，会破坏本迹约定的 TP；相对地 $i_L$ 含幺而一般不保持普通迹。

出边权重是新选择数据，而不是计数自动生成的 Born law。例如在 $A_1=M_3\oplus M_2\to A_2=M_{13}\oplus M_8$，每源均匀的 $1/5,1/3$ 给

$$
R_1(\rho)_0=(\rho_0/5)^{\oplus3}\oplus(\rho_1/3)^{\oplus2},
\qquad
R_1(\rho)_1=(\rho_0/5)^{\oplus2}\oplus(\rho_1/3).
\tag{36.4}
$$

维数分别为 $3\cdot3+2\cdot2=13$、$2\cdot3+1\cdot2=8$；粗化分别求五份旧三维块与三份旧二维块的和，恢复原块。section 选择一份细提升，不能反向恢复所有原细态。

**定理 36.2（incoming-copy 下降的精确条件）。** 对固定相邻层的 finite instruments $J_{a,z}:A_{L+1}\to A_{L+1}$，所有声明细态都在动作合法域内、结果 $z$ 可读，target coarse instruments 满足

$$
E_LJ_{a,z}=J'_{a,z}E_L
$$

当且仅当每支有

$$
J_{a,z}^\dagger(i_L(A_L))\subseteq i_L(A_L).
\tag{36.5}
$$

满足时唯一 $J'_{a,z}=E_LJ_{a,z}R_L$，且不依赖 section 权重。对每个 coarse observable $a$，写 $F=J_{a_0,z}^\dagger(i_L(a))$，(36.5) 恰等价于：同一细终态内不同 actual incoming copies 的交叉块为零，同一旧源块的全部对角 copies 相等。具体为

$$
V_e^*F_tV_f=0\quad(e\ne f,\ \operatorname{tgt}(e)=\operatorname{tgt}(f)=t),
$$

$$
V_e^*F_tV_e=b_s\quad(e:s\to t),
\tag{36.6}
$$

其中 $b_s$ 独立于该源的边及其细靶块。

证明。定理 36.1 给 $E_L^\dagger=i_L$ 与 CP section，故定理 35.1 直接给 (36.5)。由正交铺满分解 (36.1)，一个细 observable 在 $i_L(A_L)$ 内，恰是交叉角全零且各旧 $a_s$ 的副本相同，证明 (36.6) 必要且充分；尤其不能漏掉不同细终态中同源副本的相等。只需在 coarse matrix-unit basis 上检查。若已经下降，对任一 section $R$，$E_LJ_{a,z}R=J'_{a,z}E_LR=J'_{a,z}$，所以权重无关；未下降时这个 CP 复合虽可定义，却一般依赖 $R$，不能重现所有细输入。$\square$

**命题 36.3（正面提升仪器与 edge-conditioned 失败）。** 对 coarse Kraus $K_{a,z,\mu}\in A_L$、$\sum_{z,\mu}K_{a,z,\mu}^*K_{a,z,\mu}=I_L$，提升 Kraus 为 $i_L(K_{a,z,\mu})$ 得一族下降的 fine instruments，coarse successor 就是原 Kraus instrument。

证明。含幺星同态保持 Kraus 总归一化，且

$$
J_{a,z}^\dagger(i_L(a))
=\sum_\mu i_L(K_{a,z,\mu})^*i_L(a)i_L(K_{a,z,\mu})
=i_L\!\left(\sum_\mu K_{a,z,\mu}^*aK_{a,z,\mu}\right).
$$

故满足 (36.5)，唯一性给原 coarse successor。这个子类可在同终态块内部执行真正 coherent matrices；它不是所有直和代数 CP instruments 的穷尽分类，特别没有穷尽跨 coarse central blocks 的经典转移。$\square$

Fine 合法不自动下降。取 $L=1$、旧前缀 $u=[\mathrm{null}],v=[2]$，两条 $0\to0$ 边 $e_1=\mathrm{null},e_2=2$。fine block unitary 只交换 $|ue_2\rangle,|ve_2\rangle$，其它基向量不动。$|ue_1\rangle\langle ue_1|$ 与 $|ue_2\rangle\langle ue_2|$ 原来都粗化为 $|u\rangle\langle u|$，作用后却分别粗化为 $|u\rangle\langle u|$ 和 $|v\rangle\langle v|$，所以这个 edge-conditioned swap 不满足 (36.5)。这是有限矩阵合同中的反例，不新增设备权限。

**命题 36.4（全域正右逆不能创造跨旧中心块相干）。** 令 $Z_s$ 为 $A_L$ 的中心块单位，$Q_s=i_L(Z_s)$。任何线性正映射 $R:A_L\to A_{L+1}$，只要在整个 coarse algebra 上满足 $E_LR=I$，则对所有正输入有

$$
R(\rho)=\sum_sQ_sR(\rho)Q_s.
\tag{36.7}
$$

证明。输入 $\rho_s\ge0$ 只在旧块 $s$，$B_s=R(\rho_s)\ge0$。对 $r\ne s$，迹对偶给 $\operatorname{Tr}(Q_rB_s)=\operatorname{Tr}(Z_rE_LB_s)=0$。正性使 $\|B_s^{1/2}Q_r\|_{\mathrm{HS}}^2=0$，故 $B_sQ_r=Q_rB_s=0$，即 $B_s=Q_sB_sQ_s$。把一般正输入按旧中心块相加，线性性给 (36.7)。证明只需正性，无须 CP，但全域右逆与线性性不可删除。$\square$

这不是所有 fine states 的相干禁令。例如 diagonal extraction $M_2\to\mathbb C\oplus\mathbb C$ 的任何全域正右逆在 $(1/2,1/2)$ 输出 $I/2$，因为两个极端输入的正 lifts 只能支撑于各自坐标；但该特定 coarse state 也有 coherent lift $|+\rangle\langle+|$。准备 map $(a,b)\mapsto(a+b)|+\rangle\langle+|$ 是 CPTP，却只在此特定输入正确，并非全域右逆。

允许的旧块内部 multiplicity coherence 是另一回事。按

$$
\mathcal H_{L+1,t}\cong\bigoplus_s
(\mathcal H_{L,s}\otimes\mathbb C^{B_{s,t}}),
$$

为每源选 $\zeta_{s,t}\ge0$、$\sum_t\operatorname{Tr}\zeta_{s,t}=1$，则

$$
(R_L^\zeta\rho)_t=\bigoplus_s\rho_s\otimes\zeta_{s,t}
\tag{36.8}
$$

仍是 CPTP section：tensoring 固定 positive matrices 完全正，总 trace 因归一化不变，$E_L$ 对 multiplicity 作 partial trace 得 $\rho_s$。非对角 $\zeta_{s,t}$ 保留同一旧源、同一细终态的 copy coherence，符合 (36.7)；相同 diagonal weights 不规定这些 coherent entries。

若所有实际细分支满足 (36.5)，推论 35.2 直接给完整 records、任意有限 reference 和正概率 conditional boundary。section 权重、量子 preparation、fine Kraus 的实际可用性及成本仍是另行合同。这是有限层 legal coherent recursion 的正面实现，不声称无限 AF 的每个元素或 §29 的每个 geometric operation 都物理可用。

## 37. 相容有限正密度与无限 AF 态，及其相干边界

§36 的 $E_L$ 不需把所有 finite-prefix Hilbert spaces 同时放进一个预设量子空间。其相容状态可以直接完成为 §33 的 AF 态；这与 full-pair wavefunction 和固定表示中的正规 density 不同。

**定理 37.1（相容态的双射与拓扑）。** 对每层 positive block densities $\rho_L=(\rho_{L,s})_s$，采用总 trace 一而不要求各块分别 trace 一。则 restriction 给仿射双射

$$
S(A)\cong
\left\{(\rho_L)_{L\ge0}:\rho_{L,s}\ge0,
\ \sum_s\operatorname{Tr}\rho_{L,s}=1,
\ E_L\rho_{L+1}=\rho_L\right\}.
\tag{37.1}
$$

$S(A)$ 的 weak-star topology 与右侧 finite-state-space product topology 同胚。

证明。AF 态限制到每个 $j_L(A_L)$ 给唯一普通 block density。$j_{L+1}i_L=j_L$ 及 $E_L^\dagger=i_L$ 给相容式。反向在 dense algebraic union 定义 $\varphi(j_L(a))=\operatorname{Tr}_L(\rho_La)$；将任意两个表示送到共同更高层，重复迹对偶证明值一致。各层 positive normalized，所以 $|\varphi(a)|\le\|a\|$；唯一连续延拓到 $A$，仍 positive normalized。若两态有限层限制一致，稠密性使其全域一致。构造保持凸组合。

weak-star 收敛使每个有限层 density 收敛。反向，所有态范数一，将任意 $a\in A$ 范数逼近到固定 finite level，误差对态统一受控，再用该层收敛即得 weak-star 收敛。因此映射及逆均连续。此处固定层的条目、trace-norm、弱收敛等价；不声称全 AF 态的范数收敛。$\square$

给定一层 density 与全部未来 section 选择，递推 $\rho_{L+1}=R_L\rho_L$，旧层由连续 $E$ 粗化，便得一个相容无限延拓。固定种子和 section 族时该递推唯一；只给相容条件时不唯一。

**命题 37.2（指定 Perron trace）。** 令

$$
\phi=\frac{1+\sqrt5}{2},\qquad
\lambda=2+\sqrt5=\phi^3,\qquad
r=(\phi,1)^{\mathsf T},\qquad Br=\lambda r,
$$

$$
c_{L,s}=\lambda^{-L}r_s/\phi,
\qquad\tau_L(a)=\sum_sc_{L,s}\operatorname{Tr}(a_s).
\tag{37.2}
$$

这些泛函相容，定义 $A$ 上的 trace state $\tau$。

证明。$\sum_sp_{L,s}c_{L,s}=\lambda^{-L}(1,0)B^Lr/\phi=1$，所以归一化。$\sum_tB_{s,t}c_{L+1,t}=c_{L,s}$ 给嵌入相容，finite positive traces 延拓仍 trace。每条 $e:s\to t$ 若选 $w_e=r_t/(\lambda r_s)$，其出边权重和由 $Br=\lambda r$ 为一，且 $w_ec_{L,s}=c_{L+1,t}$；非相干 section (36.3) 从根态一就生成这个 trace density。$\square$

这是一个明确选择的数学态及边权，不推断来源的物理概率律，也不需要主张 trace 唯一。

**定理 37.3（全部 cylinder probabilities 不决定合法-tail 相干）。** 取同为终态零的一窗前缀 $u=[2],v=[3]$，令

$$
X=E_{uv}+E_{vu}\in A_1,\qquad 0<\eta<1,
\qquad\varphi_\pm(a)=\tau((I\pm\eta X)a).
\tag{37.3}
$$

两态都是 $\tau$-GNS 表示中的正规态，具有相同的全部长度、全部 cylinder probabilities，却有

$$
\varphi_\pm(X)=\pm2\eta/\lambda,
\qquad\tau(X^2)=2/\lambda.
\tag{37.4}
$$

证明。$X=X^*$、$\|X\|=1$、$\tau(X)=0$，$X^2=E_{uu}+E_{vv}$。$I\pm\eta X\ge(1-\eta)I$，迹性将 $\tau((I\pm\eta X)a)$ 写成 $\tau((I\pm\eta X)^{1/2}a(I\pm\eta X)^{1/2})$，故 positive normalized。它们由有界正 density 给 $\tau$-GNS 的向量态，因而正规。

$X_L=i_{L-1}\cdots i_1(X)$ 在每层仍 diagonal entries 全零。$L\ge1$ 的具体 densities 为

$$
\rho_{L,s}^{\pm}=c_{L,s}(I_{p_{L,s}}\pm\eta X_{L,s}),\qquad\rho_0^\pm=1.
\tag{37.5}
$$

copy 求和与 (37.2) 给相容性，星嵌入保范数保证正性。任意 $z\in W_{L,s}$ 的 cylinder probability 都是 $c_{L,s}$；但 $\tau(X^2)=2c_{1,0}=2/\lambda$，给 (37.4)。$\square$

具体地，各层 diagonal algebras $D_L$ 通过 cylinder refinement 嵌入，范数完成 $D\cong C(\Omega_0)$：局部常值 cylinder functions 分离路径并稠密。所有 cylinder probabilities 只决定 AF 态在 $D$ 上的限制，即一个路径 probability measure。各层 diagonal pinching 与 $i_L$ 交换，延拓为 UCP projection $\Delta:A\to D$；任意路径测度 $\mu$ 可选 diagonal extension $a\mapsto\int\Delta(a)d\mu$。定理 37.3 证明这个 extension 不是同一 measure 的唯一 AF 态。选择 measure、选择 coherent state、选择统一 section 是不同数据。

**命题 37.4（旧终态的部分同步与整个 cylinder 的不等价）。** 取同深 $L\ge1$ 的 $u,v$，旧终态分别零、一，记 $P_u=j_L(E_{uu})$、$P_v=j_L(E_{vv})$。共用下一打印标签 null、$[3]$、$[5]$，各用自己的实际 typed edges，则 $A_{L+1}$ 内有

$$
V=E_{u\mathrm{null},v\mathrm{null}}+E_{u3,v3}+E_{u5,v5},
$$

$$
V^*V=P_v,\qquad VV^*=P_{u\mathrm{null}}+P_{u3}+P_{u5}=:Q<P_u.
\tag{37.6}
$$

但 $P_u,P_v$ 在 AF algebra 内不 Murray–von Neumann 等价。

证明。三个后继中每对具有相同新终态，所以矩阵单位合法；不同末窗正交。状态一只有这三种后继，故 $V^*V$ 覆盖全部 $P_v$；状态零还缺 $u2,u25$ 两个非零子投影，故 $VV^*=Q<P_u$。trace 给 $\tau(P_u)=\lambda^{-L}$、$\tau(P_v)=\lambda^{-L}/\phi$，不相等。若整个 cylinders 等价，部分等距的 trace 恒等会强迫这两个值相等，矛盾。实际 $\tau(Q)=\tau(P_v)$，剩余 trace 为 $\lambda^{-L}(1-\phi^{-1})>0$。$\square$

所以不同旧终态不是 AF 极限中永久的 coherence 禁区。令 $Y=V+V^*$，旧 cylinders 正交使 $V^2=0$、$Y^2=Q+P_v$、$\|Y\|=1$。全部后续 diagonal entries 仍零，故 $\psi_\pm(a)=\tau((I\pm\eta Y)a)$ 是共享全部 cylinder probabilities 的态，且

$$
\psi_\pm(Y)=\pm2\eta\lambda^{-L}/\phi.
$$

这项相干已在 $L+1$ 层合法存在，反向 $E_L$ 舍去它。两种 fine densities 都粗化到相同 $\tau_L$；由命题 36.4，它们不能从该 coarse input 经任何全域线性正右逆创造，可作为 $L+1$ 层种子再向后延拓。单态 coherent lift 与统一 recovery channel 因此没有矛盾；$X,V,Y$ 的 abstract membership 也不授予实际测量权限。

**命题 37.5（finite densities 不保证固定 trace 表示中的正规性）。** 最终 null 的地址 $\omega=[2][\mathrm{null}][\mathrm{null}]\cdots$ 给相容 atomic state，但它不是固定 $\tau$-GNS closure 上正规态的限制。

证明。$u_L=[2][\mathrm{null}]^{L-1}$，取 $\sigma_{L,0}=|u_L\rangle\langle u_L|$、$\sigma_{L,1}=0$，$\sigma_0=1$。每次只有同 null extension 的一份 compression 非零，所以 $E_L\sigma_{L+1}=\sigma_L$，定理 37.1 给态 $\omega_*$。nested cylinders $P_L=j_L(E_{u_Lu_L})$ 满足 $P_{L+1}\le P_L$、$\omega_*(P_L)=1$，却有 $\tau(P_L)=\lambda^{-L}\to0$。在 $\tau$-GNS 的 dense vectors $a\Omega_\tau$ 上，迹性给

$$
\|P_La\Omega_\tau\|^2
=\tau(a^*P_La)=\tau(P_Laa^*)
\le\|a\|^2\tau(P_L)\to0.
$$

投影 uniformly bounded，故 $P_L$ strongly 趋零；正规态在这组递减投影上趋零，与 $\omega_*(P_L)=1$ 矛盾。$\square$

相容性定义的是抽象含幺 AF 态，每态可有自己的 GNS 向量表示；它没有指定所有态共同使用的无限 trace-class density，也没有给全 $\Omega_0^2$ kernel、rank-one wavefunction 或 canonical physical measure。§34 的相干几何桥、§36 的 finite-level conditional instrument bridge 和本节的 state completion 分别保持不同信息，必须在选定 representation、state 与 allowed controls 后一起使用。

## 38. 本补充的来源与适用边界

本补充使用标准框架和上文的普通证明；组合、适配或重述这些来源不构成研究原创性的证据。其来源承担的范围如下。

1. 本卷定义 1.3、命题 2.2–2.3、命题 8.2、定理 11.2、定理 14.1 提供实际 instruments、采样更新、三循环及完整低仪器效果代数；§§31–32 在其精确合同上应用，受限一次读出例另行定义。波粒事件卷[定义 20.5、定理 20.6 和定理 20.3](RECURSIVE_RELATIONAL_OBSERVATION_WAVE_PARTICLE_EVENTS.md#20-事件统计成为动态边界的充要条件)提供线性闭包和条件坐标下降，§35 增加显式 CP 实现条件，而不重复该闭包证明。
2. 母卷[§104](FIBONACCI_ATOMIC_RELATION_GENERATION.md#104-规范三位窗口正值-end-与任务相关的联合未来商)、[§149](FIBONACCI_ATOMIC_RELATION_GENERATION.md#149-五窗包含细化与组成层的四相旋转)、[§§150–151](FIBONACCI_ATOMIC_RELATION_GENERATION.md#150-共轭收缩坐标上的五窗仿射递归固定点)给规范来源合同、五 offsets、矩阵作用与收缩完成。规范编码存在唯一性沿用 standard Zeckendorf premise；[canonical-window 卷在修订 `30fe08bcd4f4f4ccd1a4dc37d75234560f06c34b` 的 §§13.1–13.4](https://github.com/the-omega-institute/trureturing/blob/30fe08bcd4f4f4ccd1a4dc37d75234560f06c34b/docs/develop/theory/FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md)明确有限来源、位次与独立 End certificate。它们不提供未知高位为空的裸 prefix 认证。
3. Emily Riehl, [*Category Theory in Context*](https://emilyriehl.github.io/files/context.pdf), Example 4.1.13，印刷页 137：quiver 的自由范畴由有限 composable paths 与 empty identities 构成，quiver map 唯一延拓到 functor。Example 4.1.15，页 138，描述形式加逆的 groupoid completion，不承诺任意范畴忠实嵌入其 completion。§27 使用前一 universal property；裸 affine 忠实性由命题 27.3 自证。
4. J. J. M. Rutten, [*Universal coalgebra: a theory of systems*](https://www.cs.cornell.edu/courses/cs6861/2024sp/Handouts/Rutten.pdf), *TCS* 249 (2000), 3–80，Theorem 10.1、Examples 10.2，印刷页 43–44：该文所定义的 polynomial Set functors 有 final systems，列出 streams、termination 与 tree examples。§28 的具体 two-sorted legal-stream finality 由逐前缀展开证明，$10+X$ initial algebra 则由 finite-term 分解证明；没有把这两个具体模型当作该文直接陈述。
5. Ruy Exel and Jean Renault, [*AF-algebras and the tail-equivalence relation on Bratteli diagrams*](https://arxiv.org/abs/math/0307228), Lemmas 2.4–2.5，页 5–6，规定不同 terminal vertices 为零及同 terminal matrix-unit 乘法；Theorem 3.4 前的 refinement 与该定理，页 8，给同 appended edge 的矩阵单位细化及 incidence inductive limit。§4，页 9–11，使用 equal-depth tail relation 的 inductive-limit topology 和 counting Haar system，明确区别于 product-subspace topology。§§33–34 的 finite FIB 实现与 relative-translation cocycle 有本章证明；该来源不提供全 pair kernels 或唯一 state/measure。
6. Kavruk–Paulsen–Todorov–Tomforde, [*Quotients, Exactness and Nuclearity in the Operator System Category*](https://arxiv.org/abs/1008.2811v2), Proposition 3.1、Definition 3.2，页 5–6，kernel 为非零 CP map 的核，等价地 UCP map 的核，且 nonunital；Proposition 3.4、Definitions 3.5 和 Proposition 3.6，页 7，规定 quotient 的 Archimedean matrix cones 与 universal property。§32 因而不把含单位的 observational subspace 作非零 operator-system quotient kernel。
7. Mawhinney–Todorov, [*Inductive limits in the operator system and related categories*](https://arxiv.org/abs/1705.04663v1), Theorem 4.11、Proposition 4.13，页 27–28，给 UCP connecting maps 的 operator-system inductive limits，以及各 map 为 complete order embedding 时的 limit embedding。若保留的只有实际 operator systems，这提供另一框架；它不授权 multiplication 或 physical realization，其所用类别允许 noncomplete systems，norm completion 仍须单独声明。本补充的 AF 模型则已直接具有星同态和指定 C* norm completion。

对象码、typed 操作、几何评价与实际事件保持的是各自明确的信息。原字的单孔 affine action 可忠实保存合法裸路径，却不能认证已被抹去的非法历史；程序码须经过额外 interpreter 才执行其 declared operations；共同尾相干可携带相对格点操作，有限 positive boundary 只有在逐分支下降条件下保留全部 declared conditional continuations。无限相容态的存在不选择物理来源或全部 controls，也不提供未经声明的全 pair completion。以上均为普通数学陈述及证明，不具有编译形式化或物理可达性结论；有限/infinite、正常形/history、probability/conditional state 与 signed/natural permissions 的区别是各结论的假设组成部分。

## 追加锚（本行以下为增补区）
