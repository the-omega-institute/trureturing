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
