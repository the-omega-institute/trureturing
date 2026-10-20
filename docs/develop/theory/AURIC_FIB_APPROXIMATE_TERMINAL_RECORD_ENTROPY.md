# AURIC FIB 近似终端记录熵

## 1. 对象、来源与结论范围

**约定 1.1（数学范围与来源）。** 本卷研究固定测量仪器的嵌入三能级恢复，只计最终保留的完整经典解码视图的条件 Shannon 熵。物理载体空间为 $H_{\mathrm{phys}}=\mathbb C^5$；除概率空间与紧群外，Hilbert 空间均为有限维复空间。记 $M_d=\mathcal B(\mathbb C^d)$，$\operatorname{Ad}_U(X)=UXU^\dagger$。信道均为复线性、完全正且保迹的映射（CPTP）。钻石范数不乘 $1/2$，并对所有未触碰的有限维参考系统取上确界。

模型、实际前向谱比较、小球估计与随机壳舍入取自《AURIC FIB approximate online recovery memory》（以下记为 AOM）：模型见其定义 2.1、定理 2.2；全空间回缩见其第 3 节；实际谱与小球见其第 6—7 节；舍入见其定义 8.1、引理 8.2—8.3。AOM 的模型拥有文献为 [OWN]，五窗口 Kraus 来源为 [FIVE]，两者的固定修订标识为 `55208d97e98beb34acc9db6cdcd1c9da16331362`。本卷逐项写出所需数学接口及推导。Gibbs 变分不等式、KL 非负性、Laplace 分层积分与信息不超过离散熵均为标准方法；它们在此用于同一个实际历史与终端视图的联合分布。

外部谱隙输入按假设 3.2 使用；AOM 将其归于 Bourgain–Gamburd [BG] 的代数稠密生成元定理。本卷的条件结论不构成对该外部文献接口的独立认证，不给出谱隙数值，也不作世界优先权或文献穷尽性主张。

**定义 1.2（实际仪器与嵌入）。** 在 $H_{\mathrm{phys}}$ 的有序基 $(e_0,e_1,e_2,e_3,e_4)$ 中，置

$$
u=(e_0+e_3)/\sqrt2,\qquad v=(e_1+e_4)/\sqrt2,\qquad z=e_2,
\qquad R=\operatorname{span}\{u,v,z\}.
$$

令 $B:\mathbb C^3\to H_{\mathrm{phys}}$ 的三列为 $u,v,z$，$P_R=BB^\dagger$，$\iota(X)=BXB^\dagger$。固定的未旋转与实际测得 Kraus 算子分别为

$$
\begin{aligned}
K_0&=|u\rangle\langle e_0|+2^{-1/2}|v\rangle\langle e_2|+|z\rangle\langle e_4|,\\
K_1&=|u\rangle\langle e_1|+2^{-1/2}|v\rangle\langle e_2|+|z\rangle\langle e_3|,\\
A_0&=(\sqrt3K_0+iK_1)/2,\qquad A_1=(iK_0+\sqrt3K_1)/2.
\end{aligned}
$$

环境有正交基 $f_0,f_1$，每轮重新准备纯态 $f_0$。等距扩张为 $x\mapsto K_0x\otimes f_0+K_1x\otimes f_1$，并延拓为整个系统—环境空间上的酉作用。离开环境的测量基固定为

$$
(\sqrt3f_0-if_1)/2,\qquad(-if_0+\sqrt3f_1)/2.
$$

这里 $\theta=\pi/6$ 是这个测量基的参数；它不是另一种切换模型中的布居参数 $\eta$。本卷不交换这两类参数，也不把实际字母换成可自由选择的群生成元。

在三能级坐标中定义

$$
U_0=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix},\quad
U_1=\begin{pmatrix}0&1&0\\0&0&1\\1&0&0\end{pmatrix},\quad
W=U_0^\dagger U_1=\begin{pmatrix}0&1&0\\1&0&0\\0&0&1\end{pmatrix},
$$

$$
V_0=(\sqrt3U_0+iU_1)/2=U_0e^{i\pi W/6},\qquad
V_1=(iU_0+\sqrt3U_1)/2=V_0W.
$$

**命题 1.3（实际公平历史与相对相位）。** 实际仪器在 $M_5$ 上合起来保迹，并且

$$
K_jB=BU_j/\sqrt2,\qquad A_jB=BV_j/\sqrt2.
$$

每个 $V_j$ 均酉。对任意嵌入三能级输入及其与有限参考系统的任意纠缠，每轮实际标签都是条件公平的新比特。长度 $n$ 的实际历史 $\mathsf H_n=h=(h_1,\ldots,h_n)$ 的概率为 $P_n(h)=2^{-n}$，分支为 $2^{-n/2}BQ_h$，其中

$$
\begin{aligned}
\xi&=(1,1,1)^{\mathsf T}/\sqrt3,\qquad T=\xi^\perp,\qquad\lambda=e^{i\pi/6},\\
Q_h&=V_{h_n}\cdots V_{h_1}=\lambda^n\oplus G_h
\quad\text{于 }\mathbb C\xi\oplus T,\\
g_j&=V_j|_T,\qquad G_h=g_{h_n}\cdots g_{h_1},\qquad
F_h=\lambda^{-n}G_h.
\end{aligned}
$$

空历史给出恒等矩阵。在 $T$ 的正交基

$$
f_1=(1,-1,0)^{\mathsf T}/\sqrt2,\qquad
f_2=(1,1,-2)^{\mathsf T}/\sqrt6
$$

中，实际矩阵为

$$
A:=g_0=\frac14\begin{pmatrix}\sqrt3-i&3+i\sqrt3\\3-i\sqrt3&-\sqrt3-i\end{pmatrix},
\quad J=\begin{pmatrix}-1&0\\0&1\end{pmatrix},\quad g_1=AJ,
\quad\det g_0=-1,\quad\det g_1=1.
\tag{1.1}
$$

证明。两个未旋转效应分别为 $\operatorname{diag}(1,0,1/2,0,1)$ 与 $\operatorname{diag}(0,1,1/2,1,0)$，其和为 $I_5$，故上述扩张等距并有酉延拓。测量基取内积正好产生 $A_0,A_1$；旋转的交叉项相消，故对任意复矩阵 $X$ 有 $\sum_jA_jXA_j^\dagger=\sum_jK_jXK_j^\dagger$。对 $u,v,z$ 逐列作用给出限制式。由于 $W=W^\dagger=W^{-1}$，$V_0$ 与 $V_1$ 酉，限制效应均为 $I_3/2$。每次输出仍在 $R$，所以即使附带参考系统，每个前缀之后的下一标签也以概率 $1/2$ 出现；归纳即得实际先验 $2^{-n}$。置换 $U_j$ 固定 $\xi$，故 $V_j\xi=\lambda\xi$，且 $T$ 为约化子空间。在所列基中限制得到 (1.1)，其行列式给出最后两式。公平性只在嵌入输入上主张。相位 $\lambda^{-n}$ 是 $T$ 相对于共同方向 $\xi$ 的相位，不能作为不可见整体相位删去。$\square$

## 2. 完整终端视图与全空间解码

**定义 2.1（允许的终端方案）。** 固定整数 $n\ge0$ 与 $0<\varepsilon<1/4$，重复定义 1.2 的同一仪器 $n$ 次，只在终点作一次量子校正。轮间只允许经典处理，不作中途量子反馈、后选择、参考读取，不保留环境，也不另有依赖量子输入的旁信息。

共享种子 $S$ 可有有限或任意标准 Borel 分布，独立于整个实际历史及输入，其值免费提供给控制器与解码器。给定 $(S=s,\mathsf H_n=h)$，任意可测随机终端核 $p_s(y\mid h)$ 生成离散的完整终端解码视图 $Y$。允许有限、可数，以及具有可测可数索引的依种子而变的字母表。后一种情形按每个种子的可测一一标号嵌入 $\mathbb N$，不存在的标签补零概率；这种标号保留条件视图及其熵。

所有终点仍保留的历史相关变量、私有状态、程序或控制选择、档案、缓冲区、时钟数据、解码输入和随机带残留都属于 $Y$。已丢弃的新随机性并入终端核。中间内存不限，但在解码前真正丢弃的内容不能暗中成为另一条解码输入。已知 $n,\varepsilon$、固定调度、静态表与静态精度描述不含运行中生成的信息；这些资源另计。每个终端解码器 $D^H_{y,s}:M_5\to M_5$ 可以是任意可测 CPTP 家族。

实际联合分布与平均校正编码信道为

$$
\begin{aligned}
P(ds,h,y)&=P_S(ds)\,2^{-n}p_s(y\mid h),\\
\mathcal E&=\int P_S(ds)\sum_{h,y}2^{-n}p_s(y\mid h)
D^H_{y,s}\circ\iota\circ\operatorname{Ad}_{Q_h}:M_3\to M_5.
\end{aligned}
\tag{2.1}
$$

成功的唯一定义为 $\|\mathcal E-\iota\|_\diamond\le\varepsilon$。这是对种子、历史和终端随机性全部平均后的要求，不附加逐种子、逐历史或逐舍入分支成功。

**定义 2.2（熵、字母表与在线宽度）。** 置

$$
q_s(y)=\sum_h2^{-n}p_s(y\mid h),\qquad
H(Y\mid S)=\int P_S(ds)\sum_y-q_s(y)\log_2q_s(y),
\tag{2.2}
$$

约定 $0\log_2 0=0$，允许值 $+\infty$。$E_n(\varepsilon)$ 是所有成功方案的 $H(Y\mid S)$ 的下确界，不假设存在取到它的方案。$M_n(\varepsilon)$ 是同样权限下最小可行的有限本质终端字母表大小，即几乎每个种子的终端支持至多有该数目的值。完整历史总是可行，所以这个整数最小值存在。另以 $W_n(\varepsilon)$ 表示 AOM 的完整在线状态在所有时刻的本质峰值宽度最小值；本卷的终端下界不以前述在线宽度为前提。

$H(Y\mid S)$ 是离散视图的条件 Shannon 熵，不是微分熵；免费标准 Borel 种子不通过微分熵计价。终端固定长度寄存器比特数由 $\lceil\log_2M\rceil$ 控制，与某个非均匀视图的 Shannon 熵不同。

**引理 2.3（有类型的回缩与复算子收缩）。** 映射

$$
C(X)=B^\dagger XB+\operatorname{Tr}((I_5-P_R)X)|0\rangle\langle0|:
M_5\to M_3
\tag{2.3}
$$

是 CPTP，且 $C\iota=\operatorname{id}_3$。$\iota\otimes\operatorname{id}_Z$ 对每个有限参考 $Z$ 保持任意复算子的迹范数。任意 CPTP 映射也在所有复算子上收缩迹范数，包括非 Hermitian 算子。

证明。取 $R^\perp$ 的正交基 $(w_a)$，$C$ 的 Kraus 算子为 $B^\dagger$ 和 $|0\rangle\langle w_a|$；平方效应之和为 $P_R+(I_5-P_R)=I_5$。$B^\dagger B=I_3$ 给出回缩。$B\otimes I_Z$ 的等距共轭保留非零奇异值，故任意复算子的迹范数不变。对于 CPTP 映射 $D$，其伴随 $D^\ast$ 为保持单位元的完全正映射；Schwarz 不等式给出

$$
D^*(A)^\dagger D^*(A)\le D^*(A^\dagger A)\le\|A\|_{\mathrm{op}}^2I.
$$

于是 $\|D^\ast(A)\|_{\mathrm{op}}\le\|A\|_{\mathrm{op}}$，再由迹范数与算子范数对偶得 $\|D(X)\|_1\le\|X\|_1$，不要求 $X$ Hermitian。对 $D\otimes\operatorname{id}_Z$ 同理，故可用于钻石范数的后复合收缩。$\square$

**命题 2.4（任意全空间解码权限的保留）。** 任意成功全空间方案经

$$
D_{y,s}=C D^H_{y,s}\iota:M_3\to M_3
$$

给出平均三能级信道 $\mathcal C$，满足

$$
\mathcal C-\operatorname{id}_3=C\circ(\mathcal E-\iota),\qquad
\|\mathcal C-\operatorname{id}_3\|_\diamond\le\varepsilon.
\tag{2.4}
$$

反之，任意三能级解码家族可取 $D^H_{y,s}=\iota D_{y,s}C$ 延拓，保持编码恢复误差恰好相等。

证明。每个复合均具有所示定义域和值域，且是 CPTP；(2.4) 来自 $C\iota=\operatorname{id}_3$。引理 2.3 给出不增误差。反向延拓满足 $\mathcal E-\iota=\iota\circ(\mathcal C-\operatorname{id}_3)$；在每个参考维度使用迹范数等距得到误差相等。有限历史和绝对收敛的终端和可与种子积分交换。这是在原有平均信道上作变换，未选择任何成功种子。$\square$

## 3. 实际前向谱接口与完整相位小球

**引理 3.1（实际代数群与维数）。** 令

$$
J_k=A^{-k}JA^k,\qquad R_1=J_0J_1,\qquad R_2=J_0J_2,\qquad
\mathcal G=\{G\in U(2):\det G=\pm1\}=SU(2)\sqcup J SU(2).
$$

$R_1,R_2$ 为代数 $SU(2)$ 矩阵，生成稠密子群；实际字母 $g_0,g_1$ 生成群的闭包为 $\mathcal G$。其单位分支具有实维数三，并在 $T$ 的单位向量上给出完整 $S^3$ 轨道。

证明。由 (1.1) 的特征多项式与矩阵乘法得到

$$
\operatorname{tr}A=-i/2,\qquad
\alpha_\pm=(\pm\sqrt{15}-i)/4,\qquad
\zeta=\alpha_+/\alpha_-=(-7+i\sqrt{15})/8.
$$

在 $A$ 的正交特征基中写 $J=\left(\begin{smallmatrix}a&b\\\bar b&-a\end{smallmatrix}\right)$。恒等式 $a(\alpha_+-\alpha_-)=\operatorname{tr}(AJ)=-\sqrt3/2$ 与 $J^2=I$ 给出 $a=-1/\sqrt5$、$|b|=2/\sqrt5$。写 $J_k=n_k\cdot\sigma$，其中 $\sigma$ 为 Pauli 矩阵，$n_k\in\mathbb R^3$ 为单位向量。乘积公式给出

$$
n_k\cdot n_\ell=\frac15+\frac45\operatorname{Re}(\zeta^{k-\ell}),\qquad
\operatorname{tr}R_1=-1,\qquad\operatorname{tr}R_2=5/4,
$$

$$
\operatorname{Gram}(n_0,n_1,n_2)=
\begin{pmatrix}1&-1/2&5/8\\-1/2&1&-1/2\\5/8&-1/2&1\end{pmatrix},
\qquad\det\operatorname{Gram}=27/64>0.
$$

因此 $R_1,R_2$ 的 Pauli 向量部分分别沿着相互独立的 $n_0\times n_1$ 和 $n_0\times n_2$，二者不交换。$R_2$ 不可能有限阶，否则其迹是代数整数，而有理数 $5/4$ 不是整数。

$\mathfrak{su}(2)$ 可认作带叉乘的 $\mathbb R^3$；非零真 Lie 子代数只能一维，因为二维平面不对叉乘封闭。无限闭子群的单位分支有正维数，零维紧 Lie 群则有限。因此真无限闭子群的单位分支是圆，且整个子群位于该圆的正规化子。圆取对角形后，正规化子中不在圆内的元素均反对角、迹为零。两个 $R_i$ 的迹非零，所以若其闭包是真无限子群，二者都在同一个圆内而交换，矛盾。故闭包为 $SU(2)$。$J=g_0^{-1}g_1$，每个 $R_i$ 均是 $A,J$ 的字；实际闭包因而含 $SU(2)$ 及一个行列式负分支，等于 $\mathcal G$。单位向量决定唯一 $SU(2)$ 矩阵的第一列，故 $SU(2)$ 在单位向量上自由且传递。这里的轨道是含复相位的 $S^3$，不是射线空间。$\square$

**假设 3.2（来源相对的正谱隙接口）。** 对归一化 Haar 测度，采用

$$
T_\eta f(x)=\int f(g^{-1}x)\,d\eta(g),\qquad
T_\alpha T_\beta=T_{\alpha*\beta},\qquad\check\eta(E)=\eta(E^{-1}).
$$

令

$$
\sigma=\tfrac14(\delta_{R_1}+\delta_{R_1^{-1}}+\delta_{R_2}+\delta_{R_2^{-1}}),
\qquad
\gamma=\inf_{0\ne f\perp1\text{ 于 }L^2(SU(2))}
\frac{\|f\|_2^2-\langle f,T_\sigma f\rangle}{\|f\|_2^2}>0.
\tag{3.1}
$$

AOM 对 [BG] 的接口是：定理 1 要求有限个代数 $SU(d)$ 矩阵生成在 $SL_d(\mathbb C)$ 中 Zariski 稠密的子群，其稠密性脚注将此条件对应于在 $SU(d)$ 中的拓扑稠密。引理 3.1 给出这里的两个实际代数生成元的拓扑稠密性。对 $d=2$、两个生成元，文献记号中的自伴未归一算子为 $zf(x)=\sum_{i=1}^2[f(R_ix)+f(R_i^{-1}x)]$，对称性给出 $z/4=T_\sigma$，其 $\lambda_1(z)<4$ 对应 (3.1)。只把此文献接口的正性作为条件，不将对称算子的顶端隙直接认作实际非对称前向游走的绝对隙。$\gamma$ 与以下 $\rho$ 均为固定、存在但未计算的常数。

**命题 3.3（由顶端隙到实际前向游走）。** 置

$$
\mu=\tfrac12(\delta_A+\delta_{AJ}),\qquad
\nu=\check{\mu^{*3}}*\mu^{*3},\qquad
\rho=\sqrt{1-\gamma/16}\in(0,1).
$$

在假设 3.2 下，

$$
\nu\ge\sigma/16,\qquad
\|T_\mu^L\|_{L^2_0(\mathcal G)}\le\rho^{\lfloor L/3\rfloor}
\quad(L\ge0).
\tag{3.2}
$$

证明。三个恰有一次标签 $1$ 的实际长度三历史给出 $A^3J_k$，$k=0,1,2$。将 $k=0$ 字分别与 $k=1,2$ 字取有序差并反向，得到 $R_1,R_1^{-1},R_2,R_2^{-1}$；每个有序对的概率为 $1/64$。因此 $\nu\ge\sigma/16$，所比较者确为实际前向历史之差。

将 $L^2(\mathcal G)$ 分为常数、行列式特征 $\det$，以及每个行列式陪集上均值为零的子空间 $\mathcal H_c$。这些空间在有关卷积下不变。在每个陪集上，左 $SU(2)$ 作用与其正则作用同构，所以 $\sigma$ 在 $\mathcal H_c$ 上具有同一顶端隙 $\gamma$。每个实际字母的行列式是公平正负号，故 $T_\mu^3\det=0$，也有 $T_\nu\det=0$。正测度 $\nu-\sigma/16$ 的质量为 $15/16$，而酉平移平均的 Dirichlet 型实部非负。因此

$$
\langle f,(I-T_\nu)f\rangle
\ge\tfrac1{16}\langle f,(I-T_\sigma)f\rangle
\ge\tfrac\gamma{16}\|f\|_2^2\qquad(f\in\mathcal H_c).
$$

关键在于 $T_\nu=(T_\mu^3)^*T_\mu^3$ 为正算子，故其在 $\mathcal H_c$ 上的范数不超过 $1-\gamma/16$，在剩余非常数行列式模态上为零。取平方根得 $\|T_\mu^3\|_{L^2_0}\le\rho$，余下少于三步的范数至多一，得 (3.2)。自伴收缩 $T_\sigma$ 还有 $\gamma\le2$，故上述 $\rho$ 确实严格介于零与一。$\square$

**定理 3.4（实际有限先验的小球）。** 在假设 3.2 下，令

$$
b_n=10\rho^{\lfloor n/3\rfloor}.
$$

对每个单位 $t\in T$、每个 $c\in S^3$、整数 $n\ge0$ 和 $0<r\le1/2$，实际公平历史满足

$$
P_n(\|F_ht-c\|\le r)\le8r^3+b_n.
\tag{3.3}
$$

证明。归一化 Haar 球面的弦距离球体积与中心无关，并为

$$
v(r)=\frac2\pi\int_0^{2\arcsin(r/2)}\sin^2u\,du.
$$

当 $0<r\le1$，置 $\vartheta=2\arcsin(r/2)$，有 $r\le\vartheta\le\pi r/3\le\pi/3$。利用此区间上的 $2u/\pi\le\sin u\le u$，得到

$$
\frac8{3\pi^3}r^3\le v(r)\le r^3.
\tag{3.4}
$$

上界可由 $2\vartheta^3/(3\pi)\le(2\pi^2/81)r^3<r^3$ 看出。对固定 $t$，映射 $f\mapsto[G\mapsto f(Gt)]$ 是 $L^2(S^3)$ 到 $L^2(\mathcal G)$ 的等距嵌入，交织左卷积；两个行列式陪集的 Haar 测度均送到同一球面均匀测度，所以 (3.2) 也控制球面密度的均值零部分。

独立于历史，将 $t$ 平滑成其半径 $r$ 球内均匀的 $t'$，并对二者施加同一个实际 $G_h$。因 $G_h$ 等距，$G_ht\in B(c,r)$ 蕴含 $G_ht'\in B(c,2r)$。初始密度的积分为一，其均值零部分的 $L^2$ 范数至多 $v(r)^{-1/2}$。由 (3.2) 与 Cauchy–Schwarz，后一个事件的概率不超过

$$
v(2r)+\rho^{\lfloor n/3\rfloor}\sqrt{v(2r)/v(r)}
\le8r^3+\sqrt{3\pi^3}\,\rho^{\lfloor n/3\rfloor}
\le8r^3+b_n.
$$

这里 $2r\le1$ 才允许两次使用 (3.4)。最后 $F_h=\lambda^{-n}G_h$ 只确定性旋转所测试的中心，保留距离与球面测度。此平滑论证给出的仍是实际有限先验 $P_n$ 的概率界；它从未用 Haar 先验取代实际历史，也未商掉相对相位。$\square$

## 4. 从平均恢复到同一联合分布上的平方失真

**引理 4.1（终端重心存活）。** 对任意成功方案，固定一个单位 $t\in T$，记

$$
U(h)=F_ht,\qquad
x_{y,s}=\sum_h2^{-n}p_s(y\mid h)U(h),\qquad
A_s=\sum_y\|x_{y,s}\|.
$$

则 $0\le A_s\le1$，且 $\mathbb E_S A_S\ge1-\varepsilon$。

证明。由三角不等式和核归一化，$\sum_y\|x_{y,s}\|\le\sum_{h,y}2^{-n}p_s(y\mid h)=1$。以命题 2.4 回缩任意全空间解码器，令 $Z_t=|t\rangle\langle\xi|$。它是迹范数为一的非 Hermitian 算子，并且

$$
\operatorname{Ad}_{Q_h}(Z_t)=|F_ht\rangle\langle\xi|.
$$

这个等式保留了 $\xi$ 与 $T$ 之间的实际相对相位。几乎每个固定种子仍有同一个实际公平先验，因为 $S$ 独立于整个历史。只作为分析量定义条件信道 $\mathcal C_s$，有

$$
\mathcal C_s(Z_t)=\sum_yD_{y,s}(|x_{y,s}\rangle\langle\xi|),\qquad
\|\mathcal C_s(Z_t)\|_1\le A_s.
$$

第二式使用引理 2.3 对复算子的迹范数收缩。所有可数和按向量范数或迹范数绝对收敛。积分后，

$$
\|\mathcal C(Z_t)\|_1\le\mathbb E_S A_S.
$$

另一方面，平均钻石误差给出 $\|\mathcal C(Z_t)\|_1\ge1-\varepsilon$，从而得结论。这里直接使用任意终端核，没有在线峰值内存假设，也没有引入在线块量 $a_W$；平均成功未被改写成逐种子成功。$\square$

**命题 4.2（可测中心与精确失真恒等式）。** 当 $x_{y,s}\ne0$ 时取 $c_{y,s}=x_{y,s}/\|x_{y,s}\|$，否则取同一固定单位向量 $t$。这些中心可测，且在 (2.1) 的同一个联合分布上有

$$
\begin{aligned}
\Delta&:=\mathbb E_{S,\mathsf H_n,Y}\|F_{\mathsf H_n}t-c_{Y,S}\|^2\\
&=2(1-\mathbb E_S A_S)\le2\varepsilon.
\end{aligned}
\tag{4.1}
$$

证明。有限历史求和使 $x_{y,s}$ 可测；在非零向量上归一化连续，补入的固定中心也可测。若 $q_s(y)=0$，则 $x_{y,s}=0$，该项联合质量为零；若 $q_s(y)>0$ 而重心为零，所取单位中心仍满足下式。逐种子展开即得

$$
\begin{aligned}
\sum_{h,y}2^{-n}p_s(y\mid h)\|U(h)-c_{y,s}\|^2
&=2-2\operatorname{Re}\sum_y\langle c_{y,s},x_{y,s}\rangle\\
&=2(1-A_s).
\end{aligned}
$$

可数和合法，因为平方距离至多四，内积项按 $\sum_y\|x_{y,s}\|\le1$ 绝对收敛。平均后使用引理 4.1。中心只是实际终端视图的辅助统计量，不限制物理解码器的形式。此恒等式允许随机核、零重心、坏种子和坏历史；不要求任何条件失真界，也不把历史与其随机终端标签拆成独立对象。$\square$

## 5. 有限先验的 Laplace 界与真正的熵下界

**引理 5.1（所有逆温度的实际先验 Laplace 界）。** 置

$$
B_n(\beta)=\min\{1,\;6\sqrt\pi\,\beta^{-3/2}+b_n+e^{-\beta/4}\},
\qquad\beta>0.
\tag{5.1}
$$

在假设 3.2 下，对每个单位 $t,c\in T$，

$$
L_{n,t,c}(\beta):=\sum_h2^{-n}e^{-\beta\|F_ht-c\|^2}\le B_n(\beta).
\tag{5.2}
$$

证明。令实际有限先验下的 $X=\|F_{\mathsf H_n}t-c\|^2\in[0,4]$。由点态恒等式和非负积分交换，

$$
e^{-\beta X}=\int_X^\infty\beta e^{-\beta u}\,du,
\qquad
L_{n,t,c}(\beta)=\int_0^\infty\beta e^{-\beta u}P_n(X\le u)\,du.
$$

对 $0<u\le1/4$，小球半径 $\sqrt u\le1/2$，所以 (3.3) 给出 $P_n(X\le u)\le8u^{3/2}+b_n$；对 $u>1/4$ 仅用概率至多一。因此

$$
\begin{aligned}
L_{n,t,c}(\beta)
&\le\int_0^{1/4}\beta e^{-\beta u}(8u^{3/2}+b_n)\,du+e^{-\beta/4}\\
&\le8\Gamma(5/2)\beta^{-3/2}+b_n+e^{-\beta/4}\\
&=6\sqrt\pi\,\beta^{-3/2}+b_n+e^{-\beta/4}.
\end{aligned}
$$

第二行只扩大非负积分范围；代换 $v=\beta u$ 并分部积分两次给出 $\Gamma(5/2)=3\sqrt\pi/4$。另外 $L\le1$，取较小上界得到 (5.2)。零距离原子不影响分层积分，$u=0$ 的单点也不要求一个未给出的零半径估计。整个推导只在小半径范围使用 (3.3)，并明确支付大半径尾项；(5.2) 中的先验始终是实际 $2^{-n}$。$\square$

**引理 5.2（有限历史后验的 Gibbs 不等式）。** 设 $a$ 为有限历史集上的任意概率分布，$c\in S^3$，$d(h)=\|F_ht-c\|$。以自然对数定义相对熵 $D(a\|P_n)$。则

$$
D(a\|P_n)\ge-\beta\mathbb E_a d^2-\ln B_n(\beta)\qquad(\beta>0).
\tag{5.3}
$$

证明。令严格正的倾斜先验为

$$
r_\beta(h)=\frac{2^{-n}e^{-\beta d(h)^2}}{L_{n,t,c}(\beta)}.
$$

$\ln x\le x-1$ 给出

$$
\sum_{a(h)>0}a(h)\ln\frac{r_\beta(h)}{a(h)}
\le\sum_{a(h)>0}r_\beta(h)-1\le0,
$$

故 $D(a\|r_\beta)\ge0$。展开对数得到精确恒等式

$$
D(a\|P_n)=D(a\|r_\beta)-\beta\mathbb E_a d^2-\ln L_{n,t,c}(\beta).
$$

用引理 5.1 即得 (5.3)。所有对数均为自然对数；这里没有微分熵，也没有确定性终端核假设。$\square$

**定理 5.3（任意时域的条件 Shannon 熵下界）。** 对所有整数 $n\ge0$ 和 $0<\varepsilon<1/4$，在假设 3.2 下有

$$
E_n(\varepsilon)\ge L_n(\varepsilon):=
\max\left\{0,\;\frac1{\ln2}\sup_{\beta>0}
[-2\beta\varepsilon-\ln B_n(\beta)]\right\}.
\tag{5.4}
$$

这是下界，不是有限 $n$ 的精确公式。

证明。固定任意成功方案。对 $q_s(y)>0$ 定义同一实际联合分布的后验

$$
a_{y,s}(h)=\frac{2^{-n}p_s(y\mid h)}{q_s(y)}.
$$

在引理 5.2 中取命题 4.2 的同一个中心 $c_{y,s}$。定义以 nat 为单位的条件互信息

$$
I_{\mathrm{nat}}(\mathsf H_n;Y\mid S)
=\int P_S(ds)\sum_{y:q_s(y)>0}q_s(y)D(a_{y,s}\|P_n).
$$

均匀有限先验保证 $0\le D(a\|P_n)\le n\ln2$，所以此式总是有定义且有限，即使 $H(Y\mid S)=+\infty$。先对所有 $(S,Y)$ 平均后才应用 (4.1)，得到

$$
I_{\mathrm{nat}}(\mathsf H_n;Y\mid S)
\ge-\beta\Delta-\ln B_n(\beta)
\ge-2\beta\varepsilon-\ln B_n(\beta).
\tag{5.5}
$$

还需要真正的熵比较。在后验支持上，$p_s(y\mid h)>0$，并且

$$
D(a_{y,s}\|P_n)
=\sum_h a_{y,s}(h)\ln p_s(y\mid h)-\ln q_s(y)
\le-\ln q_s(y),
$$

因为每个核值至多一。左端非负；乘 $q_s(y)$，对可数 $y$ 求和并对 $S$ 积分，直接得到

$$
I_{\mathrm{nat}}(\mathsf H_n;Y\mid S)\le(\ln2)H(Y\mid S).
\tag{5.6}
$$

此证明不减去任何无穷熵，也不假设字母表均匀或近均匀。种子零测集可任意补定义；依种子而变的可数标签按定义 2.1 的可测索引处理。独立种子只通过保持条件实际先验为 $P_n$ 以及可测积分进入推导，不需要把它离散化。

合并 (5.5)—(5.6)，每个成功方案对所有 $\beta>0$ 均满足 $H(Y\mid S)\ge[-2\beta\varepsilon-\ln B_n(\beta)]/\ln2$。取非负截断、上确界，再对成功方案取下确界，得到 (5.4)。无需熵最小值被取到。熵下界先由后验相对熵建立，没有从 $\log M$ 的下界倒推。$\square$

## 6. 所有时域的显式交叉下界

**推论 6.1（失真与有限历史余项的交叉）。** 定义符号常数

$$
A_{\mathrm{tail}}=(6/e)^{3/2},\qquad
K=1+6\sqrt\pi+A_{\mathrm{tail}},\qquad
C_{\mathrm{lower}}=\log_2(e^2K),
$$

以及

$$
t_n(\varepsilon)=\varepsilon+b_n^{2/3}.
$$

则在定理 5.3 的全部时域上，

$$
E_n(\varepsilon)\ge
\max\left\{0,\;\frac32\log_2\frac1{t_n(\varepsilon)}-C_{\mathrm{lower}}\right\}.
\tag{6.1}
$$

这是一个显式交叉下界，短时域可以只给零，不是 $E_n$ 的精确公式。

证明。函数 $\beta^{3/2}e^{-\beta/4}$ 的对数导数为 $3/(2\beta)-1/4$，所以它在 $\beta=6$ 取得全局最大值 $A_{\mathrm{tail}}$。因此对所有 $\beta>0$，

$$
e^{-\beta/4}\le A_{\mathrm{tail}}\beta^{-3/2}.
\tag{6.2}
$$

取 $t=t_n(\varepsilon)>0$ 与 $\beta=1/t$。由 $t\ge\varepsilon$、$t\ge b_n^{2/3}$，分别有 $\beta\varepsilon\le1$ 和 $b_n\le t^{3/2}$。于是

$$
B_n(1/t)\le(6\sqrt\pi+A_{\mathrm{tail}})t^{3/2}+b_n\le Kt^{3/2}.
$$

即使右端大于一，该不等式仍成立。将这一特定 $\beta$ 代入 (5.4)，得

$$
\frac{-2\beta\varepsilon-\ln B_n(\beta)}{\ln2}
\ge\frac{-2-\ln(Kt^{3/2})}{\ln2}
=\frac32\log_2(1/t)-C_{\mathrm{lower}}.
$$

再用非负性得 (6.1)。这也是 (5.4) 的一个显式后果，未修改原有长时域目标。$\square$

## 7. 一次最终舍入的上界与完整误差证明

**定义 7.1（实线性四元数壳）。** 对 $q\in\mathbb R^4$ 定义

$$
\Phi(q)=\begin{pmatrix}q_0+iq_1&q_2+iq_3\\-q_2+iq_3&q_0-iq_1\end{pmatrix}.
$$

其恒等式为 $\Phi(q)^\dagger\Phi(q)=\|q\|^2I_2$，$\|\Phi(q)\|_{\mathrm{op}}=\|q\|$，$\Phi(S^3)=SU(2)$。取整数 $m\ge8$，$\delta=1/m$，定义固定有限壳

$$
\mathcal N_\delta=\{a/\|a\|:\ a\in\delta\mathbb Z^4,\quad1-2\delta\le\|a\|\le1+2\delta\}.
$$

保留的终端标签为 $Y=(d,q)\in\{0,1\}\times\mathcal N_\delta$，表示 $\widetilde G_y=J^d\Phi(q)$。

给定实际历史的精确 $G_h\in\mathcal G$，先保留其行列式分支 $d$，使 $\det G_h=(-1)^d$。则 $J^dG_h\in SU(2)$，有唯一 $z\in S^3$ 使 $G_h=J^d\Phi(z)$。将每个实坐标 $z_i$ 独立随机舍入到相邻的 $\delta$ 格点，使其均值仍为 $z_i$；已经在格点上的坐标保持。写舍入向量为 $a=z+e$，最后令 $q=a/\|a\|$。这只进行一次，在所有实际测量完成之后进行。

**引理 7.2（归一化前后的矩）。** 对每个精确目标 $z$，上述条件舍入满足

$$
\mathbb Ee=0,\qquad\|e\|\le2\delta,\qquad
\mathbb E\|e\|^2\le\delta^2,
\tag{7.1}
$$

$$
\|\mathbb E(q-z)\|\le4\delta^2,\qquad
\mathbb E\|q-z\|^2\le4\delta^2.
\tag{7.2}
$$

证明。若 $z_i$ 位于相邻格点 $\ell_i,r_i$ 之间，以 $(r_i-z_i)/\delta$ 与 $(z_i-\ell_i)/\delta$ 为两端概率；则 $\mathbb Ee_i=0$，$|e_i|\le\delta$，并且 $\mathbb Ee_i^2=(z_i-\ell_i)(r_i-z_i)\le\delta^2/4$。格点情形误差为零。将四坐标相加即得 (7.1)。于是 $1-2\delta\le\|a\|\le1+2\delta$，$a$ 非零，$q$ 属于所定义的壳。

为控制径向归一化，令 $f(v)=v/\|v\|$，$u=v/\|v\|$，将方向 $e$ 写为 $e=\alpha u+b$，$b\perp u$。沿实方向微分得

$$
D^2f(v)[e,e]=-
\frac{\|b\|^2u+2\alpha b}{\|v\|^2},\qquad
\|D^2f(v)[e,e]\|\le\frac{2\|e\|^2}{\|v\|^2}.
$$

沿 $z+te$、$0\le t\le1$ 的半径至少为 $1-2\delta\ge1/2$。Taylor 积分余项的范数因而至多 $4\|e\|^2$；一阶项 $Df(z)e$ 的期望为零，得到第一条 (7.2)。另外反三角不等式给出

$$
\|a/\|a\|-z\|\le\|a/\|a\|-a\|+\|a-z\|
=|1-\|a\||+\|e\|\le2\|e\|,
$$

平方取期望即得第二条。归一化之前无偏，归一化之后只主张二阶平均偏差界。$\square$

**引理 7.3（壳的有限字母表）。** 壳中径向归一化后不同点的数目至多 $14\pi^2m^3$，加上行列式分支后终端字母表至多 $28\pi^2m^3$。

证明。在每个归一化前的壳格点周围置边长 $\delta$ 的四维立方体。它们内部不交，外接半径为 $\delta$，所以全在半径 $1-3\delta$ 与 $1+3\delta$ 之间。四维球体积为 $\pi^2r^4/2$，故格点数 $N_{\mathrm{lat}}$ 满足

$$
\begin{aligned}
N_{\mathrm{lat}}\delta^4
&\le\frac{\pi^2}{2}[(1+3\delta)^4-(1-3\delta)^4]\\
&=12\pi^2\delta(1+9\delta^2)\le14\pi^2\delta,
\end{aligned}
$$

最后一步用 $\delta\le1/8$。因此 $N_{\mathrm{lat}}\le14\pi^2m^3$。径向重合可以合并，只会减少数目；行列式标签至多再乘二。$\square$

**引理 7.4（含共同方向相位的平均钻石误差）。** 令

$$
\widehat Q_y=\lambda^n\oplus\widetilde G_y
\quad\text{于 }\mathbb C\xi\oplus T,\qquad
L_y=B\widehat Q_y^\dagger B^\dagger+(I_5-P_R).
\tag{7.3}
$$

全空间解码器 $\operatorname{Ad}_{L_y}$ 合法。对每个实际历史，条件于该历史、只平均最终舍入，其编码恢复钻石误差至多 $12/m^2$；因此全部平均的误差也至多 $12/m^2$。

证明。$L_y$ 的两个正交块分别在 $R$ 与 $R^\perp$ 上酉。对实际历史，三能级相对作用恰为

$$
\widehat Q_y^\dagger Q_h=1\oplus\widetilde G_y^\dagger G_h.
$$

共同方向上的 $\lambda^n$ 被精确校正，而未将 $T$ 的相位混作整体相位。令 $B_{\mathrm{err}}=\widetilde G_y^\dagger G_h-I_2$，并在 $\xi$ 上补零。固定历史后 $G_h=J^d\Phi(z)$，由 $\Phi$ 的实线性及范数恒等式，

$$
B_{\mathrm{err}}=(\widetilde G_y-G_h)^\dagger G_h,\qquad
\|\mathbb EB_{\mathrm{err}}\|_{\mathrm{op}}\le4\delta^2,\qquad
\mathbb E\|B_{\mathrm{err}}\|_{\mathrm{op}}^2\le4\delta^2.
$$

在任意有限参考系统上，条件平均相对信道减恒等的精确展开是

$$
X\longmapsto(\mathbb EB_{\mathrm{err}})X
+X(\mathbb EB_{\mathrm{err}})^\dagger
+\mathbb E[B_{\mathrm{err}}XB_{\mathrm{err}}^\dagger],
$$

其中隐含对参考的恒等张量。矩阵左右乘法的迹范数界由其算子范数控制，故钻石误差至多

$$
2\|\mathbb EB_{\mathrm{err}}\|_{\mathrm{op}}
+\mathbb E\|B_{\mathrm{err}}\|_{\mathrm{op}}^2
\le12\delta^2.
$$

这是对舍入随机性的条件平均界，不是每条舍入分支的二阶误差界。平均实际历史保留此界。最后用 $B\otimes I$ 的迹范数等距，三能级误差等于编码到 $M_5$ 的误差，且对所有有限参考成立。$\square$

**定理 7.5（全部时域的熵与字母表上界）。** 对整数 $n\ge0$ 与 $0<\varepsilon<1/4$，

$$
\begin{aligned}
E_n(\varepsilon)&\le
\min\{n,\;\log_2(28\pi^2\lceil4/\sqrt\varepsilon\rceil^3)\},\\
M_n(\varepsilon)&\le
\min\{2^n,\;28\pi^2\lceil4/\sqrt\varepsilon\rceil^3\}.
\end{aligned}
\tag{7.4}
$$

特别地 $E_0(\varepsilon)=0$、$M_0(\varepsilon)=1$。

证明。取常种子，$m=\lceil4/\sqrt\varepsilon\rceil\ge8$。中间保留完整实际历史和所需工作区，在终点形成精确 $G_h$，作定义 7.1 的一次舍入。由引理 7.4，误差至多 $12/m^2\le3\varepsilon/4\le\varepsilon$。此时只留下 $Y=(d,q)$，完整历史、计算工作区、所有额外控制选择以及舍入随机带均在解码前真正丢弃。解码器仅接收这个标签，并使用 (7.3)；静态壳描述和概率表不包含其他运行信息。

若一个分布支持于 $N$ 点，则对 $N$ 点均匀分布的 KL 非负性给出 $H(Y)=\log_2N-D(q\|\mathrm{unif}_N)/\ln2\le\log_2N$。由引理 7.3 得舍入项。另一方案保存公平完整历史，用 $BQ_h^\dagger B^\dagger+(I_5-P_R)$ 作精确酉校正，其熵为 $n$，字母表为 $2^n$；这个可行上界不需要历史到酉的单射。选取两方案之一即得 (7.4)。空历史用单标签和恒等校正达到熵零。所有上界均可用常种子实现。$\square$

## 8. 对数阈值之后的一致主阶

**定理 8.1（近似终端记录熵与匹配字母表）。** 在假设 3.2 下，置

$$
s_\rho=-\ln\rho>0,\qquad
n_0(\varepsilon,\rho)=3\left\lceil
\frac{\ln10+\frac32\ln(1/\varepsilon)}{s_\rho}
\right\rceil,\qquad
C_{\mathrm{upper}}=\log_2(3500\pi^2).
\tag{8.1}
$$

对全部 $0<\varepsilon<1/4$ 与整数 $n\ge n_0(\varepsilon,\rho)$，

$$
\frac32\log_2\frac1\varepsilon-C_{\mathrm{lower}}
\le E_n(\varepsilon)\le
\frac32\log_2\frac1\varepsilon+C_{\mathrm{upper}},
\tag{8.2}
$$

$$
\frac{e^{-2}}K\,\varepsilon^{-3/2}
\le M_n(\varepsilon)\le3500\pi^2\varepsilon^{-3/2}.
\tag{8.3}
$$

所以 $E_n(\varepsilon)=\frac32\log_2(1/\varepsilon)+O(1)$，$M_n(\varepsilon)=\Theta(\varepsilon^{-3/2})$，均在所述双参数范围一致成立。所显示的加法与乘法常数不依赖 $n,\varepsilon$；阈值依赖固定但未计算的 $\rho$。

证明。写 $x=[\ln10+(3/2)\ln(1/\varepsilon)]/s_\rho$。$n\ge3\lceil x\rceil$ 保证 $\lfloor n/3\rfloor\ge\lceil x\rceil\ge x$，故

$$
b_n=10e^{-s_\rho\lfloor n/3\rfloor}\le\varepsilon^{3/2}.
$$

在 (5.4) 中直接取 $\beta=1/\varepsilon$；利用 (6.2)，

$$
B_n(1/\varepsilon)\le K\varepsilon^{3/2},\qquad
E_n(\varepsilon)\ge\frac{-2-\ln(K\varepsilon^{3/2})}{\ln2}
=\frac32\log_2(1/\varepsilon)-C_{\mathrm{lower}}.
$$

若 $K\varepsilon^{3/2}>1$，所用上界仍真，结论只可能比非负性弱，不影响一致估计。长时域直接选择此 $\beta$，因而不需要把交叉下界中的 $t_n\le2\varepsilon$ 再付成另一个常数。

另一方面，$\lceil4/\sqrt\varepsilon\rceil\le4/\sqrt\varepsilon+1\le5/\sqrt\varepsilon$，定理 7.5 给出 $M_n\le3500\pi^2\varepsilon^{-3/2}$ 及 (8.2) 的上侧。若某成功方案的本质终端字母表至多 $M$，则对几乎每个种子 $H(Y\mid S=s)\le\log_2M$，从而 $H(Y\mid S)\le\log_2M$。将已经证明的真实熵下界用于每个此类方案，得 $\log_2M\ge(3/2)\log_2(1/\varepsilon)-C_{\mathrm{lower}}$。取最小可行整数 $M$ 即得 (8.3) 的下侧。这一步由熵推出字母表，而非反向用支持大小代替熵证明。$\square$

**推论 8.2（显式对数充分阈值与固定比特）。** 以下实阈值也是定理 8.1 的充分条件：

$$
n\ge\frac9{2s_\rho}\ln(1/\varepsilon)+\frac{3\ln10}{s_\rho}+3.
\tag{8.4}
$$

令 $C_\rho=\max\{9/(2s_\rho),\;3\ln10/s_\rho+3\}$，则更简洁的 $n\ge C_\rho\ln(1/\varepsilon)+C_\rho$ 充分。在相同范围，最小终端固定长度比特数为 $\lceil\log_2M_n(\varepsilon)\rceil=(3/2)\log_2(1/\varepsilon)+O(1)$。

证明。$\lceil x\rceil\le x+1$ 给出 $n_0\le3x+3$，即 (8.4)；$C_\rho$ 同时控制两项系数。固定长度比特式来自 (8.3) 取以二为底的对数以及向上取整至多加一。自然对数只用于谱衰减与信息的 nat 表示；熵与比特均用 $\log_2$。$\square$

## 9. 零误差的独立边界与有限时域相容性

**引理 9.1（固定长度单射的独立来源条件）。** 采用 [OWN] 定理 8.2、AOM 第 5 节的固定长度字单射接口。其代数证明如下，因而零误差比较与近似熵证明所用的谱接口彼此分开。

在 $T$ 的整数基 $b_1=(1,0,-1)^{\mathsf T}$、$b_2=(0,1,-1)^{\mathsf T}$ 中，令 $\tau=i\sqrt3$、$P_j=-2i\widehat V_j$，则

$$
P_0=\begin{pmatrix}-\tau&1\\\tau-1&\tau-1\end{pmatrix},\quad
P_1=\begin{pmatrix}1&-\tau\\\tau-1&\tau-1\end{pmatrix}=P_0\widehat W,
\quad\widehat W=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

证明。环同态 $\phi:\mathbb Z[\tau]\to\mathbb F_2$ 定为 $\phi(a+b\tau)=a+b\pmod2$；因 $\tau^2=-3$，此映射保持乘法。两个 $P_j$ 都约化为

$$
E=\begin{pmatrix}1&1\\0&0\end{pmatrix},\qquad E^2=E,
\qquad\phi(\widehat W)E\ne E.
$$

$\det P_j=\pm4\ne0$，故可在 $\mathbb Q(\tau)$ 中消去相同的最左字母。若两个不同固定长度字相等，消去共同前导后，第一个不同字母可写成 $P_0X=P_1Y=P_0\widehat WY$，即 $X=\widehat WY$。等长非空尾字都约化为 $E$，矛盾；空尾字则要求 $I=\widehat W$，亦矛盾。矩阵乘积的先后次序为命题 1.3 所定的实际顺序，此消去只作用于其最左端。固定长度全三能级字若只相差投影标量，作用于 $\xi$ 的共同非零特征值 $\lambda^n$ 迫使该标量为一。所以不同历史的 $Q_h$ 不相等，且不同投影类。$\square$

**定理 9.2（精确终端熵与宽度）。** 在引理 9.1 的独立单射条件下，

$$
E_n(0)=n,\qquad M_n(0)=W_n(0)=2^n\qquad(n\ge0).
\tag{9.1}
$$

证明。独立从精确平均恢复出发，对固定基向量 $t=f_1,f_2$ 分别重做引理 4.1 与命题 4.2，令误差为零。每个 $A_s^t\le1$ 而其期望为一，故其等于一的种子集合具有全测度。只交这两个全测度集合；此交集来自零失真非负性，而非任何正误差的逐种子成功假设。

在该交集上，每个正质量终端值的条件平方失真为零。有限历史与可数标签允许同时处理所有正质量项。因此，同一 $(y,s)$ 后验支持中的任意两个历史在 $f_1$ 上具有相同 $F_hf_1$，在 $f_2$ 上也相同；$F_h$ 遂在一组基上相等，进而 $G_h,Q_h$ 相等。由引理 9.1，每个后验只能支持一个历史。于是每个正质量后验相对于均匀先验的 KL 恰为 $n\ln2$，所以 $I_{\mathrm{nat}}(\mathsf H_n;Y\mid S)=n\ln2$，用 (5.6) 得 $H(Y\mid S)\ge n$。

每个历史的终端核质量为一，且不同历史的条件终端支持不交，故几乎每个种子的终端支持至少有 $2^n$ 个值。在线峰值至少为终端大小。保存二进制前缀并最后精确逆转，则终端支持为 $2^n$、熵为 $n$，所有中间前缀支持均不超过 $2^n$，达到三项上界。空历史亦满足 (9.1)。证明没有代入 $\beta=1/\varepsilon$ 或任何除以零的近似式；近似定理本身不需要引理 9.1。$\square$

**命题 9.3（有限时域下界不超过历史熵）。** 对每个固定有限 $n$，(5.4) 的下界满足 $0\le L_n(\varepsilon)\le n$；同时 $E_n(\varepsilon)\le n$、$M_n(\varepsilon)\le2^n$。不存在由本卷结论推出的固定 $n$、$\varepsilon\downarrow0$ 的发散下界。

证明。对任意一个实际历史 $h_0$，取中心 $c=F_{h_0}t$，则每个 $\beta>0$ 都有 $L_{n,t,c}(\beta)\ge2^{-n}$。由 (5.2)，$B_n(\beta)\ge2^{-n}$；因此

$$
-2\beta\varepsilon-\ln B_n(\beta)\le n\ln2.
$$

取上确界和非负截断即得。其余上界来自完整历史方案。特别地 $n=0$ 时 $b_0=10$，(5.1) 给出 $B_0(\beta)=1$，(5.4) 仅给零，与 $E_0=0$、$M_0=1$ 一致。对固定 $n$ 降低误差时，定理 8.1 的时域条件不再始终成立；不能把它删去而外推主阶。$\square$

## 10. 资源解释、归属与未决边界

**约定 10.1（终端资源与完整代价的分界）。** 以下量各有自己的含义，不能相互充当总价：

| 量 | 本卷结论及边界 |
| --- | --- |
| 终端条件 Shannon 熵 $E_n(\varepsilon)$ | 完整离散解码视图在免费独立种子条件下的熵下确界；长时域有 (8.2)，不主张下确界被取到。 |
| 终端字母表 $M_n(\varepsilon)$ | 最小有限本质支持大小；有 (7.4)、(8.3)，不要求消息均匀。 |
| 固定长度终端比特 | 由 $\lceil\log_2M_n\rceil$ 描述；与具体方案的 Shannon 熵分别计量。 |
| 在线峰值宽度 $W_n(\varepsilon)$ | 每一时刻完整持久状态的最大大小；一次最终舍入允许中间完整历史，因而不证明在线峰值改善。 |
| 实际采集与准备 | 仍需 $n$ 次实际仪器作用、标签采集及新环境准备，终端熵律不减少这些次数。 |
| 工作区、抹除与随机带 | 上界允许不限中间工作区；它们在解码前的丢弃是权限条件，其抹除、实现或热力学代价不由保留熵自动给出。 |
| 静态描述与控制精度 | 精确实概率表、精确 $G_h$ 计算与相位正确的逆控制是数学模型权限，描述长度、误差预算和实现精度另计。 |
| 时钟、通信与总成本 | 固定调度、确定性时钟、通信及全部物理价格未在本卷优化。任何运行相关解码载体仍须纳入 $Y$。 |

**约定 10.2（结论的适用边界）。** 本卷只讨论所列实际 $\theta=\pi/6$ 仪器与平均不折半钻石误差。未推广到全部角度、任意无限群、不同布居切换模型或射线空间。熵下界所需的是同一个实际联合分布上的相干存活、失真与后验；分别可达的边缘量不能拼成共同实现。

独立种子保证几乎每个种子的条件历史先验仍为公平实际先验；如果允许种子预先编码历史，问题便改变。正误差下允许部分种子或历史较差，所有损失只通过真实平均失真支付，不取逐点成功事件的交集。可数视图、随机终端核、零重心、零质量标签与无限条件熵均已在证明中处理。

维数三来自保留相对于 $\xi$ 的完整相位的 $S^3$ 小球，不是单凭群无限或字单射推得。实际模型、小球和终端舍入归于 AOM 及其模型拥有文献；本卷的结果是标准信息方法与这些接口的条件综合。精确零误差另用固定长度单射，近似主阶没有借用该条件。

谱接口保持存在而未计算；(8.1) 是以 $\rho$ 为参数的显式阈值，不是已给出数值的混合时间。更尖锐的加法常数、精确短时域交叉、熵下确界的可达性、有限精度实现及其成本仍未由本卷决定。(6.1) 提供了一个所有时域可用的交叉下界，但不把它写成精确最优熵。

本卷的条件数学陈述不包含物理可实现性、经验机器学习表现、宇宙本体、Landauer 抹除代价或完整成本最优性结论。所列终端熵压缩也不意味着中途已经保持同样小的记录。

## 11. 文献接口

AOM：《AURIC FIB approximate online recovery memory》，模型、全空间回缩、实际前向谱比较、球面小球与随机径向壳舍入的数学来源。本文将其外部正谱隙接口明确列为假设 3.2；其数值未给出。

[OWN]：《AURIC FIB environment record memory》，实际仪器坐标与固定长度字单射的拥有文献；固定修订 `55208d97e98beb34acc9db6cdcd1c9da16331362`，定义 1.3—2.1、定理 2.2、6.1、8.2、9.2—9.3。

[FIVE]：《AURIC FIB five window quantum memory》，同一固定修订，定义 17.2、定理 17.3 与式 (18.4)。

[BG]：J. Bourgain 与 A. Gamburd，*A spectral gap theorem in SU(d)*，JEMS **14**(5) (2012)，1455—1511，DOI `10.4171/JEMS/337`。AOM 所述接口为出版终版第 1455 页定理 1 及其稠密性脚注、归一化式 (0.1)；其适用性在本卷按假设 3.2 处理。

[OWN]: https://github.com/the-omega-institute/trureturing/blob/55208d97e98beb34acc9db6cdcd1c9da16331362/docs/develop/theory/AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md
[FIVE]: https://github.com/the-omega-institute/trureturing/blob/55208d97e98beb34acc9db6cdcd1c9da16331362/docs/develop/theory/AURIC_FIB_FIVE_WINDOW_QUANTUM_MEMORY.md
[BG]: https://doi.org/10.4171/JEMS/337

## 追加锚（本行以下为增补区）
