# 贝尔双轨、一只衰减器与全有限量子层级

## 167. 二体有限控制、一腿满维种子与全部有限量子锥

在固定的实际复 Hermitian 张量载体上，一、二体锥的量子形状可以由一个二元关系和两类仅作用于二体的操作确定：同一个未归一 Bell dyad 同时属于原态锥及其迹对偶锥，第一因子的全部酉合同保持二体锥，一只固定的可逆衰减器也保持该锥。旋转与这只衰减器的精确有限字先生成任意可逆滤波的正比例代表；Bell 的态轨道和对偶轨道随后分别支付两个锥包含。由原最大分块界得到的实际偏迹恢复一体锥。再接入一条腿满维的三体 GME 原 dyad，[第166章的定理166.12][Q167XIII]确定全部有限原锥。这里所有条件均在同一实际坐标和同一原层级内陈述。

### 167.1 完整原域、Bell 关系及二体控制入口

**定义 167.1（不预付低层量子形状的完整原域）。** 固定整数 $n\ge2$，令

$$
V=\operatorname{Herm}_n(\mathbb C),\qquad
W_N=V^{\otimes_{\mathbb R}N}\cong\operatorname{Herm}_{n^N}(\mathbb C),\qquad N\ge1.
\tag{167.1}
$$

这个识别始终是给定的实际 Kronecker 张量坐标。对每个有限 $N$，给定闭、尖、生成凸锥 $C_N\subset W_N$。给定的单位是 $u_N=\operatorname{Tr}=u_1^{\otimes N}$，在 $C_N\setminus\{0\}$ 上严格正。使用整个归一基、全部原极点、完整自身正对偶和整个 proper 效应区间：

$$
K_N=\{x\in C_N:u_N(x)=1\},\quad P_N=\operatorname{ext}K_N,\quad
C_N^*=\{f\in W_N^*:f(C_N)\ge0\},\quad
\mathcal E_N=[0,u_N]_{C_N^*}.
\tag{167.2}
$$

有限菜单取其中全部有限单位分解 $(f_a)$，即 $f_a\in C_N^*$、$\sum_a f_a=u_N$；凸准备及其配对使用原线性结构。每个有限实际分块 $a+b$ 满足

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}
\subseteq C_a\otimes_{\max}C_b.
\tag{167.3}
$$

左边是正简单张量的闭凸生成锥，右边是全部 $f\otimes g$、$f\in C_a^*$、$g\in C_b^*$ 的非负半空间之交。所有实际位置置换及其逆均正。不连续分块由这些置换运输；重括号只用同一实际空间的规范识别。原配对与单位兼容：

$$
(f\otimes g)(x\otimes y)=f(x)g(y),\qquad u_{a+b}=u_a\otimes u_b.
\tag{167.4}
$$

空旁观系统约定为 $W_0=\mathbb R,C_0=\mathbb R_+,u_0=\mathrm{id}$。这些是[定义166.1][Q167XIII]除去 $C_1=\operatorname{PSD}_n$、$C_2=\operatorname{PSD}_{n^2}$ 后的全部原假设。初始不假设任意 $C_N$ 为 PSD、自对偶、在转置或复共轭下不变，也不假设任何高层矩阵操作正性。

迹配对 $\langle y,x\rangle=\operatorname{Tr}(yx)$ 是实 Hermitian 空间上的非退化配对，以下用它表示每个 $C_N^*$ 的矩阵代表。单位泛函的矩阵代表为 $I_{n^N}$；这不预先断言 $I_{n^N}\in C_N$。写 $\operatorname{PSD}_D=\operatorname{Herm}_D^+(\mathbb C)$，并令 $\operatorname{Ad}_H(x)=HxH^*$。

**定义 167.2（二元条件与三元种子）。** 固定一个实数 $0<\lambda<1$，在同一原单腿基中置

$$
\Omega=\sum_{i=1}^n|ii\rangle,\qquad
B=\Omega\Omega^*,\qquad S=\operatorname{diag}(\lambda,1,\ldots,1).
\tag{167.5}
$$

考虑下列四个条件：

- **B：** $B\in C_2\cap C_2^*$。第二个成员关系指泛函 $\beta(x)=\operatorname{Tr}(Bx)$ 在整个原 $C_2$ 上非负。
- **U2：** 对每个 $U\in U(n)$，$\operatorname{Ad}_{U\otimes I}(C_2)\subseteq C_2$。
- **S2：** 对上述单个固定 $S$，$\operatorname{Ad}_{S\otimes I}(C_2)\subseteq C_2$。
- **T：** 存在非零实际向量 $\psi\in(\mathbb C^n)^{\otimes3}$，使

$$
\psi\psi^*\in C_3,\qquad
\min_{i=1,2,3}r_i(\psi)\ge2,\qquad
\max_{i=1,2,3}r_i(\psi)=n,
\tag{167.6}
$$

其中 $r_i$ 是第 $i$ 腿对其余两腿的复矩阵展平秩。前一个秩条件正是纯向量对每个二分均非乘积，即三体 GME；后一个保证至少一条实际原腿满支撑。它们是指定向量的线性代数性质，未把 $\psi\psi^*/\|\psi\|^2$ 预设为原极点。

U2、S2 的量词仅涉及 $C_2$ 的第一实际因子。若 $\tau$ 是原 SWAP，则

$$
\operatorname{Ad}_{I\otimes H}=\tau\circ\operatorname{Ad}_{H\otimes I}\circ\tau,
\tag{167.7}
$$

因此需要的第二因子版本由原置换给出。这里没有 $N\ge3$ 的 U/S 正性入口。

### 167.2 低二层与全有限层级的精确等价

**定理 167.3（二体 Bell—单衰减器判据）。** 在定义167.1的完整原域及任一固定 $0<\lambda<1$ 下：

1. B、U2、S2 同时成立，当且仅当在给定实际坐标中

$$
C_1=\operatorname{PSD}_n,\qquad C_2=\operatorname{PSD}_{n^2}.
\tag{167.8}
$$

2. B、U2、S2、T 同时成立，当且仅当

$$
C_N=\operatorname{PSD}_{n^N}\qquad\text{对每个有限 }N\ge1.
\tag{167.9}
$$

正向先只在二体上使用有限控制；恢复(167.8)之后，才取得全部原有限旁观者上的一体滤波与自身 Choi 判据，并按定理166.12调用 T。反向可对任意上述 $\lambda$ 使用标准 PSD 层级和 $g_n=\sum_i|iii\rangle$。正向不要求给定种子是原极点，也不要求它一开始具有二元控制或可逆矩阵切片。

下面逐项证明两个正向桥梁、预算与反向模型。

### 167.3 一只可逆衰减器的精确有限字

**引理 167.4（可逆矩阵的正比例有限字）。** 令 $\mathcal W_\lambda$ 为字母取自 $U(n)\cup\{S\}$ 的所有有限乘积，含空字。在任意 $A\in GL_n(\mathbb C)$ 下，存在 $W\in\mathcal W_\lambda$ 和实数 $c_A>0$，使 $W=c_AA$。因此 U2、S2 蕴含

$$
\operatorname{Ad}_{A\otimes I}(C_2)=C_2
\qquad(A\in GL_n(\mathbb C)).
\tag{167.10}
$$

证明。用置换酉共轭 $S$，得到第 $i$ 个坐标为 $\lambda$、其余坐标为一的 $S_i$。这些都是允许的实际有限字。令

$$
T_i=\prod_{k\ne i}S_k=\lambda S_i^{-1}.
\tag{167.11}
$$

右边只是矩阵恒等式；实际使用的生成字是左边的 $n-1$ 个衰减器，并未加入 $S_i^{-1}$ 字母。

固定 $i\ne j$，令 $R_{ij}(\theta)$ 只在有序平面 $(i,j)$ 上作用为实旋转

$$
R(\theta)=\begin{pmatrix}\cos\theta&-\sin\theta\\
\sin\theta&\cos\theta\end{pmatrix},\qquad 0\le\theta\le\pi/2.
$$

定义用于计算的矩阵 $M(\theta)=S_iR_{ij}(\theta)S_i^{-1}$。其平面块为

$$
\begin{pmatrix}
\cos\theta&-\lambda\sin\theta\\
\lambda^{-1}\sin\theta&\cos\theta
\end{pmatrix},\qquad \det M_{ij}(\theta)=1,
\tag{167.12}
$$

平面外是恒等。实际允许的字则是

$$
S_iR_{ij}(\theta)T_i=\lambda M(\theta).
\tag{167.13}
$$

平面块的两个奇异值之积为一，故可写为 $s(\theta),s(\theta)^{-1}$，其中 $s(\theta)\ge1$。由通常算子范数，

$$
s(\theta)\le\|S_i\|\,\|R_{ij}(\theta)\|\,\|S_i^{-1}\|=\lambda^{-1}.
$$

算子范数满足 $|\|X\|-\|Y\||\le\|X-Y\|$，所以 $s(\theta)$ 连续。在两端，$M_{ij}(0)=I_2$，而

$$
M_{ij}(\pi/2)=\begin{pmatrix}0&-\lambda\\\lambda^{-1}&0\end{pmatrix},
\quad s(0)=1,\quad s(\pi/2)=\lambda^{-1}.
$$

介值定理遂保证每个 $s\in[1,\lambda^{-1}]$ 都在某个实际角度达到。这里要求达到一个指定奇异值，并未用旋转角稠密逼近它。

对这个二阶块应用通常复 SVD（[Watrous，定理1.6及推论1.7，印刷页28—29][Q167W1]）。左右奇异向量分别扩成该平面的酉，再在平面外取恒等，得到允许的 $L,R\in U(n)$，满足

$$
L M(\theta)R=D_{ij}(s),\qquad
D_{ij}(s)=\operatorname{diag}_{i,j}(s,s^{-1}),
\tag{167.14}
$$

其余对角元为一。故 $L S_iR_{ij}(\theta)T_iR=\lambda D_{ij}(s)$ 是一个实际有限字。SVD 在这里仅供应两个平面酉，不被当作额外的正映射假设。

给定 $r>1$，选有限整数 $m\ge1$ 使 $r\le\lambda^{-m}$，置 $s=r^{1/m}$。对刚才的同一个目标字取 $m$ 次乘积，精确得到

$$
(\lambda D_{ij}(s))^m=\lambda^mD_{ij}(r).
\tag{167.15}
$$

$r=1$ 用空字；$0<r<1$ 时，用交换 $i,j$ 的酉共轭已付的 $D_{ij}(r^{-1})$。因此任意 $r>0$ 的 $D_{ij}(r)$ 均有正比例有限字。没有对单个不可逆或未付逆操作的调用。

任取正对角矩阵 $D=\operatorname{diag}(d_1,\ldots,d_n)$，令

$$
g=(d_1\cdots d_n)^{1/n}>0,\qquad t_i=d_i/g,\qquad
\prod_i t_i=1.
$$

有精确分解

$$
g^{-1}D=\prod_{i=1}^{n-1}D_{i,n}(t_i).
\tag{167.16}
$$

右边前 $n-1$ 个对角元是 $t_i$，末元是 $\prod_{i<n}t_i^{-1}=t_n$。把各因子替成已付字，其正标量相乘，得到 $cD$ 的实际有限字，其中 $c>0$。最后对任意可逆 $A$ 使用 SVD $A=UDV^*$，在该字两边乘 $U,V^*$，即得所需的 $c_AA$。

每个实际字都由 U2、S2 的二体正映射复合而成。由

$$
\operatorname{Ad}_{W\otimes I}=c_A^2\operatorname{Ad}_{A\otimes I},
$$

正锥对正标量封闭，得到(167.10)的正向包含。另对 $A^{-1}$ 应用同一有限字构造，取得其正性，再合成即得等号。此处 $A^{-1}$ 的正性是另一个已构造字的结果。∎

“有限字”允许从给定的全部 $U(n)$ 中选择精确酉参数；它不等于从有限离散门表生成，也不附带参数求取效率或统一字长界。每个字母均可逆，所以这一构造不把奇异矩阵实现为有限字。后面使用闭性取得奇异边界时，只作锥成员关系的极限。

### 167.4 对齐前的原 proper 效应及二体迹预算

**命题 167.5（以原基支付预算）。** 在尚未识别 $C_2$ 的 PSD 形状时，定义167.1、B、U2 和 S2 已足以支付 Bell proper 效应及每个有限二体字的正迹预算。

证明。先说明原 $K_2$ 紧。它闭且非空：生成性保证 $C_2$ 有非零元素，严格正迹允许归一。若存在 $x_k\in K_2$ 的范数无界，则取无界子列并归一 $y_k=x_k/\|x_k\|$。单位球面的紧性给收敛子列 $y_k\to y\in C_2$，$\|y\|=1$，而 $u_2(y)=\lim 1/\|x_k\|=0$，与严格正迹矛盾。因此 $K_2$ 有界而紧。这里任取有限维实范数即可，不使用未知一体基的 PSD 范数公式。

$\|\Omega\|^2=n$，故 $\operatorname{Tr}B=n$、$B^2=nB$。由 B 的原态成员关系，$B/n\in K_2$。于是

$$
M_B=\max_{x\in K_2}\operatorname{Tr}(Bx)<\infty,\qquad
M_B\ge\operatorname{Tr}(B\,B/n)=n>0.
\tag{167.17}
$$

B 的原对偶成员关系给下界零；对任意非零 $z\in C_2$，用 $z/u_2(z)\in K_2$ 得

$$
0\le\frac{\beta(z)}{M_B}\le u_2(z).
\tag{167.18}
$$

所以矩阵代表 $B/M_B$ 是原 proper 效应，$u_2-\beta/M_B$ 是其原补效应。此时没有使用未付的 $B\preceq nI$ 来测试原态；那个矩阵不等式本身不保证对未知原锥的单位上界。

令 $\Lambda_S=\operatorname{Ad}_{S\otimes I}$。S2 及严格正迹给 $u_2(\Lambda_Sx)>0$，对每个 $x\in K_2$ 均成立，因为 $S$ 可逆。紧性给

$$
M_S=\max_{x\in K_2}u_2(\Lambda_Sx)\in(0,\infty),\qquad
M_S\ge u_2(\Lambda_S(B/n))=\frac{\lambda^2+n-1}{n}>0.
\tag{167.19}
$$

置 $\alpha=\min\{1,M_S^{-1}\}>0$，则 $\alpha\Lambda_S$ 在整个 $C_2$ 上正且不增迹；作为矩阵合同，它是 $\operatorname{Ad}_{\sqrt\alpha S\otimes I}$。酉合同则在整个实矩阵空间上保迹，U2 因而直接给二体保迹正性。对含 $k$ 次 $S$ 的一个实际字 $W$，逐次使用上述缩放得到

$$
\alpha^k\operatorname{Ad}_{W\otimes I}:C_2\longrightarrow C_2,
\qquad u_2\alpha^k\operatorname{Ad}_{W\otimes I}\le u_2.
\tag{167.20}
$$

每个字另有自身的有限预算

$$
0<M_W:=\max_{x\in K_2}u_2(\operatorname{Ad}_{W\otimes I}x)<\infty,
\tag{167.21}
$$

所以也可整体缩放 $\min\{1,M_W^{-1}\}$。严格正下界可直接在 $B/n$ 上取得，因为其像非零且属于 $C_2$。

若该字等于 $c_AA$，逐步 proper 版本实际输出是

$$
\alpha^kc_A^2\operatorname{Ad}_{A\otimes I}(x).
\tag{167.22}
$$

其中正系数在证明锥成员关系时可以消去；在归一输入的分支质量、概率或条件化前的未归一态中必须保留。这个预算只对整个 $C_2$ 作了断言，未从 U2 或 S2 推出其高层旁观扩张。

Bell proper 效应的情形不同：由(167.3)，对任意原 $z\in C_{2+b}$，$\beta/M_B$ 和其补效应可直接切片，且

$$
0\le u_b\bigl[((\beta/M_B)\otimes\mathrm{id})z\bigr]\le u_{2+b}(z).
\tag{167.23}
$$

这是原最大界对 $(u_2-\beta/M_B)\otimes u_b$ 的应用；切片落入 $C_b$ 的理由是闭锥双极性，见 VII102.6。效应的这一结论没有把二体 U/S 映射提升到高层。∎

### 167.5 Bell 态轨道与迹对偶轨道夹出二体锥

**命题 167.6（二体整锥对齐）。** B、U2、S2 蕴含 $C_2=\operatorname{PSD}_{n^2}$，并由此得到 $C_2^*=\operatorname{PSD}_{n^2}$。

证明。固定与第166章一致的“参考在前、输出在后”向量化：

$$
|H\rangle\!\rangle=\sum_i|i\rangle\otimes H|i\rangle
=\sum_{i,j}H_{ji}|i\rangle|j\rangle.
\tag{167.24}
$$

每个二体向量唯一具有这种形式。对应于 [Watrous 的 vec 恒等式(1.127)—(1.134)][Q167W1]，本章因采用参考—输出次序，明确使用

$$
(A\otimes I)|H\rangle\!\rangle=|HA^{\mathsf T}\rangle\!\rangle,
\qquad (I\otimes D)|H\rangle\!\rangle=|DH\rangle\!\rangle.
\tag{167.25}
$$

例如第一式在 $|k\rangle|j\rangle$ 处的系数是 $\sum_iA_{ki}H_{ji}=(HA^{\mathsf T})_{jk}$。SVD 给向量的 Schmidt 分解，其 Schmidt 秩恰为 $\operatorname{rank}H$；这是同一系数对应的标准事实（[Watrous，§1.1.3，式(1.162)—(1.164)，印刷页31][Q167W1]）。

先用原态方向。引理167.4及 $B\in C_2$ 给

$$
\operatorname{Ad}_{A\otimes I}(B)
=|A^{\mathsf T}\rangle\!\rangle\langle\!\langle A^{\mathsf T}|\in C_2,
\qquad A\in GL_n(\mathbb C).
\tag{167.26}
$$

转置是 $GL_n(\mathbb C)$ 的双射，所以所有满 Schmidt 秩 dyad 已在原 $C_2$。若 $H$ 奇异，对其 SVD $H=U\operatorname{diag}(d_i)V^*$ 取

$$
H_\varepsilon=U\operatorname{diag}(d_i+\varepsilon)V^*,\qquad\varepsilon>0.
$$

这些系数矩阵可逆且趋向 $H$。相应 dyad 收敛，$C_2$ 闭，故每个 $|H\rangle\!\rangle\langle\!\langle H|$ 都在 $C_2$。再用 PSD 的有限谱分解（[Watrous，定理1.3、推论1.4及 PSD 等价刻画，印刷页20、25][Q167W1]），得到

$$
\operatorname{PSD}_{n^2}\subseteq C_2.
\tag{167.27}
$$

此处极限只补齐原锥中的边界 dyad，没有把 $H_\varepsilon$ 的字当作一个有限字实现奇异 $H$。

再用原对偶方向。设 $\Lambda_A=\operatorname{Ad}_{A\otimes I}$。由迹循环，其迹伴随是

$$
\Lambda_A^\dagger(y)=(A^*\otimes I)y(A\otimes I)
=\operatorname{Ad}_{A^*\otimes I}(y).
\tag{167.28}
$$

对 $y\in C_2^*$、$x\in C_2$，有 $\langle\Lambda_A^\dagger y,x\rangle=\langle y,\Lambda_Ax\rangle\ge0$，所以 $\Lambda_A^\dagger(C_2^*)\subseteq C_2^*$。这是正映射诱导对偶正映射的方向，不要求 $C_2$ 自对偶。由 $B\in C_2^*$ 及(167.25)，

$$
\Lambda_A^\dagger(B)
=|\overline A\rangle\!\rangle\langle\!\langle\overline A|\in C_2^*.
\tag{167.29}
$$

这里 $(A^*)^{\mathsf T}=\overline A$；没有假定共轭映射本身保持原锥。$A\mapsto\overline A$ 同样遍历全部可逆矩阵。对偶锥作为闭半空间之交是闭凸锥，故同样的奇异系数极限与谱求和给

$$
\operatorname{PSD}_{n^2}\subseteq C_2^*.
\tag{167.30}
$$

现在才使用通常 PSD 锥在迹配对下的自对偶性（[Watrous，§1.1.2，印刷页20的 PSD 等价条件4、5][Q167W1]）。对任何 $x\in C_2$，(167.30)说明 $\operatorname{Tr}(Yx)\ge0$ 对所有 $Y\succeq0$ 成立，故 $x\succeq0$。特别地，取 $Y=vv^*$ 即得 $v^*xv\ge0$。于是 $C_2\subseteq\operatorname{PSD}_{n^2}$，与(167.27)合成等号；再取完整迹对偶给所述对偶等式。∎

原态轨道支付 PSD 在原锥之内，对偶轨道支付原锥在 PSD 之内；两条方向承担不同包含。Bell 同时属于两个原锥的要求，不能在证明开始时改写成“二体原锥已经自对偶”。

### 167.6 只用原偏迹与最小积恢复一体锥

**命题 167.7（一体恢复不调用一体滤波）。** 在定义167.1下，$C_2=\operatorname{PSD}_{n^2}$ 蕴含 $C_1=\operatorname{PSD}_n$。

证明。严格正迹首先保证 $u_1\in C_1^*$。对 $z\in C_2$、任意 $f\in C_1^*$，原最大界给

$$
f\bigl[(\mathrm{id}\otimes u_1)z\bigr]=(f\otimes u_1)(z)\ge0.
$$

闭凸锥双极性遂给 $(\mathrm{id}\otimes u_1)z\in C_1$。给定的实际矩阵坐标和迹单位说明这个映射正是通常 $\operatorname{Tr}_2$，所以

$$
\operatorname{Tr}_2(C_2)\subseteq C_1.
\tag{167.31}
$$

它不依赖任何 $C_1$ 合同正性。

任取 $H\succeq0$ 及一个迹为一的环境矩阵 $q=|e\rangle\langle e|$，$\|e\|=1$。此时无需先把 $q$ 认作原态：$H\otimes q\succeq0$ 已由二体等式属于 $C_2$。因此

$$
H=\operatorname{Tr}_2(H\otimes q)\in C_1,
\qquad \operatorname{PSD}_n\subseteq C_1.
\tag{167.32}
$$

尤其 $I_n\in C_1$ 已经支付。现在对任意 $x\in C_1$，原最小界才给 $x\otimes I_n\in C_2=\operatorname{PSD}_{n^2}$。任意 $v\in\mathbb C^n$ 和非零 $w\in\mathbb C^n$ 满足

$$
0\le(v\otimes w)^*(x\otimes I_n)(v\otimes w)
=(v^*xv)\|w\|^2.
$$

故 $x\succeq0$，给反向包含。∎

这个支付次序先取得 PSD 一体元素，再使用其最小张量积；没有在未知一体锥上借用纯态、恒等矩阵或任意一体滤波作为入口。

### 167.7 对齐后的原自身 Choi、全部旁观者与三元传播

**命题 167.8（低二层支付全原旁观操作）。** 命题167.6—167.7完成之后，对任意有限 $a,b$ 和实线性 $F:W_a\to W_b$，有原自身 Choi 当且仅当；任意一体矩阵合同及其 proper 缩放具有全部原有限相关旁观者上的正性和迹预算。

证明。这里逐项使用[163.2][Q167XIII]和[VII102.6—102.7][Q167VII]。为明确前件与参考方向，低二层等式现在给

$$
B/n\in K_2,\qquad \beta/n\in\mathcal E_2.
\tag{167.33}
$$

(167.17)中的 $M_B$ 此时恰等于 $n$，因为 $0\preceq B\preceq nI$ 已可以对全部原态测试；(167.19)中的 $M_S$ 恰等于一。令 $B_a$ 为 $a$ 对 $B$ 的原乘积，按实际置换排成“全部参考腿、全部输入腿”，并置

$$
J(F)=(\mathrm{id}_{W_a}\otimes F)B_a.
\tag{167.34}
$$

实线性 $F$ 的矩阵单位公式使用其唯一复线性保 Hermitian 扩张。称 $F$ 原全旁观正，是指

$$
(\mathrm{id}_{W_s}\otimes F)C_{s+a}\subseteq C_{s+b}
\quad\text{对每个有限 }s\ge0,
\tag{167.35}
$$

也包含由原置换运输的作用位置。VII102.7的精确结论为

$$
F\text{ 原全旁观正}\quad\Longleftrightarrow\quad J(F)\in C_{a+b}.
\tag{167.36}
$$

正向把 $F$ 作用于原 $B_a\in C_{2a}$；反向将任意 $z\in C_{s+a}$ 与原 $J(F)$ 相乘，再在输入—参考腿上逐对用 $\beta$ 收缩。VII102.6保证每一步落在整个剩余原锥中，实际矩阵单位恒等式给输出恰为 $(\mathrm{id}\otimes F)z$。这包括 $z$ 的任意相关性，不用 $C_{s+a}$ 的 PSD 形状。

参考方向可由单对检查：$\beta(x\otimes y)=\operatorname{Tr}(x^{\mathsf T}y)$，而 $J(F)=\sum_{i,j}E_{ij}\otimes F(E_{ij})$，收缩给 $\sum_{i,j}x_{ij}F(E_{ij})=F(x)$，没有剩余转置。$a$ 对矩阵单位式给一般情形。

原归一杯 $B/n$ 与 proper 帽 $\beta/n$ 的每对蛇式是恒等映射的 $n^{-2}$ 倍。若直接以非零 $J(F)/\operatorname{Tr}J(F)$ 作归一资源并用 $a$ 只 proper 帽，则相应资源协议给出的正倍数为 $1/[n^a\operatorname{Tr}J(F)]$。两种归一计数的资源不同，不能互换成功质量；未缩放蛇式只承担数学正性。每只 proper 帽的不增迹由其原补效应与最大界保证。

特别地，对任意 $H\in M_n(\mathbb C)$，含奇异 $H$，

$$
J(\operatorname{Ad}_H)=|H\rangle\!\rangle\langle\!\langle H|\in C_2.
$$

所以(167.36)现在才给它在所有原有限旁观者上的正性。置 $s_H=\max\{1,\|H\|_{\rm op}\}$，则 $(H/s_H)^*(H/s_H)\preceq I$。因已取得 $C_1=\operatorname{PSD}_n$，

$$
d_H=u_1-u_1\operatorname{Ad}_{H/s_H}\in C_1^*.
$$

对 $z\in C_{s+1}$，原最大界给 $(u_s\otimes d_H)(z)\ge0$，故对应全旁观提升不增迹。酉及其逆保迹；局部合同的有限复合、不同腿的张量积和原置换因此都有相应性质。任意原 proper 效应切片同样按 VII102.6及补效应预算作用于整个原联合输入。这里标准范数界是在低二层对齐之后才使用的。∎

证明定理167.3的正向。命题167.6—167.7已经证明第一项。再假设 T。此时定理166.12的全部模型前件逐项为：固定 $n\ge2$ 及同一 $V=\operatorname{Herm}_n(\mathbb C)$；所有有限 $W_N=V^{\otimes_{\mathbb R}N}$ 的同一实际矩阵坐标；每个 $C_N$ 闭、尖、生成；严格正的乘法迹单位；整个 $K_N$、全部 $P_N$、完整自身 $C_N^*$、整个 proper 区间和全部有限单位分解；每个有限实际分块的 min/max 双界；全部实际置换及其正逆、不连续分块的运输、规范重括号和兼容原配对；空系统标量约定；以及现在已得的一、二层 PSD 等式。T 正好是定义166.2的原三体 dyad 及三展平秩条件。因此[定理166.12的条件1蕴含条件5][Q167XIII]给出(167.9)。没有额外加入原种子的极点性、全局转置正性、高层酉正性、任意外来矩阵辅助系统或物理事件菜单。

该供应对一般一腿满维种子的作用也有明确范围：它以较小实际坐标角的完整锥族作强归纳，先支付控制效应，再以两份种子、实际数据腿交换、同一个正对角权及 Bell 收缩构造可逆配对和独立相干支。维数严格下降，最后接入已具名的正则二元入口与精确有限全层级尾部。调用的是定理166.12的全部种子条件，不是“任意 GME 均可”这一更强断言。

这些协议的所有局部滤波和原帽已由命题167.8支付。它们从原最小界取得有限资源产品，逐次收缩留在原锥，proper 预算对全部相关旁观者成立。166.10—166.11给出的控制准备质量、局部缩放平方、每只帽的 $n^{-1}$ 因子与最终逆矩阵滤波均仍须保留；166.12只用有限个严格正因子得到非零成功质量，没有统一维数无关的概率或资源上界。证明中的正系数消去不把数学资源协议变成确定性物理操作。

### 167.8 标准层级的反向见证

证明定理167.3的反向。若(167.8)成立，标准 PSD 自对偶性使 $B\in C_2\cap C_2^*$；任意矩阵合同保持 PSD，因而 U2、S2 对给定 $\lambda$ 成立。这完成第一项的反向。

若对全部有限 $N$ 有(167.9)，它具有定义167.1的全部结构：PSD 锥闭、尖、生成，非零 PSD 的迹严格正；单位和迹配对按张量相乘；正简单张量给最小界；对任意正效应 $f,g$，其矩阵代表 $E,F\succeq0$ 满足 $\operatorname{Tr}[(E\otimes F)x]\ge0$，给最大界；实际置换由酉合同实现且逆同样正。完整基、极点、对偶区间和有限单位分解均取其全部原对象。

置

$$
g_n=\sum_{i=1}^n|iii\rangle.
\tag{167.37}
$$

则 $g_ng_n^*\in C_3$。对任一腿展平，$|i\rangle$ 对应的余下向量 $|ii\rangle$ 两两正交，故三个秩均为 $n$，满足 T。前段又给 B、U2、S2，且对每个 $0<\lambda<1$ 均成立。这完成定理167.3。∎

### 167.9 原态、效应、复合与过程的完整量子对应

**推论 167.9（同一实际坐标中的有限量子字典）。** 在定义167.1及 B、U2、S2、T 下，令 $D_N=n^N$。原静态数据及原全旁观数学过程具有如下对应。

| 原对象或条件 | 由整锥等式确定的量子对象 |
| --- | --- |
| 整个 $K_N$ 与凸准备 | 全部密度矩阵 $\rho\succeq0$、$\operatorname{Tr}\rho=1$，凸随机化为通常混合 |
| 全部 $P_N$ 与非零极射线 | 单位秩一投影与其正倍数；原纯态空间为 $\mathbb{CP}^{D_N-1}$ |
| 完整自身 $C_N^*$ | 同一迹配对下的完整 PSD 锥 |
| 整个 $\mathcal E_N$ | 全部 $0\preceq E\preceq I_{D_N}$，配对为 $\operatorname{Tr}(E\rho)$ |
| 全部有限单位分解 | 全部有限 POVM，$E_a\succeq0$、$\sum_aE_a=I$，含全部投影测量 |
| 原复合与所有实际分块 | 通常复 Hilbert 张量积上的全部密度矩阵，包含可分态和纠缠态 |
| 原置换、单位切片 | 通常因子置换和偏迹；适用于任意相关联合态 |
| 原全旁观正 $F:W_a\to W_b$ | 全部矩形 CP 映射及其 Choi/Kraus 表示 |
| 原逐输入不增迹、保迹 | Kraus 完备性不等式、等式；相应为数学分支、数学信道 |

证明。定理167.3给每个完整原锥的 PSD 等式。谱分解给全部密度矩阵的有限纯态混合。若密度矩阵秩至少二，沿两个正本征值作足够小的相反扰动，便是两个不同密度矩阵的非平凡中点，故非极点。若 $p=vv^*$、$\|v\|=1$ 是两个正密度矩阵的非平凡凸组合，则其正交补上的二次型全为零；各项的 PSD 性使其支撑都在 $\mathbb Cv$，迹一遂迫使各项等于 $p$。所以全部原极点恰为这些投影；基的极点与非零极射线相对应。相位商给射影空间。这是标准密度矩阵纯态几何（[Watrous，§2.1.2，印刷页62—64][Q167W2]）。给定 T 种子的归一 dyad 至此才被识别为原极点。

完整迹对偶变成 PSD；$f$ 和 $u_N-f$ 均正恰对应 $E\succeq0$、$I-E\succeq0$。完整有限单位分解遂恰为全部 POVM。原读数在这些坐标中就是

$$
\Pr(a\mid\rho)=\operatorname{Tr}(E_a\rho),\qquad
\sum_a\Pr(a\mid\rho)=1.
\tag{167.38}
$$

对纯态 $p=vv^*$、$q=ww^*$，$\operatorname{Tr}(pq)=|v^*w|^2$。这里 Born 形式来自给定线性配对与已确定的完整状态、效应区间，非另加一个非线性概率规则；标准 POVM/Born 对应见 [Watrous，定义2.34及式(2.199)—(2.202)，印刷页101—102][Q167W2]。

原坐标本已规定通常张量积，整锥等式进一步给出这个载体上的所有合法联合态，而不仅是正简单张量的凸包。对纯联合向量，Schmidt 秩大于一正是跨该切分的纠缠；一般可分态是乘积密度矩阵的凸包，纠缠态是其外的密度矩阵。例如 $B/n$ 已有 Schmidt 秩 $n\ge2$。偏迹与原单位切片一致；对原局部效应 $E$，余下未归一态为 $(f_E\otimes\mathrm{id})(\rho)$，其迹是该结果的概率。所有这些结论量化全部原有限分块。

对于过程，用命题167.8的参考在前约定，有

$$
J(F)=\sum_{i,j=1}^{n^a}|i\rangle\langle j|\otimes
F(|i\rangle\langle j|).
\tag{167.39}
$$

整锥等式使 $J(F)\in C_{a+b}$ 恰为 $J(F)\succeq0$。[Watrous，定理2.22，印刷页82—84][Q167W2]给出有限维矩形 Choi/Kraus 等价；该书 Choi 次序为输出—参考，与(167.39)相差一个给定实际因子置换。因而

$$
\begin{aligned}
F\text{ 原全旁观正}
&\Longleftrightarrow J(F)\succeq0\\
&\Longleftrightarrow F(x)=\sum_\alpha K_\alpha xK_\alpha^*,
\qquad K_\alpha:\mathbb C^{n^a}\to\mathbb C^{n^b}.
\end{aligned}
\tag{167.40}
$$

非零映射可取有限 Kraus 数等于 Choi 秩，零映射直接取零 Kraus。通常对任意矩阵参考维数的完全正性此时才成为这个数学类的等价刻画；初始假设只含原参考层级。

令 $Q_F=\sum_\alpha K_\alpha^*K_\alpha$。迹循环给 $\operatorname{Tr}F(x)=\operatorname{Tr}(Q_Fx)$，测试所有 PSD 输入得到

$$
\begin{aligned}
u_bF\le u_a&\Longleftrightarrow Q_F\preceq I_{n^a}
\Longleftrightarrow\operatorname{Tr}_{\rm out}J(F)\preceq I_{n^a},\\
u_bF=u_a&\Longleftrightarrow Q_F=I_{n^a}
\Longleftrightarrow\operatorname{Tr}_{\rm out}J(F)=I_{n^a}.
\end{aligned}
\tag{167.41}
$$

具体地，$\operatorname{Tr}_{\rm out}J(F)=Q_F^{\mathsf T}$，而转置保持通常 PSD 序。等式部分是 [Watrous，定理2.26，印刷页87—89][Q167W2]；不等式部分由同一个迹恒等式与 PSD 自对偶性得到。对附带任意原旁观者的 TNI 预算，用原最大界对 $u_a-u_bF$ 与旁观单位测试即可。$\operatorname{Tr}J(F)$ 的单个总量不能替代这一完整边缘约束。

有限 CP 分支族 $(F_a)$ 的和保迹恰要求

$$
\sum_{a,\alpha}K_{a,\alpha}^*K_{a,\alpha}=I,
\tag{167.42}
$$

其效果为 $E_a=F_a^\dagger(I)=\sum_\alpha K_{a,\alpha}^*K_{a,\alpha}$。因此有限数学仪器、分支复合、结果粗粒化也具有通常 CP 表达。任意非零 CP 映射的数学 TNI 缩放可取 $tF$，其中 $t=\min\{1,\|Q_F\|_{\rm op}^{-1}\}>0$；单个合同即 $H/s_H$ 的平方预算。这样的通常 PSD 范数公式是在全层级对齐后读取的。∎

若使用原穷尽确认读数

$$
T_p(x)=\inf\{f(x):f\in\mathcal E_N,\ f(p)=1\},
$$

对单位向量 $v$ 的秩一投影 $p=vv^*$，$0\preceq E\preceq I$ 与 $v^*Ev=1$ 蕴含 $Ev=v$，Hermitian 性使其正交交叉项为零，故 $E\succeq p$。$p$ 本身就是 proper 确认效应，遂对所有 $x\in C_N$ 有 $T_p(x)=\operatorname{Tr}(px)$。于是全部纯态间的确认比较是 $|v^*w|^2$，对有限凸准备线性延拓；这也给第166章字典中的全部有限 $S_N$，不作为本章的额外入口。

### 167.10 物理事件、条件化、更新与时间的附加前提

整锥与数学过程的识别，和哪些过程被纳入可用物理事件，是两个不同的量词。若另采用 [VII102.14][Q167VII] 的事件饱和选择，即每个数学 CP-TNI 分支及每个有限 CP 仪器都可作为事件或仪器，则上述完整数学类才成为完整可用过程菜单。单凭一个映射的正性、迹预算或非零资源收缩不能推出装置存在。

对于已给定的可用分支 $F_a$ 和归一输入 $\rho$，输出 $F_a(\rho)$ 是未归一原态，质量为

$$
p_a=\operatorname{Tr}F_a(\rho)=\operatorname{Tr}(E_a\rho).
$$

若再以归一化的输出代表已发生结果后的条件态，则只在 $p_a>0$ 时有

$$
\rho\mid a=\frac{F_a(\rho)}{p_a}.
\tag{167.43}
$$

零质量结果不定义此条件态。完整仪器给 $\sum_ap_a=1$；序列 $F_{a_k}\circ\cdots\circ F_{a_1}$ 的迹是相应有限结果串概率。这一标准仪器和条件化字典见 [Watrous，§2.3.2，式(2.255)—(2.261)，印刷页111—112][Q167W2]。若尚未选择哪个数学分支是实际更新，仅有静态效应不会选择它。

例如取 $n=2$ 的标准层级，令同一腿上的 $P_0,P_1$ 为两个基投影，其和为 $I$，$X$ 为交换这两个基向量的酉。仪器 $\rho\mapsto P_a\rho P_a$ 与 $\rho\mapsto XP_a\rho P_aX^*$ 有相同效果 $P_a$ 和相同单次概率，但输入 $P_0$、结果零的后态分别为 $P_0$ 与 $P_1$。因此本章没有选出特权 Lüders 更新。一般 $E_a^{1/2}\rho E_a^{1/2}$ 是一个可选数学仪器；要赋予它特定测量的物理更新含义，须另给更新选择或适当的不扰动公理。这里 $n=2$ 的例子已经足以区分“相同静态效果”和“相同更新”。

同样，静态层级不给物理钟、连续时间、Hamiltonian 或 $\hbar$。若额外指定带实际时间参数的可微酉一参数群 $U_{t+s}=U_tU_s$、$U_0=I$，则 $K=\dot U_0$ 满足 $K^*=-K$，群律给 $\dot U_t=KU_t$，故 $U_t=e^{tK}$。再另选时间单位和正尺度 $\hbar$，定义 $H=i\hbar K=H^*$，才写成 $U_t=e^{-itH/\hbar}$。恒等时间群和不同 $H$ 的时间群都保持同一静态锥、配对与复合数据，故本章条件不确定哪一个群是物理演化，也不确定其尺度。

### 167.11 几何简化、删除条件时的证明边界

在原结构域保持完整的意义下，本章用 B、U2、S2 替换了两条低层整锥等式。这是对充分且必要的结构条件的具体刻画，不是公理数量或逻辑独立性的最小化。U2 仍量化全部单腿酉，B 包含态和效应两个方向，原定义仍量化全部有限复合与完整效应。不能把这一条件族按几个标签数成几条离散实验。

几何上，酉只旋转方向，一只 $S$ 改变一个坐标的相对尺度。(167.11)用其余坐标上的实际衰减支付正比例逆向；将旋转夹在两者之间，连续可调的是平面的奇异值比，而最终实现是一个精确有限字。去掉正对角矩阵的几何平均，只剩乘积为一的相对伸缩，恰由这些二平面伸缩拼出。Bell 满 Schmidt 向量把每个可逆矩阵变为一个二体方向；其原态和原对偶两轨同时展开，留下完整 PSD 锥及其迹对偶。

删除入口组成部分时，可明确指出下列界限：

- 若仅保留 Bell 的原态成员关系，以上轨道论证只支付 $\operatorname{PSD}_{n^2}\subseteq C_2$；若仅保留 Bell 的原对偶成员关系，只支付 $C_2\subseteq\operatorname{PSD}_{n^2}$。两者各自并未由本证明补出另一方向。
- 若去掉 S2，或取 $\lambda=1$，所用字只给酉。Bell 的一腿酉轨道具有相同的全体 Schmidt 系数，不能由这个轨道取得具有不等 Schmidt 系数的满秩 dyad。若取 $\lambda=0$，任何含 $S$ 的字均奇异，不含 $S$ 的字均酉，也不能实现本章任意可逆矩阵的正比例生成。
- 若去掉 U2 而只用固定坐标的 $S$，其幂在 Bell 向量上的像始终位于 $\operatorname{span}\{|ii\rangle\}$，不能承担本证明的任意二平面方向控制。原置换交换的是系统腿，不自动提供全部单腿基旋转。
- 若去掉 T，本章仍证明低二层等式及原全旁观一体滤波、自身 Choi；没有由这些结论单独证明全部高层整锥 PSD。这里不据此声称存在满足其余全有限条件的非量子反模型。
- 若 T 的三个秩都小于 $n$，一般 GME 的一腿满维入口未满足。例如 $n>2$ 时嵌入的 $|111\rangle+|222\rangle$ 是 GME，但三秩都为二；166.12不能按该给定种子调用。这是本结论的未解扩展边界，不是全有限反模型。
- 若去掉完整原对偶、全部有限 min/max 分块或原正置换，整锥切片、参考—输入 Bell 接线和定理166.12均失去相应已列前件。若只给有限个层级，则没有本定理对每个有限 $N$ 的模型域。

这些是矩阵生成的明确障碍或当前推导的缺失前件，不声称已经证明各原公理互相独立。奇异系数只由闭性补入锥，不能用“每个可逆目标都有有限字”偷换成“每个奇异目标也有有限字”。若去掉闭性，(167.26)到全部 dyad 的边界步骤同样不再由本证明承担。

**完整中文图景。** 可以把二体贝尔相关想成一把同时放在“可准备”和“可测试”两边的共同标尺。旋转可以把尺子的方向转到任意位置；一只固定衰减器虽然只会压短一个方向，却能和其余方向的同类衰减拼成带正比例的反向伸缩。把旋转夹进去，就得到一段可连续选取、而实际只需有限步的相对伸缩；重复有限次便能达到任意有限尺度。这样二元贝尔轨道在状态一侧铺满全部正方向，在效应一侧排除全部负方向，二体锥就被两面夹成量子锥。原偏迹把这些方向送回一体，先取得一体恒等和纯态，随后才合法地把一体滤波送到任意相关旁观者。三元种子则负责把已经对齐的低层接口接到所有有限层：至少一条腿碰到整个原空间，另两条腿保留真正的相干分支，小角先支付控制，有限份种子与贝尔接线再把这些方向粘成可逆配对，沿现有全有限定理扩展到所有层。简化之处是把低二层的整个形状压到二元贝尔双轨、旋转和一只衰减器，把高层扩展压到一个合格三元原种子；复数矩阵载体、完整效应和全部有限复合规则仍是这幅图的地基，物理事件、更新与时间仍须各自给出额外条件。

### 167.12 数学来源、对应范围与归属

[第163章的引理163.2及第166章完整原域、定理166.12][Q167XIII]是本章全原旁观操作和一腿满维传播的仓内数学前置。其输入通过命题167.6—167.7及定义167.1逐项满足；本章不把该传播尾部当作从二体控制重新证明的结论。VII 的精确接口是[102.6的整锥切片、102.7的原自身 Bell 蛇式和 Choi 当且仅当][Q167VII]；物理事件饱和只按该卷102.14的额外定义使用。

John Watrous，*The Theory of Quantum Information*，Cambridge University Press，2018，DOI [10.1017/9781316848142][Q167Wdoi]，作者公开文本的具体供应如下：第一章印刷页20的 PSD 迹配对刻画、式(1.127)—(1.134)的向量化、定理1.3和推论1.4的谱分解、定理1.6和推论1.7的 SVD、式(1.162)—(1.164)的 Schmidt 对应；第二章§2.1.2的密度矩阵与极点、定义2.34的 POVM/Born 形式、定理2.22的矩形 Choi/Kraus 等价、定理2.26的保迹边缘条件，以及§2.3.2的仪器与正概率条件化。已知线性代数事实在上述推导内部承担相应步骤，不另作为新发现。

Aram W. Harrow，[*Exact universality from any entangling gate without inverses*][Q167H]，arXiv:0806.0631v1，推论2，对全部局部酉加一个 imprimitive 二体酉给精确有限普适性。它是第166章经正则入口消费的成熟有限生成供应之一；它不直接证明本章非酉衰减器的有限字，也不把近似普适性自动变成精确普适性。本章167.3节的构造独立给出所需非酉有限字，不将它归因于 Harrow 的酉命题。

本章的新增综合是：在保持完整原结构域的条件下，以仅在 $C_2$ 第一因子上的酉与单个衰减器正性，加同一个 Bell 的原态—原对偶关系，先推出低二层整锥等式，再连接既有一腿满维三元传播，得到定理167.3的同域等价。全有限传播属于已列仓内定理，SVD、Schmidt、PSD 自对偶与 Choi/Kraus 属于上述标准来源；这一来源范围不支持全球首创或公理独立性主张。复数域、指定维数、实际张量载体及全部有限原组合没有由该判据内生导出；无限维、任意非满腿 GME 的重建及物理动力学也不在其结论内。

[Q167XIII]: https://github.com/the-omega-institute/trureturing/blob/00427ae2ba9c9e3f6c37f2e5496b9127b6fbc6c0/docs/develop/theory/QUANTUM_ORIGIN_BINARY_TANGENT_CLOSURE_AND_GLOBAL_NONCOLLAPSE_XIII.md
[Q167VII]: https://github.com/the-omega-institute/trureturing/blob/657a8ba435bf2cae463e935d957d8038b69be8a3/docs/develop/theory/QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md
[Q167W1]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
[Q167W2]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
[Q167Wdoi]: https://doi.org/10.1017/9781316848142
[Q167H]: https://arxiv.org/abs/0806.0631v1

## 追加锚（本行以下为增补区）

## 168. 两只固定酉、一只衰减器与未知原锥的量子重建

### 完整原域与三个固定二体映射

**定义 168.1（同一实际基中的固定控制入口）。** 完整采用定义167.1的原域：固定 $n\ge2$，在给定实际 Kronecker 坐标中

$$
V=\operatorname{Herm}_n(\mathbb C),\qquad
W_N=V^{\otimes_{\mathbb R}N}
 =\operatorname{Herm}_{n^N}(\mathbb C),\qquad N\ge1.
\tag{168.1}
$$

每个 $C_N\subset W_N$ 为闭、尖、生成凸锥，$u_N=\operatorname{Tr}=u_1^{\otimes N}$ 在非零原锥上严格正。原对象取其全部：

$$
\begin{aligned}
K_N&=\{x\in C_N:\operatorname{Tr}x=1\},
&P_N&=\operatorname{ext}K_N,\\
C_N^*&=\{Y\in W_N:\operatorname{Tr}(Yx)\ge0\ (x\in C_N)\},
&\mathcal E_N&=[0,u_N]_{C_N^*}.
\end{aligned}
$$

这里以迹配对表示完整自身对偶；有限菜单是所有 $f_a\in C_N^*$、$\sum_af_a=u_N$ 的有限单位分解，凸准备及其配对使用原线性结构。对所有有限实际分块，包括经原位置置换运输的不连续分块，有

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}
 \subseteq C_a\otimes_{\max}C_b.
\tag{168.2}
$$

最小锥由正简单张量闭凸生成；最大锥由所有 $f\otimes g$、$f\in C_a^*,g\in C_b^*$ 的非负半空间相交定义。全部实际位置置换及其逆均正；重括号是同一实际空间的规范识别，且 $(f\otimes g)(x\otimes y)=f(x)g(y)$、$u_{a+b}=u_a\otimes u_b$。空系统为 $W_0=\mathbb R,C_0=\mathbb R_+,u_0=\mathrm{id}$。不预付任一层 PSD、自对偶、转置或共轭不变性，也不预付高层矩阵操作正性。复 Hermitian 载体、指定维数、全部有限复合及完整效应本身均是输入。

在实际给定单腿基 $e_0,\ldots,e_{n-1}$ 中，令 $E_{jk}=e_je_k^*$，并固定

$$
\begin{aligned}
A&=A_{\rm path}
 =\sum_{j=0}^{n-2}(E_{j,j+1}+E_{j+1,j}),
 &G&=\exp\!\left(\frac{iA}{2n}\right),\\
P_0&=E_{00},
 &D&=\exp(2\pi i\sqrt2\,P_0),\\
0&<\lambda<1,
 &S&=\operatorname{diag}(\lambda,1,\ldots,1).
\end{aligned}
\tag{168.3}
$$

其中 $G,D,S$ 对每个给定 $n,\lambda$ 均一次固定，不能在每次使用时另选参数。定义

$$
\Omega=\sum_{j=0}^{n-1}e_j\otimes e_j,\qquad
B=\Omega\Omega^*,\qquad
\beta(x)=\operatorname{Tr}(Bx).
\tag{168.4}
$$

二元入口仅为以下关系与三个正性条件：

$$
\begin{aligned}
\mathsf B &: B\in C_2\cap C_2^*,\\
\mathsf G_2 &: \operatorname{Ad}_{G\otimes I}(C_2)\subseteq C_2,\\
\mathsf D_2 &: \operatorname{Ad}_{D\otimes I}(C_2)\subseteq C_2,\\
\mathsf S_2 &: \operatorname{Ad}_{S\otimes I}(C_2)\subseteq C_2,
\qquad \operatorname{Ad}_H(x)=HxH^*.
\end{aligned}
\tag{168.5}
$$

第二个 Bell 成员关系始终是对整个未知原 $C_2$ 的非负泛函关系。三种映射均只在 $C_2$ 的第一实际因子上提出正性，未提出逆向正性、任意酉正性或任意旁观扩张正性。原 SWAP 可运输已取得的二体第一因子映射，但不等于加入单腿基变换或高层映射。

三元条件仍是167.2的同一个存在性条件：有非零实际向量 $\psi\in(\mathbb C^n)^{\otimes3}$，其 dyad 满足

$$
\mathsf T:\qquad
\psi\psi^*\in C_3,\qquad
\min_{j=1,2,3}r_j(\psi)\ge2,\qquad
\max_{j=1,2,3}r_j(\psi)=n.
\tag{168.6}
$$

$r_j$ 是该实际向量第 $j$ 腿对其余两腿的复矩阵展平秩；此时没有预设归一 dyad 是原极点。任何以已知 PSD 态或 CPTP 信道为载体的散度结论均不作为上述原域或重建入口。

### 未知闭锥上的固定映射判据

**定理 168.2（三固定映射的同域重建）。** 对定义168.1的每个完整原层级及每个固定 $0<\lambda<1$，有

$$
\mathsf B\wedge\mathsf G_2\wedge\mathsf D_2\wedge\mathsf S_2
\quad\Longleftrightarrow\quad
C_1=\operatorname{PSD}_n\ \text{且}\ C_2=\operatorname{PSD}_{n^2}.
\tag{168.7}
$$

同一原域中进一步有

$$
\mathsf B\wedge\mathsf G_2\wedge\mathsf D_2\wedge\mathsf S_2\wedge\mathsf T
\quad\Longleftrightarrow\quad
C_N=\operatorname{PSD}_{n^N}\quad\text{对全部有限 }N\ge1.
\tag{168.8}
$$

正向恢复任意一腿酉的二体正性，随后完整消费167.3的已建立证明。控制中间步骤是已知紧群及路径秩一控制数学在此固定离散对上的应用；本定理的综合内容是它们对未知原锥正性入口的作用及与167的同域接合，不主张这些控制事实的新颖性，也不主张独立公理数最小。

证明。先只处理 $n\times n$ 控制矩阵及二体原锥。下面的闭包一律取通常算子范数；有限维矩阵的其他范数给相同拓扑。

令 $\mathcal M$ 为字母表 $\{G,D\}$ 的所有有限正向字，含空字，并令

$$
H=\overline{\mathcal M}\subseteq U(n).
\tag{168.9}
$$

这里没有逆字母。矩阵乘法连续，故 $H$ 是含单位的紧闭子半群。对任意 $h\in H$，由紧性可选严格递增整数 $q_j$，使 $h^{q_j}\to a\in U(n)$。置 $m_j=q_{j+1}-q_j\ge1$，在环境酉群中计算

$$
h^{m_j}=(h^{q_j})^{-1}h^{q_{j+1}}\longrightarrow I,
\qquad
h^{m_j-1}\longrightarrow h^{-1}.
\tag{168.10}
$$

第二个序列的指数非负，各项属于 $H$；闭性遂给 $h^{-1}\in H$。因此 $H$ 是闭子群。环境矩阵求逆在这一论证中只用于计算极限，没有将任何逆映射正性当作前提。

由于 $\sqrt2$ 无理，$D$ 的整数幂在

$$
\{\exp(itP_0):t\in\mathbb R\}
\tag{168.11}
$$

中稠密。可直接用抽屉原理核清这一步：将 $0,\sqrt2,\ldots,N\sqrt2$ 的模一余数放入 $N$ 个等长区间，得到某个非零有符号整数 $q$，使 $q\sqrt2$ 模一为 $\delta\in(0,1/N)$。无理性排除 $\delta=0$；若差为负，可取相反差。因为 $H$ 已为群，$D^q\in H$。对任意 $s\in[0,1)$，取非负整数 $k$ 使 $|k\delta-s|<\delta$，便有 $D^{qk}$ 与 $\exp(2\pi isP_0)$ 的距离随 $N\to\infty$ 趋零。于是(168.11)整个包含于 $H$。

为避免把闭子群的矩阵对数误认为自动属于其无穷小代数，明确采用

$$
\mathfrak h=\{X\in\mathfrak u(n):\exp(tX)\in H
 \text{ 对所有 }t\in\mathbb R\}.
\tag{168.12}
$$

这是闭实 Lie 子代数，且 $iP_0\in\mathfrak h$。所需闭群事实对应于 von Neumann 原文第二部§§1—4的实无穷小代数与第三部§§2—4的指数接合：其闭包是保留非零行列式极限的相对 $GL$ 闭包；本处 $H\subset U(n)$ 紧闭，完全满足这一条件。[该原文][Q168VN]的相关矩阵结论在这里也可由如下极限直接取得，因而不需要更强的闭子群结构定理。

闭性与实数倍封闭直接来自指数连续性及参数重标。若 $X,Y\in\mathfrak h$，矩阵指数展开和酉矩阵乘积的望远镜估计给

$$
\left(e^{tX/m}e^{tY/m}\right)^m\longrightarrow e^{t(X+Y)}.
\tag{168.13}
$$

具体地，每个小因子与 $e^{t(X+Y)/m}$ 的差为 $O(m^{-2})$；两者及其幂均为酉，$m$ 个因子的总差至多为 $O(m^{-1})$。所有左侧矩阵属于 $H$，故 $X+Y\in\mathfrak h$。同样，直接相乘二阶指数展开得到

$$
C(s):=e^{sX}e^{sY}e^{-sX}e^{-sY}
 =I+s^2[X,Y]+O(|s|^3).
\tag{168.14}
$$

对 $t\ge0$，取 $s=\sqrt{t/m}$，则 $C(s)^m\to e^{t[X,Y]}$：与 $e^{(t/m)[X,Y]}$ 的逐因子差为 $O(m^{-3/2})$，望远镜总差为 $O(m^{-1/2})$。负 $t$ 可交换 $X,Y$。故 $[X,Y]\in\mathfrak h$。这里的 $O$ 常数只依赖固定 $t,X,Y$，不涉及原锥或物理资源预算。

下一步从固定的 $G$ 恢复对路径漂移的无穷小稳定性；不能仅由 $G\in H$ 断言其主对数在 $\mathfrak h$。设

$$
K=\frac{iA}{2n},\qquad
L=\operatorname{ad}_K,\quad L(X)=[K,X],\qquad
\mathcal T(X)=GXG^*.
\tag{168.15}
$$

由 $H$ 的群性，$\mathcal T(\mathfrak h)=\mathfrak h$。对 $e^{tK}Xe^{-tK}$ 求导，或直接比较指数级数，给出在矩阵空间上的恒等式 $\mathcal T=e^L$。

对任意 $z\in\mathbb C^n$，路径矩阵满足

$$
|z^*Az|
 \le2\sum_{j=0}^{n-2}|z_j||z_{j+1}|
 \le2\sum_{j=0}^{n-1}|z_j|^2,
\qquad \|A\|_{\rm op}\le2.
\tag{168.16}
$$

记 $A$ 的特征值为 $a_0,\ldots,a_{n-1}$。在相应矩阵单位的正交基中，$L$ 的复特征值为 $i\delta_{ab}$，其中

$$
\delta_{ab}=\frac{a_a-a_b}{2n},\qquad
|\delta_{ab}|\le\frac2n\le1.
\tag{168.17}
$$

因此在 Hilbert—Schmidt 矩阵空间上，$\mathcal T$ 为酉算子，且

$$
\|\mathcal T-I\|
 \le 2\sin(1/n)\le2\sin(1/2)<1.
\tag{168.18}
$$

这只是给定控制矩阵的范数估计，不是对未知原态作 PSD 范数预算。收敛的实系数算子级数于是满足

$$
\log\mathcal T
 =\sum_{r=1}^{\infty}\frac{(-1)^{r+1}}r(\mathcal T-I)^r
 =L.
\tag{168.19}
$$

最后一个等号可在上述特征基逐项检查：对每个 $|\delta_{ab}|\le1$，标量级数在 $|e^{i\delta_{ab}}-1|<1$ 内取值为 $i\delta_{ab}$，没有 $2\pi$ 混叠。$\mathfrak h$ 是闭实向量空间，每个 $(\mathcal T-I)^r$ 保持它，因而

$$
[iA,\mathfrak h]\subseteq\mathfrak h.
\tag{168.20}
$$

这并未先行假定 $iA\in\mathfrak h$。固定步长 $1/(2n)$ 的作用正是使(168.19)合法；所用的是共轭算子的对数，而不是未经说明地对群元素取对数。

现在给出路径端点控制所需的完整矩阵单位计算。令

$$
Z_j=iE_{jj},\qquad
X_j=E_{j,j+1}-E_{j+1,j},\qquad
Y_j=i(E_{j,j+1}+E_{j+1,j}),
\tag{168.21}
$$

并约定 $X_{-1}=X_{n-1}=0$。直接使用 $E_{ab}E_{cd}=\delta_{bc}E_{ad}$，得到

$$
\begin{aligned}
[iA,Z_j]&=X_j-X_{j-1},\\
[Z_j,X_j]&=Y_j,\\
[X_j,Y_j]&=2(Z_j-Z_{j+1})\qquad(0\le j\le n-2).
\end{aligned}
\tag{168.22}
$$

已有 $Z_0\in\mathfrak h$。由(168.20)先得 $X_0$，再用(168.22)得到 $Y_0,Z_1$。若已得 $Z_j$ 和 $X_{j-1}$，同样先得 $X_j=[iA,Z_j]+X_{j-1}$，再得 $Y_j$ 及 $Z_{j+1}=Z_j-[X_j,Y_j]/2$。有限归纳给出全部 $Z_j$ 和相邻 $X_j,Y_j$，也在此时给 $iA=\sum_jY_j\in\mathfrak h$。

对 $p<q$ 定义 $X_{pq}=E_{pq}-E_{qp}$、$Y_{pq}=i(E_{pq}+E_{qp})$。若 $p<q<r$，矩阵单位乘法另给

$$
[X_{pq},X_{qr}]=X_{pr},\qquad
[Z_p,X_{pq}]=Y_{pq}.
\tag{168.23}
$$

沿路径距离归纳，所有 $X_{pq},Y_{pq}$ 都在 $\mathfrak h$。这些矩阵连同 $Z_j$ 是 $\mathfrak u(n)$ 的实基，故

$$
\mathfrak h=\mathfrak u(n).
\tag{168.24}
$$

这一计算是路径端点的零强迫控制：端点仅有一个尚未取得的邻点，交换子逐个取得其投影，再沿边传播。Godsil—Severini 的引理1及推论3给出实对称矩阵秩一控制、路径端点与连续参数酉族的先例；[Burgarth 等的推论4.2][Q168BZ]在“实对称、非零非对角元同号、连通图、零强迫集”条件下给 $\mathfrak u(n)$。本处 $A$ 是实对称路径邻接矩阵，非零边权均为一，$\{0\}$ 按 $0\to1\to\cdots\to n-1$ 零强迫全部顶点，故这些条件逐项匹配。这些文献的连续控制结论并不直接把固定 $G,D$ 变成连续字母；(168.10)—(168.20)承担这一额外接合，(168.22)—(168.23)明确给出所需 Lie 计算。没有用结合代数的 Burnside 不可约性代替 Lie 可控性。

每个 $U\in U(n)$ 都是某个反 Hermitian 矩阵的指数：酉谱分解后为其有限个特征相位选择实角度即可。由(168.12)、(168.24)，$U\in H$。结合(168.9)，得到

$$
\overline{\mathcal M}=U(n).
\tag{168.25}
$$

这个等式只说有限正向字稠密。至此得到的全部连续参数属于数学闭包，不是新加入的原字母。

回到未知原 $C_2$。由 $\mathsf G_2,\mathsf D_2$，每个 $W\in\mathcal M$ 的第一因子合同保持 $C_2$。固定任意 $U\in U(n)$，取 $W_k\in\mathcal M$ 使 $W_k\to U$。对每个固定 $x\in C_2$，通常矩阵乘法连续，具体有

$$
\begin{aligned}
&\|(W_k\otimes I)x(W_k^*\otimes I)
 -(U\otimes I)x(U^*\otimes I)\|_{\rm op}\\
&\hspace{2em}\le2\|W_k-U\|_{\rm op}\,\|x\|_{\rm op}
 \longrightarrow0.
\end{aligned}
\tag{168.26}
$$

原锥闭性遂给

$$
\operatorname{Ad}_{U\otimes I}(C_2)\subseteq C_2
 \qquad(U\in U(n)).
\tag{168.27}
$$

这里没有假定 $x\succeq0$。对 $U^*$ 再用同一结论，取得逆向正性及等号。故第167章的 U2 已由两个固定映射导出。其迹伴随也保持原对偶锥，因为正映射对偶正性来自原配对，不需要原锥先自对偶。

在使用任何 PSD 态范数预算之前，原 proper 与迹预算完全按167.5支付。具体地，严格正迹与闭性使 $K_2$ 紧；该结论的反证是将一个无界归一原态列除以其范数，得到非零且迹零的原锥极限。设

$$
\begin{aligned}
M_B&=\max_{x\in K_2}\beta(x),\\
M_S&=\max_{x\in K_2}
 u_2\bigl(\operatorname{Ad}_{S\otimes I}x\bigr),
 &\alpha&=\min\{1,M_S^{-1}\}.
\end{aligned}
\tag{168.28}
$$

由 $B/n\in K_2$ 和 Bell 双向关系，$M_B\ge n>0$，$\beta/M_B\in\mathcal E_2$；$S$ 可逆且原正，给 $0<M_S<\infty$，故 $\alpha>0$。对任一原字母表 $\{G,D,S\}$ 的有限字 $W$，若其中有 $k$ 次 $S$，则

$$
\begin{aligned}
\alpha^k\operatorname{Ad}_{W\otimes I}&:C_2\longrightarrow C_2,\\
u_2\alpha^k\operatorname{Ad}_{W\otimes I}&\le u_2,\\
0<M_W&:=\max_{x\in K_2}
 u_2\bigl(\operatorname{Ad}_{W\otimes I}x\bigr)<\infty.
\end{aligned}
\tag{168.29}
$$

$G,D$ 的保迹性是全矩阵空间的恒等式；$S$ 的不增迹缩放由原紧基给出。$M_W>0$ 因为原字全部可逆，$B/n$ 的像非零且仍在原锥中。每个字也可整体乘 $\min\{1,M_W^{-1}\}$。这些缩放在分支质量中必须保留。此处没有把 $M_S$ 直接设为一，也没有用 $B\preceq nI$ 推出未知原态上的 proper 上界。Bell proper 效应在相关原旁观者上的切片预算可直接由(168.2)及 VII102.6取得；这不提升任何未支付的矩阵映射。

现在 $\mathsf B$、(168.27)与 $\mathsf S_2$ 正好是定理167.3第一项的 B、U2、S2，定义168.1正好保留定义167.1的所有前件。故直接消费其证明，得到(168.7)的正向。精确接口为：167.4从已恢复的整个 $U(n)$ 连续字母表和 $S$ 构造每个可逆滤波的正比例有限字；167.5保留其原预算；167.6分别用 Bell 原态轨道与原对偶轨道支付两个锥包含；167.7只用原偏迹与最小积恢复 $C_1$。这些 SVD、Bell 两包含与一体恢复论证沿用原证明，不在此重复。

只有在低二层等式取得之后，才调用167.8及 XIII163.2、VII102.6—102.7：对每个 $H_0\in M_n(\mathbb C)$，包括奇异矩阵，$\operatorname{Ad}_{H_0}$ 的 Choi dyad 已属于原 $C_2$，从而该一体合同在全部有限原相关旁观者上正；其 proper 缩放用已取得的 $C_1=\operatorname{PSD}_n$ 支付。这一支付次序不对齐前的高层矩阵映射作任何正性断言。

若再有 $\mathsf T$，定义166.1剩余前件正是已列的同一实际复张量载体、全部有限闭尖生成锥、严格正乘法迹、完整原基与效应、全部实际 min/max 分块、置换及正逆、重括号、原配对和空系统，加刚得到的两条低层 PSD 等式。$\mathsf T$ 又逐字满足166.2的 dyad 与三展平秩要求。因此按167.3第二项所接的166.12“条件1蕴含条件5”，直接得到(168.8)的正向。该传播的有限强归纳、两份种子接合及最终有限尾部均复用166.12，而不从本章的稠密控制重新证明；它们的严格正有限资源系数仍按167.8所引接口保留。

反向若 $C_1,C_2$ 是所述 PSD 锥，则 PSD 迹自对偶性给 $\mathsf B$，通常矩阵合同正性给三个固定条件，不论这些固定字母是否具有有限字长的精确普适性。若全部有限锥均标准，则另取 $g_n=\sum_{j=0}^{n-1}|jjj\rangle$；其 dyad 属于 $C_3$，三个展平秩均为 $n$，故满足 $\mathsf T$。完整标准层级的 min/max、置换及完整菜单前件正是167.3反向已核清的同域模型。于是两个等价均成立。∎

### 有限正向字、闭锥极限与奇异边界

**命题 168.3（精确有限性与闭包的不同结论）。** 对168.1的固定矩阵，以下各项同时成立；其中涉及原锥的正性与预算时，另采用168.2左侧的二元条件。

1. $\{G,D\}$ 的有限正向字在 $U(n)$ 中稠密；有限字集合不能等于 $U(n)$，其合同集合也不能包含所有酉合同。
2. 对每个 $A_0\in GL_n(\mathbb C)$，存在 $c>0$ 及 $\{G,D,S\}$ 的有限正向字序列 $W_\ell$，使 $W_\ell\to cA_0$。第167章同时给出 $cA_0$ 在扩大的字母表 $U(n)\cup\{S\}$ 中的一个精确有限字。后一事实不蕴含前一原三字母表中的精确有限表达。
3. 三个原字母均可逆，所以每个原有限字均可逆；对二体向量的一腿作用保持 Schmidt 秩，但不必保持 Schmidt 系数。奇异目标可经锥闭性进入成员关系，也可在低层对齐后经原自身 Choi 接口取得全旁观正性；两者都不是原字母的奇异有限字。

证明。第一项的稠密性是(168.25)。有限字集合可数，而 $U(n)$ 不可数；对合同去掉全局相位后仍有不可数的 $PU(n)$，因 $n\ge2$，故合同也不能全部精确命中。

对第二项，167.4给一个精确的有限乘积

$$
V_r\cdots V_1=cA_0,\qquad
V_j\in U(n)\cup\{S\},\quad c>0.
\tag{168.30}
$$

其中酉字母个数有限。分别用(168.25)的原正向酉字逼近每个酉字母，所有 $S$ 位置保持不变。有限次矩阵乘法连续，遂得 $W_\ell\to cA_0$。这里 $c$ 与(168.30)固定；不是将逼近误差吸收到一个未说明的精确等式中。另在168.2左侧的二元条件下，若(168.30)含 $k$ 次 $S$，上述每个 $W_\ell$ 仍恰含 $k$ 次 $S$，因此(168.29)的同一个 $\alpha^k$ 给其二体数学预算；极限也保持这一数学不等式。一般随目标变化的构造没有统一字长或统一概率下界。

精确原字甚至不能命中任意可逆矩阵的全部正比例类：原有限字只有可数多个正比例类，而 $GL_n(\mathbb C)/\mathbb R_{>0}$ 不可数。特定目标能否恰有一个原有限字，不由稠密性决定。167.4所给 $S^{-1}$ 及其他逆滤波的正比例实现也使用扩大后的连续酉字母表；它们的锥正性已导出，不能据此声称原三字母的精确逆字已导出。

第三项中，给二体向量写参考—输出向量化 $|H_0\rangle\!\rangle$。一腿可逆矩阵 $R$ 将其系数矩阵变成 $H_0R^{\mathsf T}$，另一腿可逆矩阵将其变成 $RH_0$；秩不变。对 Bell 向量，$S$ 给非零 Schmidt 系数 $\lambda,1,\ldots,1$，因此改变相对系数而保持满 Schmidt 秩。酉字母则保持全部 Schmidt 系数。

所有有限字可逆，故不能等于非零奇异矩阵或把满 Schmidt 向量变为降秩向量。167.6以可逆系数趋向奇异系数，使用的是闭锥成员关系；167.8取得奇异合同的原全旁观正性，使用的是低层对齐后的自身 Choi 当且仅当。这些逻辑接口均不提供原有限字表达。∎

### 全有限量子字典及其确切接口

**推论 168.4（全部原静态数据与数学过程的量子对应）。** 在定义168.1及 $\mathsf B,\mathsf G_2,\mathsf D_2,\mathsf S_2,\mathsf T$ 下，置 $d_N=n^N$，包括 $d_0=1$。下述过程的 $a,b,s$ 均为非负有限整数，沿用空系统约定。每个有限层的全部原对象具有下表的同一实际坐标对应。

| 原对象 | 所得到的完整量子对象 |
| --- | --- |
| $K_N$、凸准备 | 全部 $d_N$ 维密度矩阵及通常凸混合 |
| $P_N$、非零极射线 | 全部单位秩一投影 $vv^*$、其正倍数；纯态空间 $\mathbb{CP}^{d_N-1}$ |
| 完整 $C_N^*$、整个 $\mathcal E_N$ | 完整 PSD 迹对偶及全部 $0\preceq E\preceq I_{d_N}$ |
| 全部有限单位分解 | 全部有限 POVM，包含全部投影测量 |
| 原读数 | $\Pr(a\mid\rho)=\operatorname{Tr}(E_a\rho)$；纯态确认重叠 $|v^*w|^2$ |
| 全部有限复合、实际分块 | 通常复 Hilbert 张量积上的全部联合密度矩阵、可分态及纠缠态 |
| 原置换、单位及效应切片 | 通常因子置换、偏迹，以及任意相关联合态的局部效应切片 |
| 实线性原全旁观正映射 $F:W_a\to W_b$ | 全部相应矩形 CP 映射、Choi 矩阵及有限 Kraus 表示 |
| 不增迹、保迹数学映射 | Kraus 完备性不等式、等式；数学分支与数学信道 |
| 有限数学分支族之和保迹 | 通常有限 CP 仪器、分支复合与结果粗粒化 |

证明。由(168.27)，本推论的假设逐项蕴含167.9的 B、U2、S2、T；原域与原对象一个不变。因此直接应用推论167.9及其证明，取得表中每个结论，包括全部极点而非一个预选纯态子集、全部原效应而非有限测试子集、全部有限原参考而非可分参考。该证明的谱分解、纯态极点与 POVM 部分不需重做；其标准量子字典对应 [Watrous §2.1.2、定义2.34][Q168W2]。给定 $\mathsf T$ 的归一 dyad 此时才被认作原纯态。

为固定矩形过程的方向，采用167.8的“参考在前、输出在后”。将实线性 $F$ 唯一扩张为复线性保 Hermitian 映射，原 $a$ 对 Bell 杯按实际置换排列为 $B_a$，则

$$
\begin{aligned}
J(F)&=(\mathrm{id}_{W_a}\otimes F)B_a
 =\sum_{i,j=0}^{d_a-1}E_{ij}\otimes F(E_{ij}),\\
F\text{ 原全旁观正}
&\Longleftrightarrow J(F)\in C_{a+b}
 \Longleftrightarrow J(F)\succeq0\\
&\Longleftrightarrow
F(x)=\sum_{\gamma}K_\gamma xK_\gamma^*,
\qquad K_\gamma:\mathbb C^{d_a}\to\mathbb C^{d_b}.
\end{aligned}
\tag{168.31}
$$

第一个当且仅当是167.8精确消费的 VII102.7，不要求先把所有高层锥认作 PSD；第二个是本定理的整锥等式；最后一个是167.9消费的有限维矩形 Choi/Kraus 结论，即 [Watrous 定理2.22][Q168W2]，其输出—参考次序以原实际置换转换。非零 $F$ 可取 Kraus 数等于 Choi 秩；零映射可用空和。任意矩阵参考维数的通常完全正性至此才成为这个已得到数学类的等价刻画。

设 $Q_F=\sum_\gamma K_\gamma^*K_\gamma$，则完整迹预算为

$$
\begin{aligned}
\operatorname{Tr}_{\rm out}J(F)&=Q_F^{\mathsf T},\\
u_bF\le u_a
&\Longleftrightarrow Q_F\preceq I_{d_a}
 \Longleftrightarrow\operatorname{Tr}_{\rm out}J(F)\preceq I_{d_a},\\
u_bF=u_a
&\Longleftrightarrow Q_F=I_{d_a}
 \Longleftrightarrow\operatorname{Tr}_{\rm out}J(F)=I_{d_a}.
\end{aligned}
\tag{168.32}
$$

这些是167.41的同一公式；保迹部分对应 [Watrous 定理2.26][Q168W2]，不等式部分由相同迹配对证明。只约束 $\operatorname{Tr}J(F)$ 不足以替代完整边缘条件。每个有限族 $(F_a)$ 是数学仪器恰要求其和保迹，即

$$
\sum_{a,\gamma}K_{a,\gamma}^*K_{a,\gamma}=I,
\qquad
E_a=F_a^\dagger(I)=\sum_\gamma K_{a,\gamma}^*K_{a,\gamma}.
\tag{168.33}
$$

分支质量为 $\operatorname{Tr}F_a(\rho)=\operatorname{Tr}(E_a\rho)$。原全旁观 TNI 预算由原最大界对 $u_a-u_bF$ 与旁观单位测试，故包括所有相关联合输入。

单位切片就是偏迹；局部效应 $E$ 的剩余未归一态可写为

$$
(f_E\otimes\mathrm{id})(\rho)
 =\operatorname{Tr}_{\rm measured}
 \bigl[(E^{1/2}\otimes I)\rho(E^{1/2}\otimes I)\bigr].
\tag{168.34}
$$

这是对余下系统的原线性切片，不选择被测系统自身的特权更新。对原穷尽确认读数

$$
T_p(x)=\inf\{f(x):f\in\mathcal E_N,\ f(p)=1\},
\tag{168.35}
$$

167.9末段的同一接口给 $T_p(x)=\operatorname{Tr}(px)$；故 $p=vv^*,q=ww^*$、单位 $v,w$ 时 $T_p(q)=|v^*w|^2$，并对全部有限凸准备线性延拓。这给全部有限纯态比较，而非另添 Born 入口。∎

### 物理事件、更新、时间与数学极限的边界

**命题 168.5（数学过程菜单不选定物理实现）。** 定理168.2与推论168.4不额外指定事件饱和、特权测量更新、物理时间群或 $\hbar$；它们的有限字稠密性也不提供极限操作的物理实现或正成功质量的极限协议。

证明。定义168.1只要求原锥上的数学正性和给定静态配对，未将每个正映射列为物理事件。按167.10及 VII102.14，另加“全部 CP-TNI 分支及全部有限 CP 仪器均可用”的事件饱和选择，才把推论168.4的完整数学类变成完整可用过程菜单。原锥闭性只保证极限向量或极限映射的数学正性，没有关于装置、可执行极限、误差成本或成功事件的存在量词。

若已经指定一个可用分支 $F_a$，并另采用按已发生结果归一输出的条件化约定，则只对

$$
p_a=\operatorname{Tr}F_a(\rho)>0
\quad\text{有}\quad
\rho\mid a=\frac{F_a(\rho)}{p_a}.
\tag{168.36}
$$

零质量结果不定义此条件态。此式及有限仪器的串联质量复用167.10的接口，与 [Watrous §2.3.2][Q168W2]一致。一个 POVM 不唯一指定 $F_a$：取实际基投影 $P_a=e_ae_a^*$，并取交换 $e_0,e_1$ 的酉 $U$，则两族 $P_a\rho P_a$ 与 $UP_a\rho P_aU^*$ 的效果同为 $P_a$、和均保迹，但输入 $P_0$ 在结果零后的状态分别为 $P_0$ 与 $P_1$。故静态字典不选择 Lüders 更新；$E_a^{1/2}\rho E_a^{1/2}$ 是一个数学选择，物理特权须另有更新或不扰动前提。

同一标准层级既容纳恒等时间群，也容纳任意选定 Hermitian $H$ 的酉时间群。若另指定具有实际时间参数的可微酉一参数群 $U_t$，其生成元 $K=\dot U_0$ 反 Hermitian，$U_t=e^{tK}$；另定时间单位和正尺度 $\hbar$ 后，定义 $H=i\hbar K$ 才有

$$
U_t=e^{-itH/\hbar}.
\tag{168.37}
$$

(168.3)中定义矩阵指数的参数只是一组固定无量纲控制常数，没有物理钟的输入。因此不能把该控制计算读成对实际 Hamiltonian、时间标度或 $\hbar$ 的重建。

对原有限字，(168.29)支付的是每个固定字的数学迹预算；对扩大连续字母表的精确有限协议，167.5、167.8及166.12支付其各自严格正的有限系数。这些结论不能互换为“任意极限协议以正成功质量实现目标”。甚至在标准模型中，$S^k$ 的每一步都可逆且不增迹，但其对输入 $P_0$ 的质量为 $\lambda^{2k}\to0$。所以逐字质量严格正并不产生关于所有字列的统一正下界；更不产生无限操作已经发生的物理事件。∎

### 几何含义、前提范围与来源的组合

**命题 168.6（固定控制压缩的几何表述）。** 在完整原域内，两固定酉条件对本章的闭原锥重建恰足以代替167的全部酉条件；此替代不减少完整复载体与全有限复合的输入，不把控制生成视为新发现，也不解决一般三条腿均非满维的 GME 入口。

证明。$\mathsf G_2,\mathsf D_2$ 通过(168.9)—(168.27)给167的 U2；反过来 U2 包含这两个指定酉。因此在其余原条件保留时，两者作为闭锥上的正性条件等价。变化在酉正性入口的索引集合：从全部酉缩到两只明确固定矩阵。原三个门的数量对 $n$ 为常数，矩阵大小及 $G$ 本身依赖 $n$；这不是对独立结构假设数量、信息量或实验成本的最小化。

用中文几何语言表述同一证明：把给定单腿基看成一条有 $n$ 个点的链，$G$ 是固定的一次短程混合，$D$ 只在链端留下一个无理相位。反复走这个相位会在闭包里扫过整圈；紧性使正向重复的闭包还包含反向运动。端点的相位方向经过固定混合后，因步长足够小，可以从共轭作用的收敛对数中取回连续的交换方向。第一个交换子抓住第一条边，再用两次交换子分离第二个点的投影，依次走到链尾；边之间的交换子又连起任意两个点，于是所有酉方向都在闭包里。这里“走到任意方向”指可以任意逼近，并由闭锥接纳极限，不是声称有限离散字能精确画出一个不可数的群。

接下来才接上167的几何：酉只转方向，$S$ 压短一个坐标并改变相对 Schmidt 系数。恢复的连续酉字母与这只衰减器的精确有限组合取得任意可逆相对伸缩。Bell 标尺同时属于原可准备锥与原可测试对偶锥：准备一侧的轨道把全部 PSD 方向送入原锥，测试一侧的轨道排除所有非 PSD 方向；原闭性补进降秩边界。偏迹再把二体形状送回一体，直到这一步之后才把任意局部合同提升到所有相关旁观者。三体种子负责把低层对齐接到全部有限层：一条腿满维使其触及原空间的每个方向，另两条腿保留非乘积相干；166.12的有限递降与接合供应全层级结论，而不是用稠密门列代替那个精确传播证明。

在这幅图里，矩阵锥的边界可以由极限补齐，物理装置的菜单却不会由闭性自动补齐；可准备和可测试的共同标尺决定 Born 配对，却不决定一次测量之后采用哪一种更新，也不决定链上的混合是怎样随物理时间发生的。复数 Hermitian 载体、整个效应区间和所有有限复合规则是这幅图已给的地基，事件饱和、特权更新及时间结构各有自己的额外前提。

准确的未解范围也由接口给出。保留全部二元条件而不要求 $\mathsf T$ 时，已经得到低二层整锥及167.8的自身 Choi、一体全旁观操作，但本证明不从这些前件单独推出所有高层 PSD，也不据此给出一个高层非量子反模型。若给定 GME 向量的三个展平秩均小于 $n$，166.12的满腿前件未满足；本章不把它提升为一般 GME 定理。若删掉原锥闭性，(168.26)不能支付极限正性；若把固定步长或无理相位任意换掉，(168.11)、(168.19)也不再由本证明保证。上述缺失是相应证明接口的边界，不是未经反例证明的公理独立性结论。

来源按每一步的数学作用区分：紧子半群的逆极限、指数与交换子极限及无混叠对数在168.2证明内完整给出；闭矩阵群的无穷小代数与指数关系是 [von Neumann 第二、三部][Q168VN]的成熟结论，原文使用的相对 $GL$ 闭包与本处紧闭酉子群兼容。路径和秩一控制的先例是 [Godsil—Severini 引理1、推论3][Q168GS]及 [Burgarth 等推论4.2][Q168BZ]；其连续参数假设与本章固定字母的区别已在(168.20)—(168.25)之间逐项承担。低二层 Bell 双轨、单衰减器与全有限接合是[第167章][Q168XVI]的原证明；进一步的原切片、自身 Choi 与满腿传播是[XIII163.2、166.12][Q168XIII]及[VII102.6—102.7][Q168VII]。完整有限字典消费167.9，其标准矩形 Choi/Kraus、POVM及仪器对应由 [Watrous 第二章][Q168W2]供应。这里新增的是这些结果在未知原 $C_2$ 的三个固定正映射入口上的综合判据；文献对应不支持全球首创或最小独立公理数主张。

上述原始控制文献为 Chris Godsil、Simone Severini，*Control by quantum dynamics on graphs*，Physical Review A **81**, 052316，DOI [10.1103/PhysRevA.81.052316](https://doi.org/10.1103/PhysRevA.81.052316)，所引公开文本为 [arXiv:0910.5397v3][Q168GS]；Daniel Burgarth、Domenico D'Alessandro、Leslie Hogben、Simone Severini、Michael Young，*Zero forcing, linear and quantum controllability for systems evolving on networks*，DOI [10.1109/TAC.2013.2250075](https://doi.org/10.1109/TAC.2013.2250075)，所引公开文本为 [arXiv:1111.1475v1][Q168BZ]。后者§4的同号、连通、零强迫条件在本处均有明确实现，不以一般不可约性替代。

闭矩阵群原文为 J. von Neumann，*Über die analytischen Eigenschaften von Gruppen linearer Transformationen und ihrer Darstellungen*，Mathematische Zeitschrift **30**, 3–42，DOI [10.1007/BF01187749](https://doi.org/10.1007/BF01187749)，[Göttingen 原文][Q168VN]第二部§§1—4、第三部§§2—4，印刷页15—24。量子字典的标准文献为 John Watrous，*The Theory of Quantum Information*，Cambridge University Press，DOI [10.1017/9781316848142](https://doi.org/10.1017/9781316848142)，[作者公开第二章][Q168W2]的§2.1.2、定理2.22、定理2.26、定义2.34及§2.3.2；各自仅供应已在对应公式中列出的标准结论。∎

[Q168XVI]: https://github.com/the-omega-institute/trureturing/blob/649238845556f2cffa315c3a8f7baeb458154f2b/docs/develop/theory/QUANTUM_ORIGIN_BINARY_BELL_ORBITS_AND_SINGLE_ATTENUATOR_XVI.md
[Q168XIII]: https://github.com/the-omega-institute/trureturing/blob/00427ae2ba9c9e3f6c37f2e5496b9127b6fbc6c0/docs/develop/theory/QUANTUM_ORIGIN_BINARY_TANGENT_CLOSURE_AND_GLOBAL_NONCOLLAPSE_XIII.md
[Q168VII]: https://github.com/the-omega-institute/trureturing/blob/657a8ba435bf2cae463e935d957d8038b69be8a3/docs/develop/theory/QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md
[Q168GS]: https://arxiv.org/abs/0910.5397v3
[Q168BZ]: https://arxiv.org/abs/1111.1475v1
[Q168VN]: https://gdz.sub.uni-goettingen.de/download/pdf/PPN266833020_0030/LOG_0005.pdf
[Q168W2]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf

## 追加锚（本行以下为增补区）

## 169. 两个固定二体映射、Fourier 相位与完整有限量子重建

**定义 169.1（与167.1完全相同的原结构域）。** 固定整数 $n\ge2$，以实向量空间

$$
V=\operatorname{Herm}_n(\mathbb C),\qquad
W_N=V^{\otimes_{\mathbb R}N}
\cong\operatorname{Herm}_{n^N}(\mathbb C),\qquad N\ge1
$$

为载体。此识别是给定的实际 Kronecker 张量坐标。对每个有限 $N$，给定闭、尖、生成凸锥 $C_N\subset W_N$；单位

$$
u_N=\operatorname{Tr}=u_1^{\otimes N}
$$

在 $C_N\setminus\{0\}$ 上严格正。配对始终为实际迹配对

$$
\langle y,x\rangle=\operatorname{Tr}(yx).
$$

用此非退化实配对表示完整自身正对偶，并始终取

$$
\begin{aligned}
C_N^{\ast}&=\{y\in W_N:\operatorname{Tr}(yx)\ge0\ \text{对所有 }x\in C_N\},\\
K_N&=\{x\in C_N:u_N(x)=1\},\qquad
P_N=\operatorname{ext}K_N,\\
\mathcal E_N&=\{y\in C_N^{\ast}:I_{n^N}-y\in C_N^{\ast}\}.
\end{aligned}
$$

这里分别使用整个归一基、全部原极点、完整自身正对偶及整个 proper 效应区间。有限菜单是全部有限单位分解：$y_a\in C_N^{\ast}$、$\sum_a y_a=I_{n^N}$；凸准备和读数使用原线性结构及上述配对。单位的矩阵代表为 $I_{n^N}$，此时并不要求它属于 $C_N$。

对所有有限正整数 $a,b$，在每个实际分块中要求

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}
\subseteq C_a\otimes_{\max}C_b.
$$

最小锥是所有正简单张量的闭凸生成锥；最大锥是所有 $f\otimes g$ 的非负半空间之交，其中 $f\in C_a^{\ast}$、$g\in C_b^{\ast}$ 遍历完整原对偶。所有实际位置置换及其逆均正；不连续分块由这些置换运输；重括号使用同一实际空间和同一联合锥的规范识别。保留

$$
(f\otimes g)(x\otimes y)=f(x)g(y),\qquad
u_{a+b}=u_a\otimes u_b,
$$

及空系统 $W_0=\mathbb R$、$C_0=\mathbb R_+$、$u_0=\mathrm{id}$。因此也保留空旁观者和标量切片。

这正是[167.1][Q169167]的整个原域；没有增加任何低层 PSD 等式、原锥自对偶性、转置或复共轭正性，以及高层矩阵操作正性。复载体、指定维数与全部有限复合是输入。记 $\operatorname{PSD}_d=\operatorname{Herm}_d^+(\mathbb C)$，并区分两种作用：

$$
\operatorname{Ad}_A(x)=AxA^{\ast},\qquad
\operatorname{Int}_A(X)=AXA^{-1}.
$$

前者是 Hermitian 载体上的合同，后者是在矩阵空间上的相似作用。以下 $\Gamma_A=\operatorname{Ad}_{A\otimes I_n}$ 只表示原二体第一因子上的合同。

**定义 169.2（两个固定正性包含及不变的种子）。** 在原单腿基 $e_0,\ldots,e_{n-1}$ 中，置

$$
\omega=e^{2\pi i/n},\qquad F_{jk}=n^{-1/2}\omega^{jk},
\qquad 0\le j,k<n,\qquad a=2^{1/(n+1)}.
$$

$F$ 是标准酉 Fourier 矩阵。固定任意一个 $0<\lambda<1$，例如 $\lambda=1/2$，并定义

$$
\begin{aligned}
G&=F\operatorname{diag}
\bigl(e^{2\pi ia},e^{2\pi ia^2},\ldots,e^{2\pi ia^n}\bigr)F^{\ast},\\
R&=\operatorname{diag}(i\lambda,1,\ldots,1),\\
\Omega&=\sum_{j=0}^{n-1}e_j\otimes e_j,\qquad B=\Omega\Omega^{\ast},
\qquad \beta(x)=\operatorname{Tr}(Bx).
\end{aligned}
$$

使用以下条件：

- **B：** $B\in C_2\cap C_2^{\ast}$，第二个成员关系量化整个原 $C_2$。
- **G2：** $\Gamma_G(C_2)\subseteq C_2$。
- **R2：** $\Gamma_R(C_2)\subseteq C_2$。
- **T：** 存在非零实际向量 $\psi\in(\mathbb C^n)^{\otimes3}$，使

$$
\psi\psi^{\ast}\in C_3,\qquad
\min_{j=1,2,3}r_j(\psi)\ge2,\qquad
\max_{j=1,2,3}r_j(\psi)=n.
$$

$r_j$ 是第 $j$ 腿对另外两腿的复矩阵展平秩。T 保持[167.2][Q169167]及[XIII166.2][Q169XIII]的完整实际三体 dyad 条件；不要求它预先为原极点。G2、R2 各是一个固定映射对整个未知二体锥的包含。它们不输入逆、环面、全部酉或任何 $N\ge3$ 的映射正性。

**定理 169.3（两个固定映射的同域充要判据）。** 在定义169.1的完整原域，对每个固定 $n\ge2$ 及每个固定 $0<\lambda<1$：

$$
\boxed{
\mathrm B+\mathrm{G2}+\mathrm{R2}
\quad\Longleftrightarrow\quad
C_1=\operatorname{PSD}_n,\quad C_2=\operatorname{PSD}_{n^2}.
}
$$

在同一个原域中还有

$$
\boxed{
\mathrm B+\mathrm{G2}+\mathrm{R2}+\mathrm T
\quad\Longleftrightarrow\quad
C_N=\operatorname{PSD}_{n^N}\quad\text{对每个有限 }N\ge1.
}
$$

其中仅 G2、R2 是矩阵正性包含的新增入口；矩阵随 $n$ 改变。正向证明先在原 $C_2$ 上取得所需连续操作的数学正性，随后直接消费167的低层判据，低层识别后才使用167.8和166.12。

**证明。** 先证明两个包含恢复167所需的全部第一腿酉正性。

第一步是固定 $G$ 的正向幂闭包。多项式 $t^{n+1}-2$ 在素数二处满足 Eisenstein 判据：所有非首项系数被二整除，常数项不被四整除。因此它在 $\mathbb Q[t]$ 上不可约。这里使用[Conrad，定理4.1及例1.6][Q169E]，参数为次数 $n+1$、素数二。于是

$$
1,a,a^2,\ldots,a^n
\quad\text{在 }\mathbb Q\text{ 上线性无关}.
$$

特别地，对 $\alpha=(a,a^2,\ldots,a^n)$ 及每个非零 $m\in\mathbb Z^n$，有 $m\cdot\alpha\notin\mathbb Z$。这只是有理线性无关性；这些数都是代数数。

为明确只需正向幂，令 $\zeta_m=e^{2\pi i m\cdot\alpha}\ne1$。几何级数给

$$
\frac1L\sum_{k=0}^{L-1}e^{2\pi ikm\cdot\alpha}
=\frac{1-\zeta_m^L}{L(1-\zeta_m)}
\longrightarrow0.
$$

[Tao，命题1的 Weyl 判据及练习5的线性情形][Q169Tao]，取环面维数 $n$、序列 $k\alpha$，说明这条正整数序列在 $\mathbb R^n/\mathbb Z^n$ 上等分布，故稠密。后一个推论也可直接看出：任一非空开集支持一个积分严格正的非负连续函数，其沿序列的平均趋向该积分，故序列必进入此开集。因此

$$
\overline{\{G^k:k\ge0\}}
=\mathbb T_F,\qquad
\mathbb T_F=
\left\{F\operatorname{diag}(e^{i\theta_0},\ldots,e^{i\theta_{n-1}})F^{\ast}:
\theta_j\in\mathbb R\right\}.
$$

闭包在通常矩阵拓扑中取。这里没有加入负幂。

第二步在调用群之前取得逆向正性。定义

$$
\mathscr M=\{A\in GL_n(\mathbb C):\Gamma_A(C_2)\subseteq C_2\}.
$$

$\mathscr M$ 含单位且对乘法封闭。它在 $GL_n(\mathbb C)$ 的相对拓扑中闭：若 $A_\ell\to A$ 且 $A$ 可逆，则对每个 $x\in C_2$，

$$
\Gamma_{A_\ell}(x)\longrightarrow\Gamma_A(x),
$$

原锥的闭性给 $\Gamma_A(x)\in C_2$。此外，对每个非零复数 $c$，

$$
\Gamma_{cA}=|c|^2\Gamma_A,\qquad
cA\in\mathscr M\ \Longleftrightarrow\ A\in\mathscr M,
$$

因为正锥允许乘除严格正的实数。这一等价仅关于锥成员关系。

G2、正向复合和上一步闭包给 $\mathbb T_F\subseteq\mathscr M$。环面自身含所有逆，故特别有 $G^{-1}\in\mathscr M$。取

$$
\begin{aligned}
P&=F\operatorname{diag}(1,\omega^{-1},\ldots,\omega^{-(n-1)})F^{\ast},\\
s&=n^{-1/2}\sum_{j=0}^{n-1}e_j,\qquad Q=ss^{\ast}.
\end{aligned}
$$

Fourier 求和给 $Pe_j=e_{j+1\bmod n}$，且

$$
P,P^{-1}\in\mathbb T_F,\qquad
e^{itQ}=F\operatorname{diag}(e^{it},1,\ldots,1)F^{\ast}
\in\mathbb T_F\quad(t\in\mathbb R).
$$

令 $z=i\lambda$、$R_j=P^jRP^{-j}$。由已得的 $P$、$P^{-1}$ 正性和 R2，各 $R_j\in\mathscr M$。$R_j$ 仅在第 $j$ 坐标上为 $z$，故

$$
\prod_{j=0}^{n-1}R_j=zI_n,\qquad
\prod_{j=1}^{n-1}R_j=zR^{-1}.
$$

第二式左边的每个因子已经具有原二体正性。因此

$$
\lambda^2\Gamma_{R^{-1}}(C_2)\subseteq C_2,
$$

除以 $\lambda^2>0$ 得 $R^{-1}\in\mathscr M$。此处没有把相位标量、逆操作或其概率当作输入。

现在才令

$$
\mathcal H=\overline{\langle G,R\rangle}^{\,GL_n(\mathbb C)},
$$

其中尖括号表示允许正负整数幂的矩阵群。乘法与求逆在 $GL_n(\mathbb C)$ 中连续，故 $\mathcal H$ 是相对闭子群；此前取得的四个字母 $G,G^{-1},R,R^{-1}$ 的正性和 $\mathscr M$ 的相对闭性给

$$
\mathcal H\subseteq\mathscr M,\qquad
\Gamma_A(C_2)=C_2\quad(A\in\mathcal H).
$$

等号还使用 $A^{-1}\in\mathcal H$。这一步没有在所有矩阵的闭包中把奇异极限当作群元素。

第三步使用实 Lie 代数，始终保持相似作用与合同的区别。按[Hall，定义2.2、定义3.13、命题3.15及定理3.16][Q169Hall]，对上述相对闭矩阵群定义

$$
\mathfrak h=\{X\in M_n(\mathbb C):e^{tX}\in\mathcal H
\ \text{对所有实数 }t\}.
$$

这里矩阵空间作为实向量空间使用。所需的一般性质可以直接在这个定义下核清：实数倍由参数重标定给出；[Hall，定理3.9][Q169Hall]的矩阵 Lie 乘积公式给

$$
e^{t(X+Y)}
=\lim_{m\to\infty}
\bigl(e^{tX/m}e^{tY/m}\bigr)^m\in\mathcal H.
$$

极限是可逆指数矩阵，所以相对闭性足够，完全不要求 $\mathcal H$ 紧。指数的连续性同样说明 $\mathfrak h$ 闭。对 $A\in\mathcal H$，

$$
e^{t\operatorname{Int}_A(X)}
=Ae^{tX}A^{-1}\in\mathcal H,
$$

故 $\operatorname{Int}_A(\mathfrak h)=\mathfrak h$。最后，对 $X,Y\in\mathfrak h$，实线性和闭性使

$$
\lim_{t\to0}\frac{e^{tX}Ye^{-tX}-Y}{t}
=XY-YX=[X,Y]
$$

仍在 $\mathfrak h$。这些是所用的全部一般 Lie 性质；指数属于群由 $\mathfrak h$ 的定义保证，无须额外假定非紧群的全局指数满射，也无须调用闭子群的流形定理。尤其没有假定 $\mathfrak h$ 对乘以 $i$ 封闭。

由 $\mathbb T_F\subseteq\mathcal H$ 和全部实参数的 $e^{itQ}\in\mathbb T_F$，得到 $iQ\in\mathfrak h$。令

$$
u=(n-1)^{-1/2}\sum_{j=1}^{n-1}e_j,\quad
P_0=e_0e_0^{\ast},\quad P_u=uu^{\ast},\quad
E=e_0u^{\ast},\quad D=ue_0^{\ast},\quad c=\frac{\sqrt{n-1}}n.
$$

因为 $e_0$ 与 $u$ 正交，

$$
iQ=\frac{i}{n}P_0+c(iE+iD)+\frac{i(n-1)}nP_u.
$$

在实矩阵空间上取 $\mathcal T=\operatorname{Int}_R$。这是相似作用 $X\mapsto RXR^{-1}$，不是 $X\mapsto RXR^{\ast}$。它保持 $\mathfrak h$，且直接计算给

$$
\begin{aligned}
\mathcal T(iP_0)&=iP_0,&
\mathcal T(iP_u)&=iP_u,\\
\mathcal T(E)&=\lambda\,iE,&
\mathcal T(iE)&=-\lambda E,\\
\mathcal T(D)&=-\lambda^{-1}iD,&
\mathcal T(iD)&=\lambda^{-1}D.
\end{aligned}
$$

因此以下三个互素的实多项式分别消去相应实块：

$$
f_0(t)=t-1,\qquad
f_E(t)=t^2+\lambda^2,\qquad
f_D(t)=t^2+\lambda^{-2}.
$$

$f_0$ 与两个二次式互素，因为二次式在 $t=1$ 处非零；两个二次式互素，因为它们的差是非零实常数。由[Conrad，实多项式中国剩余定理4.18][Q169CRT]，存在 $p_E,p_D\in\mathbb R[t]$，使

$$
\begin{array}{c|ccc}
&\bmod f_0&\bmod f_E&\bmod f_D\\ \hline
p_E&0&1&0\\
p_D&0&0&1
\end{array}
$$

成立。具体的存在理由是实 Euclidean 算法给
$b_E f_0f_D+d_E f_E=1$，取 $p_E=b_Ef_0f_D$；交换 $E,D$ 同理。因而这里所有系数均为实数，没有进行不受约束的复值插值。

将这些实多项式作用于已在 $\mathfrak h$ 中的 $iQ$，有

$$
p_E(\mathcal T)(iQ)=c\,iE,\qquad
p_D(\mathcal T)(iQ)=c\,iD.
$$

这些等式可以逐块核对：对角块被 $f_0$ 消去，$E,iE$ 的实平面被 $f_E$ 消去，$D,iD$ 的实平面被 $f_D$ 消去。每个 $p(\mathcal T)(iQ)$ 都是 $\mathcal T^k(iQ)$ 的有限实线性组合，故属于 $\mathfrak h$。再对两式各作用一次 $\mathcal T$，分别得到 $-c\lambda E$ 和 $c\lambda^{-1}D$。因为 $c,\lambda$ 非零，实线性遂给出

$$
E,\ iE,\ D,\ iD\in\mathfrak h.
$$

这独立取得了每个所需实方向和虚方向。

第四步恢复全部酉方向。普通矩阵乘法给 $ED=P_0$、$DE=P_u$，因此正确的交换子为

$$
[iE,D]=i(ED-DE)=i(P_0-P_u)=:C\in\mathfrak h.
$$

从 $iQ$ 扣除已得交叉项，置

$$
L=iQ-c(iE+iD)
=\frac{i}{n}P_0+\frac{i(n-1)}nP_u.
$$

于是仅用实线性组合便有

$$
iP_0=L+\frac{n-1}{n}C\in\mathfrak h.
$$

令 $P_j=e_je_j^{\ast}$。相似作用的已得不变性给

$$
iP_j=\operatorname{Int}_{P^j}(iP_0)\in\mathfrak h
\qquad(0\le j<n).
$$

对于 $j\ge1$，记 $E_{jk}=e_je_k^{\ast}$，直接计算

$$
\begin{aligned}
[iP_j,E]&=-\frac{iE_{0j}}{\sqrt{n-1}},&
[iP_j,iE]&=\frac{E_{0j}}{\sqrt{n-1}},\\
[iP_j,D]&=\frac{iE_{j0}}{\sqrt{n-1}},&
[iP_j,iD]&=-\frac{E_{j0}}{\sqrt{n-1}}.
\end{aligned}
$$

所以这四类矩阵单位方向全部在 $\mathfrak h$ 中。对不同的 $j,k\ge1$，再用

$$
[E_{j0},E_{0k}]=E_{jk},\qquad
[iE_{j0},E_{0k}]=iE_{jk}
$$

得到其余全部非对角方向。故斜 Hermitian 矩阵的下列实基包含于 $\mathfrak h$：

$$
\{iP_j:0\le j<n\}
\ \cup\
\{E_{jk}-E_{kj},\ iE_{jk}+iE_{kj}:0\le j<k<n\}.
$$

这证明 $\mathfrak u(n)\subseteq\mathfrak h$。$n=2$ 时 $u=e_1$，前面的四个交换子已经给全部非对角方向，无须使用存在不同 $j,k\ge1$ 的最后一步。

任意 $U\in U(n)$ 的通常酉谱分解可写成

$$
U=V_0\operatorname{diag}(e^{i\theta_0},\ldots,e^{i\theta_{n-1}})V_0^{\ast}
=e^X,\quad
X=V_0\operatorname{diag}(i\theta_0,\ldots,i\theta_{n-1})V_0^{\ast}
\in\mathfrak u(n).
$$

这里的谱分解仅是矩阵恒等式，[Watrous，定理1.3及推论1.4][Q169W1]供应该线性代数事实，并没有预设 $V_0$ 对原锥正。由 $\mathfrak h$ 的定义，$U=e^X\in\mathcal H$。于是

$$
\Gamma_U(C_2)=C_2\qquad(U\in U(n)).
$$

第五步直接回接已发表的低层定理。原正向四字给

$$
S=R^4=\operatorname{diag}(\lambda^4,1,\ldots,1),\qquad
\Gamma_S(C_2)\subseteq C_2.
$$

取167中的衰减参数为 $\lambda_{\mathrm{167}}=\lambda^4\in(0,1)$，所得恰为该章 U2、S2。B 未变，定义169.1也正是167.1。因此[定理167.3第一项][Q169167]直接给

$$
C_1=\operatorname{PSD}_n,\qquad C_2=\operatorname{PSD}_{n^2}.
$$

这一调用消费167.4的有限相对伸缩与SVD供应、167.6的 Bell 态轨道和原对偶轨道，以及167.7的原偏迹恢复；不重复这些证明。两轨的输出分别为 $\operatorname{PSD}_{n^2}\subseteq C_2$ 与 $\operatorname{PSD}_{n^2}\subseteq C_2^{\ast}$，并非事先的原锥自对偶假设。

第六步只在现在取得全原旁观接口。低二层等式使[命题167.8][Q169167]的全部前件满足：同一实际坐标、原全有限 min/max 分块、全原效应、置换及其正逆，和已经识别的一、二层 PSD 锥。它按[XIII163.2][Q169XIII]及[VII102.6—102.7][Q169VII]给出每个一体矩阵合同在任意有限原相关旁观者上的正性。若 $H$ 为任意一体矩阵，取 $s_H=\max\{1,\|H\|_{\mathrm{op}}\}$，其合同缩放 $\operatorname{Ad}_{H/s_H}$ 的所有这些提升不增迹。

同一命题还给每个实线性 $\Phi:W_p\to W_q$ 的原自身 Choi 当且仅当，$p,q\ge0$ 为整数。按“参考在前、输出在后”的次序，令 $B_p$ 为 $p$ 对 $B$ 经原置换排列的乘积，$B_0=1$，则

$$
J(\Phi)=(\mathrm{id}_{W_p}\otimes\Phi)B_p,\qquad
J(\Phi)\in C_{p+q}
\ \Longleftrightarrow\
(\mathrm{id}_{W_s}\otimes\Phi)C_{s+p}\subseteq C_{s+q}
\quad\text{对所有有限 }s\ge0.
$$

空输入或空输出由标量准备或效应切片解释。此接口含整个相关联合锥，尚不使用任何 $C_N$、$N\ge3$ 的 PSD 结论。其精确原蛇式没有剩余转置；在归一杯 $B/n$ 与 proper 帽 $\beta/n$ 下，每对蛇式乘 $n^{-2}$，该系数仅在数学正性中可消去。

最后加入 T，按精确的[XIII定理166.12，条件1蕴含条件5][Q169XIII]传播。前件对应如下：

| 166.12的前件 | 本章已给或已得的对象 |
| --- | --- |
| 166.1的固定复 Hermitian 单体及全部实际张量载体 | 定义169.1，同一个 $n$ 与实际 Kronecker 坐标 |
| 各层闭、尖、生成及严格正乘法迹 | 定义169.1的每个有限 $N$，没有截断层级 |
| 整个基、全部极点、完整自身对偶、整个 proper 区间及全部有限菜单 | 定义169.1逐项保留 |
| 每个实际 min/max 分块、正置换与正逆、规范重括号、配对、单位及空系统 | 定义169.1逐项保留 |
| 同坐标中的低二层 PSD 等式 | 第五步 |
| 原全旁观滤波、切片和自身 Choi 供应 | 第六步，167.8及其163.2、VII接口 |
| 166.2的一腿满维 GME 实际原 dyad | 定义169.2的同一个 T |

因此得到每个有限 $N$ 的 $C_N=\operatorname{PSD}_{n^N}$。166.12的严格递减支撑、控制准备、九腿收缩及其有限严格正预算按该定理消费；此处不重证其全有限尾部，也不把一般全腿非满维 GME 替代其前件。T 不需要预先是原极点。

反向先看低层：若给定实际 $C_1,C_2$ 为上述 PSD 锥，则通常 PSD 的迹自对偶性给 B，任意矩阵合同保持 PSD 给 G2、R2，对每个固定 $\lambda$ 都成立。

若全部有限原锥均为 PSD，前述低层反向仍适用。另取

$$
g_n=\sum_{j=0}^{n-1}e_j\otimes e_j\otimes e_j.
$$

其 dyad 属于 $C_3$；对任一腿展平，另两腿的向量 $e_j\otimes e_j$ 两两正交，故三个秩都是 $n$，满足 T。标准层级具有完整原域：PSD 闭、尖、生成，非零 PSD 的迹严格正；正简单张量给最小界，两个正对偶矩阵的张量为 PSD 给最大界；实际置换由酉合同实现，逆同样正。原配对、迹、全部基与效应菜单以及空系统均与定义169.1一致。这完成两个等价。∎

**命题 169.4（原始 $G,R$ 有限字的 proper 预算）。** 在尚未识别低层 PSD 时，定义169.1及 B、G2、R2 已使 Bell 效应和每个原始正向有限字具有原二体 proper 预算。该断言使用原 $K_2$ 和原 $R$，不以事后的 $R^4$ 预算替代。

**证明。** [167.5][Q169167]的原基紧性论证只用闭性、生成性与严格正单位，故适用于此处。具体地，$K_2$ 闭且非空；若其中 $x_\ell$ 范数无界，归一后的单位球面子列趋向非零 $y\in C_2$，但
$u_2(y)=\lim1/\|x_\ell\|=0$，与严格正迹矛盾。因此 $K_2$ 紧。

$B/n\in K_2$ 且 $\beta$ 在原锥上非负，所以

$$
M_B=\max_{x\in K_2}\beta(x)\ge\beta(B/n)=n>0,\qquad
0\le\frac{\beta(z)}{M_B}\le u_2(z)\quad(z\in C_2).
$$

于是 $\beta/M_B$ 和它的补效应都属于原 proper 菜单。对任意 $z\in C_{2+b}$，[VII102.6][Q169VII]的整锥切片和原最大界还给

$$
((\beta/M_B)\otimes\mathrm{id})z\in C_b,\qquad
0\le u_b\bigl[((\beta/M_B)\otimes\mathrm{id})z\bigr]
\le u_{2+b}(z).
$$

这项效应切片结论本来就量化全部原相关输入，不把二体映射正性提前提升到高层。

对于原始复衰减器，R2、可逆性、严格正迹及紧性给

$$
\begin{aligned}
0<M_R&=\max_{x\in K_2}u_2(\Gamma_Rx)<\infty,\\
M_R&\ge u_2(\Gamma_R(B/n))
=\frac{\lambda^2+n-1}{n}>0.
\end{aligned}
$$

令 $\alpha_R=\min\{1,M_R^{-1}\}>0$，则

$$
\alpha_R\Gamma_R:C_2\longrightarrow C_2,\qquad
u_2\alpha_R\Gamma_R\le u_2.
$$

它是 $\operatorname{Ad}_{\sqrt{\alpha_R}R\otimes I_n}$。$G$ 酉，故 $\Gamma_G$ 在整个矩阵空间保迹；G2 给其原二体正性。因此对任何字母取自 $\{G,R\}$ 的有限字 $W$，若含 $k$ 个 $R$，逐次复合给

$$
\alpha_R^k\Gamma_W:C_2\longrightarrow C_2,\qquad
u_2\alpha_R^k\Gamma_W\le u_2.
$$

每个字均可逆；对归一输入 $x\in K_2$，这项输出非零，质量

$$
0<\alpha_R^k u_2(\Gamma_Wx)\le1
$$

是保留全部缩放后的数学分支质量。每个字也可独立用

$$
M_W=\max_{x\in K_2}u_2(\Gamma_Wx)\in(0,\infty)
$$

取得整体预算 $\min\{1,M_W^{-1}\}\Gamma_W$。这些是逐字预算，不是字长无关的界。

在定理169.3识别低层之后，才可用通常 PSD 谱范数读出 $M_B=n$、$M_R=1$；后一等式用 $R^{\ast}R$ 的最大本征值为一且 $n\ge2$。识别之前不以 $R^{\ast}R\preceq I$ 对未知 $C_2$ 预付这一结论。

同理，定理证明中 $\prod_{j=1}^{n-1}R_j=i\lambda R^{-1}$ 的合同携带系数 $\lambda^2$。若再给各因子 proper 缩放，还须乘全部缩放系数。消去这些正系数只能取得锥成员关系，不能保留同一分支概率或把该分支变成确定事件。∎

**推论 169.5（完整有限量子字典）。** 在 B、G2、R2、T 下，令 $D_N=n^N$。同一实际坐标中的全部原静态数据和原全旁观数学过程具有如下对应：

| 完整原对象 | 确定的量子表达 |
| --- | --- |
| 整个 $K_N$、凸准备 | 全部 $\rho\succeq0$、$\operatorname{Tr}\rho=1$，凸随机化为密度矩阵混合 |
| 全部 $P_N$、非零极射线 | 全部单位秩一投影 $vv^{\ast}$、其正倍数；纯态空间为 $\mathbb{CP}^{D_N-1}$ |
| 完整自身 $C_N^{\ast}$ | 同一迹配对下的整个 $\operatorname{PSD}_{D_N}$ |
| 整个 $\mathcal E_N$ | 全部 $0\preceq E\preceq I_{D_N}$ |
| 全部有限单位分解 | 全部有限 POVM：$E_a\succeq0$、$\sum_aE_a=I$，含全部投影菜单 |
| 所有原有限实际分块及复合 | 通常复 Hilbert 张量积上的全部联合密度矩阵 |
| 原单位切片和位置置换 | 对全部相关联合态的通常偏迹与因子置换 |
| 每个原全旁观正 $\Phi:W_p\to W_q$ | 全部矩形 CP 映射及有限 Choi/Kraus 表示 |
| 逐输入不增迹、保迹 | 完整 Kraus 不等式、等式，分别为数学分支、数学信道 |

**证明。** 定理169.3已给全部整锥等式，且其证明已经支付167.9的 B、U2、S2、T 前件。因此此表是[推论167.9][Q169167]在同一载体、同一完整菜单下的直接应用。以下写明概率及矩形过程的精确参数对应。

给定原线性配对使每个归一输入及有限菜单具有

$$
p(a\mid\rho)=\operatorname{Tr}(E_a\rho),\qquad
\sum_a p(a\mid\rho)=1.
$$

全部极点是单位秩一投影，单位向量模去相位给上述射影空间；所有密度矩阵是其有限凸混合。其通常来源是[Watrous，第一章谱分解][Q169W1]及[第二章§2.1.2、定义2.34][Q169W2]，在此只用于已识别的整锥。Born 形式由原配对和完整效应区间给出。

对 $x\in C_N$，若记原穷尽确认读数为

$$
T_p(x)=\inf\{\operatorname{Tr}(Ex):0\preceq E\preceq I,\
\operatorname{Tr}(Ep)=1\},
$$

则对单位秩一 $p=vv^{\ast}$，确认条件给 $Ev=v$，故 $E\succeq p$，而 $p$ 自身是可用 proper 确认效应。因此

$$
T_p(x)=\operatorname{Tr}(px),\qquad
T_{vv^{\ast}}(ww^{\ast})=|v^{\ast}w|^2.
$$

这也确定任意有限凸准备的相应线性读数。原复合保留通常张量坐标，整锥等式进一步取得所有联合态，既含乘积态的凸包，也含其外的纠缠态；例如 $B/n$ 的 Schmidt 秩为 $n$。任意分块的边缘是偏迹，局部效应切片给余下未归一态，其迹为该结果的质量。

对于过程，$p,q,s$ 可为任意非负有限整数。实线性 $\Phi:W_p\to W_q$ 使用唯一的复线性保 Hermitian 扩张来书写矩阵单位。定理169.3证明中的原自身参考给

$$
J(\Phi)=\sum_{j,k=0}^{D_p-1}E_{jk}\otimes\Phi(E_{jk}),
\qquad
\Phi\text{ 原全旁观正}\ \Longleftrightarrow\
J(\Phi)\succeq0.
$$

[Watrous，定理2.22][Q169W2]的次序是输出—参考；交换两个实际因子后，取输入维数 $D_p$、输出维数 $D_q$，恰给

$$
J(\Phi)\succeq0
\ \Longleftrightarrow\
\Phi(x)=\sum_\mu K_\mu xK_\mu^{\ast},\qquad
K_\mu:\mathbb C^{D_p}\longrightarrow\mathbb C^{D_q}.
$$

非零映射可取 Kraus 数为 $\operatorname{rank}J(\Phi)$；零映射可取空族。该表达也说明对任意有限矩阵参考维数的通常完全正性，至此与原自身层级的全旁观正性等价；任意外来参考并非初始假设。

令 $Q_\Phi=\sum_\mu K_\mu^{\ast}K_\mu$。迹循环给

$$
\operatorname{Tr}\Phi(x)=\operatorname{Tr}(Q_\Phi x),\qquad
\operatorname{Tr}_{\mathrm{out}}J(\Phi)=Q_\Phi^{\mathsf T}.
$$

逐输入测试整个 PSD 锥，遂有

$$
\begin{aligned}
u_q\Phi\le u_p
&\Longleftrightarrow Q_\Phi\preceq I_{D_p}
\Longleftrightarrow
\operatorname{Tr}_{\mathrm{out}}J(\Phi)\preceq I_{D_p},\\
u_q\Phi=u_p
&\Longleftrightarrow Q_\Phi=I_{D_p}
\Longleftrightarrow
\operatorname{Tr}_{\mathrm{out}}J(\Phi)=I_{D_p}.
\end{aligned}
$$

等式与[Watrous，定理2.26][Q169W2]一致；不等式由同一迹恒等式得到。这里的转置只用于已识别的通常 PSD 序，不是一个原正性入口。单个总量 $\operatorname{Tr}J(\Phi)$ 不能替代这项完整边缘约束。把正泛函 $u_p-u_q\Phi$ 与旁观单位相乘，再用原最大界，给所有原相关旁观者的同一不增迹预算。

一个有限族 $(\Phi_\ell)$ 是数学仪器，当且仅当各项 CP 且

$$
\sum_{\ell,\mu}K_{\ell,\mu}^{\ast}K_{\ell,\mu}=I_{D_p}.
$$

其效果为 $E_\ell=\Phi_\ell^\dagger(I_{D_q})$，即相应 Kraus 平方和。矩形 Kraus 的乘积及标签求和分别给顺序复合和粗粒化。任意非零 CP 映射还可缩放为数学 CP-TNI：

$$
t\Phi,\qquad t=\min\{1,\|Q_\Phi\|_{\mathrm{op}}^{-1}\}>0.
$$

这些范数预算均是在整锥识别后使用。∎

**命题 169.6（事件、条件更新与时间的附加选择）。** 定理169.3确定完整静态层级及推论169.5的数学过程类。若另选[VII102.14][Q169VII]的事件饱和菜单，全部数学 CP-TNI 分支和全部有限数学仪器才具有该菜单中的物理事件解释。静态效果本身不唯一确定更新，定理也不选出物理钟、Hamiltonian 或 $\hbar$。

**证明。** 对已给定的可用分支 $\Phi_\ell$ 及输入 $\rho$，未归一输出的质量为

$$
p_\ell=\operatorname{Tr}\Phi_\ell(\rho)
=\operatorname{Tr}(E_\ell\rho).
$$

若另以归一输出解释已发生结果后的条件态，则仅在 $p_\ell>0$ 时定义

$$
\rho\mid\ell=\frac{\Phi_\ell(\rho)}{p_\ell}.
$$

零质量结果不定义该除法。完整仪器给 $\sum_\ell p_\ell=1$；有限序列的联合质量是相应分支复合后输出的迹。这是[Watrous，§2.3.2，式(2.255)—(2.261)][Q169W2]的仪器及条件化对应。把全部这些数学映射放入实际可用菜单，是VII102.14明列的额外选择，不由闭锥正性或一个有限预算断言推出。

为区分效果与更新，在任意 $n\ge2$ 的已识别单腿取基投影 $P_j$，令 $U$ 交换 $e_0,e_1$ 并固定其余基向量。两族

$$
\Phi_j(x)=P_jxP_j,\qquad
\Psi_j(x)=UP_jxP_jU^{\ast}
$$

都是数学仪器，效果同为 $P_j$。输入 $P_0$、结果零的条件态却分别为 $P_0$ 与 $P_1$。所以静态 POVM 不选出唯一更新。Lüders 族 $x\mapsto E_j^{1/2}xE_j^{1/2}$ 是一个数学选择；若赋予它特定物理测量的更新意义，还须另给更新选择或合适的不扰动条件。

同样，固定矩阵 $G$ 的幂及证明中的实参数指数不指定实际时间。若额外给定带实际时间参数的可微酉一参数群 $U_{t+s}=U_tU_s$、$U_0=I$，则 $K=\dot U_0$ 满足 $K^{\ast}=-K$，群律给 $U_t=e^{tK}$。另选时间单位和正尺度 $\hbar$，令 $H_{\mathrm{phys}}=i\hbar K$，才有

$$
H_{\mathrm{phys}}=H_{\mathrm{phys}}^{\ast},\qquad
U_t=e^{-itH_{\mathrm{phys}}/\hbar}.
$$

恒等时间群和不同此类生成元都保持同一静态 PSD 层级，故静态条件不能选定其中哪一个是物理演化或确定其尺度。∎

**命题 169.7（群闭包、原始字及标量的精确界限）。** 令 $\mathcal W^+$ 为字母取自 $\{G,R\}$ 的全部有限正向字，含空字。它可数且每个元素可逆。定理169.3所用的 $\mathcal H$ 含 $U(n)$，但

$$
\overline{\mathcal W^+}^{\,M_n(\mathbb C)}\cap U(n)=\mathbb T_F,\qquad
|\det\mathcal H|\subseteq\lambda^{\mathbb Z}.
$$

特别地 $\mathcal H\ne GL_n(\mathbb C)$，其 $\mathfrak h$ 含 $iI_n$ 而不含 $I_n$。所证闭包正性不是从原始两字母精确有限生成任意酉，也不附带统一预算、有效综合算法或具有非零成功质量的物理极限协议。

**证明。** 长度有限的二字母串可数，且 $G,R$ 均可逆。若 $W\in\mathcal W^+$ 含 $k$ 个 $R$，则

$$
|\det W|=\lambda^k.
$$

若 $W_\ell\to U\in U(n)$，则 $\lambda^{k_\ell}\to1$。由于 $k_\ell\ge0$ 为整数，最终 $k_\ell=0$，故最终 $W_\ell$ 只是 $G$ 的非负幂。定理169.3的正向幂结论便给第一式，反向包含显然。$\mathbb T_F$ 是真子群：其中矩阵的全部对角元相同，而 $e^{itP_0}$ 在 $t\notin2\pi\mathbb Z$ 时没有此性质。因此原始正向字的闭包本身不含全部 $U(n)$。

对允许逆的群字，行列式模长属于 $\lambda^{\mathbb Z}$。此集合在 $\mathbb R_{>0}$ 中闭，故取 $GL_n(\mathbb C)$ 内的相对闭包仍给第二式。对任意 $X\in\mathfrak h$，连续函数

$$
|\det e^{tX}|=e^{t\operatorname{Re}\operatorname{Tr}X}
$$

只能在该离散集合中恒等于一，所以 $\operatorname{Re}\operatorname{Tr}X=0$。这排除 $I_n\in\mathfrak h$；另一方面，定理证明已经逐个取得 $iP_j$，其实和为 $iI_n$。因而这里确实不能把实 Lie 代数当作复线性空间，也不能从相位标量推出现实伸缩生成元。

有限字至多给可数多个射影矩阵方向，$U(n)$ 模去相位仍不可数；故即使允许逐字消去标量，也不能把全部酉解释为原始有限字的精确实现。167.4的精确有限字允许从整个连续 $U(n)$ 中选取字母，本章只先证明这些字母的正性；该消费没有变成原始 $\{G,R\}$ 的有限综合。奇异系数在167的 Bell 轨道中由闭性补入，也不能成为这些可逆字的精确矩阵输出。

逆向支付使用环面极限、已正的共轭因子和正标量消去；Lie 步骤又使用相对闭群中的指数与极限。每个给定有限原始字的预算由命题169.4给出；对极限过程不存在由这些论证自动取得的统一成功下界或实际事件闭包。所有被消去的正数，在任何分支质量计算中均须保留。∎

**命题 169.8（入口节省、适用边界与来源对应）。** 在完整原结构域内，本章以 G2、R2 这两个固定二体包含替代167中的全部第一腿酉包含及单实衰减器包含，同时保持 B 和 T。节省的对象是所列矩阵正性包含的数量；独立公理数、总描述复杂度、有效门综合及物理普适性没有由这个数量最小化。

**证明。** 正向替代由定理169.3中 $U(n)\subseteq\mathcal H$ 及 $S=R^4$ 给出；反向在同一低层 PSD 等式下成立。因此这是同域条件的等价改写。每个固定包含仍量化整个原 $C_2$；Fourier 相位的次数、载体维数和矩阵条目依赖 $n$。完整原对偶、全部有限菜单、全部 min/max 复合与正置换从未被删去。

若没有 T，上述证明仍给低二层等式和167.8的全原旁观接口，但没有以此单独推出全部高层 PSD，也没有据此建立全有限非量子反模型。若给定 GME dyad 的三个展平秩均小于 $n$，则没有满足本章消费的166.12入口；例如 $n>2$ 时嵌入的 $e_0^{\otimes3}+e_1^{\otimes3}$ 三秩均为二。将这类全腿非满维 GME 作为一般重建入口仍是本章未解决的开放扩展。复数域、实际复张量载体及完整有限组合也没有由两个包含导出；无限维与物理动力学须另行处理。$\lambda=0$ 时逆向支付失效，$\lambda=1$ 时两实二次因子重合，均不在定理参数范围内。这里不据这些证明边界主张原条件彼此逻辑独立或全球最小。

数学供应及其实际参数对应如下；已知一般事实只在定理169.3及量子字典内部承担中间步骤。

| 原始来源 | 本章消费的精确范围 |
| --- | --- |
| [XVI167，固定提交649238845556f2cffa315c3a8f7baeb458154f2b][Q169167] | 完整167.1；167.3第一项，以衰减参数 $\lambda^4$ 识别低层；167.5的原基预算；167.8的全旁观/Choi接口；167.9—167.10的完整字典及物理边界 |
| [XIII，固定提交00427ae2ba9c9e3f6c37f2e5496b9127b6fbc6c0][Q169XIII] | 163.1—163.2的原合同、切片与预算；166.1—166.2的完整域和不变种子；166.12条件1到5的既有全有限传播 |
| [VII，固定提交657a8ba435bf2cae463e935d957d8038b69be8a3][Q169VII] | 102.6整锥切片；102.7自身参考的精确蛇式/Choi；102.14—102.15额外事件饱和与条件化 |
| [Keith Conrad，Irreducibility tests in Q[T]，定理4.1、例1.6][Q169E] | 对 $t^{n+1}-2$ 取素数二；仅供应 $1,a,\ldots,a^n$ 的有理线性无关性 |
| [Terence Tao，254B, Notes 1，2010年3月28日，命题1、练习2及5][Q169Tao] | 标准 $n$ 维环面、正向序列 $k(a,\ldots,a^n)$；Weyl 判据加几何级数给所需 Kronecker 线性稠密性 |
| [Brian C. Hall，An Elementary Introduction to Groups and Representations，arXiv:math-ph/0005032v1][Q169Hall] | 定义2.2的相对闭矩阵群；定理3.9、定义3.13、命题3.15、定理3.16的实指数 Lie 操作；不需要全局指数满射或群紧性 |
| [Keith Conrad，The Chinese Remainder Theorem，定理4.18][Q169CRT] | 在 $\mathbb R[t]$ 中对 $t-1,t^2+\lambda^2,t^2+\lambda^{-2}$ 作实系数分离 |
| [John Watrous，The Theory of Quantum Information，第一章][Q169W1] | 印刷页20的PSD迹配对、定理1.3及推论1.4、向量化式(1.127)—(1.134)；167内部的SVD/Schmidt供应不在此重证 |
| [同书第二章][Q169W2] | §2.1.2的状态/纯态，定义2.34的POVM，定理2.22的矩形Choi/Kraus、定理2.26的边缘预算，§2.3.2的仪器/条件化；本章参考—输出次序经实际SWAP与该书对应 |

本章的承重综合是把指定的两个固定包含经实系数相似分离接到167的原二体接口；全有限传播属于166.12，Eisenstein、环面等分布、矩阵实 Lie 性质、多项式余数分离及量子字典属于表列既有来源。这个归属不作全球新颖性或最少独立公理的主张。

[Q169167]: https://github.com/the-omega-institute/trureturing/blob/649238845556f2cffa315c3a8f7baeb458154f2b/docs/develop/theory/QUANTUM_ORIGIN_BINARY_BELL_ORBITS_AND_SINGLE_ATTENUATOR_XVI.md
[Q169XIII]: https://github.com/the-omega-institute/trureturing/blob/00427ae2ba9c9e3f6c37f2e5496b9127b6fbc6c0/docs/develop/theory/QUANTUM_ORIGIN_BINARY_TANGENT_CLOSURE_AND_GLOBAL_NONCOLLAPSE_XIII.md
[Q169VII]: https://github.com/the-omega-institute/trureturing/blob/657a8ba435bf2cae463e935d957d8038b69be8a3/docs/develop/theory/QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md
[Q169E]: https://kconrad.math.uconn.edu/blurbs/ringtheory/irredtestsoverQ.pdf
[Q169Tao]: https://terrytao.wordpress.com/2010/03/28/254b-notes-1-equidistribution-of-polynomial-sequences-in-torii/
[Q169Hall]: https://arxiv.org/pdf/math-ph/0005032v1
[Q169CRT]: https://kconrad.math.uconn.edu/blurbs/ugradnumthy/crt.pdf
[Q169W1]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
[Q169W2]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf

证明的中文几何表述如下：把原二体 Bell 相关同时放在“态”和“测试”两边，它就是一把双面的共同标尺。固定的 Fourier 谱矩阵 $G$ 虽然只给一步移动，但其相位角与一的有理线性无关性使正向反复移动在闭锥意义下遍及整个 Fourier 环面，因而取得坐标循环和沿均匀向量的一条连续秩一相位流。复衰减器 $R$ 在一个坐标上同时改变相位与长度；把它移到其余坐标后相乘，先以明确的正比例支付反向正性。随后在实矩阵空间中，向外和向内的两个交叉方向分别具有不同的长度尺度，实多项式把它们分开，再用各自已经取得的虚方向及正确的交换子补齐所有酉旋转。四次原衰减又给167所需的一只实衰减器，于是直接由既有 Bell 两轨从内外夹出二体量子锥，原偏迹恢复一体，至此才把滤波和自身 Choi 接到全部原相关旁观者。至少一条腿满维且三个二分都非乘积的原三体种子，再按166.12把低层识别传播到每个有限层。这里极限只支付数学正性，有限分支的缩放与成功质量始终保留；复载体、完整效应和全部有限复合是地基，实际事件菜单、测后更新与物理时间各有自己的额外前提。∎

## 追加锚（本行以下为增补区）

## 170. 一个端点相位的固定复正交混合与全有限量子对应

**定义 170.1（完整原域）。** 固定整数 $n\ge2$。完整采用[定义167.1][Q170XVI]的域，在给定实际 Kronecker 坐标中令

$$
V=\operatorname{Herm}_n(\mathbb C),\qquad
W_N=V^{\otimes_{\mathbb R}N}=\operatorname{Herm}_{n^N}(\mathbb C).
$$

每个有限 $N\ge1$ 有闭、尖、生成凸锥 $C_N\subset W_N$；给定单位 $u_N=\operatorname{Tr}=u_1^{\otimes N}$ 在 $C_N\setminus\{0\}$ 上严格正。原对象取整个归一基 $K_N=\{x\in C_N:u_N(x)=1\}$、全部极点 $P_N=\operatorname{ext}K_N$、完整自身正对偶 $C_N^*$、整个 proper 区间 $\mathcal E_N=[0,u_N]_{C_N^*}$，以及其中全部有限单位分解 $(f_a)$，$f_a\in C_N^*$、$\sum_af_a=u_N$。凸准备与配对使用原实线性结构，以非退化迹配对表示对偶矩阵。

对每个有限实际分块，要求

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}
 \subseteq C_a\otimes_{\max}C_b.
$$

最小锥是正简单张量的闭凸生成锥；最大锥是全部 $f\otimes g$，$f\in C_a^*,g\in C_b^*$，的非负半空间之交。全部实际位置置换及其逆均正；不连续分块由它们运输，重括号使用同一实际空间的规范识别。原配对和单位满足

$$
(f\otimes g)(x\otimes y)=f(x)g(y),\qquad u_{a+b}=u_a\otimes u_b.
$$

空系统为 $W_0=\mathbb R,C_0=\mathbb R_+,u_0=\mathrm{id}$。这些条件不预付任何一层 PSD、自对偶、转置或复共轭不变性，以及高层矩阵操作正性。单位的迹代表为 $I$，尚不据此断言 $I\in C_N$。称实线性 $F:W_a\to W_b$ 原全旁观正，若

$$
(\mathrm{id}_{W_s}\otimes F)C_{s+a}\subseteq C_{s+b}
\quad\text{对每个有限 }s\ge0,
$$

并由原置换运输至所有作用位置。数学不增迹预算也量化整个相关联合输入。

**定义 170.2（唯一固定映射与不变的 Bell、三元入口）。** 在给定基 $e_0,\ldots,e_{n-1}$ 中置 $E_{jk}=e_je_k^*$、$P_j=E_{jj}$，并一次固定

$$
\begin{aligned}
K&=\sum_{j=0}^{n-2}(E_{j,j+1}-E_{j+1,j}),
&t&=\frac1{32n},&c&=(1+i)t,\\
H&=cK,&O&=e^H,&W&=e^{\pi i\sqrt2 P_0},&M&=WO.
\end{aligned}
$$

写 $\operatorname{Ad}_A(x)=AxA^*$，以及

$$
\Omega=\sum_{j=0}^{n-1}e_j\otimes e_j,\qquad B=\Omega\Omega^*,\qquad
\beta(x)=\operatorname{Tr}(Bx).
$$

只提出两个二元条件：

$$
\mathsf B:\ B\in C_2\cap C_2^*,\qquad
\mathsf M_2:\ \operatorname{Ad}_{M\otimes I}(C_2)\subseteq C_2.
$$

这里的第二个 Bell 成员关系是在完整原 $C_2$ 上的非负泛函关系；$\mathsf M_2$ 只涉及二体第一因子，没有逆、转置态映射、连续控制或额外固定映射条件。三元条件仍为[167.2][Q170XVI]、[166.2][Q170XIII]：

$$
\mathsf T:\quad \exists\,0\ne\psi\in(\mathbb C^n)^{\otimes3},\quad
\psi\psi^*\in C_3,\quad \min_i r_i(\psi)\ge2,\quad \max_i r_i(\psi)=n.
$$

$r_i$ 是第 $i$ 腿对其余两腿的复矩阵展平秩；不要求该归一 dyad 预先为原极点。上述 $K$ 是路径的实反对称矩阵，$O^{\mathsf T}O=I$。这里的复正交与酉不同；事实上

$$
O^*O=e^{2itK}\ne I,\qquad O^*\ne O.
$$

后两式由 $K\ne0$、$\|K\|\le2$ 得到：$iK$ 为非零 Hermitian，故 $e^{2itK}\ne I$；若 $O^*=O$，则 $e^{2tK}=I$，而 $K$ 的特征值 $i\theta$ 满足 $|2t\theta|\le4t<2\pi$，迫使所有 $\theta=0$，矛盾。因此该指定 $O$ 既非酉也非 Hermitian。

**引理 170.3（低层对齐之前的原 Bell 转向及预算）。** 在170.1、$\mathsf B,\mathsf M_2$ 下，$\operatorname{Ad}_{M}$ 和 $\operatorname{Ad}_{M^{\mathsf T}}$ 均原全旁观正，并各有严格正的统一全旁观不增迹缩放。这里 $M^{\mathsf T}$ 是局部矩阵的转置，不是对未知原态作转置。

证明。先支付原帽。170.1使 $K_2$ 非空且紧：若归一原态列无界，除以其范数并取单位球面收敛子列，闭性会给一个范数一、迹零的原正向量，违反单位严格正性。于是

$$
b=\max_{x\in K_2}\beta(x)<\infty,\qquad b\ge\beta(B/n)=n>0,
\qquad \beta/b\in\mathcal E_2.
$$

这里用了 $\operatorname{Tr}B=n$、$B^2=nB$ 和 $B/n\in K_2$；上下界 $0\le\beta/b\le u_2$ 来自原对偶成员关系及原基上的最大值，没有用 PSD 序 $B\preceq nI$ 测试未知原态。

[引理VII102.6][Q170VII]在此可直接使用：对 $f\in C_a^*$、$z\in C_{a+b}$，任意 $g\in C_b^*$ 满足

$$
g((f\otimes\mathrm{id})z)=(f\otimes g)(z)\ge0,
$$

故闭锥双极性给 $(f\otimes\mathrm{id})z\in C_b$。其全部前件就是原最大界、完整自身对偶、闭性及正置换。若 $f$ proper，则对整个联合锥还有

$$
0\le u_b((f\otimes\mathrm{id})z)\le u_{a+b}(z),
$$

因为 $(u_a-f)\otimes u_b$ 也非负。它适用于任意相关输入和逐次收缩。

固定参考在前、输出在后的向量化 $|A\rangle\!\rangle=\sum_j e_j\otimes Ae_j$。由唯一固定映射得原资源

$$
R_T=(M\otimes I)B(M^*\otimes I)
 =|M^{\mathsf T}\rangle\!\rangle\langle\!\langle M^{\mathsf T}|\in C_2.
$$

原 SWAP 给 $R_M=\tau R_T=|M\rangle\!\rangle\langle\!\langle M|\in C_2$。对 $Q=M^{\mathsf T}$ 或 $M$，在输入腿 $X$、资源参考腿 $X'$ 上用 $\beta$ 收缩，则对任意 $z\in C_{s+1}$，

$$
\operatorname{cap}_{X,X'}[z_{SX}\otimes |Q\rangle\!\rangle\langle\!\langle Q|_{X'Y}]
 =(\mathrm{id}_{W_s}\otimes\operatorname{Ad}_Q)z.
$$

矩阵单位检查为

$$
\beta(E_{ab}\otimes E_{ij})=\delta_{ai}\delta_{bj},\qquad
|Q\rangle\!\rangle\langle\!\langle Q|
 =\sum_{i,j}E_{ij}\otimes QE_{ij}Q^*.
$$

复矩阵单位仅书写实 Hermitian 张量映射的唯一复线性扩张；展开后输出为 $\sum_{a,b}z_{ab}\otimes QE_{ab}Q^*$，没有剩余转置。这个恒等式也就是VII102.7证明中的原始蛇式。该引理印本开头先用低层 PSD 支付杯帽，故本处没有直接调用整条VII102.7；本处的杯与 proper 帽已由 $\mathsf B$ 和紧基独立支付。

具体原分块是 $\min(s+1,2)$ 把资源积放入 $C_{s+3}$，正置换把 $X,X'$ 移为同块，$\max(2,s+1)$ 与切片再给 $C_{s+1}$。在用于二体控制的 $s=1$ 情形，实际经过 $C_2\otimes C_2\subset C_4$ 再回 $C_2$，未使用 $C_4$ 的 PSD 形状。因而两种合同的全部原旁观正性均已取得。

令

$$
r=\operatorname{Tr}(M^*M)>0,\quad
m=\max_{x\in K_2}u_2(\operatorname{Ad}_{M\otimes I}x)>0,\quad
\alpha=\min\{1,m^{-1}\}>0.
$$

$m$ 有限由紧性，严格正由可逆 $M$ 在 $B/n$ 上的非零原像。原二体分支 $\alpha\operatorname{Ad}_{M\otimes I}$ 不增迹；施于 $B/n$ 给 $\alpha R_T/n$，其质量为 $\alpha r/n\in(0,1]$。保留这一未归一资源，再用一只 proper 帽 $\beta/b$，准确得到

$$
\frac{\alpha}{nb}\operatorname{Ad}_{M^{\mathsf T}};
$$

交换资源则得到同系数的 $\operatorname{Ad}_M$，均有全旁观预算。若改用原归一资源 $R_T/r$ 或 $R_M/r$，系数则为

$$
\eta=\frac1{br}>0.
$$

这两个计数使用不同的资源供应，不能互换实际分支质量。归一资源属于整个原 $K_2$；把它作为数学资源不宣称原来一次制备已确定性成功。对非零正输入，两种合同的像非零，严格正迹给严格正输出质量。所有原系数只在锥成员关系中可消去，在概率和未归一输出中须保留。∎

**命题 170.4（由一个圆逐边取得全部所需控制）。** 设 $\mathcal P$ 为字母 $M,M^{\mathsf T}$ 的全部有限正向矩阵字，含空字；第二个字母的原合同由170.3推导，不是第二个正性入口。则

$$
G:=\overline{\mathcal P}^{\,GL_n(\mathbb C)}
 =\{A\in GL_n(\mathbb C):|\det A|=1\}.
$$

其证明只使用一个端点圆；没有以 $U(n)\subset G$ 为假设。在170.3的原锥前件下，任意可逆局部矩阵合同及其逆均原全旁观正。

证明。由 $H^{\mathsf T}=-H$、$\det O=e^{\operatorname{Tr}H}=1$，有

$$
MM^{\mathsf T}=WOO^{\mathsf T}W=W^2
 =D:=e^{2\pi i\sqrt2 P_0},\qquad |\det M|=1.
$$

所以 $D$ 的非负幂都是正向字。其闭包是端点圆的紧子半群，包含逆：若递增 $q_j$ 满足 $D^{q_j}\to a$，则 $D^{q_{j+1}-q_j}\to I$，而非负幂 $D^{q_{j+1}-q_j-1}\to D^{-1}$。闭包因而是群。无理性和抽屉原理使任意小的非零有符号模一角出现；其非负整数倍逼近任意目标角，于是

$$
\{e^{isP_0}:s\in\mathbb R\}\subseteq G.
$$

这正是[168.10—168.11][Q170XVI]的正向循环闭包论证，所用 $D$ 完全相同。故 $W,W^{-1},D^{-1}\in G$，且

$$
M^{-1}=M^{\mathsf T}D^{-1},\qquad
(M^{\mathsf T})^{-1}=D^{-1}M,\qquad O=W^{-1}M\in G.
$$

这些是闭包中已支付的矩阵恒等式。乘法连续使 $G$ 为闭半群；现已包含两个字母的逆，故包含全部有限字的逆。若 $A_k\in\mathcal P$ 趋向可逆 $A\in G$，求逆连续给 $A_k^{-1}\to A^{-1}\in G$。因此 $G$ 确为相对 $GL$ 闭子群。每个字的行列式模为一，任何有限矩阵极限也如此，故这里的全矩阵闭包同样没有奇异元素。

采用闭矩阵群的实 Lie 代数

$$
\mathfrak g=\{X\in M_n(\mathbb C):e^{sX}\in G\ (s\in\mathbb R)\}.
$$

它是闭实向量空间，对交换子及 $X\mapsto AXA^{-1}$、$A\in G$ 不变，且 $Z_0=iP_0\in\mathfrak g$。这些结论适用的是相对 $GL$ 闭群，见 [Hall，定义2.2、定义3.13、命题3.15、定理3.16][Q170Hall]；不要求群紧，也不使 $\mathfrak g$ 成为复向量空间。

须从固定 $O$ 取得漂移交换方向。令 $\mathcal T(X)=OXO^{-1}$、$L=\operatorname{ad}_H$，作用于全部复矩阵的实向量空间，使用 Hilbert—Schmidt 范数所诱导的算子范数。注意这是相似作用；$OXO^*$ 才是合同，二者在本处不同。指数恒等式给 $\mathcal T=e^L$。把 $K$ 写成单向移位减其转置，得

$$
\|K\|_{\rm op}\le2,\qquad
\|L\|\le2\|H\|_{\rm op}\le4\sqrt2t
 =\frac{\sqrt2}{8n}<\frac18<\log2,
$$

故 $\|\mathcal T-I\|\le e^{\|L\|}-1<1/7<1$。在这个实算子空间上，[Hall定理3.6][Q170Hall]的绝对收敛实系数对数给

$$
\log\mathcal T
 =\sum_{r\ge1}\frac{(-1)^{r+1}}r(\mathcal T-I)^r=L.
$$

该定理的 $\|X\|<\log2$ 条件用于 $X=L$，不是仅凭 $O\in G$ 就声称 $\log O\in\mathfrak g$。因 $\mathcal T$ 保持闭实空间 $\mathfrak g$，逐项及极限均保持它，所以

$$
[H,\mathfrak g]\subseteq\mathfrak g.
$$

下面从 $Z_0$ 感染整条路径，逐项分离实、虚方向。置

$$
K_j=E_{j,j+1}-E_{j+1,j},\quad
S_j=E_{j,j+1}+E_{j+1,j},\quad
\Delta_j=P_j-P_{j+1},\quad Z_j=iP_j,
$$

并约定 $K_{-1}=K_{n-1}=0$。矩阵单位乘法给

$$
[Z_j,[H,Z_j]]=c(K_{j-1}+K_j).
$$

若已有 $Z_j$ 和 $cK_{j-1}$，便取得

$$
A_j=[Z_j,[H,Z_j]]-cK_{j-1}=cK_j,\qquad
B_j=[Z_j,A_j]=icS_j.
$$

对 $j=0$，所减项为零。随后

$$
\begin{aligned}
[A_j,B_j]&=2ic^2\Delta_j=-4t^2\Delta_j,\\
R_j:=[\Delta_j,A_j]/2&=cS_j,\\
[A_j,R_j]&=2c^2\Delta_j=4t^2(i\Delta_j),\\
Z_{j+1}&=Z_j-\frac{[A_j,R_j]}{4t^2}.
\end{aligned}
$$

每次除数都是非零实数。因此 $\Delta_j,i\Delta_j,Z_{j+1}\in\mathfrak g$；此处的 $i\Delta_j$ 是第三式导出的矩阵，没有将任意已知元素乘以 $i$。从 $j=0$ 到 $n-2$ 的有限归纳取得全部 $Z_j$、$A_j,B_j,\Delta_j$，也覆盖只有一条边的 $n=2$。

进一步置 $C_j=[\Delta_j,B_j]/2=icK_j$，则下列仍全为实线性组合：

$$
K_j=\frac{A_j-C_j}{2t},\qquad
iK_j=\frac{A_j+C_j}{2t},\qquad
iS_j=[Z_j,K_j],\qquad S_j=-[Z_j,iK_j].
$$

对 $p<q<r$，有 $[K_{pq},K_{qr}]=K_{pr}$，其中 $K_{pq}=E_{pq}-E_{qp}$；又 $[iP_p,K_{pq}]=i(E_{pq}+E_{qp})$。沿距离归纳得到 $\mathfrak u(n)$ 的全部实基。因此 $\mathfrak u(n)\subseteq\mathfrak g$。每个酉矩阵由有限维谱分解是一个反 Hermitian 矩阵的指数，故 $U(n)\subseteq G$；这已经是计算的结论。

相邻 $\Delta_j$ 又张成全部实无迹对角空间，其指数给所有行列式一的正对角矩阵。对任意 $|\det A|=1$ 的可逆矩阵作 SVD $A=UDV^*$，$U,V\in U(n)$、$D$ 正对角且 $\det D=1$，于是 $A\in G$。SVD在这里仅是已取得控制之间的矩阵分解，所需标准条件见 [Watrous定理1.6、推论1.7][Q170W1]。反向包含已由行列式支付。因此所述闭包等式成立；相应 $\mathfrak g=\{X:\operatorname{Re}\operatorname{Tr}X=0\}$，特别是 $iI\in\mathfrak g$，实 $I$ 则被行列式条件排除。

回到原锥：170.3使每个正向字的局部合同在每个固定原旁观层上正。若 $A_k\to A$，则对该层每个固定 $z$，合同像按通常矩阵乘法连续收敛；原锥闭性给 $A\in G$ 的同一正性。对任意可逆 $A$，令 $\widehat A=|\det A|^{-1/n}A\in G$，则

$$
\operatorname{Ad}_A=|\det A|^{2/n}\operatorname{Ad}_{\widehat A}.
$$

正标量齐次性给 $A$ 的正性；对 $A^{-1}$ 另用同一结论，给正逆及锥等号。没有假定逆映射正性，也没有从相似作用推出合同正性；后者始终由原正字和闭锥取得。∎

**定理 170.5（单固定映射的同域两层与全有限等价）。** 在170.1的完整原域、170.2的指定固定矩阵下，

$$
\mathsf B\wedge\mathsf M_2
\quad\Longleftrightarrow\quad
C_1=\operatorname{PSD}_n\ \text{且}\ C_2=\operatorname{PSD}_{n^2}.
$$

同域中还有

$$
\mathsf B\wedge\mathsf M_2\wedge\mathsf T
\quad\Longleftrightarrow\quad
C_N=\operatorname{PSD}_{n^N}\quad\text{对每个有限 }N\ge1.
$$

证明。170.4已给所有酉的二体第一因子正性，即167.2的 U2。任取一个固定 $0<\lambda<1$，令 $S=\operatorname{diag}(\lambda,1,\ldots,1)$，则

$$
\widehat S=\lambda^{-1/n}S\in G,\qquad
\operatorname{Ad}_S=\lambda^{2/n}\operatorname{Ad}_{\widehat S}.
$$

这给167.2的 S2；$S$ 是推论中的目标，并非另一个原正性输入。两项 Bell 成员关系和完整原域均未改变。于是直接应用[定理167.3第一项及其证明][Q170XVI]，取得低二层等式。精确消费的是167.4的连续酉字母加单衰减器的正比例可逆有限字，167.5的原预算，167.6的原态轨道与迹对偶轨道两个不同包含，以及167.7的原偏迹和最小积恢复一体。这里不重证 SVD 控制、Bell 双夹逼或一体恢复，也不把“Bell 满秩”当作这些步骤的替代。

这些供应的预算仍须保留：对已恢复的 $S$，

$$
m_S=\max_{x\in K_2}u_2(\operatorname{Ad}_{S\otimes I}x)\in(0,\infty),\qquad
\alpha_S=\min\{1,m_S^{-1}\}>0.
$$

167.4在字母表 $U(n)\cup\{S\}$ 中给出的字若为 $Q=c_AA$、含 $k$ 只衰减器，其逐步 proper 输出系数为 $\alpha_S^kc_A^2$，而非一。这个扩大字母表中的精确有限实现，与170.4中 Bell 转向后的两字母稠密性是不同结论。

低二层对齐后，167.8、XIII163.2及VII102.6—102.7的低层前件才全部到位：$B/n\in K_2$、$\beta/n\in\mathcal E_2$，此时 $b=n$。它们给全部原自身 Choi 接口、奇异一体合同及全部相关旁观者预算。对于任意一体矩阵 $A$，$s_A=\max\{1,\|A\|_{\rm op}\}$ 给 $A/s_A$ 的全旁观不增迹合同。这里才可用 $A^*A/s_A^2\preceq I$ 测试全部原一体态。

再加 $\mathsf T$。定义166.1的全部前件逐项是170.1的实际复 Hermitian 张量载体、全部有限闭尖生成锥、严格正乘法迹、整个基和全部极点、完整自身对偶及整个 proper 区间、全部有限单位分解、每个实际 min/max 分块、全部实际置换及其正逆、不连续分块运输、规范重括号、兼容原配对、空系统，加刚取得的两条低层 PSD 等式。$\mathsf T$ 正好是166.2的原 dyad、三秩至少二和至少一腿满维。故直接消费[166.12的条件1蕴含条件5][Q170XIII]，得到全部有限等式。该定理的强归纳、小角完整对偶延拓、实控制准备和九腿桥保持其原证明；本章的群闭包不替代全有限传播。

其有限资源系数也保持原式：在166.11的局部维数 $d$，每份种子为 $h\psi\psi^*/\delta$、$\delta=\|\psi\|^2$，控制为 $t_Q QQ^*/q_Q$。两份种子、共同滤波 $L/s_L$ 及三只 proper Bell 帽给

$$
\kappa=\frac{h^2t_Q}{\delta^2q_Qs_L^2d^3}>0.
$$

最终 $C^{-1}/s_C$，$s_C=\max\{1,\|C^{-1}\|\}$，再给 $\kappa/s_C^2$；令 $N=C^{-1}D\notin\mathbb CI_d$，所得归一质量为

$$
\frac{h^2t_Q[d+\operatorname{Tr}(N^*N)]}
 {\delta^2q_Qs_L^2d^3s_C^2}\in(0,1].
$$

166.10用三份归一 Bell 供应控制时 $t_Q=d^{-3}$；若其供应质量为 $b_1,b_2,b_3>0$，则 $t_Q=b_1b_2b_3/d^3$，总 dyad 系数含 $d^{-6}$。小角的限制副本用于支付效应，并非这两份未限制种子；不能漏掉六腿控制准备，也不能把限制副本质量重复乘入后续控制。166.12中每次控制维数严格下降，所有选片、缩放、帽及正则尾部都有限，逐个严格正的原系数仍按其供应保留，不产生统一副本数或成功率下界。

反向若低二层为 PSD，则 PSD 的完整迹自对偶给 $\mathsf B$，任意矩阵合同保持 PSD，故这个指定 $M$ 满足 $\mathsf M_2$。若全部有限层标准，还可取 $g_n=\sum_j|jjj\rangle$；其 dyad 属于 $C_3$，三个展平秩均为 $n$，支付同一个 $\mathsf T$。完整标准层级的全部 min/max、迹、置换及菜单前件正是167.3反向核对的同域模型。两个等价均成立。∎

**命题 170.6（原有限字、恢复资源与极限的量词）。** 在170.5左侧的二元前件下，下述预算及边界同时成立。

证明。对170.4中长度 $k$ 的正向字 $Q$，170.3的归一资源逐步给 $\eta^k\operatorname{Ad}_Q$ 的全旁观不增迹预算；若使用原一次制备所给的未归一资源，每步系数为 $\alpha/(nb)$，乘积亦须逐个保留。后一有限收缩使用 $k$ 份原 $B/n$、$k$ 次仅在资源二体上的 $\alpha\operatorname{Ad}_{M\otimes I}$、所需原 SWAP，以及 $k$ 只原 proper 帽；逐步可在输入 $C_{s+1}$ 外只接入两条资源腿，再收回 $C_{s+1}$。因此两字母只是这个单映射有限资源语法的矩阵记号，不是原单字母幂 $M^k$ 已经稠密的断言。仅在二体上，另有紧基整体预算

$$
0<m_Q=\max_{x\in K_2}u_2(\operatorname{Ad}_{Q\otimes I}x)<\infty,
\qquad \min\{1,m_Q^{-1}\}\operatorname{Ad}_{Q\otimes I}
$$

不增迹。这一整体二体公式本身不支付高层预算；高层预算来自已给的 Bell 资源切片。

对每个恢复的固定可逆 $A$，其 Choi dyad $R_A=|A\rangle\!\rangle\langle\!\langle A|\in C_2$，令 $r_A=\operatorname{Tr}(A^*A)>0$。以原 $R_A/r_A$ 和原 $\beta/b$ 收缩，得到

$$
\frac1{br_A}\operatorname{Ad}_A
$$

在所有原有限旁观者上的不增迹预算，也适用于另一个固定目标 $A^{-1}$。它使用闭锥中的恢复资源，给每个目标一个有限正系数；并不宣称逼近该资源的原字列具有统一正制备概率。低二层等式后，同一公式有 $b=n$，并对任意非零奇异 $A$ 由167.8的 Choi dyad适用；$A=0$ 直接给零映射，无须归一零资源。

$\mathcal P$ 可数，其闭包 $G$ 不可数；即使去掉全局相位，$n\ge2$ 时酉合同仍不可数。因此原有限字不可能精确覆盖全部恢复合同，也不能覆盖全部可逆矩阵的正比例类。170.4只给每个 $\widehat A$ 的正向字逼近及锥正性；逆可能只在闭包中，未给每个原逆的精确正向字。全部原字及其未缩放有限矩阵极限都满足 $|\det|=1$，故没有奇异矩阵。一般 $A$ 的正比例因子和相应合同平方必须单独记账；奇异滤波来自正比例合同的闭锥边界或对齐后的 Choi 接口。

连续方向属于数学闭包。锥闭性没有物理事件存在、极限装置、误差成本或概率极限的量词；每个字质量严格正也不给所有字列的正下界。例如对齐后的标准层级中，固定 proper 合同 $x\mapsto (aI)x(aI)^*$，$0<a<1$，重复 $k$ 次对迹一输入的质量为 $a^{2k}\to0$。这说明一般的逐步正预算不能被换成无限协议的正成功质量，不对本章原字列另作概率普遍断言。∎

**命题 170.7（纯虚路径漂移的可复用障碍）。** 设实反对称矩阵 $K$ 与 Hermitian 对合 $J$ 满足 $KJ=-JK$，且酉矩阵 $W$ 与 $J$ 可交换。对 $O_c=e^{cK}$、$M_c=WO_c$，有精确恒等式

$$
O_c^*JO_c=J e^{(c+\bar c)K}.
$$

特别地，若 $c$ 纯虚，则 $M_c$、$M_c^{\mathsf T}$ 在 $W^{\mathsf T}$ 也保持 $J$ 时均属于 $U(J)=\{A:A^*JA=J\}$；其正向字闭包也留在这个闭群。对170.2路径及端点相位，取

$$
J=\operatorname{diag}(1,-1,1,-1,\ldots).
$$

则替换漂移为 $itK$ 会产生上述障碍，不能用该控制闭包恢复 $U(n)$。混合系数 $(1+i)t$ 则不保持此 $J$。

证明。$K^*=-K$ 及反交换关系给

$$
e^{-\bar cK}J e^{cK}=J e^{\bar cK}e^{cK}.
$$

$W^*JW=J$ 给 $M_c$ 的相同公式。纯虚时 $O_c\in U(J)$，且 $O_c^{\mathsf T}=O_c^{-1}$；若 $W^{\mathsf T}\in U(J)$，则 $M_c^{\mathsf T}=O_c^{-1}W^{\mathsf T}\in U(J)$。本章的对角 $W$ 满足这些条件。路径的相邻符号相反，故 $KJ=-JK$。$U(J)$ 是签名 $(\lceil n/2\rceil,\lfloor n/2\rfloor)$ 的不定酉群，普通酉旋转若混合第零、第一坐标便不保持 $J$，所以它不包含 $U(n)$。

对指定混合 $c$，$M^*JM=Je^{2tK}\ne J$，不等号由170.2的小谱角论证给出。破坏这个不变量本身只排除这一障碍；完整生成由170.4的实 Lie 计算另行证明。本命题只是不变式和控制闭包的障碍，没有构造满足170.1全部有限 min/max 与 Bell 双成员关系的非量子层级，故不声称纯虚候选已有全域非量子反模型。∎

**推论 170.8（完整状态、效应、复合与过程字典）。** 在170.1及 $\mathsf B,\mathsf M_2,\mathsf T$ 下，置 $d_N=n^N$、$d_0=1$。全部原对象在同一实际坐标中有如下对应。

| 原对象 | 完整量子对应 |
| --- | --- |
| 整个 $K_N$、凸准备 | 全部 $\rho\succeq0$、$\operatorname{Tr}\rho=1$，通常凸混合 |
| 全部 $P_N$、非零极射线 | 全部 $vv^*$、$\|v\|=1$，及其正倍数；纯态空间 $\mathbb{CP}^{d_N-1}$ |
| 完整自身对偶、整个 proper 区间 | 完整 PSD 迹对偶、全部 $0\preceq E\preceq I_{d_N}$ |
| 全部有限单位分解、原配对 | 全部有限 POVM；$\Pr(a\mid\rho)=\operatorname{Tr}(E_a\rho)$，包括 PVM |
| 所有有限实际复合 | $\mathcal H_N=(\mathbb C^n)^{\otimes N}$ 上全部联合密度矩阵，包括纠缠态 |
| 原置换、单位切片 | 通常因子置换及对全部相关输入的偏迹 |
| 实线性原全旁观正 $F:W_a\to W_b$ | 相应全部矩形 CP 映射、完整 Choi 及有限 Kraus 表示 |
| 原全输入不增迹、保迹 | 完整 Kraus 不等式、等式；数学分支、数学信道 |
| 和保迹的有限分支族 | 全部有限数学 CP 仪器、有限顺序、自适应、粗粒化及张量规则 |

证明。170.5已逐项支付[推论167.9、168.4][Q170XVI]的完整原域和 B、U2、S2、T，因此消费其同一矩阵字典及证明。谱分解给全部密度矩阵的有限纯态混合，秩一且仅秩一为极点；整体相位商给全部射线，给定三元种子的归一 dyad至此才识别为原极点。这些标准事实对应 [Watrous §2.1.2，式(2.12)—(2.13)][Q170W2]。完整迹对偶给全部效应和 POVM，而非选定子菜单。纯态 $p=vv^*$、$q=ww^*$ 的确认重叠为 $\operatorname{Tr}(pq)=|v^*w|^2$；穷尽确认读数满足

$$
\inf\{f(x):f\in\mathcal E_N,\ f(p)=1\}=\operatorname{Tr}(px)
\quad(x\in C_N).
$$

这是167.9末段对全部确认效应的 least 结论。Born 形式来自原配对与完整区间；标准 POVM/Born 定义见 [Watrous定义2.34及(2.199)—(2.202)][Q170W2]。Hermitian 观测量的谱分解给 PVM，未添加特权更新。

所有 $a,b,s$ 可为非负有限整数。按参考—输出次序、实线性映射的唯一复线性保 Hermitian 扩张，

$$
\begin{aligned}
J(F)&=\sum_{i,j=0}^{d_a-1}E_{ij}\otimes F(E_{ij}),\\
F\text{ 原全旁观正}
&\Longleftrightarrow J(F)\in C_{a+b}
 \Longleftrightarrow J(F)\succeq0\\
&\Longleftrightarrow F(x)=\sum_\gamma K_\gamma xK_\gamma^*,\qquad
K_\gamma:\mathbb C^{d_a}\to\mathbb C^{d_b}.
\end{aligned}
$$

第一步是低层已支付后的167.8、VII102.7自身参考判据；下一步是整锥等式；矩形 Kraus 步是[Watrous定理2.22，印刷页82—84][Q170W2]，其输出—参考次序由实际 SWAP 转换。该定理陈述非零映射；零映射另用空 Kraus 和。非零映射可取 Kraus 数为 Choi 秩，不超过 $d_ad_b$。原参考只量化 $n^s$ 维自身系统；所得 Kraus 式随后才给任意矩阵辅助维数的通常完全正性。

令 $Q_F=\sum_\gamma K_\gamma^*K_\gamma$，则

$$
\begin{aligned}
\operatorname{Tr}_{\rm out}J(F)&=Q_F^{\mathsf T},\\
u_bF\le u_a&\Longleftrightarrow Q_F\preceq I_{d_a}
 \Longleftrightarrow\operatorname{Tr}_{\rm out}J(F)\preceq I_{d_a},\\
u_bF=u_a&\Longleftrightarrow Q_F=I_{d_a}
 \Longleftrightarrow\operatorname{Tr}_{\rm out}J(F)=I_{d_a}.
\end{aligned}
$$

完整输入上的迹恒等式及 PSD 自对偶给不等式，等式对应[Watrous定理2.26，印刷页87—89][Q170W2]。不能以一个总 Choi 迹代替完整参考边缘。原最大界将 $u_a-u_bF$ 的非负性提升为每个相关旁观预算。非零 CP 映射可乘 $\min\{1,\|Q_F\|^{-1}\}>0$ 成为数学分支；零映射直接不增迹。

有限数学仪器恰为

$$
F_\ell(x)=\sum_\gamma K_{\ell\gamma}xK_{\ell\gamma}^*,\qquad
\sum_{\ell,\gamma}K_{\ell\gamma}^*K_{\ell\gamma}=I_{d_a},\qquad
E_\ell=F_\ell^\dagger(I)=\sum_\gamma K_{\ell\gamma}^*K_{\ell\gamma}.
$$

这里 $\ell$ 为结果标签，$a,b$ 仍为输入、输出层数。零标签允许保留。每个分支有同输出型补分支；取单位输出向量 $v$ 及输入正交基 $b_j$，既有161.9的补 Kraus 为 $|v\rangle\langle b_j|\sqrt{I-Q_F}$。所有效应和 POVM 都可作为数学分支、仪器的效果，例如 $x\mapsto\operatorname{Tr}(E_\ell x)\omega$，$\omega$ 为固定归一输出态。

标量输入 $a=0$ 给 $F(q)=q\sigma$，$\sigma\succeq0$，TNI/TP 分别是 $\operatorname{Tr}\sigma\le1$、$=1$；标量输出 $b=0$ 给 $F(x)=\operatorname{Tr}(Ex)$，TNI/TP 是 $0\preceq E\preceq I$、$E=I$。两端均标量时是乘 $q_0\ge0$，TNI 为 $q_0\le1$，TP 为 $q_0=1$。空参考杯是标量一，没有加入新物理系统。$K_0$ 为单点、效应为 $[0,1]$、纯态空间 $\mathbb{CP}^0$，上述零分支约定全部适用。

对任意质量的相关原输入 $Z\succeq0$，令

$$
Z_\ell=(\mathrm{id}\otimes F_\ell)Z,\qquad
m_\ell=\operatorname{Tr}Z_\ell=\operatorname{Tr}[(I\otimes E_\ell)Z],\qquad
\sum_\ell m_\ell=\operatorname{Tr}Z.
$$

直接应用[161.9的矩阵证明、(161.27)—(161.30)][Q170XIII]，得到 $m_\ell=0$ 时 $Z_\ell=0$，仅 $m_\ell>0$ 时定义条件态 $Z_\ell/m_\ell$；输入质量一时 $m_\ell$ 为概率，一般正质量时概率为 $m_\ell/\operatorname{Tr}Z$。零输入的全部输出为零。旁观边缘及无信号和是

$$
\operatorname{Tr}_{\rm out}Z_\ell
 =\operatorname{Tr}_{\rm in}[(I\otimes\sqrt{E_\ell})Z(I\otimes\sqrt{E_\ell})],\qquad
\sum_\ell\operatorname{Tr}_{\rm out}Z_\ell=\operatorname{Tr}_{\rm in}Z.
$$

该同一既有证明也给全部有限顺序、自适应、粗粒化、张量和条件概率规则；标准仪器形式见 [Watrous §2.3.2，(2.255)—(2.261)][Q170W2]。余下系统的效应切片不选择被测系统自身的唯一更新。∎

**推论 170.9（既有理想锐更新和指定连续实作用的消费者）。** 在170.8的前件下，理想锐中性条件和给定连续可逆实序作用，分别有已出版161的 Lüders 与 Hamiltonian 对应；这些附加数据不是170.2的结论。

证明。本章取得的是实际坐标中的全有限 PSD、迹、产品和完整对象，即161的共同矩阵目标，取 $\Theta_N=\mathrm{id}_{W_N}$。对有限 $k\ge0$ 记 $d=d_k$。不据此声称161.5正向的全部几何前件 $\mathsf G_3$ 或其单锥供应已由本章重新核清。这里复用的是从该目标之后开始的矩阵级证明，正如[162.9所明示的后置应用][Q170XIII]。

具体地，另给同型原正实线性分支 $L:W_k\to W_k$ 和 sharp 效应 $e_P(x)=\operatorname{Tr}(Px)$，$P=P^*=P^2$，满足

$$
u_kL=e_P,\qquad Lp=p\quad\text{对每个原 }p\in P_k\text{ 且 }e_P(p)=1.
$$

170.8使这些 $p$ 正好遍历 $\operatorname{Ran}P$ 中全部单位秩一投影。因此其矩阵作用的精确前件为正实线性、$L^\dagger(I)=P$、逐点固定全部 certain-yes 纯态。直接应用[161.7.1对既有 Atlas Proposition13.4(1)的单矩阵扇区应用][Q170XIII]，得到

$$
L(x)=PxP.
$$

不预设 CP；CP 和全部旁观提升随得到的压缩式及170.8而来。对有限正交分解 $\sum_aP_a=I$，既有(161.30c)给

$$
p_a=\operatorname{Tr}[(I\otimes P_a)Z],\qquad
Z_{\mid a}=\frac{(I\otimes P_a)Z(I\otimes P_a)}{p_a}\quad(p_a>0),\qquad
Z_{\rm ns}=\sum_a(I\otimes P_a)Z(I\otimes P_a).
$$

$P=0$ 给零分支、$P=I$ 给恒等；零概率无归一条件态，标量维数也包括在既有供应的端点中。逐点中性必须覆盖退化 yes 子空间的每条射线；结果可重复并不能代替它。161.7.1的 $VPxPV^*$，$V$ 在 yes 子空间内部转动，已给可重复而非逐点中性的对照；sharp 效应本身也允许不同更新。这是既有唯一性应用，没有新增一个更新重建定理。

再另给实际有限层 $k$ 上的实线性族 $A_\tau$，满足

$$
A_0=I,\quad A_{\tau+\sigma}=A_\tau A_\sigma,\quad
A_\tau(C_k)=C_k,\quad u_kA_\tau=u_k,
$$

且在有限维算子拓扑中连续。其矩阵输运就是连续、保迹的 PSD 序自同构实一参数群。直接复用[161.10证明中从这一矩阵前件开始的分类和局部提升][Q170XIII]：该证明的等维单因子秩一保持分类给酉合同或转置酉合同，连通性排除转置分支，随后从原实作用构造局部酉提升及生成元。于是存在 $\mathsf H=\mathsf H^*$，唯一到实标量，满足

$$
A_\tau(x)=e^{-i\tau\mathsf H}xe^{i\tau\mathsf H},\qquad
\mathcal L(x)=-i[\mathsf H,x].
$$

这里没有预给酉族，也不需要先假设可微性。$d=2$ 包括在该既有分类应用中；标量 $d=1$ 的作用为恒等，生成元任意实标量。相应向量代表和密度矩阵满足 $i\dot\psi=\mathsf H\psi$、$i\dot\rho=[\mathsf H,\rho]$。物理钟、能量标定、单位和正尺度 $\hbar$ 另给后，才写 $\mathsf H_{\rm phys}=\hbar\mathsf H$ 及通常带 $\hbar$ 的方程。170.2中的固定无量纲小参数不是物理时间。

数学 CP-TNI 与仪器的完整表征不等于实际可用事件的完整菜单。[VII102.14][Q170VII]的事件饱和是额外选择；某个装置被指定理想还须给其逐点中性，某个群被指定动力学还须给上述实际时间作用。恒等作用与不同 Hamiltonian 保持同一静态层级，故静态判据不选择这些数据。∎

**命题 170.10（几何解释、供应归属及结论边界）。** 170.5在保持完整原域的条件下，把167的全部酉及一只衰减器的正性入口压为一个明确固定映射的正性；它不重建已给的复矩阵载体、维数和全部有限组合规则，也不推出物理实现、全球首创或独立公理最小性。

证明。170.3—170.4已从唯一 $\mathsf M_2$ 取得 U2、S2，而标准低层反向使该 $\mathsf M_2$ 必要，故这里的压缩是同域逻辑等价。Bell 仍有原态与原对偶两个成员关系，全有限域与整个效应菜单也仍是输入；不能按条件标签数断言独立假设数最小。

用完整的中文几何语言说，同一个贝尔关系同时放在“可准备”和“可测试”两边，像一把两面校准的尺子。把固定矩阵作用到这把尺子上，再用尺子的测试端接回输入，就得到局部矩阵转置的作用；这是接线后的合同，不是把态作转置。原基的紧性先保证这次接线有有限 proper 帽和正预算。两个正向作用相乘只露出链端的一圈无理相位；短程混合的相似作用足够接近恒等，收敛对数便把这一个圆带到第一条边。混合系数的实部和虚部共同使交换子既能分开相对伸缩，又能取得下一点的相位，沿链重复就得到全部转向和相对尺度。闭包中的反向也是由这些正向矩阵支付的。随后贝尔尺子的准备轨道填入正方向，测试轨道排除负方向，167的双夹逼把低层锥确定为量子锥；一腿满维且各腿非乘积的三元种子再接上166的有限传播。全部密度矩阵、Born 效应、纠缠复合和 CP 仪器由此成为完整原对象的矩阵表达。闭锥容纳数学极限，却不会自动供应装置、理想更新或物理钟；后几项各自保留自己的条件。

若不加 $\mathsf T$，本章已给低二层及全部局部合同的原全旁观正性，但没有由此单独证明全部高层 PSD，也没有给出其余条件的全域非量子反模型。若给定 GME 的三秩都小于 $n$，例如 $n>2$ 时嵌入的 $|000\rangle+|111\rangle$，它不支付166.12的满腿入口；本章不把该供应改成任意 GME 定理。删去闭性、完整自身对偶、全部 min/max 分块或正置换，会分别失去闭包、切片、资源积和 Bell 接线的已列前件。170.7则给任意同型纯虚漂移的精确不变式障碍，未将控制不足升级为完整锥反模型。

来源的数学作用如下。[已出版167—168][Q170XVI]供应原域、Bell 双夹逼、单衰减器有限字、原预算、量子字典，以及一个端点无理相位的正向闭包和相似算子对数的接口思想；[XIII166.1—166.3、166.10—166.12][Q170XIII]供应满腿全有限传播，163.2与[VII102.6—102.7][Q170VII]供应匹配前件后的原旁观与自身 Choi。[XIII161.9、161.7.1、161.10的矩阵级应用][Q170XIII]分别供应仪器与零质量规则、既有 sharp-neutral 唯一性和给定连续实序作用的 Hamiltonian 分类；不调用其前置几何重建来替代本章证明。

[Hall的公开作者文本][Q170Hall]，*An Elementary Introduction to Groups and Representations*，arXiv:math-ph/0005032v1，定义2.2（印刷页9）、定理3.6（页32—33）、定义3.13（页36—37）、命题3.15及定理3.16（页40—41），只供应相对闭矩阵群、范数内对数、实 Lie 封闭和相似不变性；本章逐项满足这些条件。[Watrous第一章][Q170W1]的页20 PSD迹刻画、定理1.3/推论1.4、定理1.6/推论1.7、式(1.127)—(1.134)、(1.162)—(1.164)供应所用标准矩阵、向量化与分解事实；[第二章][Q170W2]的§2.1.2、定理2.22、2.26、定义2.34及§2.3.2供应对应的有限量子字典。这些是推导内的成熟中间成分；本章新增组合是未知原锥上的 pre-PSD Bell 转向及单端点混合路径的实方向计算与既有重建接口的接合，不把一般闭群、SVD 或 Choi 事实另列为新发现。全有限结论消费所列已出版传播供应及其具名依赖；本章没有另行重证其整个依赖链。无限维、一般非满腿 GME、时空、事件可用性与实际能量尺度不在此结论内。∎

[Q170XVI]: https://github.com/the-omega-institute/trureturing/blob/d91fdb64e60124b82bcead3c5dbe4d33cd50eaf5/docs/develop/theory/QUANTUM_ORIGIN_BINARY_BELL_ORBITS_AND_SINGLE_ATTENUATOR_XVI.md
[Q170XIII]: https://github.com/the-omega-institute/trureturing/blob/00427ae2ba9c9e3f6c37f2e5496b9127b6fbc6c0/docs/develop/theory/QUANTUM_ORIGIN_BINARY_TANGENT_CLOSURE_AND_GLOBAL_NONCOLLAPSE_XIII.md
[Q170VII]: https://github.com/the-omega-institute/trureturing/blob/657a8ba435bf2cae463e935d957d8038b69be8a3/docs/develop/theory/QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md
[Q170Hall]: https://arxiv.org/pdf/math-ph/0005032v1
[Q170W1]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
[Q170W2]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf

## 追加锚（本行以下为增补区）

## 171. Raw Bell relations, derived cone properness, and the parity orientation

The two binary relations considered here determine the ordinary two-body positive semidefinite cone even when pointedness, generation, and positivity of the trace have been removed from the model assumptions. They determine the one-body cone up to a sign. The actual finite tensor relations then force pointedness, generation, and a strictly positive, multiplicative **signed** trace at every finite level. The unchanged three-body seed has two distinct duties: its nonzero positive semidefinite dyad selects the ordinary orientation, and its flattening ranks meet the existing all-finite propagation theorem.

The proof separates a raw, unnormalized cone argument from the later use of normalized resources. Its matrix-generation dependency is precisely the algebraic part of candidate §170.4 at the immutable commit [4a2c3cc8bb4620516476cd923a7334f4df59e1a9][A170]. Neither its full-domain reconstruction theorem nor its pre-normalization budget lemma is used to establish the premises removed here. All-finite propagation is supplied, after its complete domain has been established, by [XIII, Theorem 166.12][XIII]. The known operation dictionary and its additional update and dynamics conditions are consumed at the same point, rather than reconstructed again.

### 171.1 The weak actual finite domain and the exact relations

**Definition 171.1 (weak actual finite cone hierarchy).** Fix an integer $n\ge2$. For every finite $N\ge0$, retain the actual spaces and Kronecker coordinates

$$
V=\operatorname{Herm}_n(\mathbb C),\qquad
W_N=V^{\otimes_{\mathbb R}N}
 =\operatorname{Herm}_{n^N}(\mathbb C),\qquad W_0=\mathbb R.
\tag{171.1}
$$

For $N\ge1$, let $C_N\subset W_N$ be a closed convex cone, with no initial requirement that it be nonzero, pointed, generating, or contained in a positive-trace half-space. Set $C_0=\mathbb R_+$. The fixed linear functionals are

$$
u_N=\operatorname{Tr}=u_1^{\otimes N},\qquad u_0=\mathrm{id}_{\mathbb R}.
\tag{171.2}
$$

At this stage, the word “unit” is not used to assert that $u_N$ is positive on $C_N$. The complete trace dual is

$$
C_N^*=\{Y\in W_N:\operatorname{Tr}(YX)\ge0
                         \text{ for every }X\in C_N\}.
\tag{171.3}
$$

The real trace pairing is nondegenerate. All functionals in (171.3), rather than a selected testing family, are retained. For every pair of finite nonnegative integers $a,b$, require

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}
             \subseteq C_a\otimes_{\max}C_b.
\tag{171.4}
$$

Here the minimum is the closed convex cone generated by $X\otimes Y$ with $X\in C_a$, $Y\in C_b$. The maximum is

$$
\{Z\in W_{a+b}:\operatorname{Tr}[(F\otimes G)Z]\ge0
                     \text{ for all }F\in C_a^*,\ G\in C_b^*\}.
\tag{171.5}
$$

Every actual permutation of tensor positions and its inverse preserves the corresponding cone. Arbitrary noncontiguous partitions are transported by these actual maps. Reassociation is the canonical identification in the same actual space, with the same joint cone. The pairing and trace retain the identities

$$
\langle F\otimes G,X\otimes Y\rangle
  =\langle F,X\rangle\langle G,Y\rangle,
\qquad u_{a+b}=u_a\otimes u_b.
\tag{171.6}
$$

These requirements quantify every finite level and every finite partition, including those with a scalar factor. They do not posit higher-level PSD cones, self-duality, transpose invariance, or positivity of arbitrary matrix operations. In particular, no normalized base, proper effect interval, probability menu, or resource budget is an input to this definition.

A real-linear map $F:W_a\to W_b$ is called **positive with every original finite spectator** if

$$
(\mathrm{id}_{W_s}\otimes F)C_{s+a}\subseteq C_{s+b}
                   \qquad(s\ge0\text{ finite}),
\tag{171.7}
$$

with the analogous positions supplied by actual permutations. This definition concerns cone membership only.

**Definition 171.2 (the unchanged fixed matrix, Bell relation, and ternary seed).** In the actual basis $e_0,\ldots,e_{n-1}$, put $E_{jk}=e_je_k^*$ and $P_j=E_{jj}$. Use exactly the matrices of [candidate 170.2][A170]:

$$
\begin{aligned}
K&=\sum_{j=0}^{n-2}(E_{j,j+1}-E_{j+1,j}),
&t&=\frac1{32n},&c&=(1+i)t,\\
H&=cK,&O&=e^H,&W&=e^{\pi i\sqrt2 P_0},&M&=WO.
\end{aligned}
\tag{171.8}
$$

The symbol $W$ in (171.8) is the endpoint phase matrix; $W_N$ continues to denote the actual real carrier. Write $\operatorname{Ad}_A(X)=AXA^*$. Define

$$
\Omega=\sum_{j=0}^{n-1}e_j\otimes e_j,
\qquad B=\Omega\Omega^*,\qquad
\beta(Z)=\operatorname{Tr}(BZ).
\tag{171.9}
$$

The two binary relations are exactly

$$
\mathsf B:\quad B\in C_2\cap C_2^*,
\qquad
\mathsf M_2:\quad \operatorname{Ad}_{M\otimes I}(C_2)\subseteq C_2.
\tag{171.10}
$$

The second membership in $\mathsf B$ means nonnegativity of $\beta$ on the entire actual $C_2$. The map condition is imposed only on the first factor of $C_2$. It contains no inverse or transpose-map assumption.

The ternary relation remains

$$
\mathsf T:\quad
\exists\,0\ne\psi\in(\mathbb C^n)^{\otimes3},\quad
\psi\psi^*\in C_3,\quad
\min_i r_i(\psi)\ge2,\quad \max_i r_i(\psi)=n,
\tag{171.11}
$$

where $r_i$ is the complex matrix rank of the flattening of leg $i$ against the other two legs. Thus every bipartition is nonproduct and at least one original leg has full support. No original extremality or normalization of this dyad is assumed.

### 171.2 The isolated matrix supplier and the raw Bell bridge

**Supplier 171.3 (the algebraic part of candidate 170.4).** For the matrices (171.8), let $\mathcal P$ consist of the finite positive words in the two matrices $M,M^{\mathsf T}$, including the empty word. The algebraic assertion reused from [170.4 at the fixed candidate commit][A170] is

$$
\overline{\mathcal P}^{\,GL_n(\mathbb C)}
       =\{A\in GL_n(\mathbb C):|\det A|=1\}.
\tag{171.12}
$$

Only this matrix assertion is imported. Its hypotheses are the integer $n\ge2$, the actual matrix units, and the exact constants and matrices (171.8). It has no cone, trace-positivity, compact-base, proper-effect, or normalization premise. The cone-dependent last assertion of candidate 170.4 is not imported; its replacement on the weak domain is proved below. Candidate 170.3 and Theorem 170.5 are not suppliers for the weak-domain argument.

The distinction can be checked directly in the source proof. It obtains the endpoint circle from

$$
MM^{\mathsf T}=e^{2\pi i\sqrt2P_0},\qquad
M^{-1}=M^{\mathsf T}e^{-2\pi i\sqrt2P_0},
\tag{171.13}
$$

and applies real Lie algebra operations to the relative closed matrix group. Its similarity logarithm is justified by

$$
\|\operatorname{ad}_{cK}\|
 \le4\sqrt2t=\frac{\sqrt2}{8n}<\frac18<\log2.
\tag{171.14}
$$

The real and imaginary edge directions are separated using $c^2=2it^2$ and division by nonzero real numbers. No assumption that a Lie algebra is a complex vector space, or that $O$ is unitary, is involved. The general closed-group, real Lie algebra, and logarithm statements used there are exactly [Hall, Definition 2.2, Theorem 3.6, Definition 3.13, Proposition 3.15, and Theorem 3.16][Hall]. Their relative-closed-group and norm hypotheses agree with (171.13)–(171.14).

This is exact source reuse of a candidate algebraic proof, not independent certification of that candidate. In dependency-explicit form, the forward binary conclusions below are conditional on the isolated algebraic assertion (171.12) as a paper supplier. They do not depend on a cone-dependent reconstruction theorem of candidate170. The new weak-cone bridges are supplied in full here. The later all-finite and quantum conclusions additionally use the stated published paper suppliers; none is being described as kernel-certified.

**Lemma 171.4 (raw complete-dual slicing).** In Definition 171.1, for every finite $a,b$, every $f\in C_a^*$, and every $Z\in C_{a+b}$,

$$
(f\otimes\mathrm{id}_{W_b})Z\in C_b.
\tag{171.15}
$$

This remains true after any actual permutation and under any finite sequence of such slices. No positivity of the trace is required.

**Proof.** For every $g\in C_b^*$, the maximum inclusion gives

$$
g\bigl((f\otimes\mathrm{id})Z\bigr)=(f\otimes g)(Z)\ge0.
\tag{171.16}
$$

The bipolar identity $(C_b^*)^*=C_b$ holds for every finite-dimensional closed convex cone, including a cone with lineality or a cone with deficient span. Indeed, if a vector lies outside that closed cone, separation and positive scaling of the cone give a linear functional nonnegative on the cone and negative on the vector. Thus (171.16) proves (171.15). Actual permutations give the other positions. Each slice leaves an element of the complete remaining cone, so the argument iterates. When one factor is scalar, it is the same assertion with $C_0=\mathbb R_+$. This is also the proof of [VII, Lemma 102.6][VII], with its exact closed-cone premises exposed. $\square$

**Lemma 171.5 (raw Bell bending before normalization).** Under Definition 171.1 and (171.10), both $\operatorname{Ad}_M$ and $\operatorname{Ad}_{M^{\mathsf T}}$ are positive with every original finite spectator.

**Proof.** Use reference–output vectorization

$$
|Q\rangle\!\rangle=\sum_j e_j\otimes Qe_j,
\qquad R_Q=|Q\rangle\!\rangle\langle\!\langle Q|.
\tag{171.17}
$$

The unique binary map condition applied to the Bell element gives

$$
(M\otimes I)B(M^*\otimes I)=R_{M^{\mathsf T}}\in C_2.
\tag{171.18}
$$

The actual SWAP then gives $R_M\in C_2$. Both resources are unnormalized cone elements. The functional $\beta$ is in the complete $C_2^*$ by $\mathsf B$.

Fix $s\ge0$, and label an arbitrary input $Z\in C_{s+1}$ by spectator legs $S$ and input leg $X$. For $Q=M$ or $M^{\mathsf T}$, the minimum inclusion places

$$
Z_{SX}\otimes R_{Q,X'Y}\in C_{s+3}.
\tag{171.19}
$$

Permute the actual $X,X'$ legs into a two-leg block, and slice that block with $\beta$. Lemma 171.4, applied to the maximum split $(2,s+1)$, puts the output in $C_{s+1}$. The output is exactly

$$
\operatorname{cap}_{XX'}[Z_{SX}\otimes R_{Q,X'Y}]
              =(\mathrm{id}_{W_s}\otimes\operatorname{Ad}_Q)Z.
\tag{171.20}
$$

To verify the transpose and multiplication order, matrix units give

$$
\beta(E_{ab}\otimes E_{ij})=\delta_{ai}\delta_{bj},
\qquad R_Q=\sum_{i,j}E_{ij}\otimes QE_{ij}Q^*.
\tag{171.21}
$$

Expanding $Z=\sum_{a,b}Z_{ab}\otimes E_{ab}$ therefore leaves
$\sum_{a,b}Z_{ab}\otimes QE_{ab}Q^*$, which is (171.20). Matrix units here express the unique complex-linear extension of the original real Hermitian tensor map. Their sum defines the stated real-linear identity on the entire original space.

For $s=1$, the required passage is specifically $C_2\otimes C_2\subseteq C_4$, followed by a two-leg slice back to $C_2$. No PSD description of $C_4$ is used. The argument covers arbitrary correlated input $Z$ and every finite $s$.

Nothing in this proof bounds $\beta$ by the trace, divides by an input mass, or asserts a probability. In particular, it does not import the proper-cap part of candidate 170.3 or the low-level PSD premise at the beginning of VII102.7. It proves the raw identity and its cone positivity directly. $\square$

**Proposition 171.6 (closed-word transfer to the weak cones).** With Supplier 171.3 and the hypotheses of Lemma 171.5, for every $A\in GL_n(\mathbb C)$ and every finite $s\ge0$,

$$
(\mathrm{id}_{W_s}\otimes\operatorname{Ad}_A)C_{s+1}=C_{s+1}.
\tag{171.22}
$$

The same assertion holds on any single actual leg.

**Proof.** Lemma 171.5 makes the local congruence of every word $Q\in\mathcal P$ positive on each fixed original spectator level. If $Q_k\to Q$ in matrices and $Z\in C_{s+1}$ is fixed, ordinary matrix multiplication gives convergence of the congruence images. Closedness of $C_{s+1}$ then gives positivity of $\operatorname{Ad}_Q$ on that level.

For an arbitrary invertible $A$, set

$$
\widehat A=|\det A|^{-1/n}A.
\tag{171.23}
$$

Supplier 171.3 puts $\widehat A$ in the word closure. The positive scalar identity

$$
\operatorname{Ad}_A
       =|\det A|^{2/n}\operatorname{Ad}_{\widehat A}
\tag{171.24}
$$

gives positivity of $\operatorname{Ad}_A$. Apply the same reasoning separately to $A^{-1}$. The two positive maps are inverse, proving (171.22). The argument is valid for each finite $s$; no exchange of an infinite-level limit with a cone is involved. Actual permutations transport the conclusion to any leg. These are congruences obtained from positive words and cone closedness, rather than an inference of congruence positivity from the similarity action in the algebraic supplier. $\square$

### 171.3 The double orbit and the one-body sign

**Proposition 171.7 (two-body alignment on the weak domain).** Under the binary hypotheses, with the algebraic dependency specified in Supplier 171.3,

$$
C_2=C_2^*=\operatorname{PSD}_{n^2}.
\tag{171.25}
$$

**Proof.** For reference–output vectorization,

$$
(A\otimes I)|Q\rangle\!\rangle
                 =|QA^{\mathsf T}\rangle\!\rangle.
\tag{171.26}
$$

Consequently $B\in C_2$ and Proposition 171.6 imply

$$
|A^{\mathsf T}\rangle\!\rangle
 \langle\!\langle A^{\mathsf T}|\in C_2
                        \qquad(A\in GL_n(\mathbb C)).
\tag{171.27}
$$

Transposition is a bijection on $GL_n(\mathbb C)$. Every two-body vector is $|Q\rangle\!\rangle$ for a unique matrix $Q$. Every matrix $Q$ is a limit of invertible matrices: for a singular value decomposition $Q=U\operatorname{diag}(d_j)V^*$, replace each $d_j$ by $d_j+\delta$, $\delta>0$. Thus closedness gives every rank-one PSD dyad in $C_2$. Finite spectral sums give

$$
\operatorname{PSD}_{n^2}\subseteq C_2.
\tag{171.28}
$$

For the other inclusion, let $\Lambda_A=\operatorname{Ad}_{A\otimes I}$. Its trace adjoint is

$$
\Lambda_A^\dagger(Y)=(A^*\otimes I)Y(A\otimes I).
\tag{171.29}
$$

Positivity of $\Lambda_A$ on $C_2$ implies positivity of $\Lambda_A^\dagger$ on $C_2^*$ by the defining pairing, without a self-duality premise. Since $B\in C_2^*$, this yields

$$
\Lambda_A^\dagger(B)
      =|\overline A\rangle\!\rangle
         \langle\!\langle\overline A|\in C_2^*.
\tag{171.30}
$$

Complex conjugation is also a bijection on invertible matrices. The complete dual is closed, so the same matrix limits and finite spectral sums prove

$$
\operatorname{PSD}_{n^2}\subseteq C_2^*.
\tag{171.31}
$$

If $X\in C_2$, testing (171.31) with $vv^*$ gives $v^*Xv\ge0$ for every vector $v$. Hence $X\succeq0$. This proves $C_2\subseteq\operatorname{PSD}_{n^2}$ and (171.25), including its dual equality.

These two orbits prove two different inclusions. Their matrix ingredients coincide with those exposed in published [167.6][P167], but the argument above proves them on the present weak domain and invokes neither 167.3 nor 170.5. Its only cone inputs are the raw bridge, closedness, and the two Bell memberships. Spectral decomposition and singular value decomposition are the standard finite-dimensional statements in [Watrous, Theorem 1.3, Corollary 1.4, Theorem 1.6, and Corollary 1.7][W1]. $\square$

**Proposition 171.8 (the exact one-body orientation).** In Definition 171.1, the equality $C_2=\operatorname{PSD}_{n^2}$ already implies that there is a unique $\varepsilon\in\{+1,-1\}$ such that

$$
C_1=C_1^*=\varepsilon\operatorname{PSD}_n.
\tag{171.32}
$$

**Proof.** First $C_1\ne\{0\}$. Otherwise its complete dual would be all of $W_1$. In the maximum split $(1,1)$ we could then test $B\in C_2$ with $I\otimes(-I)$, obtaining $-\operatorname{Tr}B=-n<0$, a contradiction.

For every $X\in C_1$, the minimum inclusion gives $X\otimes X\in C_2$, hence $X\otimes X\succeq0$. If $X$ had a positive and a negative eigenvalue, their product would be a negative eigenvalue of $X\otimes X$. Therefore every nonzero $X\in C_1$ is semidefinite, with one of the two signs.

Fix one such nonzero $X$. Two nonzero elements of opposite semidefinite signs cannot both belong to $C_1$: their tensor product would be a nonzero negative semidefinite element of $C_2$. It follows that one sign $\varepsilon$ satisfies

$$
C_1\subseteq\varepsilon\operatorname{PSD}_n.
\tag{171.33}
$$

In particular, the functional $\varepsilon\operatorname{Tr}$ belongs to $C_1^*$. This positivity is now derived, and may be used in Lemma 171.4. For arbitrary $P\succeq0$ and any usual rank-one projector $q$ of trace one, the actual matrix $P\otimes q$ belongs to $C_2$ by its known PSD shape, regardless of whether $q$ has yet been identified as an original one-body element. Its signed trace slice is

$$
(\mathrm{id}\otimes\varepsilon\operatorname{Tr})(P\otimes q)
                      =\varepsilon P\in C_1.
\tag{171.34}
$$

Thus (171.33) is equality. The PSD trace dual is PSD; multiplying a cone by a sign multiplies its trace dual by the same sign. This proves the dual equality in (171.32). The two alternatives are distinct because their intersection is zero and $C_1$ is nonzero. $\square$

The use of the signed trace in (171.34) is essential. The ordinary partial trace used in published 167.7 cannot simply be imported before its positive orientation has been earned.

### 171.4 A finite projector frame pays the domain at every level

**Theorem 171.9 (all-level pointedness, generation, and strict signed trace).** Suppose Definition 171.1 holds and $C_2=\operatorname{PSD}_{n^2}$. Let $\varepsilon$ be the sign in Proposition 171.8 and put

$$
D_N=\varepsilon^N C_N\qquad(N\ge0).
\tag{171.35}
$$

Then $(D_N)$ is another hierarchy satisfying all the structural requirements (171.1)–(171.6), and

$$
D_1=\operatorname{PSD}_n,\qquad D_2=\operatorname{PSD}_{n^2}.
\tag{171.36}
$$

For every finite $N$, both $D_N$ and $C_N$ are pointed and generating. Moreover

$$
X\in D_N\setminus\{0\}\Longrightarrow\operatorname{Tr}X>0,
\qquad
Y\in C_N\setminus\{0\}\Longrightarrow
                      \varepsilon^N\operatorname{Tr}Y>0.
\tag{171.37}
$$

The complete trace-one base of $D_N$ and the complete signed-trace-one base of $C_N$ are nonempty compact convex bases.

**Proof.** For signs $s,t\in\{\pm1\}$ and closed convex cones $A,B$,

$$
(sA)^*=sA^*,\qquad
(sA)\otimes_{\min}(tB)=st(A\otimes_{\min}B),\qquad
(sA)\otimes_{\max}(tB)=st(A\otimes_{\max}B).
\tag{171.38}
$$

The first equality follows by testing $\langle sF,sX\rangle=\langle F,X\rangle$. The minimum equality follows from the generators and closedness. For the maximum equality, its product tests have the form $sF\otimes tG$, and pairing them with $stZ$ gives $\langle F\otimes G,Z\rangle$. Thus (171.4) transports to $D_N$ because $\varepsilon^{a+b}=\varepsilon^a\varepsilon^b$. Closedness, convexity, the full duals, actual permutations, reassociation, and pairings transport as well. The scalar cone stays $\mathbb R_+$, and (171.36) follows.

We now give a finite frame for every $n\ge2$. On one leg take the following labeled unit rank-one projectors:

$$
\begin{aligned}
P_j&=e_je_j^* &&(0\le j<n),\\
Q_{jk}^{\pm}&=\frac12(e_j\pm e_k)(e_j\pm e_k)^*,\\
R_{jk}^{\pm}&=\frac12(e_j\pm i e_k)(e_j\pm i e_k)^*
                                      &&(0\le j<k<n).
\end{aligned}
\tag{171.39}
$$

Let $\mathcal F$ denote this family. Every member belongs to both $D_1$ and $D_1^*$. The differences $Q_{jk}^+-Q_{jk}^-$ supply $E_{jk}+E_{kj}$, while $R_{jk}^+-R_{jk}^-$ supply $-iE_{jk}+iE_{kj}$. Together with the $P_j$, they span the entire real Hermitian space. For each pair $j<k$, the four projectors in that pair sum to $2(P_j+P_k)$. Consequently

$$
|\mathcal F|=n(2n-1),\qquad
\sum_{F\in\mathcal F}F=(2n-1)I_n.
\tag{171.40}
$$

For a fixed finite $N\ge1$, take all labeled products

$$
F_{\boldsymbol\alpha}=F_{\alpha_1}\otimes\cdots\otimes F_{\alpha_N},
                    \qquad F_{\alpha_j}\in\mathcal F.
\tag{171.41}
$$

Repeated minimum inclusions put each product in $D_N$. Repeated maximum inclusions put each product in $D_N^*$: whenever $f\in D_a^*$ and $g\in D_b^*$, (171.5) asserts precisely that $f\otimes g$ is in $D_{a+b}^*$. The products in (171.41) span $W_N$, because their one-leg factors span $V$ and the carrier is the actual full real tensor product. They also satisfy

$$
\sum_{\boldsymbol\alpha}F_{\boldsymbol\alpha}
                  =(2n-1)^N I_{n^N}.
\tag{171.42}
$$

Hence, for $X\in D_N$,

$$
(2n-1)^N\operatorname{Tr}X
  =\sum_{\boldsymbol\alpha}
       \operatorname{Tr}(F_{\boldsymbol\alpha}X)\ge0.
\tag{171.43}
$$

Every summand is nonnegative. If the trace is zero, every summand is zero. Since the frame products span $W_N$ and the trace pairing is nondegenerate, this forces $X=0$. This proves strict trace positivity on $D_N\setminus\{0\}$.

The span of $D_N$ is all of $W_N$, because it contains the spanning family (171.41). Thus $D_N-D_N=W_N$, so $D_N$ is generating. If $X$ and $-X$ are both in $D_N$, (171.43) gives trace zero and hence $X=0$. Thus $D_N$ is pointed. Multiplication by $\varepsilon^N$ is a real-linear isomorphism, so the same two properties hold for $C_N$, and (171.37) follows.

Only now define the full bases

$$
\begin{aligned}
K(D_N)&=\{X\in D_N:\operatorname{Tr}X=1\},\\
\widehat K_N^{\varepsilon}
  &=\{Y\in C_N:\varepsilon^N\operatorname{Tr}Y=1\}.
\end{aligned}
\tag{171.44}
$$

They are nonempty because the frame products have trace one after transport. Every nonzero cone element is a unique positive scalar multiple of an element of its respective base. For compactness, $K(D_N)$ is closed. If a sequence in it were unbounded in any fixed finite-dimensional norm, division by its norm and passage to a convergent subsequence on the unit sphere would produce $0\ne X\in D_N$ with trace zero, contradicting (171.37). Thus the base is bounded and compact. The sign isomorphism transports it to $\widehat K_N^{\varepsilon}$. For $N=0$, the base is the singleton $\{1\}$ and the claims follow from $C_0=D_0=\mathbb R_+$. $\square$

One can express the bounds used in this proof as

$$
\operatorname{Sep}_N\subseteq D_N
                 \subseteq\operatorname{Sep}_N^*,
\tag{171.45}
$$

where $\operatorname{Sep}_N$ is the closed cone generated by all products of one-leg PSD elements. The left inclusion uses repeated minimum bounds; the right uses all products of one-leg PSD functionals in repeated maximum bounds. The finite family (171.39) proves the asserted strict trace statement inside this interval. Neither (171.45) nor Theorem 171.9 identifies an arbitrary higher $D_N$ with the PSD cone.

**Corollary 171.10 (any nonzero odd-level PSD element selects the sign).** Under Theorem 171.9, for each fixed odd integer $m\ge1$,

$$
\varepsilon=+1
\quad\Longleftrightarrow\quad
C_m\cap\operatorname{PSD}_{n^m}\ne\{0\}.
\tag{171.46}
$$

In particular, $\mathsf T$ forces $\varepsilon=+1$. Its rank conditions are unnecessary for this orientation step.

**Proof.** If $0\ne X\succeq0$ belongs to $C_m$ and $m$ is odd, then $\operatorname{Tr}X>0$. Equation (171.37) gives $\varepsilon\operatorname{Tr}X>0$, so $\varepsilon=+1$. Conversely, if $\varepsilon=+1$, then $C_1=\operatorname{PSD}_n$, and the minimum inclusions put every nonzero product of $m$ one-body PSD elements in $C_m$. Such a product is a nonzero usual PSD matrix. Finally the dyad in $\mathsf T$ is one such nonzero usual PSD element at the odd level three. $\square$

### 171.5 The weak-domain theorem and the exact propagation handoff

**Theorem 171.11 (binary orientation theorem and ternary all-finite reconstruction).** Work throughout in Definition 171.1, with the fixed matrix (171.8) and the matrix supplier explicitly identified in 171.3.

1. The following conditions are equivalent:

$$
\begin{aligned}
&\mathsf B\ \wedge\ \mathsf M_2;\\
&C_2=\operatorname{PSD}_{n^2};\\
&\text{there exists }\varepsilon\in\{\pm1\}\text{ such that }
  C_1=\varepsilon\operatorname{PSD}_n,
  \quad C_2=\operatorname{PSD}_{n^2}.
\end{aligned}
\tag{171.47}
$$

The sign is unique, and every finite signed cone $\varepsilon^N C_N$ has all the properties in Theorem 171.9. Thus pointedness and generation of the original cones themselves, and strict positivity of the signed trace, are consequences of the binary relations.

2. On the same weak domain,

$$
\mathsf B\wedge\mathsf M_2\wedge\mathsf T
\quad\Longleftrightarrow\quad
C_N=\operatorname{PSD}_{n^N}
                    \quad\text{for every finite }N\ge0.
\tag{171.48}
$$

In the forward direction the ternary seed first fixes $\varepsilon=+1$. The resulting ordinary positive-trace hierarchy satisfies every premise of published Definition 167.1 and of XIII Definition 166.1 before Theorem 166.12 is invoked.

**Proof.** Proposition 171.7 proves the first implication in (171.47). Proposition 171.8 proves the next implication. If $C_2=\operatorname{PSD}_{n^2}$, its complete trace dual is also PSD, so $B$ belongs to both cones. Congruence by the specified matrix $M\otimes I$ preserves PSD. This proves the converse without any condition on the other levels beyond the standing weak hierarchy. The remaining binary conclusions are Theorem 171.9.

Assume now all three relations in (171.48). Corollary 171.10 gives $\varepsilon=+1$. Therefore the ordinary $u_N=\operatorname{Tr}$ is strictly positive on every $C_N\setminus\{0\}$, and every $C_N$ is closed, pointed, and generating. At this earned stage put

$$
\begin{aligned}
K_N&=\{X\in C_N:u_N(X)=1\},
&P_N&=\operatorname{ext}K_N,\\
\mathcal E_N&=[0,u_N]_{C_N^*}
 =\{f\in C_N^*:u_N-f\in C_N^*\}.
\end{aligned}
\tag{171.49}
$$

Use the whole $K_N$, all of its extreme points, the already complete dual, the entire interval $\mathcal E_N$, and every finite family $f_a\in C_N^*$ with $\sum_a f_a=u_N$. Each such $f_a$ lies in $\mathcal E_N$ because its complement is the sum of the other nonnegative functionals. This is the full menu convention of the suppliers, with no selected subfamily substituted for it. Compactness and the cone-base interpretation were proved in Theorem 171.9.

The premise correspondence for [XIII, Theorem 166.12, condition 1 implies condition 5][XIII] is now complete:

| Exact premise of the supplier | Object or result here |
| --- | --- |
| A fixed integer $n\ge2$ and actual complex Hermitian real tensor carriers | Definition 171.1, including (171.1) |
| Every finite cone closed, pointed, and generating | Closedness in 171.1; pointedness and generation in 171.9 |
| Strictly positive multiplicative ordinary trace | (171.2), (171.6), 171.9, and the positive orientation from 171.10 |
| Entire bases and extreme-point sets, complete duals, entire proper intervals, all finite unit decompositions | (171.3), (171.44), and the full convention (171.49) |
| All actual finite min/max partitions | (171.4)–(171.5), without truncation |
| Actual positive permutations and positive inverses; noncontiguous partitions | Definition 171.1 |
| Canonical reassociation and compatible actual pairings | (171.1), (171.6) |
| Scalar object, cone, and unit | $W_0=\mathbb R$, $C_0=\mathbb R_+$, $u_0=\mathrm{id}$ |
| Both low-level PSD equalities in the same coordinates | Propositions 171.7–171.8 with $\varepsilon=+1$ |
| A nonzero actual ternary dyad with all flattening ranks at least two and one rank $n$ | Exactly (171.11) |

Consequently Theorem 166.12 applies to the original family $C_N$, and gives $C_N=\operatorname{PSD}_{n^N}$ for every finite $N$. Its inheritance by smaller actual coordinate corners, strictly decreasing control-support induction, two-copy Gram bridge, and exact finite propagation tail are reused under their published premises. They are not reproved here. In particular, neither an arbitrary GME without a full leg nor an assumed high-level PSD cone has replaced a supplier premise.

For the reverse implication in (171.48), the full PSD hierarchy satisfies the weak domain. Products of PSD matrices give the minimum inclusion; testing a PSD joint matrix with any PSD product functional gives the maximum inclusion. Permutations and inverses are unitary congruences, the trace and pairing multiply, and the scalar case agrees with $\mathbb R_+$. The two binary relations then hold as above. The vector

$$
g_n=\sum_{j=0}^{n-1}e_j\otimes e_j\otimes e_j
\tag{171.50}
$$

has dyad in $C_3$ and three flattening ranks $n$, so it supplies the unchanged $\mathsf T$. This proves both directions. $\square$

Pointedness, generation, and ordinary trace positivity have therefore been removed from the input domain of (171.48), rather than renamed as a “state cone” assumption. Ordinary trace positivity is not a consequence of the two binary relations alone; the next model supplies the exact obstruction.

### 171.6 A complete all-finite sign countermodel

**Proposition 171.12 (the alternating PSD hierarchy).** For every fixed $n\ge2$, define at every finite level

$$
C_N^{(-)}=(-1)^N\operatorname{PSD}_{n^N},
\qquad N\ge0,
\tag{171.51}
$$

in the actual carriers (171.1), retaining the ordinary trace and the actual pairings. This is a whole weak-domain model satisfying $\mathsf B$ and the exact $\mathsf M_2$. It fails ordinary strict trace positivity at every odd level and fails $\mathsf T$.

**Proof.** Write $s_N=(-1)^N$. Every $C_N^{(-)}$ is a closed convex cone, and its complete trace dual is exactly

$$
(C_N^{(-)})^*=s_N\operatorname{PSD}_{n^N}.
\tag{171.52}
$$

Indeed $F\in(C_N^{(-)})^*$ means $\operatorname{Tr}(s_NFP)\ge0$ for every $P\succeq0$, which is equivalent to $s_NF\succeq0$. Thus the model has the complete dual, including all of its elements, at every level.

For any finite split $a+b$, if $X=s_aP$ and $Y=s_bQ$ with $P,Q\succeq0$, then

$$
X\otimes Y=s_{a+b}(P\otimes Q)\in C_{a+b}^{(-)}.
\tag{171.53}
$$

Closed conic sums give the full minimum inclusion. For the maximum inclusion, take an arbitrary $Z=s_{a+b}R\in C_{a+b}^{(-)}$ and arbitrary complete-dual elements $F=s_aE$, $G=s_bD$, where $R,E,D\succeq0$. Then

$$
\operatorname{Tr}[(F\otimes G)Z]
   =s_as_bs_{a+b}\operatorname{Tr}[(E\otimes D)R]
   =\operatorname{Tr}[(E\otimes D)R]\ge0.
\tag{171.54}
$$

The last inequality holds for arbitrary PSD $R$, including entangled $R$. The sign product is one because $s_as_b=s_{a+b}$. These computations include zero factors and scalar factors; at level zero (171.51) gives exactly $C_0^{(-)}=\mathbb R_+$.

Every actual tensor-position permutation is a unitary congruence and preserves the parity $N$, so it and its inverse preserve $C_N^{(-)}$. The same is true for transported noncontiguous partitions. Actual reassociation changes no joint matrix or joint cone. The trace pairing and ordinary trace keep (171.6) as algebraic identities. Therefore every structural clause of the weak domain holds for all finite levels simultaneously.

At level two both the cone and its complete dual are the usual PSD cone, so $B$ belongs to both. The specified matrix $M$ is invertible, and its local congruence preserves $C_2^{(-)}=\operatorname{PSD}_{n^2}$, proving the exact single-map relation. In fact any same-level local matrix congruence preserves (171.51).

At every odd $N$, a nonzero element has the form $X=-P$, $0\ne P\succeq0$, and

$$
u_N(X)=-\operatorname{Tr}P<0.
\tag{171.55}
$$

Thus $u_N$ is not even a nonnegative functional on that cone. The ordinary trace-one section is empty at every odd level. The signed trace $s_Nu_N$ is strictly positive and has the usual compact base after sign transport, exactly as Theorem 171.9 predicts.

Finally, $C_3^{(-)}=-\operatorname{PSD}_{n^3}$ contains no nonzero usual PSD dyad. Hence $\mathsf T$ fails independently of its rank requirements. The cones themselves remain pointed and generating; the counterexample concerns the ordinary orientation and the ordinary positive-trace/full-PSD conclusion, not the derived pointedness or generation. $\square$

More generally, the parity operation $C_N\mapsto(-1)^NC_N$ preserves the weak structural domain and both binary relations, since level two is unchanged. It interchanges the two signs in (171.32). It does not preserve the odd-level positive-dyad selector. This is an exact $\mathbb Z_2$ obstruction. Model (171.51) is a countermodel in the enlarged weak domain; it is not a countermodel to the old theorem whose input already required ordinary strict trace positivity. It also does not exhibit a non-PSD higher cone after the sign has been removed: its signed cones are precisely PSD. No stronger claim about all weak higher cones is inferred from this example.

### 171.7 Proper resources and exact finite coefficients after the domain is earned

**Proposition 171.13 (the retained budget interfaces).** Assume the binary relations and a nonzero usual PSD element at any odd level. In particular, this applies under $\mathsf T$. The ordinary full bases and proper intervals (171.49) are then defined on a closed, pointed, generating, strictly positive-trace hierarchy. The following are the original proper-resource coefficients, used only at this stage.

**Proof and supplier substitution.** Corollary 171.10 fixes the positive orientation, and Theorem 171.9 establishes the entire proper domain. Since $C_2=\operatorname{PSD}_{n^2}$, the complete Bell cap bound is now

$$
b=\max_{X\in K_2}\beta(X)=n,
\qquad B/n\in K_2,\qquad \beta/n\in\mathcal E_2.
\tag{171.56}
$$

The value $n$ follows because $B$ has largest eigenvalue $n$, attained on $B/n$. This bound is now being tested on the already identified whole $C_2$. It was not used in the raw proof.

For every proper $f\in\mathcal E_a$ and every correlated $Z\in C_{a+b}$, complete-dual slicing and the maximum inclusion give

$$
0\le u_b((f\otimes\mathrm{id})Z)\le u_{a+b}(Z).
\tag{171.57}
$$

Both inequalities now have their premises: $u_b\in C_b^*$ and $f,u_a-f\in C_a^*$. This is exactly the proper-budget part of [163.2][XIII] and [VII102.7][VII]. It applies at each intermediate correlated input of a finite contraction.

For the specified $M$, retain the quantities

$$
\begin{aligned}
r&=\operatorname{Tr}(M^*M)>0,\\
m&=\max_{X\in K_2}u_2(\operatorname{Ad}_{M\otimes I}X)
      =\|M\|_{\rm op}^2>0,\\
\alpha&=\min\{1,m^{-1}\}>0.
\end{aligned}
\tag{171.58}
$$

Applying the proper two-body branch $\alpha\operatorname{Ad}_{M\otimes I}$ to $B/n$ supplies $\alpha R_{M^{\mathsf T}}/n$, of mass $\alpha r/n\in(0,1]$. Using that unnormalized resource and a proper cap $\beta/n$ produces

$$
\frac{\alpha}{n^2}\operatorname{Ad}_{M^{\mathsf T}};
\tag{171.59}
$$

SWAP gives the same coefficient for $\operatorname{Ad}_M$. If instead the normalized mathematical resource $R_Q/r\in K_2$, $Q=M$ or $M^{\mathsf T}$, is supplied, the coefficient is

$$
\eta\operatorname{Ad}_Q,\qquad \eta=\frac1{nr}>0.
\tag{171.60}
$$

These are the two distinct resource conventions in candidate 170.3, now independently licensed by the earned domain. They have different supply masses. A length-$k$ word $Q$ in these two letters has coefficient $\eta^k$ with normalized resources, or $(\alpha/n^2)^k$ with the once-produced unnormalized resources. For the latter convention the finite contraction uses $k$ copies of $B/n$, $k$ uses of the proper binary branch on resource pairs, the required actual permutations, and $k$ proper Bell caps. These operations successively return to the same spectator-plus-input type. For a nonzero positive input, the invertibility of the word gives a nonzero output, whose mass is strictly positive by Theorem 171.9.

For an individual recovered nonzero one-body matrix $A$, the whole PSD $C_2$ contains $R_A$, including when $A$ is singular. Set $r_A=\operatorname{Tr}(A^*A)>0$. The normalized-resource coefficient is exactly

$$
\frac1{nr_A}\operatorname{Ad}_A.
\tag{171.61}
$$

The full original Choi and budget interfaces may now be consumed from [167.8][P167], [163.2][XIII], and [VII102.6–102.7][VII]. In particular, $s_A=\max\{1,\|A\|_{\rm op}\}$ gives the all-spectator TNI congruence $\operatorname{Ad}_{A/s_A}$. For $A=0$ use the zero map, without normalizing a zero resource. On $a$ input legs, normalized identity cups and proper caps give $n^{-2a}\mathrm{id}$; using a directly supplied nonzero Choi resource $J(F)/\operatorname{Tr}J(F)$ instead gives

$$
\frac{1}{n^a\operatorname{Tr}J(F)}F.
\tag{171.62}
$$

The two formulas involve different resources and retain their respective coefficients.

The published exact finite control statement [167.4–167.5][P167] is also available after this handoff. Choose any $0<\lambda<1$ and $S=\operatorname{diag}(\lambda,1,\ldots,1)$. Proposition 171.6 supplies its positivity and all local unitary positivity. If the supplied exact finite word is $Q=c_AA$, $c_A>0$, and contains $k$ occurrences of $S$, its proper output coefficient is

$$
\alpha_S^k c_A^2,
\qquad
\alpha_S=\min\{1,m_S^{-1}\},\quad
m_S=\max_{X\in K_2}u_2(\operatorname{Ad}_{S\otimes I}X).
\tag{171.63}
$$

Here $m_S=1$ in the identified PSD cone, so $\alpha_S=1$; the factor $c_A^2$ still remains. This is an exact finite realization with an enlarged continuous unitary alphabet. Supplier 171.3 concerns a closure of a countable two-letter alphabet. These are different assertions; the latter does not make every recovered matrix an exact two-letter word.

Under $\mathsf T$, the full-finite supplier carries its original coefficients as well. To state them without confusing the original fixed matrix $M$ with a later regular pencil, let $d$ be the supplier's current local dimension, let each selected but otherwise unrestricted seed be supplied as $h\psi\psi^*/\delta$, $\delta=\|\psi\|^2$, and let the actual real control be supplied as $t_Q QQ^*/q_Q$, $q_Q=\|Q\|^2$. With the supplier's common filter $L/s_L$, its three proper Bell caps and two seed copies give [166.11][XIII]

$$
\kappa\,\xi\xi^*,\qquad
\kappa=\frac{h^2t_Q}{\delta^2q_Qs_L^2d^3}>0,
\quad
\xi=|C\rangle\!\rangle|0\rangle+|D\rangle\!\rangle|1\rangle.
\tag{171.64}
$$

Here $C$ is invertible and $D\notin\mathbb CC$ by that supplier. The final filter $C^{-1}/s_C$, $s_C=\max\{1,\|C^{-1}\|\}$, gives coefficient $\kappa/s_C^2$. Writing $\mathsf N=C^{-1}D$, its mass is

$$
\frac{h^2t_Q[d+\operatorname{Tr}(\mathsf N^*\mathsf N)]}
 {\delta^2q_Qs_L^2d^3s_C^2}\in(0,1].
\tag{171.65}
$$

The control is itself paid for by [166.10][XIII]: three normalized Bell resources give $t_Q=d^{-3}$; if their supply masses are $b_1,b_2,b_3>0$, then $t_Q=b_1b_2b_3/d^3$. Thus the full dyad coefficient in (171.64) contains $d^{-6}$ after including this preparation. Its six preparation legs are separate from the nine-leg core consisting of the two seeds and the control. The restricted copies that establish a smaller corner and pay its effects are not the two unrestricted seed copies in the core, and their masses are not multiplied into the later control a second time.

Equations (171.64)–(171.65) are explicit reuse of the existing supplier, with the complete premises paid in Theorem 171.11. Its strictly smaller control dimensions, finite choices, proper filters, and proper caps ensure finite products of strictly positive coefficients. They supply no dimension-independent copy bound or success lower bound.

Finally, closed-cone membership of a recovered limit resource is a mathematical conclusion. It gives neither a limiting device nor a uniform positive production probability along its approximating words. Already in the ordinary PSD hierarchy, repeating the proper scalar filter $aI$, $0<a<1$, gives mass $a^{2k}$ on trace-one inputs. Thus positivity of every fixed finite coefficient does not establish positive mass for an infinite protocol. $\square$

### 171.8 The complete original quantum correspondence

**Corollary 171.14 (the existing full finite dictionary on the earned domain).** Under Theorem 171.11(2), put $d_N=n^N$ and $d_0=1$. The original objects have the following complete correspondence in the same actual coordinates.

| Original object or relation | Quantum expression |
| --- | --- |
| Entire $K_N$ and its convex preparations | All $\rho\succeq0$ with $\operatorname{Tr}\rho=1$, with usual convex mixtures |
| Entire $P_N$ and nonzero extreme rays | All unit rank-one projectors and their positive multiples; pure-state space $\mathbb{CP}^{d_N-1}$ |
| Complete trace dual and entire proper interval | All PSD functionals and every $0\preceq E\preceq I_{d_N}$ |
| All finite unit decompositions and original pairing | All finite POVMs, including PVMs; $p(a\mid\rho)=\operatorname{Tr}(E_a\rho)$ |
| Hermitian observables | Their spectral PVMs and expectations $\operatorname{Tr}(A\rho)$ |
| Actual finite composition and all partitions | The whole density-matrix space on $(\mathbb C^n)^{\otimes N}$, including entangled states |
| Actual permutations and unit slices | Ordinary factor permutations and partial traces on arbitrary correlated inputs |
| Exhaustive confirmation at a pure projector $p$ | $\inf\{f(X):f\in\mathcal E_N,\ f(p)=1\}=\operatorname{Tr}(pX)$ for $X\in C_N$ |
| Pure-state confirmation overlap | $\operatorname{Tr}(vv^*ww^*)=|v^*w|^2$ for unit vectors |
| Maps positive with every original finite spectator | All rectangular completely positive maps, with the Choi and Kraus expressions below |
| Full-input TNI or TP budgets | Kraus completeness inequality or equality |
| Finite branch families with TP sum | All finite mathematical CP instruments, with the original sequential, adaptive, coarse-graining, and tensor rules |

**Proof by exact supplier reuse.** Theorem 171.11 has established the actual all-finite PSD target and the full domain of [167.9][P167] and [166.14][XIII]. Their proofs give the first nine rows, including all extreme points and the least confirmation formula, rather than a selected collection of states or effects. The supplied Hilbert carrier, actual tensor product, convex linear preparation law, and trace pairing remain standing inputs. The derived assertion is the complete allowed cone and the resulting full dictionary on that carrier. The standard matrix ingredients are also identified in [Watrous, §§1.1.2–1.1.3 and §2.1.2][W1W2].

For clarity, the exact process interface being consumed from [VII102.7 and 102.13][VII], [167.8–167.9][P167], and [XIII161.9][XIII] is as follows. For finite $a,b\ge0$ and real-linear $F:W_a\to W_b$, use its unique complex-linear Hermiticity-preserving extension and reference–output order:

$$
J(F)=\sum_{i,j=0}^{d_a-1}E_{ij}\otimes F(E_{ij}).
\tag{171.66}
$$

Then

$$
\begin{aligned}
F\text{ positive with every original finite spectator}
&\Longleftrightarrow J(F)\in C_{a+b}
 \Longleftrightarrow J(F)\succeq0\\
&\Longleftrightarrow
F(X)=\sum_\gamma K_\gamma XK_\gamma^*,
\qquad K_\gamma:\mathbb C^{d_a}\to\mathbb C^{d_b}.
\end{aligned}
\tag{171.67}
$$

The full original self-reference criterion now has its low-level and proper-domain premises. The last equivalence is the existing rectangular Choi/Kraus theorem, [Watrous, Theorem 2.22][W2], after the actual SWAP between that text's output–reference order and (171.66). For nonzero $F$ its Kraus number can equal $\operatorname{rank}J(F)\le d_ad_b$; for zero $F$ use the empty Kraus sum. Only original reference dimensions $n^s$ were initial objects. Usual CP with arbitrary finite matrix reference dimension follows from the resulting Kraus form.

Writing $Q_F=\sum_\gamma K_\gamma^*K_\gamma$, the budget interface is

$$
\begin{aligned}
\operatorname{Tr}_{\rm out}J(F)&=Q_F^{\mathsf T},\\
u_bF\le u_a&\Longleftrightarrow Q_F\preceq I_{d_a},\\
u_bF=u_a&\Longleftrightarrow Q_F=I_{d_a}.
\end{aligned}
\tag{171.68}
$$

These are whole-input conditions, including all original correlated spectator extensions. They are the exact budget conclusions of the cited suppliers and [Watrous, Theorem 2.26][W2]; a single total trace of $J(F)$ does not replace its full reference marginal.

For a finite mathematical instrument of fixed input and output types,

$$
F_\ell(X)=\sum_\gamma K_{\ell\gamma}XK_{\ell\gamma}^*,
\quad
\sum_{\ell,\gamma}K_{\ell\gamma}^*K_{\ell\gamma}=I_{d_a},
\quad E_\ell=F_\ell^\dagger(I)=\sum_\gamma K_{\ell\gamma}^*K_{\ell\gamma}.
\tag{171.69}
$$

Every branch has a same-output-type complement by the existing Kraus family $|v\rangle\langle b_j|\sqrt{I-Q_F}$, for a unit output vector $v$ and an input orthonormal basis $(b_j)$. Every effect and finite POVM occurs as the effect family of a mathematical instrument, for example through $X\mapsto\operatorname{Tr}(E_\ell X)\omega$ with a fixed normalized output $\omega$.

For an arbitrary correlated original input $Z\succeq0$ of mass $m=\operatorname{Tr}Z$, the complete conditioning statement consumed from [161.9, (161.27)–(161.30)][XIII] is

$$
\begin{aligned}
Z_\ell&=(\mathrm{id}\otimes F_\ell)Z,\\
m_\ell&=\operatorname{Tr}Z_\ell
       =\operatorname{Tr}[(I\otimes E_\ell)Z],
\qquad \sum_\ell m_\ell=m.
\end{aligned}
\tag{171.70}
$$

For $m>0$, outcome probability on the normalized input is $m_\ell/m$. Only for $m_\ell>0$ is the conditional joint state $Z_\ell/m_\ell$ defined. If $m_\ell=0$, the unnormalized positive output is zero; no normalized zero-mass state is prescribed. Zero input gives all zero outputs, and zero-labeled branches can be retained. The same supplier gives

$$
\operatorname{Tr}_{\rm out}Z_\ell
 =\operatorname{Tr}_{\rm in}
  [(I\otimes\sqrt{E_\ell})Z(I\otimes\sqrt{E_\ell})],
\qquad
\sum_\ell\operatorname{Tr}_{\rm out}Z_\ell
                 =\operatorname{Tr}_{\rm in}Z.
\tag{171.71}
$$

It also supplies the finite sequential and adaptive composition laws, addition of unnormalized outputs under coarse-graining, and tensor-product instrument laws. These are the previously proved matrix-level rules, not a new propagation or instrument proof. Their standard instrument form is [Watrous, §2.3.2, (2.255)–(2.261)][W2].

Scalar boundaries remain part of this full correspondence. For $a=0$, $F(q)=q\sigma$ with $\sigma\succeq0$, and TNI/TP means $\operatorname{Tr}\sigma\le1$ or $=1$. For $b=0$, $F(X)=\operatorname{Tr}(EX)$, and TNI/TP means $0\preceq E\preceq I$ or $E=I$. With both types scalar, the map is multiplication by a nonnegative scalar, TNI at most one and TP equal to one. The scalar base is $\{1\}$ and its effect interval is $[0,1]$; the one-dimensional ray space is $\mathbb{CP}^0$. The empty reference cup is the scalar one. $\square$

Mathematical admissibility is not event availability. Identifying this entire branch and instrument theory with an actual available device menu requires the additional **event-saturation choice** of [VII, Definition 102.14][VII]. Static effects specify probabilities and conditional spectator marginals; a whole post-measurement output requires a specified branch. The next two consumers retain their own additional data.

### 171.9 Ideal sharp update and a given continuous reversible action

**Corollary 171.15 (the existing ideal sharp-neutral update correspondence).** Under Theorem 171.11(2), fix any finite $k\ge0$. Let $P=P^*=P^2$ on $\mathbb C^{d_k}$, and let $L:W_k\to W_k$ be a positive real-linear map satisfying

$$
u_kL(X)=\operatorname{Tr}(PX),\qquad
L(p)=p\quad\text{for every }p\in P_k
                         \text{ with }\operatorname{Tr}(Pp)=1.
\tag{171.72}
$$

Then the existing matrix sharp-neutral supplier gives

$$
L(X)=PXP.
\tag{171.73}
$$

**Proof by supplier substitution.** The complete pure-state dictionary in Corollary 171.14 makes the second quantifier in (171.72) exactly the quantifier over every unit ray in $\operatorname{Ran}P$, including all rays in a degenerate yes subspace. The first identity is $L^\dagger(I)=P$. Thus the matrix premises in [XIII161.7.1, application of Atlas Proposition 13.4(1)][XIII] hold with the same single matrix sector and coordinate transport $\Theta_k=\mathrm{id}$. That existing positive real-linear uniqueness argument yields (171.73) on all of $W_k$. No CP assumption is needed in that supplier; CP and all spectator lifts follow from the obtained compression and the earned dictionary. The endpoints $P=0$, $P=I$, and $d_k=1$ are included.

For a finite orthogonal decomposition $\sum_\ell P_\ell=I$ and a normalized correlated input $Z\succeq0$, the supplied joint-state formulas are

$$
\begin{aligned}
p_\ell&=\operatorname{Tr}[(I\otimes P_\ell)Z],\\
Z_{\mid\ell}&=
 \frac{(I\otimes P_\ell)Z(I\otimes P_\ell)}{p_\ell}
                  \quad(p_\ell>0),\\
Z_{\rm ns}&=\sum_\ell(I\otimes P_\ell)Z(I\otimes P_\ell).
\end{aligned}
\tag{171.74}
$$

These are [161.30b–161.30c][XIII], now with identity coordinate transport. At zero probability only the zero unnormalized output is specified. The pointwise neutrality in (171.72) is additional data characterizing an ideal sharp branch. Outcome repeatability alone does not supply it: a map $X\mapsto VPXPV^*$ with $V$ rotating rays within $\operatorname{Ran}P$ has the same sharp effect and repeats that outcome, while disturbing some certain-yes rays. This distinction, including its degenerate-subspace requirement, is already part of the cited supplier. $\square$

**Corollary 171.16 (Hamiltonian classification of a given continuous real order action).** Under Theorem 171.11(2), additionally give a real-linear family $A_\tau:W_k\to W_k$ on a fixed finite level, satisfying

$$
A_0=I,\quad A_{\tau+\sigma}=A_\tau A_\sigma,\quad
A_\tau(C_k)=C_k,\quad u_kA_\tau=u_k,
\tag{171.75}
$$

and continuity in the finite-dimensional operator topology for $\tau\in\mathbb R$. Then there is a Hermitian matrix $\mathsf H$, unique modulo a real scalar multiple of the identity, such that

$$
A_\tau(X)=e^{-i\tau\mathsf H}Xe^{i\tau\mathsf H},
\qquad \mathcal L(X)=-i[\mathsf H,X].
\tag{171.76}
$$

**Proof by supplier substitution.** The cone and trace have already become the ordinary whole matrix PSD cone and trace. Thus (171.75) is precisely a given continuous trace-preserving real order-automorphism group on that matrix space. Apply the matrix-level proof of [XIII, Theorem 161.10, starting from its transported group $B_t$][XIII], with coordinate transport the identity. Its equal-size rank-one-preserver classification, exclusion of the transpose component by connectedness, and local unitary lift have exactly these premises. It neither assumes an implementing unitary family nor requires differentiability as an extra hypothesis. It gives (171.76), including matrix size two. At size one the action is the identity and every Hermitian scalar represents the generator. This application does not invoke the earlier geometric reconstruction assumptions of Theorem 161.5. $\square$

For a vector representative and density matrix, the corresponding supplied equations are $i\dot\psi=\mathsf H\psi$ and $i\dot\rho=[\mathsf H,\rho]$. They describe the **given** real action. A physical clock, identification of its parameter with physical time, energy calibration, and a positive action scale $\hbar$ are additional data; after those are given one may write $H_{\rm phys}=\hbar\mathsf H$ and the usual equations with $\hbar$. The fixed dimensionless $t=1/(32n)$ in (171.8) is not that physical time. Different Hamiltonians, the identity action, and parameter rescalings preserve the same static hierarchy. Neither the binary relations nor $\mathsf T$ selects such a dynamics or an actual ideal measuring device.

### 171.10 Provenance, scope, and the remaining questions

**Proposition 171.17 (the exact dependency and limitation statement).** The bridges used on the weakened domain are Lemmas 171.4–171.5, the cone-closure transfer in 171.6, the weak-domain double orbit in 171.7, the sign argument in 171.8, the finite projector-frame argument in 171.9, and the selector in 171.10. Their proofs above do not use pointedness, generation, or positive ordinary trace as an input, and do not invoke the old full-domain reconstruction to establish any of them.

**Proof and source accounting.** The raw slice uses only the maximum bound and closed-cone bipolarity. The raw Bell bridge additionally uses the minimum bound, complete Bell dual membership, and actual permutations. The transfer uses only cone closedness and the isolated matrix closure assertion. The double orbit additionally uses Bell state membership and finite matrix decompositions. The one-body sign uses the actual $(1,1)$ bounds; the finite frame uses the actual tensor span and all repeated min/max bounds. The selector uses strict signed trace, established by that frame. This lists the full antecedents of every new bridge and their order of use.

The exact source dependencies and their mathematical roles are as follows.

| Source | Exact role in this chapter |
| --- | --- |
| Candidate XVI §170 at `4a2c3cc8bb4620516476cd923a7334f4df59e1a9` [A170] | The exact fixed matrices, and only the algebraic closure statement and its matrix proof in 170.4; candidate 170.3/170.5 are not antecedents of the new weak-domain bridges |
| Published XVI §167 at `d91fdb64e60124b82bcead3c5dbe4d33cd50eaf5` [P167] | The old full-domain contract for comparison; after the domain is earned, 167.4–167.5 exact finite-word budgets and 167.8–167.9 original Choi and dictionary consumers |
| XIII §166 at `00427ae2ba9c9e3f6c37f2e5496b9127b6fbc6c0` [XIII] | Complete 166.1–166.2 premise and seed contracts; 166.10–166.11 exact finite coefficients; 166.12 condition 1 to condition 5; 166.14 dictionary |
| XIII §163.1–163.2 at that same pin | The earned low-two-level full-spectator filters, complete slicing, Choi interface, and proper budgets |
| XIII Definition 161.8, Theorems 161.9–161.10, and §161.7.1 at that same pin | Only their post-reconstruction matrix instrument/zero-mass rules, ideal sharp-neutral consumer, and classification of a given continuous real order action |
| VII102.6–102.7 and 102.13–102.15 at `657a8ba435bf2cae463e935d957d8038b69be8a3` [VII] | The exact original slicing/Choi interfaces after their premises are paid, rectangular process and complement dictionary, and separate event-saturation choice |
| Hall, author text `math-ph/0005032v1` [Hall] | Relative closed matrix groups, real Lie algebra operations, and the norm-controlled logarithm cited by the algebraic supplier |
| Watrous, author Chapters 1 and 2 [W1], [W2] | Spectral/SVD facts, finite PSD and density-matrix geometry, rectangular Choi/Kraus theorem 2.22, TP marginal theorem 2.26, and the standard POVM/instrument correspondence |

The exact mathematical dependency on §170.4 at the fixed source [A170] is (171.12), not its stronger theorem on the original positive-trace domain. Hall supplies the general group tools, not the particular generation computation as an independently established external theorem. Theorem 171.11 consequently has the ordinary status of a paper proof with that expressly identified candidate algebraic dependency. The all-finite and dictionary conclusions similarly consume the published paper suppliers and their named dependencies; reading them is not an independent re-verification of their entire dependency chains.

No gap has been used to skip a new cone bridge: they are proved above for the stated weak domain. The source reliance just identified remains visible and is not promoted into kernel certification or independent settlement of candidate170. There are also precise mathematical questions not resolved by this chapter. Without $\mathsf T$ the theorem gives $C_2=\operatorname{PSD}$, $C_1=\varepsilon\operatorname{PSD}$, and properness with signed trace at every level. It does not conclude $\varepsilon^N C_N=\operatorname{PSD}_{n^N}$ for all higher $N$. Nor does the frame argument supply a countermodel to that stronger signed higher-level claim. Even an arbitrary odd PSD selector pays only orientation; its ranks need not pay 166.12.

If a given GME vector has every one-leg rank below $n$, the particular full-leg propagation interface has not been met. For example, when $n>2$, the embedded vector $e_0^{\otimes3}+e_1^{\otimes3}$ has all three ranks two. The present argument does not settle reconstruction from such a general non-full-leg seed. This is an unmet supplier premise, not a full finite nonquantum countermodel. Removing closedness, replacing complete duals by a selected family, truncating the finite hierarchy, or deleting actual positive permutations would likewise remove specifically used premises; no independence theorem for those premises is claimed.

The exact counterexample proved here is (171.51). It refutes recovery of the ordinary positive orientation from the binary relations alone while satisfying the entire weak all-finite structural domain. Complex scalars, the actual Hermitian carrier, local dimension, all finite actual compositions, and pairing compatibility remain model assumptions. Nothing here reconstructs infinite-dimensional theory, a physical event menu, a clock, an energy assignment, spacetime, or a numerical value of $\hbar$. There is no claim of kernel verification, empirical confirmation, global novelty, or a globally minimal independent axiom list. $\square$

### 171.11 完整中文几何说明

**说明 171.18（先接线、再定方向、最后归一的完整图景）。** 这章从一开始就保留原来的复 Hermitian 矩阵空间，保留任意有限多个系统的真实张量空间、全部分块和全部位置交换，也保留对每个锥非负的所有线性测试。这里的“全部”很重要：不是只检查某几份输入，也不是只保留乘积态。先不规定锥一定尖、一定张满空间，甚至不规定普通迹在锥上为正，因此最初没有理由把迹叫作概率总量，也没有先定义归一态、合法概率效果或成功率。

贝尔矩阵同时属于二体锥和它的完整对偶，意味着它既能作为一个原锥中的相关对象，也能作为一个非负线性测试。把唯一给定矩阵作用到这个对象上，再用同一个贝尔测试接回输入，就得到局部矩阵转置对应的合同。这里转置的是局部矩阵的系数，接线后的输出仍是通常的 $QXQ^*$，没有把任意输入态作转置。整条接线先只说明输出仍在锥内，不声称测试值小于一，也不把它当成已归一的实验。最小分块关系允许把输入和资源放在一起，最大分块关系保证完整对偶测试切走两条腿后，剩下的仍在整个原锥里；所以与输入相关的任意旁观者也一直保留。

候选170中单独使用的代数计算说明，这两个正向矩阵的闭包先露出链端的一圈无理相位，再沿固定混合的路径取得各个方向的旋转和相对伸缩。这里准确复用的是那一段矩阵生成证明，而不是候选170已经要求正迹的整域定理。每个固定有限层的锥是闭的，所以这些矩阵极限仍保持该层的锥。贝尔对象的准备轨道因此填入全部二体 PSD 方向；贝尔测试的对偶轨道又排除全部非 PSD 方向。两面同时夹住，二体锥就成为通常量子锥。整个过程尚未借用紧归一基或 proper 帽。

二体形状确定后，一个一体元素和自己相乘不能出现负特征值，这迫使每个非零一体元素要么全向普通正半边，要么全向负半边。正半边和负半边又不能同时存在，否则它们的乘积会落到二体负半边。因此一体锥只有一个共同方向，但二体关系还分不清这个共同方向究竟朝上还是朝下。把一体方向反过来时，两体的两个负号相消；更一般地，把所有奇数层同时反过来，全部有限张量分块关系仍然成立。明确模型就是偶数层取 PSD、奇数层取负 PSD。它保留全部原关系和那一个矩阵，却在每个奇数层具有负的普通迹，并且没有任何非零普通正的三体 dyad。这是完整有限层级的符号障碍，不是旧正迹域里的反例。

选定这个共同符号以后，还有一项不能省略的工作：为什么任意高层锥都会尖、都会张满，而且非零元素的带符号迹一定严格为正？可以在一条腿上取基向量的投影，再取每对基向量实相加、实相减、带 $i$ 相加和带 $i$ 相减的投影。这是一个明确的有限家族，能分清整张 Hermitian 矩阵的所有实方向，它们相加又是恒等矩阵的正倍数。取任意有限条腿的所有这些投影乘积，最小关系保证它们在锥里，最大关系保证它们也都能作非负测试。它们仍张满整个真实张量空间，总和仍是恒等的正倍数。

因此，一个高层锥元素如果带符号总迹为零，每个投影测试就都只能为零；完整张成又迫使这个元素本身为零。这说明任何非零元素的带符号总迹都严格为正，正反两条同一直线不能同时留在锥中，锥中的元素之差又能表达空间的所有方向。到这一步，尖性、生成性和严格正迹才全部成为推论。把带符号迹截成一得到完整归一基；它不能向无穷远跑，否则归一方向的极限会给出一个非零但迹为零的锥元素，所以这个基是紧的。这个有限投影论证对每个有限层、每个 $n\ge2$ 都适用，并没有假定高层锥已经等于 PSD。

任何奇数层只要真的包含一个非零的普通 PSD 元素，它的普通迹就是正的，便能排除朝下的共同方向。原来的三体种子当然有这个作用；选择正方向根本不需要它的秩条件。但该种子的另一项工作确实需要那些秩：三条腿都不能是乘积方向，而且至少一条腿要占满原局部空间。正方向确定以后，旧定理要求的闭、尖、生成、严格正乘法迹、完整基、全部极点、完整对偶、整个 proper 区间、全部有限单位分解、每个实际分块和正逆交换，才逐项全部齐备。此时准确接入166.12，由它已有的小角控制、有限种子接合和全有限传播，得到每一层都是完整量子 PSD 锥。这一段传播没有被本章的符号论证代替，也没有把任意一个未满腿的纠缠态都擅自当成合格入口。

归一和预算必须放在这个次序之后。贝尔态除以 $n$、贝尔测试除以 $n$ 才分别成为归一资源和 proper 帽，接线会留下明确的 $n$ 因子；由唯一矩阵的一次实际数学分支供应资源时，还要保留该分支的缩放和质量。两份种子、控制态、三只帽以及最后的逆矩阵滤波也各有自己的平方系数和供应质量。有限个严格正因子相乘仍严格正，但这不保证一串越来越长的协议有统一成功下界，更不保证极限装置存在。锥内正比例可以用来证明方向属于锥，不能在概率账目中把那个比例抹去。

最后才读取熟悉的量子对应：完整归一基是全部密度矩阵，全部极点是单位射线，完整效果和有限单位分解是所有 POVM，原配对给 Born 读数，真实张量空间上的完整联合锥包括纠缠态；原自身参考的 Choi 判据给所有矩形 CP 映射，逐输入的迹预算给 TNI、TP 和有限数学仪器。正质量时才有条件态，零质量输出只能是零，不能除以零。一个效果没有替整台测量指定唯一更新；还给出对每条确定为 yes 的射线逐点不扰动，才能消费已有锐中性定理，得到 Lüders 压缩。静态锥也没有挑出时间演化；还给出一个连续、可逆、保迹的真实实线性序作用，才由已有分类取得 Hamiltonian。物理钟、能量单位和 $\hbar$ 仍须另外标定，数学仪器是否真的属于可用装置菜单也须另给事件选择。本章的简化是把锥的良好形状和归一结构从完整关系中推出，并准确保留一个不可避免的奇偶符号；它没有从零生成复数载体、物理设备或所有量子公理的独立最小列表。

[A170]: https://github.com/the-omega-institute/trureturing/blob/4a2c3cc8bb4620516476cd923a7334f4df59e1a9/docs/develop/theory/QUANTUM_ORIGIN_BINARY_BELL_ORBITS_AND_SINGLE_ATTENUATOR_XVI.md#170-一个端点相位的固定复正交混合与全有限量子对应
[P167]: https://github.com/the-omega-institute/trureturing/blob/d91fdb64e60124b82bcead3c5dbe4d33cd50eaf5/docs/develop/theory/QUANTUM_ORIGIN_BINARY_BELL_ORBITS_AND_SINGLE_ATTENUATOR_XVI.md#167-二体有限控制一腿满维种子与全部有限量子锥
[XIII]: https://github.com/the-omega-institute/trureturing/blob/00427ae2ba9c9e3f6c37f2e5496b9127b6fbc6c0/docs/develop/theory/QUANTUM_ORIGIN_BINARY_TANGENT_CLOSURE_AND_GLOBAL_NONCOLLAPSE_XIII.md
[VII]: https://github.com/the-omega-institute/trureturing/blob/657a8ba435bf2cae463e935d957d8038b69be8a3/docs/develop/theory/QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md
[Hall]: https://arxiv.org/pdf/math-ph/0005032v1
[W1]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
[W2]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
[W1W2]: https://cs.uwaterloo.ca/~watrous/TQI/

## 追加锚（本行以下为增补区）

## 172. A native deformed cup, the Bell cap, and a full classical countermodel

On the weak actual complex Hermitian tensor domain, one specified deformed binary cup and the ordinary Bell cap recover the ordinary Bell cup and every local matrix congruence. Thus they replace the old operation-preservation premise by a resource membership. Mathematical cone positivity comes first: no normalized state, positive ordinary trace, proper cap, or probability is used in this recovery. The unchanged ternary seed then selects the ordinary orientation and meets the existing all-finite propagation theorem.

The converse limitation is also exact. At every odd prime local dimension there is a full finite hierarchy of Wigner simplex cones, with complete duals and complete effect menus, satisfying the ordinary Bell relation and the ternary seed. It is not the quantum hierarchy and cannot contain the specified deformed cup. In particular, the condition being refuted is Bell plus the ternary seed **without** the deformation; no additional unitary-preservation premise is retained in that target.

The control closure is reused from published §170.4 at its immutable source [S170]. The weak-domain sign and properness results are reused from §171 at the fixed source [S171]. All-finite propagation is the published Theorem 166.12 at [S166]. These are explicit mathematical source dependencies. The new resource bridge and the complete classical model are proved below.

### 172.1 The actual weak domain and the two supplied resources

**Definition 172.1 (weak actual all-finite hierarchy).** Fix an integer $n\ge2$. In fixed actual Kronecker coordinates let

$$
V=\operatorname{Herm}_n(\mathbb C),\qquad
W_N=V^{\otimes_{\mathbb R}N}
    =\operatorname{Herm}_{n^N}(\mathbb C),\qquad W_0=\mathbb R.
\tag{172.1}
$$

For every finite $N\ge1$ take a closed convex cone $C_N\subset W_N$, initially with no pointedness, generation, nonzero-span, or trace-positivity requirement. Set $C_0=\mathbb R_+$ and retain the algebraic functionals

$$
u_N=\operatorname{Tr}=u_1^{\otimes N},\qquad u_0=\mathrm{id}.
\tag{172.2}
$$

The real trace pairing represents the **complete** dual:

$$
C_N^*=\{Y\in W_N:\operatorname{Tr}(YX)\ge0
                         \text{ for all }X\in C_N\}.
\tag{172.3}
$$

For all finite nonnegative $a,b$ require

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}
                  \subseteq C_a\otimes_{\max}C_b.
\tag{172.4}
$$

The minimum is the closed convex cone generated by positive simple tensors. The maximum is the set of $Z\in W_{a+b}$ for which

$$
\operatorname{Tr}[(F\otimes G)Z]\ge0
                  \quad(F\in C_a^*,\ G\in C_b^*).
\tag{172.5}
$$

Every actual permutation of positions and its inverse preserves the relevant cone. These maps transport all noncontiguous partitions. Reassociation is the canonical identification in the same actual space with the same joint cone. Pairing and trace satisfy

$$
\langle F\otimes G,X\otimes Y\rangle
 =\langle F,X\rangle\langle G,Y\rangle,
\qquad u_{a+b}=u_a\otimes u_b.
\tag{172.6}
$$

All clauses include scalar factors and every finite level. This is precisely the structural weak domain of [171.1][S171]. No proper effect interval or normalized probability menu is assumed at this point. The trace representative $I$ need not yet be a positive functional or a primal cone element. No PSD, transpose invariance, operation positivity, event saturation, or external matrix-reference system is supplied.

Call a real-linear $F:W_a\to W_b$ **positive with every original finite spectator** when

$$
(\mathrm{id}_{W_s}\otimes F)C_{s+a}\subseteq C_{s+b}
                       \quad(s\ge0\text{ finite}),
\tag{172.7}
$$

including all transported positions. This definition concerns cone membership, not a trace budget.

**Definition 172.2 (the fixed deformation and the unchanged seed).** In the fixed basis $e_0,\ldots,e_{n-1}$ put $E_{jk}=e_je_k^*$, $P_j=E_{jj}$, and use exactly [170.2][S170], equivalently [171.2][S171]:

$$
\begin{aligned}
K&=\sum_{j=0}^{n-2}(E_{j,j+1}-E_{j+1,j}),
&t&=\frac1{32n},&c&=(1+i)t,\\
H&=cK,&O&=e^H,&W&=e^{\pi i\sqrt2P_0},&M&=WO.
\end{aligned}
\tag{172.8}
$$

Here $W$ is a matrix, whereas $W_N$ is a real carrier. In particular $M$ is invertible. Set

$$
\Omega=\sum_j e_j\otimes e_j,\quad B=\Omega\Omega^*,\quad
\beta(Z)=\operatorname{Tr}(BZ),\quad
D_M=(M\otimes I)B(M^*\otimes I).
\tag{172.9}
$$

The only binary input is

$$
\mathsf R:\qquad D_M\in C_2,\qquad B\in C_2^*.
\tag{172.10}
$$

The first object is supplied natively; its notation as a matrix congruence does not assume that congruence preserves any original cone. The second object is an unnormalized nonnegative functional on the **whole** $C_2$, not initially a proper effect. In particular, $B\in C_2$ is not an input.

The unchanged ternary condition is

$$
\mathsf T:\quad \exists\,0\ne\psi\in(\mathbb C^n)^{\otimes3},\quad
\psi\psi^*\in C_3,\quad
\min_i r_i(\psi)\ge2,\quad\max_i r_i(\psi)=n.
\tag{172.11}
$$

Here $r_i$ is the complex matrix rank of the flattening at leg $i$. These are ordinary vector ranks: every bipartition is nonproduct, and at least one leg has full local support. A usual matrix-rank-one dyad is required; original extremality is not required.

For comparison, name the old binary criterion

$$
\mathsf B:\ B\in C_2\cap C_2^*,\qquad
\mathsf M_2:\ \operatorname{Ad}_{M\otimes I}(C_2)\subseteq C_2,
\qquad \operatorname{Ad}_A(X)=AXA^*.
\tag{172.12}
$$

Neither $\mathsf M_2$ nor its inverse, a full unitary family, or any other preservation premise is included in (172.10).

### 172.2 Raw wiring before any normalization

**Lemma 172.3 (complete-dual slice).** Under Definition 172.1, if $f\in C_a^*$ and $Z\in C_{a+b}$, then

$$
(f\otimes\mathrm{id})Z\in C_b.
\tag{172.13}
$$

The assertion includes arbitrary actual positions, finite sequences of slices, and scalar outputs.

**Proof.** Every $g\in C_b^*$ gives
$g((f\otimes\mathrm{id})Z)=(f\otimes g)(Z)\ge0$ by the maximum bound. Closed-cone bipolarity therefore puts the slice in $C_b$. Bipolarity needs neither pointedness nor generation: separation of a point outside a closed convex cone gives a linear functional nonnegative on that cone and negative on the point. Actual positive permutations give the other positions. Each step leaves an element of the complete remaining cone, so the argument iterates. This is the raw proof of [171.4][S171], also the slicing argument underlying VII102.6. No trace is used. $\square$

**Lemma 172.4 (a native cup transfers its matrix).** Under $\mathsf R$, both $\operatorname{Ad}_M$ and $\operatorname{Ad}_{M^{\mathsf T}}$ are positive with every original finite spectator.

**Proof.** Fix reference–output vectorization

$$
|Q\rangle\!\rangle=\sum_j e_j\otimes Qe_j,
\qquad R_Q=|Q\rangle\!\rangle\langle\!\langle Q|.
\tag{172.14}
$$

Expanding $\Omega$ shows

$$
D_M=R_{M^{\mathsf T}}\in C_2,\qquad
\mathrm{SWAP}(D_M)=R_M\in C_2.
\tag{172.15}
$$

SWAP here is the actual exchange of both tensor factors of a Hermitian operator. It transposes the coefficient matrix of the vectorization; it is not partial transposition of an unknown original state.

Take any finite $s\ge0$, any correlated $Z_{SX}\in C_{s+1}$, and $Q=M$ or $M^{\mathsf T}$. The minimum bound puts

$$
Z_{SX}\otimes R_{Q,X'Y}\in C_{s+3}.
\tag{172.16}
$$

Move $X,X'$ to one actual two-leg block and slice with $\beta\in C_2^*$. Lemma 172.3 for the split $(2,s+1)$ returns an element of $C_{s+1}$. Its exact value is

$$
\operatorname{cap}_{XX'}[Z_{SX}\otimes R_{Q,X'Y}]
       =(\mathrm{id}_{W_s}\otimes\operatorname{Ad}_Q)Z.
\tag{172.17}
$$

Indeed, the complex matrix-unit expressions for the unique complex-linear extension of these real Hermitian maps give

$$
\beta(E_{ab}\otimes E_{ij})=\delta_{ai}\delta_{bj},\qquad
R_Q=\sum_{i,j}E_{ij}\otimes QE_{ij}Q^*.
\tag{172.18}
$$

For $Z=\sum_{a,b}Z_{ab}\otimes E_{ab}$, contraction leaves
$\sum_{a,b}Z_{ab}\otimes QE_{ab}Q^*$, proving (172.17) on the whole real space. There is no residual input transposition. For $s=1$, the actual passage is $C_2\otimes C_2\subset C_4$, followed by a cap back to $C_2$; no shape of $C_4$ has been assumed.

The only inputs were the native resources, the minimum and maximum bounds, complete duality, closedness, and actual permutations. In particular, no primal $B$, positive trace, compact base, proper cap, or already positive $M$ operation has entered. This proves the needed replacement for the start of 171.5; that lemma's unpaid primal-Bell premise has not been borrowed. $\square$

### 172.3 Matrix closure recovers the Bell cup and the old criterion

**Supplier 172.5 (the isolated matrix theorem).** Let $\mathcal P$ be the finite positive words in $M,M^{\mathsf T}$, including the empty word. The purely matrix part of [170.4][S170] states

$$
\overline{\mathcal P}^{\,GL_n(\mathbb C)}
       =\{A\in GL_n(\mathbb C):|\det A|=1\}.
\tag{172.19}
$$

Its exact hypotheses are $n\ge2$ and (172.8). It has no cone or normalization premise. Its proof starts with

$$
MM^{\mathsf T}=W^2=e^{2\pi i\sqrt2P_0},\qquad
M^{-1}=M^{\mathsf T}W^{-2},
\tag{172.20}
$$

obtains the endpoint circle from positive powers, and uses the real Lie algebra of the resulting relative closed matrix group. The similarity logarithm is paid by

$$
\|\operatorname{ad}_{cK}\|\le4\sqrt2t
 =\frac{\sqrt2}{8n}<\frac18<\log2.
\tag{172.21}
$$

The source separates the real and imaginary edge directions using $c^2=2it^2$ and real divisions; it derives $U(n)$ and determinant-one positive diagonals before using SVD. It does not assume $U(n)$, complex-linearity of a Lie algebra, or unitarity of $O$. Hall's relative closed-group, real Lie, and logarithm tools are supplied there with their exact conditions: Definition 2.2, Theorem 3.6, Definition 3.13, Proposition 3.15, and Theorem 3.16 of [Hall]. The specific path-generation computation is the proof in 170.4, not a theorem attributed to Hall.

Only (172.19) and its matrix proof are reused. The cone-dependent conclusion of 170.4, its proper-cap Lemma 170.3, and its old-domain reconstruction theorem are not inputs to the next argument.

**Proposition 172.6 (inverse positivity and the recovered cup).** Under $\mathsf R$, using Supplier 172.5, every invertible local matrix congruence is an order automorphism on every original finite spectator level:

$$
(\mathrm{id}_{W_s}\otimes\operatorname{Ad}_A)C_{s+1}=C_{s+1}
       \quad(A\in GL_n(\mathbb C),\ s\ge0\text{ finite}).
\tag{172.22}
$$

Consequently $B\in C_2$ and $\mathsf M_2$ holds.

**Proof.** Lemma 172.4 makes each positive word's congruence positive on each fixed spectator level. If $Q_k\in\mathcal P$ tends to an invertible $Q$, its image on each fixed $Z\in C_{s+1}$ converges to the congruence image of $Q$. Closedness of that cone proves positivity for $Q$.

For an arbitrary invertible $A$, set $\widehat A=|\det A|^{-1/n}A$. Equation (172.19) applies to $\widehat A$, and

$$
\operatorname{Ad}_A=|\det A|^{2/n}\operatorname{Ad}_{\widehat A}
\tag{172.23}
$$

gives positivity by cone homogeneity. Apply this reasoning separately to $A^{-1}$; the positive inverse gives equality in (172.22). Actual permutations move the operation to any leg. This uses a matrix limit inside each fixed finite closed cone, with no infinite-level cone or exchange of limits.

In particular, the now-derived inverse congruence on the first leg of $C_2$ gives

$$
\operatorname{Ad}_{M^{-1}\otimes I}(D_M)=B\in C_2.
\tag{172.24}
$$

Lemma 172.4 at $s=1$, transported to the first leg, already gives $\mathsf M_2$. The cap membership was supplied. Thus **all** of $\mathsf B\wedge\mathsf M_2$ has now been paid. No inverse-preservation axiom or Bell preparation was used to pay it. $\square$

**Theorem 172.7 (binary equivalence and full finite reconstruction).** On Definition 172.1, with the fixed matrices (172.8), the following are equivalent in paper-supplier form:

$$
\begin{aligned}
&D_M\in C_2\ \text{ and }\ B\in C_2^*;\\
&\mathsf B\wedge\mathsf M_2;\\
&C_2=\operatorname{PSD}_{n^2};\\
&\exists\varepsilon\in\{\pm1\}:\quad
 C_1=\varepsilon\operatorname{PSD}_n,\quad
 C_2=\operatorname{PSD}_{n^2}.
\end{aligned}
\tag{172.25}
$$

The sign is unique. Every finite $C_N$ is pointed and generating, and

$$
0\ne X\in C_N\quad\Longrightarrow\quad
                    \varepsilon^N\operatorname{Tr}X>0.
\tag{172.26}
$$

The full signed-trace-one bases are compact and nonempty. Any nonzero usual PSD element at an odd level selects $\varepsilon=+1$. In particular,

$$
\begin{aligned}
\mathsf R\wedge\mathsf T
&\Longleftrightarrow
 \bigl(C_1=\operatorname{PSD}_n,\ C_2=\operatorname{PSD}_{n^2},\ \mathsf T\bigr)\\
&\Longleftrightarrow
 C_N=\operatorname{PSD}_{n^N}\quad\text{for every finite }N\ge0.
\end{aligned}
\tag{172.27}
$$

**Proof.** Proposition 172.6 proves the first implication to the old binary criterion. Conversely, $\mathsf B\wedge\mathsf M_2$ supplies $D_M$ by applying its stated operation to $B$, and already supplies the cap. This converse needs no closure theorem.

At this point the precise weak-domain antecedents of [171.11(1)][S171] are met: the same all-finite structural domain, complete duals, exact fixed $M$, both Bell memberships, and $\mathsf M_2$. Consume that theorem, specifically its weak double orbit 171.7, sign argument 171.8, finite-frame Theorem 171.9, and selector 171.10. They give all remaining assertions in (172.25)–(172.26). In the other direction, $C_2=\operatorname{PSD}$ has complete PSD trace dual, contains $D_M$ and $B$, and admits every matrix congruence, proving the needed binary converses directly.

The content and boundary of that properness supplier are explicit. From $C_2=\operatorname{PSD}$, the $(1,1)$ minimum bound makes $X\otimes X$ PSD for $X\in C_1$, forcing semidefiniteness. Opposite nonzero signs cannot coexist; the signed trace slice then fills exactly one of $\pm\operatorname{PSD}$. For $\varepsilon^NC_N$, the supplier's one-leg frame consists of the $P_j$ and the projectors onto $(e_j\pm e_k)/\sqrt2$ and $(e_j\pm i e_k)/\sqrt2$. It spans $V$ and sums to $(2n-1)I$. Its $N$-fold products belong to both the signed cone and its complete dual by the repeated min/max bounds, span $W_N$, and sum to $(2n-1)^NI$. Their nonnegative tests force a trace-zero cone element to vanish. This pays strict signed trace, pointedness, generation, and compact bases, without asserting higher-level PSD. These are the already proved 171.8–171.9, not an assumption of high-level properness.

Under $\mathsf T$, the ordinary positive trace of $\psi\psi^*$ at odd level three fixes $\varepsilon=+1$ by 171.10. Only this nonzero PSD membership is needed for orientation. The ranks in $\mathsf T$ have their separate propagation role. Define now, and retain in full,

$$
K_N=\{X\in C_N:u_N(X)=1\},\quad
P_N=\operatorname{ext}K_N,\quad
\mathcal E_N=[0,u_N]_{C_N^*}.
\tag{172.28}
$$

Take every finite unit decomposition $f_\ell\in C_N^*$, $\sum_\ell f_\ell=u_N$. Each member is proper because its complement is the sum of the other positive functionals. No selected state, extreme-point, or effect subfamily is substituted for these complete objects.

The exact handoff to [166.12, condition 1 implies condition 5][S166] is:

| Premise of Definition 166.1 and its seed | Paid object here |
| --- | --- |
| Fixed $n\ge2$; actual complex Hermitian real tensor carriers | (172.1) |
| All finite closed, pointed, generating cones | Definition 172.1 and the earned 171.9 conclusions |
| Strictly positive multiplicative ordinary trace | (172.2), (172.6), (172.26), and the orientation selected by $\mathsf T$ |
| Whole bases, all extreme points, complete duals, whole proper intervals, all finite menus | (172.3), (172.28), and the preceding full-menu convention |
| Every actual finite min/max split, including transported noncontiguous ones | (172.4)–(172.5) and actual permutations |
| Positive permutations and inverses, canonical reassociation, compatible pairing | Definition 172.1 and (172.6) |
| Scalar carrier, cone, and unit | $W_0=\mathbb R$, $C_0=\mathbb R_+$, $u_0=\mathrm{id}$ |
| $C_1=\operatorname{PSD}_n$, $C_2=\operatorname{PSD}_{n^2}$ in those coordinates | (172.25) with $\varepsilon=+1$ |
| Nonzero ternary dyad, all three flattening ranks at least two, one rank $n$ | Exactly (172.11), the seed of Definition 166.2 |

The published propagation theorem therefore gives all finite PSD cones. Its smaller-corner inheritance, strictly decreasing support induction, finite control preparation, and propagation tail are consumed with their original premises and proofs. An arbitrary non-full-leg GME has not replaced the last row.

Conversely, the ordinary PSD hierarchy has the required minimum and maximum inclusions: products of PSD matrices are PSD, and a PSD joint matrix pairs nonnegatively with every PSD product. Actual permutations are unitary congruences with positive inverses; trace, pairing, reassociation, and scalar clauses agree. It contains the two binary resources, and $\sum_j e_j^{\otimes3}$ supplies a ternary dyad with all ranks $n$. This proves (172.27). $\square$

The sign and properness step uses the named §171 supplier at its fixed pin. Theorem 172.7 also retains the published matrix closure and all-finite propagation dependencies. The new native-resource bridge does not assume the result it is used to enter.

### 172.4 The surviving parity obstruction

**Proposition 172.8 (binary resources do not select ordinary trace).** For every $n\ge2$, the hierarchy

$$
C_N^{(-)}=(-1)^N\operatorname{PSD}_{n^N},\qquad N\ge0,
\tag{172.29}
$$

is a full weak-domain model of $\mathsf R$ that fails $\mathsf T$ and ordinary positive trace at odd levels.

**Proof.** This is the model of [171.12][S171]. Its clauses can also be checked directly. Put $s_N=(-1)^N$. The complete trace dual is $s_N\operatorname{PSD}$ by ordinary PSD self-duality. Positive simple tensors have sign $s_as_b=s_{a+b}$, giving every minimum bound. For arbitrary PSD $P,E,F$, pairing $s_{a+b}P$ with $(s_aE)\otimes(s_bF)$ gives $\operatorname{Tr}[(E\otimes F)P]\ge0$, giving every maximum bound. This includes scalar factors. Permutations and inverses preserve signed PSD; actual pairing and reassociation are unchanged. The cones are closed and convex at every finite level. At level two the cone and its complete dual are PSD, so both resources in (172.10) belong. At odd levels each nonzero element has negative ordinary trace, and $C_3^{(-)}$ contains no nonzero usual PSD dyad. $\square$

Thus binary recovery alone gives signed properness, not ordinary orientation or all higher signed PSD equalities. An odd PSD selector fixes the sign, but its membership without the flattening ranks does not pay the propagation seed. No stronger higher-level conclusion without $\mathsf T$ is asserted here.

### 172.5 Proper resources and coefficients after positivity is established

**Proposition 172.9 (native-resource budgets).** Assume $\mathsf R$ and a nonzero usual PSD element at an odd level; in particular assume $\mathsf R\wedge\mathsf T$. Use the earned ordinary bases and intervals (172.28). Then

$$
b=\max_{X\in K_2}\beta(X)=n,\qquad
B/n\in K_2,\qquad \beta/b\in\mathcal E_2.
\tag{172.30}
$$

Set $r=\operatorname{Tr}(M^*M)>0$. With directly normalized native resource $D_M/r$ or its SWAP, one transfer letter has coefficient

$$
\eta=\frac1{br}=\frac1{nr},\qquad
\eta\operatorname{Ad}_{M^{\mathsf T}}
       \ \text{or}\ \eta\operatorname{Ad}_M.
\tag{172.31}
$$

Each is positive and trace-nonincreasing on every entire original finite spectator cone.

**Proof.** Theorem 172.7 and the odd selector have now paid strict ordinary trace at every level and the two-body PSD equality. The matrix $B$ has largest eigenvalue $n$ and attains it on $B/n$, so (172.30) is valid on the **whole** original $K_2$. Also $\operatorname{Tr}D_M=r$, with the same trace after SWAP, giving the normalized resources in $K_2$.

If $f\in\mathcal E_a$ and $Z\in C_{a+b}$, the two product functionals $f\otimes u_b$ and $(u_a-f)\otimes u_b$ give

$$
0\le u_b((f\otimes\mathrm{id})Z)\le u_{a+b}(Z).
\tag{172.32}
$$

The slice is positive by Lemma 172.3. Tensoring an arbitrary input with a trace-one resource preserves its mass by (172.6). Hence the proper slice in (172.17), with resource divided by $r$ and cap divided by $b$, has exactly the coefficient $1/(br)$ and the claimed entire-input budget. The proof does not require the remaining higher cone to be PSD. $\square$

This native convention has no preparatory $M$ event and therefore no preparational factor $\alpha$. After recovery one may separately choose to produce $D_M$ by applying $\alpha\operatorname{Ad}_{M\otimes I}$ to $B/n$, where $\alpha=\min\{1,\|M\|_{\rm op}^{-2}\}$. That distinct supply is $\alpha D_M/n$, of mass $\alpha r/n$, and its transfer coefficient with cap $\beta/b$ is $\alpha/(nb)$. It is the alternative convention of 170.3 and 171.13. It is not a missing factor in (172.31).

For a length-$k$ original positive word $Q$, using directly normalized native resources gives $\eta^k\operatorname{Ad}_Q$, with one resource and one proper cap per letter. It returns after each step to the same spectator-plus-input type. For a nonzero input, invertibility gives a nonzero output and earned strict trace gives positive mass. All finite positive factors remain in unnormalized outputs and probabilities.

The distinction between words and closure is unchanged. There are countably many original two-letter words; (172.19) gives their closure, not exact finite representation of every matrix or projective congruence. Each word is invertible, so it cannot realize a singular target. After low-level recovery, every nonzero matrix $A$ has the resource $R_A\in C_2$, including singular $A$, and direct normalized supply gives

$$
\frac1{n\operatorname{Tr}(A^*A)}\operatorname{Ad}_A.
\tag{172.33}
$$

For $A=0$ use the zero map, with no normalization of a zero resource. The previously proved low-two-level interfaces [163.2][S166] and [167.8][S170], and VII102.6–102.7 as consumed there, now apply with all their premises: $B/n$ is a whole-base state, $\beta/n$ is proper, the original hierarchy is proper, and every original finite split is present. In particular $s_A=\max\{1,\|A\|_{\rm op}\}$ gives the full-spectator TNI map $\operatorname{Ad}_{A/s_A}$. The scalar empty cup is one. For $a$ input legs, the paired normalized identity cups and proper caps give $n^{-2a}\mathrm{id}$; a directly supplied nonzero Choi resource $J(F)/\operatorname{Tr}J(F)$ instead gives $F/[n^a\operatorname{Tr}J(F)]$.

The exact finite-word supplier [167.4–167.5][S170] is available only with its now-earned inputs. Choose $0<\lambda<1$, $S=\operatorname{diag}(\lambda,1,\ldots,1)$. Local unitaries and $S$ are positive by Proposition 172.6. That supplier gives an exact finite word $Q=c_AA$ in the enlarged alphabet $U(n)\cup\{S\}$ for each invertible $A$, with $c_A>0$. If it contains $k$ occurrences of $S$, its proper coefficient is $\alpha_S^kc_A^2$, where

$$
m_S=\max_{X\in K_2}\operatorname{Tr}[(S\otimes I)X(S\otimes I)],
\qquad \alpha_S=\min\{1,m_S^{-1}\}=1.
\tag{172.34}
$$

The equality uses the earned PSD cone and $\|S\|=1$. It does not turn that continuous enlarged alphabet into an exact original two-letter synthesis.

Under $\mathsf T$, retain the complete propagation budget of [166.10–166.12][S166]. At a current local dimension $d$, let each selected, unrestricted seed supply be $h\psi\psi^*/\delta$, $\delta=\|\psi\|^2$, and the real control supply be $t_Q QQ^*/q_Q$, $q_Q=\|Q\|^2$. The common filter $L/s_L$, two seed copies, and three proper $d$-Bell caps give

$$
\kappa\,\xi\xi^*,\qquad
\kappa=\frac{h^2t_Q}{\delta^2q_Qs_L^2d^3},\qquad
\xi=|C\rangle\!\rangle|0\rangle+|D\rangle\!\rangle|1\rangle.
\tag{172.35}
$$

Here $C$ is invertible and $D\notin\mathbb CC$ by that supplier. The final $C^{-1}/s_C$, $s_C=\max\{1,\|C^{-1}\|\}$, gives coefficient $\kappa/s_C^2$ and mass

$$
\frac{h^2t_Q[d+\operatorname{Tr}(\mathsf N^*\mathsf N)]}
 {\delta^2q_Qs_L^2d^3s_C^2}\in(0,1],\qquad \mathsf N=C^{-1}D.
\tag{172.36}
$$

This $\mathsf N$ is unrelated to the fixed deformation matrix $M$. Three normalized Bell resources prepare the control with $t_Q=d^{-3}$; with supply masses $b_1,b_2,b_3>0$, $t_Q=b_1b_2b_3/d^3$. Thus the complete dyad coefficient contains $d^{-6}$. The six control-preparation legs precede the nine-leg core. Restricted copies used to establish a smaller corner and pay its effects are distinct from the two unrestricted bridge seeds, and their masses are not charged again to the control. These are the exact old coefficients, with the full domain and seed correspondence proved in Theorem 172.7. The smaller control dimensions make the recursion finite.

Closed-cone membership of a recovered limit resource supplies a mathematical normalized resource; it supplies neither a limiting physical event nor a uniform production probability along approximating words. A proper scalar filter $aI$, $0<a<1$, repeated $k$ times has mass $a^{2k}$ on trace-one inputs. Thus strictly positive mass for each fixed finite protocol gives no uniform success bound or infinite-protocol assertion. Mathematical branch admissibility and physical event availability remain separate.

### 172.6 Explicit odd-prime phase-point coordinates

**Lemma 172.10 (phase-point basis, with conventions fixed).** Let $p$ be an odd prime, use indices in $\mathbb F_p$, and set $\omega=e^{2\pi i/p}$. Division by two means multiplication by $2^{-1}$ in that field. Define

$$
A_{q,k}=\sum_{x\in\mathbb F_p}
 \omega^{kx}|q+x/2\rangle\langle q-x/2|.
\tag{172.37}
$$

These are Hermitian and satisfy

$$
\begin{gathered}
\operatorname{Tr}A_{q,k}=1,\qquad A_{q,k}^2=I,\qquad
A_{q,k}^{\mathsf T}=A_{q,-k},\\
\operatorname{Tr}(A_{q,k}A_{q',k'})
       =p\,\delta_{q,q'}\delta_{k,k'},\qquad
\sum_{q,k}A_{q,k}=pI.
\end{gathered}
\tag{172.38}
$$

Consequently they are a real orthogonal basis of $\operatorname{Herm}_p(\mathbb C)$, and $A_{0,0}|j\rangle=|-j\rangle$ is parity.

**Proof.** Taking the adjoint and replacing $x$ by $-x$ proves Hermiticity. Taking only the transpose and making the same replacement gives the displayed transpose formula. A diagonal term requires $x=0$, and then has coefficient one, proving the trace formula. Directly,

$$
A_{q,k}|y\rangle=\omega^{2k(q-y)}|2q-y\rangle.
\tag{172.39}
$$

Two applications cancel the phases and return $y$, proving the square and parity assertions. A product $A_{q,k}A_{q',k'}$ sends $|y\rangle$ to a multiple of $|y+2(q-q')\rangle$. Its trace is zero unless $q=q'$. In that case its diagonal phase is $\omega^{2(k'-k)(q-y)}$, whose sum over $y$ is $p$ if $k=k'$ and zero otherwise. This uses the elementary character sum

$$
\sum_{y\in\mathbb F_p}\omega^{ay}=p\,\delta_{a,0},
\tag{172.40}
$$

which is a finite geometric series when $a\ne0$. Finally summing (172.37) first over $k$ kills $x\ne0$ and gives $p\sum_q|q\rangle\langle q|=pI$. There are $p^2$ nonzero mutually orthogonal Hermitian matrices, the real dimension of the space, so they form its full real basis. $\square$

The normalization and convention agree with the original author source [Gross], Definition 5 and equation (15), printed page 5: for $N$ particles,
$W_X(\boldsymbol q,\boldsymbol k)=p^{-N}\operatorname{Tr}(A_{\boldsymbol q,\boldsymbol k}X)$. Our label $(q,k)$ is Gross's momentum–position label $(k,q)$ written in the opposite order. To check the phase rather than infer it from terminology, (172.37) gives

$$
p^{-1}\langle\psi,A_{q,k}\psi\rangle
 =p^{-1}\sum_\xi\omega^{-k\xi}
       \overline{\psi(q-\xi/2)}\psi(q+\xi/2),
\tag{172.41}
$$

after $x=-\xi$. This is his Theorem 6(2) formula. Theorem 6(1), (4), and (5) on page 5 give the trace-orthogonal basis, tensor factorization, and parity facts in that convention. Theorem 7 on pages 5–6 gives Clifford covariance, and Lemma 9 on page 6 gives a stabilizer state's $p^{-N}$ indicator on an affine maximal isotropic set. These explain the standard phase-space setting. We do not use Clifford covariance or the stabilizer characterization to infer the full cone clauses below; those clauses and the two resource expansions are proved directly.

### 172.7 The complete all-finite Wigner simplex hierarchy

**Theorem 172.11 (a full classical cone model on the actual carrier).** At local dimension $n=p$, for every finite $N\ge1$ and label $z=((q_1,k_1),\ldots,(q_N,k_N))$, put

$$
A_z=A_{q_1,k_1}\otimes\cdots\otimes A_{q_N,k_N},\qquad
C_N^{\mathrm W}=\Bigl\{\sum_z\lambda_zA_z:\lambda_z\ge0\Bigr\}.
\tag{172.42}
$$

At $N=0$, use one empty label, $A_\varnothing=1$, and $C_0^{\mathrm W}=\mathbb R_+$. These cones satisfy every clause of Definition 172.1. In fact, every cone is closed, pointed, generating, strictly positive under ordinary trace, and self-dual for the **full** trace dual. For every finite split,

$$
C_a^{\mathrm W}\otimes_{\min}C_b^{\mathrm W}
 =C_{a+b}^{\mathrm W}
 =C_a^{\mathrm W}\otimes_{\max}C_b^{\mathrm W}.
\tag{172.43}
$$

Their entire trace-one bases are simplices with $p^{2N}$ vertices. Their entire proper effect intervals and all finite menus are the classical ones in these coordinates.

**Proof.** Tensoring the basis identities of Lemma 172.10 gives

$$
\operatorname{Tr}A_z=1,\qquad
\operatorname{Tr}(A_zA_w)=p^N\delta_{z,w},\qquad
I_{p^N}=p^{-N}\sum_z A_z.
\tag{172.44}
$$

The $p^{2N}$ products are a basis of the **entire actual** $W_N$. Thus every Hermitian $X$ has the unique real expansion

$$
X=\sum_z\lambda_z(X)A_z,\qquad
\lambda_z(X)=p^{-N}\operatorname{Tr}(A_zX).
\tag{172.45}
$$

This linear coordinate isomorphism takes $C_N^{\mathrm W}$ exactly to the positive orthant. The cone is therefore closed and convex; it is pointed because both $\lambda$ and $-\lambda$ are nonnegative only at zero; it is generating because the basis is contained in it. Also
$\operatorname{Tr}X=\sum_z\lambda_z(X)>0$ on its nonzero elements.

For an arbitrary Hermitian $Y=\sum_z\mu_zA_z$, its pairing with $A_w$ is $p^N\mu_w$. Nonnegativity on the whole cone is therefore equivalent to $\mu_w\ge0$ for every $w$. This proves the exact full-dual identity

$$
(C_N^{\mathrm W})^*=C_N^{\mathrm W},
\tag{172.46}
$$

not merely positivity of a chosen test family. It also shows that

$$
\begin{aligned}
K_N^{\mathrm W}&=\Bigl\{\sum_z\lambda_zA_z:
                   \lambda_z\ge0,\ \sum_z\lambda_z=1\Bigr\},\\
P_N^{\mathrm W}&=\{A_z:z\},\\
\mathcal E_N^{\mathrm W}&=
 \Bigl\{E=p^{-N}\sum_z e(z)A_z:0\le e(z)\le1\Bigr\}.
\end{aligned}
\tag{172.47}
$$

Indeed the vertices of a coordinate simplex are precisely its coordinate unit vectors, and $E,I-E$ are dual-positive precisely for the displayed coordinate bounds. The trace-one simplex is nonempty and compact. Pairing with a state is

$$
\operatorname{Tr}(EX)=\sum_z e(z)\lambda_z.
\tag{172.48}
$$

Consequently the **whole** finite menu set consists exactly of all families $e_\ell(z)\ge0$ with $\sum_\ell e_\ell(z)=1$ for every $z$. Each coordinate is automatically at most one. Conversely each finite dual-positive unit decomposition has exactly this form by uniqueness of the basis expansion. These include all effects and menus of the full dual, with no restriction to a selected stabilizer set.

For a split $a+b$, the full basis is $A_z\otimes A_w$. Every product generator is in the joint cone; every joint basis ray is such a generator. Their finite conic span is already closed. This proves the first equality in (172.43). An arbitrary joint Hermitian matrix has expansion $Z=\sum_{z,w}\nu_{z,w}A_z\otimes A_w$. Testing with the dual elements $A_z,A_w$ gives

$$
\operatorname{Tr}[(A_z\otimes A_w)Z]=p^{a+b}\nu_{z,w}.
\tag{172.49}
$$

Hence the maximum inequalities force every coefficient to be nonnegative. Conversely, for any nonnegative joint coefficients and any complete-dual $F=\sum_z f_zA_z$, $G=\sum_w g_wA_w$, the product pairing is
$p^{a+b}\sum_{z,w}\nu_{z,w}f_zg_w\ge0$. This proves the second equality for arbitrary full-cone tests and arbitrary joint matrices. The actual unit slice is the classical marginal: $\operatorname{Tr}_b Z=\sum_z(\sum_w\nu_{z,w})A_z$, since every $A_w$ has trace one.

Every actual position permutation permutes the product basis labels. It and its inverse are positive, preserve trace, and transport (172.43) to noncontiguous splits. Canonical reassociation changes neither basis product nor coefficient and hence neither cone. The actual trace pairing factors as (172.6), and traces of tensor products multiply. With an empty factor all these computations use $p^0=1$ and the single scalar ray, proving every scalar min/max, pairing, trace, and reassociation clause as well. No finite level or split has been omitted. $\square$

This is a classical probability theory in the coordinates $\lambda_z$, embedded by an invertible real linear map into the given Hermitian carrier. Ordinary matrix positivity is different from positivity of these coordinates. At $p=3$,

$$
A_{0,0}\frac{e_1-e_2}{\sqrt2}
       =-\frac{e_1-e_2}{\sqrt2},
\tag{172.50}
$$

so the original one-body cone contains a non-PSD vertex. More generally $(e_1-e_{-1})/\sqrt2$ is a negative eigenvector at every odd prime. This observation concerns the actual matrices and does not change the classical order in (172.42).

### 172.8 Bell and GHZ in the full classical cones

**Proposition 172.12 (ordinary Bell plus the unchanged ternary seed).** The hierarchy of Theorem 172.11 satisfies $\mathsf B$ and $\mathsf T$. Explicitly,

$$
B=\frac1p\sum_{q,k\in\mathbb F_p}
                  A_{q,k}\otimes A_{q,-k}.
\tag{172.51}
$$

For $g=p^{-1/2}\sum_j|jjj\rangle$,

$$
gg^*=\frac1{p^3}
 \sum_{\substack{q_1=q_2=q_3\\ k_1+k_2+k_3=0}}
 A_{q_1,k_1}\otimes A_{q_2,k_2}\otimes A_{q_3,k_3}.
\tag{172.52}
$$

The Bell expansion has $p^2$ terms; the GHZ expansion has exactly $p^3$ terms, trace one, and all three flattening ranks $p$.

**Proof.** For arbitrary matrices $X,Y$ on one leg,

$$
\operatorname{Tr}[(X\otimes Y)B]
 =\langle\Omega,(X\otimes Y)\Omega\rangle
 =\operatorname{Tr}(X^{\mathsf T}Y).
\tag{172.53}
$$

Apply (172.38) with $X=A_{q,k}$, $Y=A_{q',k'}$. This pairing is $p\delta_{q,q'}\delta_{k',-k}$. Dividing by the squared basis norm $p^2$ gives the unique coefficients (172.51). They are all nonnegative, so $B\in C_2^{\mathrm W}$, and full self-duality gives $B\in(C_2^{\mathrm W})^*$. Its trace is $p^2/p=p$, as required for the unnormalized Bell dyad.

For the ternary formula, (172.39) gives

$$
\begin{aligned}
&\langle g,(A_{q_1,k_1}\otimes A_{q_2,k_2}
                         \otimes A_{q_3,k_3})g\rangle\\
&\quad=\frac1p\sum_{j,\ell}
 \omega^{2\sum_i k_i(q_i-j)}
 \prod_{i=1}^3\delta_{\ell,\,2q_i-j}.
\end{aligned}
\tag{172.54}
$$

Since two is invertible, the product of deltas vanishes unless all $q_i$ coincide. If their common value is $q$, there is exactly one $\ell=2q-j$ per $j$, leaving
$p^{-1}\sum_j\omega^{2(q-j)(k_1+k_2+k_3)}$. By (172.40), it equals one when the sum of the $k_i$ is zero, and otherwise zero. The squared ternary basis norm is $p^3$, so (172.45) proves precisely (172.52).

There are $p$ choices of common $q$ and $p^2$ choices of $k_1,k_2$, with $k_3$ then fixed. Thus there are $p^3$ summands, and their coefficients sum to one. The expansion is in the full primal cone. Finally, across any leg,
$g=p^{-1/2}\sum_j|j\rangle\otimes|jj\rangle$ after a permutation; both displayed families are orthonormal. Each flattening has rank $p$. Hence this **usual matrix-rank-one** dyad satisfies exactly $\mathsf T$. $\square$

**Corollary 172.13 (the complete countermodel target).** Bell primal and dual membership plus $\mathsf T$, on the entire proper all-finite actual domain, do not imply the quantum hierarchy. This holds already at $n=3$ and in fact at every odd prime.

**Proof.** Theorem 172.11 verifies the complete structural domain, full duals, full bases, all extrema, entire proper intervals, and all finite menus. Proposition 172.12 supplies $\mathsf B$ and $\mathsf T$. Equation (172.50), or its odd-prime version, violates $C_1=\operatorname{PSD}_p$. $\square$

The failed implication is exactly $\mathsf B\wedge\mathsf T\Rightarrow$ all-finite PSD, with $\mathsf M_2$ absent.

### 172.9 Why the exact deformation is absent, and what extremality changes

**Proposition 172.14 (the specified deformed cup cannot belong).** For the exact matrix (172.8) at $n=p$, $D_M\notin C_2^{\mathrm W}$.

**Proof.** Suppose the contrary. The cap already belongs to the complete dual by Proposition 172.12. Lemmas 172.3–172.4 and Supplier 172.5, followed by the closure transfer in Proposition 172.6, would give every $\operatorname{Ad}_U$, $U\in U(p)$, as an order automorphism of $C_1^{\mathrm W}$. This consequence uses no unitary-preservation input and no reconstruction theorem from §171.

An invertible cone automorphism permutes extreme rays: a decomposition of an image into positive elements pulls back to a decomposition of its preimage. Here the extreme rays are the finitely many $\mathbb R_+A_{q,k}$. Unitary congruence preserves trace, and each ray has unique trace-one representative $A_{q,k}$, so $UA_{q,k}U^*$ must be one of these finitely many representatives.

The group $U(p)$ is path connected: spectral decomposition writes any unitary as $e^{iH}$ for Hermitian $H$, and $e^{isH}$ joins it to the identity. For fixed $(q,k)$, the continuous map $U\mapsto UA_{q,k}U^*$ into a finite set is constant. Thus every $A_{q,k}$ would commute with every unitary. Commutation with all diagonal phase unitaries kills every off-diagonal entry; commutation with all permutation matrices makes all diagonal entries equal. Hence every phase point would be scalar. But parity $A_{0,0}$ fixes $e_0$ and has the negative eigenvector $(e_1-e_{-1})/\sqrt2$. It is not scalar. This contradiction excludes the exact $D_M$. $\square$

The continuous group was derived from the two resources and the fixed matrix closure. It also follows that the exact old $\mathsf M_2$ fails in this model: if it held, its action on the already primal $B$ would produce the excluded $D_M$.

**Proposition 172.15 (ordinary matrix purity is not original extremality).** The ordinary matrix-rank-one Bell dyad is not an extreme ray of $C_2^{\mathrm W}$. Its minimal original face has exactly $p^2$ basis rays.

**Proof.** In the unique positive-orthant coordinates (172.51), the support consists of the $p^2$ distinct labels $((q,k),(q,-k))$, each with positive coefficient. In a positive orthant, the smallest face containing a vector is the orthant on its nonzero coordinates: the coordinate-zero equations define a face containing it, and its positive coordinate decomposition forces every supported coordinate ray into any face containing it. Transporting this argument by the basis isomorphism proves the claim. In particular,
$B/p=p^{-2}\sum_{q,k}A_{q,k}\otimes A_{q,-k}$ is a nontrivial convex combination of $p^2$ different original vertices. $\square$

The same coordinate argument makes (172.52) a convex combination of $p^3$ original vertices. This does not violate $\mathsf T$: that condition asks for a usual matrix-rank-one dyad with the specified vector flattening ranks, not for an extreme point of the original trace-one simplex.

An additional requirement that the ordinary Bell ray be original-extreme would exclude this particular classical model. Its sufficiency, together with Bell and $\mathsf T$, to force quantum cones on the weak domain is not established here. Nor is it established here that one and the same dyad, supplied as both cup and cap, can replace the two distinct resources in (172.10). These are open variants of the presentation, not premises for Theorem 172.7.

### 172.10 The complete quantum dictionary and its conditional consumers

**Corollary 172.16 (full finite state and process correspondence).** Under $\mathsf R\wedge\mathsf T$, use $d_N=n^N$, $d_0=1$, and the complete objects (172.28). The known dictionary applies in the same actual coordinates:

| Original object | Complete quantum object |
| --- | --- |
| $K_N$, its convex preparations | All density matrices $\rho\succeq0$, $\operatorname{Tr}\rho=1$ |
| $P_N$ and extreme rays | All unit rank-one projectors and their positive multiples; $\mathbb{CP}^{d_N-1}$ |
| Complete trace dual and proper interval | All PSD functionals and every $0\preceq E\preceq I_{d_N}$ |
| All finite unit decompositions and original pairing | All finite POVMs, including PVMs; $p(\ell\mid\rho)=\operatorname{Tr}(E_\ell\rho)$ |
| Hermitian observable and spectral PVM | Expectation $\operatorname{Tr}(A\rho)$ |
| Actual finite tensor carrier and joint cone | The whole density-matrix theory, including entangled states, on $(\mathbb C^n)^{\otimes N}$ |
| Actual permutations and unit slices | Ordinary factor permutations and partial traces of arbitrary correlated inputs |
| Least pure-state confirmation | $T_p(X)=\operatorname{Tr}(pX)$; unit-vector overlap $\lvert v^*w\rvert^2$ |
| All maps positive with every original finite spectator | All rectangular CP maps |
| Whole-input TNI/TP budgets and finite TP-sum families | All CP-TNI branches, channels, and finite mathematical CP instruments |

**Proof by precise supplier substitution.** Theorem 172.7 has established the actual all-finite PSD cones, the ordinary trace, every original tensor split, and the whole bases and menus. These are exactly the target premises of [166.14][S166], [167.8–167.9][S170], and the complete post-reconstruction dictionary [171.14][S171]. Their matrix proofs give the table, including all pure rays and least confirmation, rather than a restricted state or effect list. In particular $T_p$ is the infimum over **all** proper $f$ with $f(p)=1$. Their standard spectral and density-matrix ingredients are Watrous, Chapter 1, §§1.1.2–1.1.3, and Chapter 2, §2.1.2, as consumed in those actual repository suppliers [W1], [W2].

For clarity the full rectangular interface being reused is, for finite $a,b\ge0$ and the unique complex-linear Hermiticity-preserving extension of a real-linear $F:W_a\to W_b$,

$$
\begin{aligned}
J(F)&=\sum_{i,j=0}^{d_a-1}E_{ij}\otimes F(E_{ij}),\\
F\text{ satisfies (172.7)}
&\Longleftrightarrow J(F)\in C_{a+b}
 \Longleftrightarrow J(F)\succeq0\\
&\Longleftrightarrow F(X)=\sum_\gamma K_\gamma XK_\gamma^*,
\quad K_\gamma:\mathbb C^{d_a}\to\mathbb C^{d_b}.
\end{aligned}
\tag{172.55}
$$

The original self-reference theorem VII102.7 has its low-level cups, caps, and full finite structural premises paid in §§172.3–172.5. The rectangular conversion is VII102.13 as consumed in 167.9 and 171.14, and [Watrous, Theorem 2.22][W2]; the actual SWAP converts his output–reference Choi order to (172.55). Nonzero maps admit a Kraus family of size $\operatorname{rank}J(F)\le d_ad_b$; the zero map uses the empty sum. Ordinary CP at arbitrary finite reference dimensions follows from the Kraus form. Such reference dimensions were not additional input systems.

Writing $Q_F=\sum_\gamma K_\gamma^*K_\gamma$, the exact full-input budget statement is

$$
\operatorname{Tr}_{\rm out}J(F)=Q_F^{\mathsf T},\qquad
u_bF\le u_a\Longleftrightarrow Q_F\preceq I_{d_a},\qquad
u_bF=u_a\Longleftrightarrow Q_F=I_{d_a}.
\tag{172.56}
$$

This is the budget theorem of those suppliers and Watrous Theorem 2.26, including all correlated original spectator extensions. A single scalar total trace of $J(F)$ is not the required marginal inequality.

A finite instrument of fixed input and output types is precisely

$$
F_\ell(X)=\sum_\gamma K_{\ell\gamma}XK_{\ell\gamma}^*,\qquad
\sum_{\ell,\gamma}K_{\ell\gamma}^*K_{\ell\gamma}=I_{d_a},\qquad
E_\ell=\sum_\gamma K_{\ell\gamma}^*K_{\ell\gamma}.
\tag{172.57}
$$

The matrix-level instrument proof [161.9, equations (161.27)–(161.30)][S166], consumed also in 171.14, applies with identity coordinate transport. Each branch has a same-output-type complement; for unit output $v$ and input orthonormal basis $(b_j)$ the complement Kraus family is $|v\rangle\langle b_j|\sqrt{I-Q_F}$. Every POVM is the effect family of an instrument, for example $F_\ell(X)=\operatorname{Tr}(E_\ell X)\omega_0$ with a fixed normalized output $\omega_0$.

For any correlated $Z\succeq0$, that same supplier gives

$$
Z_\ell=(\mathrm{id}\otimes F_\ell)Z,\quad
m_\ell=\operatorname{Tr}Z_\ell=\operatorname{Tr}[(I\otimes E_\ell)Z],\quad
\sum_\ell m_\ell=\operatorname{Tr}Z.
\tag{172.58}
$$

For input mass $m>0$ the probability is $m_\ell/m$. Only $m_\ell>0$ allows the conditional state $Z_\ell/m_\ell$. At zero mass the positive unnormalized branch output is zero; zero input gives only zero outputs. Zero-labeled branches may be retained. The supplied spectator formulas are

$$
\begin{aligned}
\operatorname{Tr}_{\rm out}Z_\ell
 &=\operatorname{Tr}_{\rm in}
 [(I\otimes\sqrt{E_\ell})Z(I\otimes\sqrt{E_\ell})],\\
\sum_\ell\operatorname{Tr}_{\rm out}Z_\ell
 &=\operatorname{Tr}_{\rm in}Z.
\end{aligned}
\tag{172.59}
$$

The same matrix proof supplies finite sequential and adaptive composition, addition of unnormalized outputs under coarse-graining, and tensor-product instruments. The standard instrument description is Watrous §2.3.2, equations (2.255)–(2.261), as used by these suppliers.

All scalar cases remain included. For $a=0$, $F(q)=q\sigma$ with $\sigma\succeq0$, and TNI/TP means $\operatorname{Tr}\sigma\le1$ or $=1$. For $b=0$, $F(X)=\operatorname{Tr}(EX)$, and TNI/TP means $0\preceq E\preceq I$ or $E=I$. For $a=b=0$ the multiplier is nonnegative, at most one for TNI and equal to one for TP. The scalar base is $\{1\}$, effect interval $[0,1]$, pure ray space $\mathbb{CP}^0$, and empty reference cup one. These are the exact scalar and zero-map conventions of the named dictionary suppliers. $\square$

**Corollary 172.17 (the retained ideal-update and continuous-action conditions).** Under the preceding quantum target, the existing sharp-neutral and Hamiltonian consumers apply with their additional premises, as follows.

First, let $P=P^*=P^2$ on a finite level and let $L:W_k\to W_k$ be positive real-linear, with

$$
u_kL(X)=\operatorname{Tr}(PX),\qquad
L(p)=p\quad(p\in P_k,\ \operatorname{Tr}(Pp)=1).
\tag{172.60}
$$

Then $L(X)=PXP$. For a finite orthogonal decomposition $\sum_\ell P_\ell=I$, the associated normalized correlated-input formulas are

$$
p_\ell=\operatorname{Tr}[(I\otimes P_\ell)Z],\qquad
Z_{\mid\ell}=\frac{(I\otimes P_\ell)Z(I\otimes P_\ell)}{p_\ell}
  \ (p_\ell>0),\qquad
Z_{\rm ns}=\sum_\ell(I\otimes P_\ell)Z(I\otimes P_\ell).
\tag{172.61}
$$

Second, additionally give a real-linear continuous one-parameter family on a finite level with

$$
A_0=I,\quad A_{\tau+\sigma}=A_\tau A_\sigma,\quad
A_\tau(C_k)=C_k,\quad u_kA_\tau=u_k\quad(\tau\in\mathbb R).
\tag{172.62}
$$

There is a Hermitian $\mathsf H$, unique modulo a real scalar identity, with

$$
A_\tau(X)=e^{-i\tau\mathsf H}Xe^{i\tau\mathsf H},\qquad
\mathcal L(X)=-i[\mathsf H,X].
\tag{172.63}
$$

**Proof by exact consumer reuse.** Corollary 172.16 makes the pure-state quantifier in (172.60) exactly all unit rays in $\operatorname{Ran}P$, and its effect identity exactly $L^\dagger(I)=P$. Thus [161.7.1, the single-matrix application of Atlas Proposition 13.4(1)][S166] has its positive real-linear, sharp-effect, and pointwise-neutrality premises, with transport $\Theta_k=\mathrm{id}$. Consume that existing uniqueness argument, equivalently the specified substitution in [171.15][S171], and its formulas (161.30b–c). No CP premise is added: the resulting compression supplies CP. The cases $P=0$, $P=I$, and scalar level are included. Repeatability alone does not replace pointwise neutrality on all rays of a degenerate yes subspace; the supplier's $VPXPV^*$ with a nontrivial rotation inside that subspace gives the distinction.

Equation (172.62) is, after the all-finite target, precisely a given continuous trace-preserving real order-automorphism group of the full matrix PSD cone. Consume the matrix-level part of [161.10][S166], starting at its transported group $B_t$, as specified in [171.16][S171]. Its equal-size rank-one-preserver classification, connectedness exclusion of the transpose component, and local unitary lift yield (172.63). No implementing unitary group or differentiability is assumed. Size two is included; at size one the action is the identity and the generator is any real scalar. The earlier geometric reconstruction hypotheses of 161.5 are not invoked by this post-target application. $\square$

These are additional choices of update and action. A static effect fixes probabilities and conditional spectator marginals, not a unique output branch. Mathematical availability of all CP-TNI maps and finite instruments as physical events still needs the event-saturation choice VII102.14, as distinguished in 167.9 and 171.14. A physical clock, energy calibration, and positive action scale $\hbar$ also remain extra data. Only after those choices can $H_{\rm phys}=\hbar\mathsf H$ express the usual physical Schrödinger and von Neumann equations. The fixed dimensionless $t=1/(32n)$ is not physical time. The static resource relations select neither a Hamiltonian nor an ideal measuring device.

### 172.11 Exact simplification, source scope, and open boundaries

**Proposition 172.18 (the relational claim and its scope).** On the fixed weak actual all-finite domain, (172.25) is an equivalent relational presentation of the old binary criterion: the native membership of $D_M$ and complete-dual membership of $B$ replace primal Bell membership together with the supplied preservation premise $\mathsf M_2$. Primal Bell membership, both transfer letters, all inverse local congruences, signed properness, and, with $\mathsf T$, ordinary properness and all finite quantum cones are earned in the stated order.

**Proof and source accounting.** Lemmas 172.3–172.4 prove raw slicing and transfer from the two memberships. Supplier 172.5 and closedness prove inverse positivity; (172.24) recovers the missing Bell cup. Only then does the weak-domain §171 theorem apply. Its orientation and frame results precede all budgets, and the complete 166.12 handoff precedes propagation and the quantum dictionary. The converse native memberships follow directly from the old binary criterion. This is exactly the claimed equivalence.

The classical model proves a different, complementary statement: with the same actual carrier rules and even full ordinary properness, $\mathsf B+\mathsf T$ without $\mathsf M_2$ need not be quantum. It verifies the whole cone and menu contracts, rather than selected stabilizer operations. Its exclusion of this exact $D_M$ uses the raw bridge and the matrix closure, without using the §171 reconstruction or a unitary-preservation input. The model is a counterexample at every odd prime, not a counterexample at every integer dimension.

The source ledger is:

| Immutable or original source | Exact mathematical use |
| --- | --- |
| [S170], XVI at `4a2c3cc8bb4620516476cd923a7334f4df59e1a9` | Exact 170.2 matrices; only the matrix closure and matrix proof of 170.4 before recovery; after properness, 167.4–167.5 finite-word budgets and 167.8–167.9 Choi/dictionary consumers |
| [S171], XVI at `391dab57b5977a43d6feb08d8229cb57f0e02a8e` | Complete §171; 171.7–171.11 are consumed only after $\mathsf B+\mathsf M_2$ is paid; 171.12 parity; 171.13–171.16 identify the retained budget and dictionary interfaces |
| [S166], XIII at `00427ae2ba9c9e3f6c37f2e5496b9127b6fbc6c0` | Definitions 166.1–166.2 and 166.12(1)$\Rightarrow$(5); 166.10–166.11 coefficients; 166.14 dictionary; 163.2 low-level operations; the post-target matrix parts of 161.9, 161.7.1, and 161.10 |
| [Gross], `quant-ph/0602001v3`, printed pp. 5–6 | Definition 5, equation (15), Theorem 6(1,2,4,5), Theorem 7, and Lemma 9; phase-point conventions and mature Wigner/stabilizer facts, not this whole hierarchy reconstruction |
| [Hall], `math-ph/0005032v1` | Only the general closed matrix group, real Lie algebra, and norm-controlled logarithm tools actually used by the 170.4 supplier |
| [W1], [W2], through the named repository suppliers | Finite spectral/SVD and pure-state geometry; rectangular Choi/Kraus Theorem 2.22, TP marginal Theorem 2.26, POVM and instrument facts with the explicitly stated order conversion |

The positive-orthant hierarchy, full-dual/full-menu checks, GHZ coefficient and term count, and exact-deformation exclusion have their proofs in §§172.6–172.9. They are not attributed to Gross's Hudson theorem or to an associated citation alone. The new synthesis is the native-resource replacement and its precise relation to that complete countermodel. General Lie theory, Wigner phase points, SVD, Choi/Kraus, and the previously proved propagation and dictionary remain their named sources' contributions.

The fixed §171 source supplies sign and properness only after its antecedents are established. Its named dependency chains, the matrix-closure theorem and the all-finite propagation theorem remain explicit premises of this source-based derivation; the stronger old positive-trace domain is not an input to the new resource bridge.

The simplification concerns the **form of supplied relations and operations** on this fixed domain. The exact matrix $M$, complex scalars, actual Hermitian carriers, fixed local dimension, all finite compositions and complete duals remain substantive assumptions. No global description-length saving, minimum independent axiom count, or reconstruction of complex carriers from nothing is claimed.

The single identical cup/cap variant and sufficiency of Bell original extremality remain open here. Binary relations without $\mathsf T$ do not here settle all higher signed cones. A seed with every leg rank below $n$ does not meet 166.12; general GME without a full leg remains outside this conclusion. Deleting closedness, complete duals, positive permutations, or any needed finite min/max split removes a used premise; no independence result for each such deletion is claimed. Infinite-dimensional reconstruction, physical event menus, clocks, energy scales, spacetime, and the value of $\hbar$ are not conclusions. $\square$

### 172.12 中文白话与几何图景

这里从一开始就保留复 Hermitian 矩阵、固定局部维数和任意有限个系统的真实张量空间。锥起初只要求闭、凸，不要求尖、不要求张满，也不要求普通迹非负。因此最初只能谈“仍在原锥里”，还不能把迹当总概率，不能先叫某个对象归一态，也不能把贝尔测试先当成概率不超过一的合法效果。

新的入口给两件不同的东西：一个已经变形的二体杯 $D_M$，以及原来的贝尔帽 $B$。杯是原锥里的对象，帽是对整个原锥非负的线性测试。我们不先给“矩阵 $M$ 可以作用在任意原态上”的操作公理。把任意输入和杯并排放好，再用帽接掉输入腿和杯的一条腿，矩阵单位计算直接留下 $MXM^*$ 或 $M^{\mathsf T}X\overline M$。后一个仍是通常的合同；转置在局部矩阵的系数上，不是对未知态作转置。最小分块保证并排的对象在原联合锥里，最大分块和完整对偶保证切掉两腿后仍在整个剩余锥里，所以任意相关旁观者也保留下来。

两个方向的正向字再接入170.4已经证明的矩阵闭包。一个端点的无理相位与固定复混合沿路径产生全部需要的转向和相对伸缩；每个有限层的锥闭，矩阵极限也保持该层。这样逆矩阵的正性才成为结论。现在才能把 $M^{-1}$ 作用到原生变形杯上，恢复原来的贝尔杯。也就是说，普通杯不是偷偷预付的；它是先接线、再用闭包、最后倒回来的成果。

到这一步，171真正要求的贝尔杯、贝尔帽和唯一操作正性已经全部齐备，才能消费它的弱域定理。二体的准备轨道填入所有 PSD 方向，测试轨道排除非 PSD 方向，二体锥由两边夹住。一体仍有共同朝上或朝下的符号；奇数层全部翻面而偶数层不动，所有分块关系都能保留，所以二体资源本身不能选择普通正迹。有限投影框架才把每一层的尖性、张满性和严格带符号迹一起推出。三体种子的非零普通 PSD 性负责选择朝上的方向，它的展平秩则另外负责接入166.12的满腿传播。这两项职责不能混成一句“有纠缠就够了”。

归一放在这些数学正性之后。变形杯直接除以 $r=\operatorname{Tr}(M^*M)$，贝尔帽除以 $n$，每接一次就明确留下 $1/(nr)$。因为杯是原生供应，这里没有一份尚未发生的 $M$ 制备事件需要再乘成功系数。若另选“先制备普通杯，再作一次缩放的 $M$ 分支”的供应方式，那才有另一套质量和系数。有限字、闭包中恢复的资源、奇异目标、控制准备、三只帽及最后逆滤波都保留各自账目；每个固定有限协议质量为正，不表示无限长的序列有统一成功率，也不表示数学极限已经是一台物理装置。

经典反模型说明变形资源确实承担了工作。奇素数维里，可以把每张 Hermitian 矩阵唯一写成有限个相位点矩阵的实系数。规定系数全非负，就得到一个完整的经典概率锥；迹一截面是概率单纯形，整个对偶、整个效果区间和全部有限菜单也都能逐坐标写清。任意有限张量积仍是同一类非负坐标锥，最小与最大锥完全重合，真实交换及其逆只是重排坐标。这不是只检查稳定子态的一小部分测试，而是完整原空间上的所有状态、所有对偶测试和所有菜单。

这些相位点矩阵自身不一定是通常 PSD。三维的原点相位点就是宇称，它在 $(e_1-e_2)/\sqrt2$ 上有负特征值。但普通贝尔 dyad 是 $p^2$ 个正坐标项之和；归一 GHZ dyad 是 $p^3$ 个正坐标项之和，而且三条展平秩都等于 $p$。所以普通杯、普通帽和完整三体种子都在，整个层级却仍然是经典的。这里没有额外保留全部酉操作公理。若精确的变形杯也在，原始接线与矩阵闭包反而会强迫所有酉合同保持这一体经典锥。连续酉群只能固定有限条极端射线，迹一又固定比例，最终会逼每个相位点都成为标量，这与宇称的正负特征值矛盾。故这个精确变形杯确实不在反模型中。

普通矩阵秩一与原理论极端性也不同。贝尔矩阵在通常量子意义下是纯 dyad，但在这个经典锥里落在含 $p^2$ 条基射线的面内；GHZ 也落在含多个经典顶点的面内。这没有违反三体条件，因为三体条件从未要求它是原菜单里的极端准备。若再要求贝尔本身原极端，会排除这个反例，但是否足够完成重建，本章没有解决；用同一个对象同时充当杯与帽是否能更简洁，也保留为开放问题。

全有限 PSD 确定以后，旧字典才完整读出密度矩阵、复射影纯态、全部 POVM 和 Born 概率、纠缠张量积、偏迹、矩形 CP 映射、TNI/TP 和有限数学仪器。零质量只给零输出，不能除以零。Lüders 更新还需给定每条确定为 yes 的射线逐点不受扰动；Hamiltonian 还需给定一个连续可逆保迹实序作用。装置事件是否可用、物理时钟与能量单位、$\hbar$ 标定也仍须另给。本章准确减少的是需要外供的操作保持条件，并将普通杯改为可推导资源；它没有声称把所有量子理论的描述长度或独立公理数降到全局最小。

[S170]: https://github.com/the-omega-institute/trureturing/blob/4a2c3cc8bb4620516476cd923a7334f4df59e1a9/docs/develop/theory/QUANTUM_ORIGIN_BINARY_BELL_ORBITS_AND_SINGLE_ATTENUATOR_XVI.md
[S171]: https://github.com/the-omega-institute/trureturing/blob/391dab57b5977a43d6feb08d8229cb57f0e02a8e/docs/develop/theory/QUANTUM_ORIGIN_BINARY_BELL_ORBITS_AND_SINGLE_ATTENUATOR_XVI.md
[S166]: https://github.com/the-omega-institute/trureturing/blob/00427ae2ba9c9e3f6c37f2e5496b9127b6fbc6c0/docs/develop/theory/QUANTUM_ORIGIN_BINARY_TANGENT_CLOSURE_AND_GLOBAL_NONCOLLAPSE_XIII.md
[Gross]: https://arxiv.org/pdf/quant-ph/0602001v3
[Hall]: https://arxiv.org/pdf/math-ph/0005032v1
[W1]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
[W2]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf

## 追加锚（本行以下为增补区）

## 173. Bell reciprocity and signed rank-one resolution

### 173.1 The weak domain and an operation-free binary candidate

**Definition 173.1 (the retained domain).** Retain exactly Definition 172.1: a fixed integer $n\ge2$, the actual real carriers

$$
W_N=\operatorname{Herm}_{n^N}(\mathbb C),\qquad W_0=\mathbb R,
\tag{173.1}
$$

closed convex cones $C_N$, $C_0=\mathbb R_+$, their complete trace duals, every finite minimum/maximum tensor inclusion, actual positive permutations with positive inverses, and canonical reassociation. The ordinary trace is initially only the multiplicative algebraic functional. In particular no pointedness, generation, positive trace, PSD containment, transpose preservation, or positive matrix operation is assumed. Put

$$
\Omega=\sum_{j=0}^{n-1}e_j\otimes e_j,\qquad B=\Omega\Omega^*.
\tag{173.2}
$$

**Definition 173.2 (signed native rank-one resolution).** For a cone $K\subset\operatorname{Herm}_d(\mathbb C)$, write $\mathsf{SR}(K)$ when every $X\in K$ admits a finite expression

$$
X=\sum_{j=1}^{m}\sigma_jv_jv_j^*,\qquad
0\ne v_j\in\mathbb C^d,\quad \sigma_j\in\{+1,-1\},\quad
\sigma_jv_jv_j^*\in K.
\tag{173.3}
$$

The empty sum represents zero. Positive scalar coefficients can be absorbed into the vectors. Each term must belong to the same original cone; an arbitrary spectral decomposition whose terms leave $K$ does not satisfy this definition. This is ordinary Hermitian matrix rank one. It is not tensor rank one or Schmidt rank one: an entangled vector supplies an allowed rank-one dyad. No sign is specified in advance, and an original extreme ray has not been identified with a matrix-rank-one ray.

The binary candidate is the pair of structural relations

$$
\mathsf Q_{\mathrm{bin}}:\qquad
B\in C_2\cap C_2^*,\qquad \mathsf{SR}(C_2).
\tag{173.4}
$$

There is no specified deformation matrix or operation-preservation premise. Retain the same separate ternary condition

$$
\mathsf T:\quad
\exists\,0\ne\psi\in(\mathbb C^n)^{\otimes3},\quad
\psi\psi^*\in C_3,\quad
\min_i r_i(\psi)\ge2,\quad \max_i r_i(\psi)=n.
\tag{173.5}
$$

The three $r_i$ are the actual complex flattening ranks. Neither $B$ nor $\psi\psi^*$ is assumed original-extreme. The candidate concerns the entire two-system cone and its complete test relation, rather than only a chosen set of preparations or effects.

### 173.2 Bell relations determine the complete transpose dual

**Lemma 173.3 (reciprocity at every original finite block).** On Definition 173.1, the first relation of (173.4) alone implies

$$
C_k^*=\{X^{\mathsf T}:X\in C_k\}
\qquad(k\ge0\text{ finite}).
\tag{173.6}
$$

This is equality with the transpose image, not an assertion that transpose preserves $C_k$ or that $C_k$ is self-dual for the usual positive-definite trace inner product.

**Proof.** The scalar case is immediate. Fix $k\ge1$, put $d=n^k$, and regard the same actual $2k$ legs as two $k$-leg blocks. Tensor $k$ copies of the primal Bell resource and permute their positions. The minimum inclusions and positive permutations put the resulting matrix

$$
\mathcal B_k=\Omega_k\Omega_k^*,\qquad
\Omega_k=\sum_{\alpha\in\{0,\ldots,n-1\}^k}
e_\alpha\otimes e_\alpha
\tag{173.7}
$$

in $C_{2k}$. The product of the $k$ dual Bell functionals is nonnegative on all of $C_{2k}$ by successive maximum inclusions. Transporting this functional by the inverse of the same actual permutation proves $\mathcal B_k\in C_{2k}^*$. These constructions use the complete original cones, with no normalized state or proper cap.

For arbitrary Hermitian $X,Y$ on the $k$-leg block, the matrix-unit identity is

$$
\operatorname{Tr}[\mathcal B_k(X\otimes Y)]
=\operatorname{Tr}(X^{\mathsf T}Y).
\tag{173.8}
$$

For $X,Y\in C_k$, the minimum bound and the dual membership of $\mathcal B_k$ make this quantity nonnegative. Consequently $C_k^{\mathsf T}\subseteq C_k^*$. For $F,G\in C_k^*$, the primal membership of $\mathcal B_k$ and the maximum bound instead give $\operatorname{Tr}(F^{\mathsf T}G)\ge0$. The complete bipolar identity for a closed convex cone gives

$$
(C_k^*)^{\mathsf T}\subseteq C_k^{**}=C_k.
\tag{173.9}
$$

Transposing (173.9) gives the other containment in (173.6). Neither containment used pointedness, generation, or trace positivity. $\square$

### 173.3 The signed support obstruction, including lineality

**Theorem 173.4 (signed rank-one resolution under transpose reciprocity).** Let $d\ge1$. If a closed convex cone $K\subset\operatorname{Herm}_d(\mathbb C)$ satisfies

$$
K^*=K^{\mathsf T},\qquad \mathsf{SR}(K),
\tag{173.10}
$$

then $K=\operatorname{PSD}_d$ or $K=-\operatorname{PSD}_d$. In particular pointedness, full span, and one common sign are consequences, including when none was supplied.

**Proof.** Define complex support spaces using all native signed rank-one elements:

$$
\begin{aligned}
U&=\operatorname{span}_{\mathbb C}\{v:vv^*\in K\},\\
V&=\operatorname{span}_{\mathbb C}\{w:-ww^*\in K\},\\
p&=\dim_{\mathbb C}U,\quad q=\dim_{\mathbb C}V,
\quad r=\dim_{\mathbb C}(U\cap V).
\end{aligned}
\tag{173.11}
$$

For each displayed pair of generators, $(vv^*)^{\mathsf T}\in K^*$, hence

$$
0\le\operatorname{Tr}[(vv^*)^{\mathsf T}(-ww^*)]
=-|v^{\mathsf T}w|^2.
\tag{173.12}
$$

Thus $U$ and $V$ annihilate each other for the nondegenerate complex bilinear form $(v,w)\mapsto v^{\mathsf T}w$, and

$$
p+q\le d.
\tag{173.13}
$$

This is bilinear orthogonality, not Hermitian orthogonality; $U\cap V$ may be nonzero. The proof must retain that intersection and the possible lineality of $K$.

For a complex subspace $E$, let $\operatorname{Herm}(E)$ denote the real space of Hermitian matrices whose ranges lie in $E$, embedded by zero on $E^\perp$. Its real dimension is $(\dim_{\mathbb C}E)^2$, and
$\operatorname{Herm}(U)\cap\operatorname{Herm}(V)=\operatorname{Herm}(U\cap V)$. Signed resolution gives

$$
S:=\operatorname{span}_{\mathbb R}K
\subseteq\operatorname{Herm}(U)+\operatorname{Herm}(V),
\qquad \dim_{\mathbb R}S\le p^2+q^2-r^2.
\tag{173.14}
$$

Next let $L=K\cap(-K)$, its real lineality space. For $X\in L$, resolve $X$ and $-X$ separately and group terms by matrix sign:

$$
X=P_1-Q_1=-(P_2-Q_2),\qquad
Z:=P_1+P_2=Q_1+Q_2\succeq0.
\tag{173.15}
$$

Each $P_i$ is PSD supported on $U$ and each $Q_i$ is PSD supported on $V$. Therefore $Z$ is supported on $U\cap V$. The inequalities $0\preceq P_i,Q_i\preceq Z$ imply that all four matrices are supported on that intersection: if $z\in\ker Z$, positivity gives $P_i z=Q_i z=0$. It follows that

$$
L\subseteq\operatorname{Herm}(U\cap V),\qquad
\dim_{\mathbb R}L\le r^2.
\tag{173.16}
$$

Complete duality gives $\operatorname{lin}(K^*)=S^\perp$, where the perpendicular is for the real trace inner product. Equation (173.10) also gives $\operatorname{lin}(K^*)=L^{\mathsf T}$. Transpose is a real linear isomorphism, so

$$
d^2=\dim_{\mathbb R}S+\dim_{\mathbb R}L
\le p^2+q^2\le(p+q)^2\le d^2.
\tag{173.17}
$$

All inequalities are equalities. In particular $pq=0$ and $p+q=d$. Thus all native rank-one terms have one common matrix sign, and signed resolution puts $K$ inside $\operatorname{PSD}_d$ or $-\operatorname{PSD}_d$. Both of these usual cones are trace self-dual and transpose invariant. If, for example, $K\subseteq\operatorname{PSD}_d$, then

$$
\operatorname{PSD}_d\subseteq K^*=K^{\mathsf T}
\subseteq\operatorname{PSD}_d.
\tag{173.18}
$$

Therefore $K^{\mathsf T}=K=\operatorname{PSD}_d$. The negative case has the identical dual-containment argument with $-\operatorname{PSD}_d$. This also excludes zero and proper subspace cones without a separate nondegeneracy assumption. $\square$

### 173.4 A complete replacement of the binary criterion

**Theorem 173.5 (binary resolution and all-finite reconstruction).** On the same weak actual domain, the following binary statements are equivalent:

$$
\begin{aligned}
&\mathsf Q_{\mathrm{bin}};\\
&C_2=\operatorname{PSD}_{n^2};\\
&\exists\varepsilon\in\{+1,-1\},\quad
C_1=\varepsilon\operatorname{PSD}_n,\quad
C_2=\operatorname{PSD}_{n^2}.
\end{aligned}
\tag{173.19}
$$

The sign is unique. Every $\varepsilon^N C_N$ is closed, pointed and generating, its signed trace is strictly positive away from zero, and its signed trace-one base is compact. Moreover

$$
\mathsf Q_{\mathrm{bin}}\wedge\mathsf T
\quad\Longleftrightarrow\quad
C_N=\operatorname{PSD}_{n^N}\quad
\text{for every finite }N\ge0.
\tag{173.20}
$$

Bell original extremality and the positivity of all local matrix congruences are conclusions of this criterion, rather than extra binary inputs.

**Proof.** Lemma 173.3 at $k=2$ and Theorem 173.4 with $d=n^2$ give $C_2=\pm\operatorname{PSD}_{n^2}$. The nonzero positive matrix $B\in C_2$ excludes the negative choice. This proves the first implication in (173.19) without any deformation or preservation axiom.

The remainder of the binary statement is precisely [171.11(1)][Q173XVI], in its already proved direction from $C_2=\operatorname{PSD}_{n^2}$. The fixed matrix in that older equivalent formulation requires no new premise: once $C_2$ is PSD, its congruence preserves $C_2$. The older result uses 171.8 for the common one-body sign and 171.9 for the finite-frame pointedness, generation, strict signed trace and compactness. This direction uses no matrix-generation supplier. These implications are reused, not assumptions that the weak domain has silently inherited. Conversely the usual PSD cone contains $B$, is its complete trace dual, and its ordinary spectral decomposition supplies (173.3) with only positive signs. This completes (173.19).

Under $\mathsf T$, the nonzero ordinary positive dyad at the odd level three fixes $\varepsilon=+1$ by 171.10. The rank conditions in (173.5) are not needed for that sign selection; their separate purpose is the full-support propagation premise. Now use the entire sets

$$
\begin{aligned}
K_N&=\{X\in C_N:\operatorname{Tr}X=1\},\qquad P_N=\operatorname{ext}K_N,\\
\mathcal E_N&=\{F\in C_N^*:I_{n^N}-F\in C_N^*\},\\
\mathcal M_N&=\{(F_1,\ldots,F_m):m\ge1,\ F_j\in C_N^*,\ \sum_jF_j=I_{n^N}\}.
\end{aligned}
\tag{173.20a}
$$

These are mathematical full-menu objects, with no physical availability claim. At this point every supplier premise of [166.12, condition 1 implies condition 5][Q173XIII] is paid, with the same correspondence as 171.11:

| Supplier requirement | Its actual source here |
| --- | --- |
| Fixed complex Hermitian carriers, all finite tensor levels, scalar object | Definition 173.1 |
| Closed, pointed, generating cones and strictly positive multiplicative ordinary trace | (173.19), 171.9, and the positive sign selected by (173.5) |
| Entire bases, all extreme points, complete duals, full proper intervals and finite unit decompositions | Take those full sets after signed properness and sign selection; the duals were complete from the beginning |
| Every finite min/max partition, positive actual permutations with positive inverses, canonical reassociation | Definition 173.1, including noncontiguous transported partitions |
| Actual one- and two-body PSD equalities | (173.19) with $\varepsilon=+1$ |
| A ternary dyad, nonproduct at every cut, with at least one full leg | Exactly (173.5) |

The supplier therefore gives all finite PSD cones. Its smaller-corner induction, two-copy Gram bridge, three Bell contractions and exact finite propagation remain the previously proved construction; no arbitrary GME state lacking a full leg replaces its seed. Conversely the full PSD hierarchy satisfies the weak domain and (173.4), and $\sum_j e_j\otimes e_j\otimes e_j$ supplies (173.5).

Finally every ordinary rank-one positive ray is extreme in a PSD cone, so the recovered Bell ray is original-extreme. Every local matrix congruence, including singular ones, preserves every PSD level, proving its positivity with all original finite spectators. $\square$

### 173.5 Geometric meaning and the exact quantum dictionary

**Corollary 173.6 (the candidate's finite quantum geometry and consumers).** Under (173.20), write $d_N=n^N$. The whole original state and process theory has the following correspondence, with no selected state or effect subfamily substituted:

| Original definition | Resulting finite quantum structure |
| --- | --- |
| $K_N=\{X\in C_N:\operatorname{Tr}X=1\}$ | All density matrices on the actual $\mathbb C^{d_N}$ |
| All extreme points of $K_N$ | Unit rank-one projections; $\mathbb{CP}^{d_N-1}$ |
| Complete dual and proper interval | All PSD functionals and all $0\preceq E\preceq I$ |
| All finite dual-positive unit decompositions | Every finite POVM, with $p(a\mid\rho)=\operatorname{Tr}(E_a\rho)$ |
| Actual tensor products, permutations and unit slices | Entangled joint states, ordinary permutations and partial traces |
| All real-linear maps positive with every original finite spectator | All rectangular complex CP maps, through their Hermiticity-preserving extensions |
| Whole-input TNI/TP order budgets | CP branches and channels; all finite TP-sum mathematical instruments |

The whole normalized minimal face containing any two distinct pure states is a three-dimensional real ball. Its pure boundary is $\mathbb{CP}^{1}\cong S^2$, not a filled projective line. This geometric three-dimensional face is distinct from the three-system tensor seed in (173.5).

**Proof and parameter correspondence.** Theorem 173.5 gives exactly the original all-finite PSD domain required by [166.14][Q173XIII] and the full rectangular dictionary 172.16. Apply those results with the unchanged $W_N$, $C_N$, trace, complete duals, all original spectators and every finite unit decomposition. Their spectral and Choi ingredients are the standard results in [Watrous, Chapters 1–2][Q173W1][Q173W2]. In particular

$$
\begin{aligned}
J(F)&=\sum_{i,j=0}^{d_a-1}E_{ij}\otimes F(E_{ij}),\\
F\text{ is positive with all original spectators}
&\Longleftrightarrow J(F)\succeq0
\Longleftrightarrow F(X)=\sum_\gamma K_\gamma XK_\gamma^*,\\
u_bF\le u_a&\Longleftrightarrow\sum_\gamma K_\gamma^*K_\gamma\preceq I_{d_a},\\
u_bF=u_a&\Longleftrightarrow\sum_\gamma K_\gamma^*K_\gamma=I_{d_a}.
\end{aligned}
\tag{173.21}
$$

These are the actual rectangular interfaces, with $K_\gamma:\mathbb C^{d_a}\to\mathbb C^{d_b}$, not just square maps or a scalar Choi trace budget. The zero map uses an empty Kraus family. The original pairing, complete effect interval and all finite unit decompositions give the displayed Born probabilities; pure-state least confirmation gives $|v^*w|^2$ as in 172.16. Neither rule is supplied again as an independent probability axiom after the cones have been identified.

For the geometric statement let $p=vv^*$ and $q=ww^*$ be distinct normalized pure states. Their complex span $E=\operatorname{span}_{\mathbb C}\{v,w\}$ has dimension two. The PSD matrices supported on $E$ form an exposed face, and $p+q$ is positive definite on $E$, so this is the full minimal cone face containing both. In an orthonormal basis of $E$ its trace-one section is

$$
\rho(x,y,z)=\frac12
\begin{pmatrix}1+z&x-iy\\x+iy&1-z\end{pmatrix},
\qquad x^2+y^2+z^2\le1.
\tag{173.22}
$$

The eigenvalues are $(1\pm\sqrt{x^2+y^2+z^2})/2$. Rank one is exactly the sphere. This standard two-dimensional Hermitian face calculation identifies the geometry forced by the new binary criterion, including nonorthogonal pairs; it is not an extra reconstruction premise. $\square$

### 173.6 Counterfactuals and the precise simplification

**Proposition 173.7 (the missing relation in the Wigner model).** At every odd prime local dimension, the complete Wigner simplex hierarchy of 172.11–172.13 satisfies the Bell primal/dual relation and the unchanged $\mathsf T$, but fails $\mathsf{SR}(C_2)$. Thus ordinary matrix-rank-one Bell and GHZ resources alone do not supply the decomposition relation used here.

**Proof.** That hierarchy has every finite weak-domain structure, complete duals and full menus, the two Bell memberships, and the required three flattening ranks. Its two-body cone is the finite positive-orthant cone on the product phase-point basis, so is simplicial. It cannot equal $\operatorname{PSD}_{p^2}$: the former has finitely many extreme rays, the latter has a distinct extreme ray for every point of $\mathbb{CP}^{p^2-1}$. If signed native rank-one resolution held, Lemma 173.3 and Theorem 173.4 would instead make that cone PSD; the positive Bell member would select its positive sign. This contradiction proves the exact failed condition without restricting the model's dual tests. $\square$

**Proposition 173.8 (the binary orientation obstruction survives).** Binary candidate (173.4) alone does not fix ordinary positive trace on odd levels. The all-finite hierarchy

$$
C_N=(-1)^N\operatorname{PSD}_{n^N}
\tag{173.23}
$$

satisfies that candidate and the complete weak domain, but fails (173.5) and the positive all-finite conclusion.

**Proof.** This is exactly the complete countermodel 171.12, including its duals and every finite partition. At level two its cone and complete dual are PSD, so both Bell memberships and native rank-one resolution hold. Every odd-level nonzero matrix has negative ordinary trace, and $C_3$ contains no nonzero ordinary positive dyad. This proves the asserted failure. The sign part of the ternary condition therefore has a concrete job even after the deformation has been deleted. $\square$

**Proposition 173.9 (what is and is not compressed).** On Definition 173.1, (173.4) and the old binary criterion $\mathsf B\wedge\mathsf M_2$ are equivalent. The new presentation supplies ordinary Bell primal membership and a cone-wide finite resolution relation, and no longer supplies the exact deformation $M$ or any operation-preservation relation. It does not establish that Bell original extremality alone suffices, or that fewer independent assumptions or smaller total description length have been attained.

**Proof.** Each binary criterion is equivalent to $C_2=\operatorname{PSD}_{n^2}$ by (173.19) and 171.11(1). Their forward mechanisms differ: 172 recovers the Bell cup from a deformed cup and cap through a matrix closure argument; (173.4) supplies the Bell cup and uses signed support resolution and full duality instead. Thus neither an unsupplied operation nor the absent deformation is borrowed. Bell original extremality follows at the end of 173.5; it does not imply the quantified resolution (173.3) by any argument here. In particular changing the presentation into that extremality-only variant would reopen a different mathematical problem.

The geometric compression is from a chosen matrix with specified mixing and phase parameters to the reciprocal cone and its own rank-one directions. The representation is still the fixed complex Hermitian carrier; ordinary matrix rank is still a substantive part of the new condition. The reduction does not derive the complex field or the actual tensor product from an unspecified ontology. $\square$

### 173.7 Conditions on physical updates, time and sources

**Proposition 173.10 (conditional physical consumers and source scope).** The reconstruction establishes the finite mathematical state/effect/process dictionary in 173.6. To identify all these mathematical instruments with available physical events requires the event-saturation condition of 172.17. The Lüders branch and a Hamiltonian evolution retain their separate premises:

$$
\mathcal I_P(X)=PXP,
\qquad
\rho_t=e^{-itH}\rho e^{itH}.
\tag{173.24}
$$

The signed rank-one relation is not itself a choice of physical measurement disturbance, clock or energy unit.

**Proof and mathematical attribution.** Consume 172.17 on the all-finite PSD family already proved. For the first formula the required premise is that every ray certainly passing the projection-$P$ outcome is fixed by its branch; an effect alone permits other CP updates. For the second formula the premise is a continuous one-parameter group of reversible trace-preserving real order automorphisms. Continuity connects the group to the identity component and gives the usual unitary Hamiltonian form, with $H$ defined up to an additive scalar. Physical time and energy units, the value of $\hbar$, event availability, and infinite-dimensional extensions are not supplied by (173.4)–(173.5).

Rank-one generation inside an already PSD spectrahedral cone is established terminology: [Hildebrand, Property 1.1 and Lemma 3.9][Q173H] formulate finite native rank-one sums and their extreme rays; [Argue–Kılınç-Karzan–Wang][Q173AKW] study the corresponding PSD-subcone property and sufficient conditions. Those results begin with PSD containment and do not supply the signed weak-domain theorem 173.4. The earlier real/complex ROG sections 93–94 of VI likewise retain their own PSD representation hypotheses. Their classifications are not invoked to assume a sign or a PSD representation for the present unknown cones.

The repository-derived addition here is the signed support/lineality obstruction (173.11)–(173.18) and its Bell-recursive application (173.19)–(173.20). The tensor Bell identity, bipolar duality, finite-dimensional support dimensions, spectral facts and Bloch ball calculation are mature intermediate tools. The positive orientation, finite-frame properness, full-leg ternary propagation, and rectangular quantum dictionary are the named existing repository suppliers, not new proofs of those results. This attribution makes no claim of an exhaustive literature classification or global originality. $\square$

### 173.8 中文白话与完整关系图景

**命题 173.11（有限二元分解与三元提升的白话表述）。** 在定义173.1的固定复矩阵关系空间中，候选 (173.4)–(173.5) 可表述如下：二体整体既能提供同一张贝尔配对，也能用它测试整个原锥；每个二体对象还能拆成有限条仍属于原锥的矩阵秩一细线，起初不指定这些细线朝正还是朝负。这个条件连同指定的三体种子，给出173.5–173.6的全部有限量子结构。

**证明与图景。** 把贝尔配对成对接起来，任意有限块的准备与全部测试就由转置互相对应。如果正细线和负细线的双线性配对不为零，就会给出负数；要避免这一点，两类细线的支撑只能彼此躲开。即使允许原锥含有整条正反都可走的直线，把这种余地完整算进去，支撑维数仍不够支付完整对偶。因此所有细线只能共同朝一边；二体贝尔本身朝正，便把整个二体锥锁成正半定锥，贝尔在原锥里不可再分也随之成为结论。此时任意两个不同纯方向所张成的完整归一面是一颗实三维球，球面上的点是纯态，球内是混合态。三体种子再做两件不同的事：它的普通正性选定奇数层也朝正，它的满维腿和每切口非乘积性接上已有的有限传播定理。这样全部有限层的密度矩阵、玻恩概率、纠缠复合和完全正过程一起恢复。复矩阵载体、这条整体分解关系和三体种子仍是明确前提；具体装置、测后扰动与时间标度各保留173.10的条件。这里内生出来的是符号、原极端性和操作正性，而不是把这些结果预先写进“秩一”的名称。$\square$

[Q173XVI]: https://github.com/the-omega-institute/trureturing/blob/ca8ae24c6a0b7a0348fe24b411bf0b09fb14d455/docs/develop/theory/QUANTUM_ORIGIN_BINARY_BELL_ORBITS_AND_SINGLE_ATTENUATOR_XVI.md
[Q173XIII]: https://github.com/the-omega-institute/trureturing/blob/00427ae2ba9c9e3f6c37f2e5496b9127b6fbc6c0/docs/develop/theory/QUANTUM_ORIGIN_BINARY_TANGENT_CLOSURE_AND_GLOBAL_NONCOLLAPSE_XIII.md
[Q173H]: https://arxiv.org/html/1409.4781v2#S1
[Q173AKW]: https://arxiv.org/abs/2007.07433v2
[Q173W1]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
[Q173W2]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf

## 追加锚（本行以下为增补区）


## 174. Zero overlap as a binary support relation

### 174.1 The same actual domain and a two-element condition

**Definition 174.1 (binary zero overlap).** Retain exactly [Definition 173.1][Q174XVI], including every finite actual complex Hermitian carrier, closed convex cone, complete trace dual, minimum/maximum partition, positive actual permutation with positive inverse, and the scalar object. Keep the Bell resource $B=\Omega\Omega^*$ of (173.2) and the unchanged ternary seed $\mathsf T$ of (173.5). Initially the ordinary trace is only an algebraic functional; neither properness nor trace positivity is supplied.

For $K\subseteq\operatorname{Herm}_d(\mathbb C)$, define

$$
\mathsf Z(K):\quad
X\in K,\ Y\in K^*,\ \operatorname{Tr}(XY)=0
\quad\Longrightarrow\quad XY=0.
\tag{174.1}
$$

The quantifiers cover the **whole** cone and its complete ambient trace dual. For Hermitian matrices, $XY=0$ is equivalent to orthogonality of their ordinary complex ranges. Thus (174.1) is a constraint on the zero relation between an object and a test. The product expresses matrix support; it is not an operation assumed to preserve any cone. The binary candidate is

$$
\mathsf Q_0:\qquad B\in C_2\cap C_2^*,\qquad \mathsf Z(C_2).
\tag{174.2}
$$

It supplies neither the signed decomposition of 173.2, original Bell extremality, nor a positive matrix operation. The matrix-support geometry and complex carriers remain part of its stated domain.

### 174.2 A projection dichotomy without prior cone properness

**Theorem 174.2 (zero overlap fixes a transpose-reciprocal matrix cone).** For $d\ge1$, let $K\subseteq\operatorname{Herm}_d(\mathbb C)$ be a closed convex cone. If

$$
K^*=K^{\mathsf T},\qquad \mathsf Z(K),
\tag{174.3}
$$

then $K=\operatorname{PSD}_d$ or $K=-\operatorname{PSD}_d$. Any nonzero ordinary positive rank-one member selects the positive choice. No pointedness, generation, positive trace or identity membership is needed.

**Proof.** Equip the real Hermitian space with $\langle X,Y\rangle=\operatorname{Tr}(XY)$. Let $P$ be any ordinary rank-one orthogonal projection in this ambient space; it is not assumed to be a native preparation. Moreau's cone decomposition gives

$$
P=A-B,\qquad A=\Pi_K(P)\in K,\qquad B\in K^*,\qquad
\operatorname{Tr}(AB)=0.
\tag{174.4}
$$

Here $\Pi_K$ is the mathematical nearest-point projection. Precisely, [Moreau, §4.b, printed p.281][Q174M] uses the nonpositive polar $K^\circ=-K^*$ and writes $P=\Pi_K(P)+\Pi_{K^\circ}(P)$; set $B=-\Pi_{K^\circ}(P)$. His §5.b, p.282 proves that this projection is nonexpansive, hence continuous. This mathematical minimizer is not a physical measurement or an assumed positive map.

By (174.1), $AB=0$; taking adjoints also gives $BA=0$. If $v\in\ker P$, then $Av=Bv$, so

$$
A^2v=ABv=0,\qquad \|Av\|^2=v^*A^2v=0.
\tag{174.5}
$$

Consequently both $A$ and $B$ vanish on $\ker P$. Hermiticity puts their ranges in the one-dimensional range of $P$. Write $A=aP$, $B=bP$ with real scalars. Equations (174.4) and $AB=0$ give $a-b=1$, $ab=0$, whose only possibilities are

$$
(A,B)=(P,0)\quad\text{or}\quad(A,B)=(0,-P).
\tag{174.6}
$$

The rank-one orthogonal projections form the connected space $\mathbb{CP}^{d-1}$. This includes $d=1$, where it is a point; in general it is the continuous image of the connected unit sphere. Continuity therefore makes

$$
P\longmapsto\operatorname{Tr}\Pi_K(P)\in\{0,1\}
\tag{174.7}
$$

constant. If its value is one, all positive rank-one projections belong to $K$. Finite spectral sums give $\operatorname{PSD}_d\subseteq K$. Dualizing and using $K^*=K^{\mathsf T}$ and transpose invariance of the usual PSD cone gives the reverse inclusion.

If the value is zero, (174.6) gives every $-P\in K^*$. Spectral sums give $-\operatorname{PSD}_d\subseteq K^*$. Transposing this inclusion gives $-\operatorname{PSD}_d\subseteq K$, while dualizing it gives $K\subseteq-\operatorname{PSD}_d$. Thus equality holds. If a nonzero ordinary positive rank-one member was supplied, its normalized projection belongs to $K$ and is its own nearest point; the constant in (174.7) must be one. $\square$

### 174.3 Relation to signed rank-one resolution

**Proposition 174.3 (equivalent presentations under the earned duality).** On closed convex Hermitian cones satisfying $K^*=K^{\mathsf T}$,

$$
\mathsf{SR}(K)\quad\Longleftrightarrow\quad\mathsf Z(K)
\quad\Longleftrightarrow\quad
K\in\{\operatorname{PSD}_d,-\operatorname{PSD}_d\}.
\tag{174.8}
$$

In particular the zero relation may replace the cone-wide finite resolution in the binary candidate, while no inequality in independent axiom counts follows.

**Proof.** Suppose $\mathsf{SR}(K)$. Transpose transports a native signed rank-one resolution to $K^*$, so both sides have such resolutions. For $X\in K$, $Y\in K^*$ with $\operatorname{Tr}(XY)=0$, write $X=\sum_i R_i$, $Y=\sum_j S_j$, with each signed rank-one term in its respective cone. Every $\operatorname{Tr}(R_iS_j)$ is nonnegative by complete duality. Their finite sum is zero, so each is zero. For signed rank-one Hermitian matrices

$$
R=\sigma vv^*,\quad S=\tau ww^*,\qquad
\operatorname{Tr}(RS)=\sigma\tau|v^*w|^2,
\tag{174.9}
$$

zero trace forces $v^*w=0$, hence $RS=0$. Summing gives $XY=0$ and $\mathsf Z(K)$. Theorem 174.2 gives the next implication, and either signed PSD cone has native signed rank-one resolutions by spectral decomposition. Empty resolutions and zero matrices cause no exception. The support/lineality proof 173.4 remains an independent route from resolution to the same classification. $\square$

### 174.4 The entire finite quantum conclusion

**Theorem 174.4 (binary zero relation and ternary propagation).** On Definition 174.1,

$$
\mathsf Q_0\quad\Longleftrightarrow\quad
C_2=\operatorname{PSD}_{n^2},
\tag{174.10}
$$

and

$$
\mathsf Q_0\wedge\mathsf T
\quad\Longleftrightarrow\quad
C_N=\operatorname{PSD}_{n^N}\quad\text{for every finite }N\ge0.
\tag{174.11}
$$

**Proof and full supplier correspondence.** The Bell memberships give $C_k^*=C_k^{\mathsf T}$ at every finite block by 173.3. At $k=2$, Theorem 174.2 applies with $d=n^2$; the positive Bell member selects $C_2=\operatorname{PSD}_{n^2}$. Conversely the usual PSD cone has both Bell memberships and (174.1): for PSD $X,Y$, zero trace implies $Y^{1/2}XY^{1/2}=0$, hence $X^{1/2}Y^{1/2}=0$ and $XY=0$. These are the standard PSD support facts also underlying spectral decompositions in 173.6.

Now use the already proved direction from $C_2=\operatorname{PSD}$ in 173.5, namely 171.8–171.10 followed by 166.12. The fixed carrier, all original finite partitions, permutations, reassociation, scalar object and complete duals are unchanged. The binary equality first earns $C_1=\varepsilon\operatorname{PSD}_n$ and all signed properness. The nonzero ordinary positive ternary dyad selects $\varepsilon=+1$. Take the **entire** bases, all extreme points, full proper intervals and all finite unit decompositions (173.20a) at this earned stage. The unchanged minimum flattening rank two and one full leg supply exactly 166.2; no original extremality of that seed is needed. Thus every premise of 166.12 is paid and (174.11) follows. Its converse uses the ordinary full PSD hierarchy and the GHZ vector as in 173.5.

The exact dictionary is consequently 173.6, with $d_N=n^N$, all original spectators, the same trace, and those full menus:

| Recovered definition or relation | Standard finite quantum statement |
| --- | --- |
| Whole trace-one original cones | All density matrices on the actual carriers |
| Complete dual interval and every finite unit decomposition | All effects and POVMs |
| Original pairing and least pure confirmation | $\operatorname{Tr}(E\rho)$ and $|v^*w|^2$ |
| Actual finite tensor carrier, joint cone and unit slices | Entangled composition and partial traces |
| Positivity with every original finite spectator | Rectangular CP/Choi/Kraus correspondence |
| Whole-input TNI/TP budgets and finite TP-sum families | Mathematical branches, channels and instruments |

The pure geometry is $\mathbb{CP}^{n^N-1}$; the normalized minimal face of every pair of distinct pure rays is the real three-ball (173.22). Event availability, particular updates and continuous time retain the distinct additional premises of 173.10. This application introduces no extra Born, spectral-resolution or operation-preservation premise into (174.2). $\square$

### 174.5 A transported full hierarchy with an extreme Bell ray

**Definition 174.5 (a fixed rational rotation of matrix coordinates).** At local dimension two use the usual Hermitian Pauli basis $I,X,Y,Z$, put $c=4/5$, $s=3/5$, and define the real linear map

$$
\begin{aligned}
R(I)&=cI+sZ,& R(Z)&=-sI+cZ,\\
R(X)&=X,& R(Y)&=Y.
\end{aligned}
\tag{174.12}
$$

For every finite $N$ set

$$
R_N=R^{\otimes N},\qquad
\widehat C_N=R_N(\operatorname{PSD}_{2^N}),\qquad
R_0=\mathrm{id},\quad \widehat C_0=\mathbb R_+.
\tag{174.13}
$$

The tensors and matrix coordinates in (174.13) are the actual original ones; the definition does not redefine the ordinary matrix rank or product. On non-Hermitian matrix units, $R$ and $R^{-1}$ denote the unique complex-linear extensions of their real-linear Hermitian maps, obtained by writing a matrix uniquely as $A+iB$ with $A,B$ Hermitian. This convention supplies no positive operation.

**Theorem 174.6 (full positive-trace countermodel to the Bell-extreme shortcut).** The whole hierarchy (174.13) satisfies Definition 174.1's weak structural domain, and additionally every cone is pointed and generating with strictly positive ordinary trace. It has

$$
B\in\widehat C_2\cap\widehat C_2^*,\qquad
\mathbb R_+B\text{ an extreme ray of }\widehat C_2,
\qquad \mathsf T.
\tag{174.14}
$$

Nevertheless $\widehat C_2\ne\operatorname{PSD}_4$ and $\mathsf Z(\widehat C_2)$ fails, even on a native trace-one state paired with a full proper effect. In particular original Bell extremality cannot replace the resolution or zero-support condition in the fixed actual-coordinate reconstruction.

**Proof.** The four Pauli matrices are orthogonal and have equal squared Hilbert–Schmidt norm. Since $c^2+s^2=1$, $R$ is orthogonal for the real trace inner product. It commutes with ordinary transpose: only $Y$ changes sign under transpose and it is fixed by $R$. Thus $R_N$ is orthogonal and commutes with full transpose. The usual PSD self-duality gives the **complete** dual equality

$$
\widehat C_N^*=R_N(\operatorname{PSD}_{2^N})
=\widehat C_N=\widehat C_N^{\mathsf T}.
\tag{174.15}
$$

Invertible real linear images preserve closedness, convexity, pointedness and generation. For an arbitrary finite split $a+b$, products satisfy $R_a(P)\otimes R_b(Q)=R_{a+b}(P\otimes Q)$, proving the minimum bound after conic closure. For every $F=R_a(E)\in\widehat C_a^*$, $G=R_b(D)\in\widehat C_b^*$ and $Z=R_{a+b}(Q)\in\widehat C_{a+b}$, with $E,D,Q$ PSD, orthogonality gives

$$
\operatorname{Tr}[(F\otimes G)Z]
=\operatorname{Tr}[(E\otimes D)Q]\ge0.
\tag{174.16}
$$

This proves the maximum bound for the entire duals. Every actual permutation commutes with the identical local tensor powers $R_N$ and is an order isomorphism on PSD; it and its inverse therefore preserve $\widehat C_N$. Canonical reassociation changes neither the tensor map nor the joint cone. These arguments include zero blocks and the scalar case.

The ordinary trace is strictly positive because

$$
D:=R^{-1}(I)=\operatorname{diag}(1/5,7/5)\succ0,
\qquad
\operatorname{Tr}R_N(P)=\operatorname{Tr}(D^{\otimes N}P)>0
\quad(0\ne P\succeq0).
\tag{174.17}
$$

All bases, complete duals and full mathematical menus are therefore available. Explicitly the entire proper interval consists of $F=R_N(E)$ with $0\preceq E\preceq D^{\otimes N}$; all finite menus correspond to PSD families with sum $D^{\otimes N}$. No selected effect set is used.

The Bell dyad is

$$
B=\tfrac12(I\otimes I+X\otimes X-Y\otimes Y+Z\otimes Z).
\tag{174.18}
$$

The rotation fixes $I\otimes I+Z\otimes Z$ and fixes the other two terms, so $R_2(B)=B$. Equations (174.13) and (174.15) give both Bell memberships. Since $B$ generates an ordinary extreme PSD ray and $R_2$ is an order isomorphism fixing $B$, that same native Bell ray is extreme.

Write $P_j=|j\rangle\langle j|$. Directly,

$$
A_0:=R(P_0)=\operatorname{diag}(c,-s),\qquad
A_1:=R(P_1)=\operatorname{diag}(s,c).
\tag{174.19}
$$

In particular the native binary extreme generator and complete-dual test

$$
\begin{aligned}
U&=A_0\otimes A_1=\operatorname{diag}(12,16,-9,-12)/25,\\
F&=A_1\otimes A_1=\operatorname{diag}(9,12,12,16)/25
\end{aligned}
\tag{174.20}
$$

satisfy

$$
\operatorname{Tr}(UF)=0,\qquad
UF=\operatorname{diag}(108,192,-108,-192)/625\ne0.
\tag{174.21}
$$

The matrix $U=R_2(P_0\otimes P_1)$ is extreme in the native cone, has ordinary matrix rank four and is indefinite, so $\widehat C_2$ is not ordinary PSD. Moreover $R_2^{-1}(F)=P_1\otimes P_1\succeq0$ and

$$
R_2^{-1}(I-F)=\operatorname{diag}(1,7,7,24)/25\succeq0.
\tag{174.22}
$$

Thus $F$ is a proper effect in the **whole** native interval. Since $\operatorname{Tr}U=7/25$, $\rho=25U/7$ is a native state with $\operatorname{Tr}(\rho F)=0$ but $\rho F\ne0$. Its zero readout arises from cancellation in the ordinary matrix coordinates, not support orthogonality. All native proper readouts are nevertheless valid nonnegative probabilities by complete duality and (174.17).

It remains to supply the precise ternary premise. Put

$$
\epsilon=1/10,\qquad \psi=|000\rangle+\epsilon|111\rangle.
\tag{174.23}
$$

Both coefficients are nonzero, so every flattening has rank two, the full local dimension. The inverse map gives

$$
D_0=R^{-1}(P_0)=\operatorname{diag}(c,s),\qquad
D_1=R^{-1}(P_1)=\operatorname{diag}(-s,c),\qquad
R^{-1}(E_{01})=E_{01}.
\tag{174.24}
$$

Consequently

$$
R_3^{-1}(\psi\psi^*)
=D_0^{\otimes3}+\epsilon^2D_1^{\otimes3}
+\epsilon(E_{01}^{\otimes3}+E_{10}^{\otimes3}).
\tag{174.25}
$$

The first term is at least $s^3I$, the second is at least $-\epsilon^2c^3I$, and the norm of the displayed Hermitian off-diagonal sum is one. Hence

$$
R_3^{-1}(\psi\psi^*)\succeq
(s^3-\epsilon-\epsilon^2c^3)I
=\frac{693}{6250}I\succ0.
\tag{174.26}
$$

Thus the ordinary rank-one positive dyad $\psi\psi^*$ lies in the interior of the native $\widehat C_3$ and satisfies exactly $\mathsf T$. This proves every assertion, including all finite-level and full-menu requirements. $\square$

### 174.6 What the countermodel decides and what the new relation fixes

**Corollary 174.7 (the earlier extremality question has a negative answer in the actual domain).** The Bell-extreme sufficiency question stated in 172.15 and left undecided in 173.9 is false on their fixed actual all-finite domain, even if ordinary strict trace positivity and cone properness are also required. The countermodel concerns actual PSD equality; it does not deny abstract order-isomorphism to a quantum theory.

**Proof.** Theorem 174.6 meets the two ordinary Bell memberships, original Bell extremality, the unchanged full-leg ternary seed, every finite structural requirement and ordinary trace positivity, but fails the conclusion already at level two. It is therefore a counterexample to that precise implication. It also has an ordinary rank-one dyad in the interior of a higher native cone, and an extreme binary ray of ordinary rank four. Neither direction of identifying ordinary matrix rank with native purity is available from Bell extremality alone.

By construction $R_N^{-1}$ transports every native cone back to a usual PSD cone; it transports the ordinary native trace unit to $D^{\otimes N}$. A further congruence by $(D^{1/2})^{\otimes N}$ yields the standard trace normalization. Thus this is a transported quantum order, with a misalignment relative to the **given** matrix product, supports and rank. Condition (174.1) removes that misalignment through its two-element zero relation. It is not claimed to derive the given matrix representation from an otherwise unspecified ontology. $\square$

**Proposition 174.8 (source scope and the conditional physical theory).** The new zero-relation route and the countermodel preserve the preceding reconstruction's explicit physical and representational limits.

**Proof and attribution.** Theorem 174.2 combines the mature Moreau projection theorem with the connected ambient complex ray space and the supplied zero relation; Moreau's original decomposition and continuity are intermediate inputs, not newly proved convex analysis. Bell transpose reciprocity is 173.3. The binary orientation and finite-frame properness are 171.8–171.10; full-leg propagation is 166.12, with the explicit correspondence in 173.5 and 174.4. Full density-state, POVM, Born, rectangular CP and budget consumers are 173.6 and its Watrous sources, not new proofs of their standard ingredients.

The repository-derived additions are the zero-support presentation and its projective projection dichotomy, together with the explicit rational whole-hierarchy countermodel (174.12)–(174.26) to the stated extremality shortcut. This attribution makes no exhaustive literature or global-originality claim. The zero relation uses the fixed matrix support geometry, so neither the complex field, the ordinary matrix product nor the specified tensor carriers has been made a consequence of Bell alone. The odd-level sign still needs the positive ternary seed; the parity hierarchy 173.8 also satisfies (174.2) and fails that seed.

Under (174.11), mathematical instrument availability, a specified least-disturbing projection update, and continuous Hamiltonian dynamics retain exactly 173.10's separate premises. The nearest-point projection in (174.4) supplies no physical operation, clock or energy calibration. Thus the new simplification replaces one cone-wide decomposition relation with a relation between two elements while leaving those conditions explicit. $\square$

### 174.7 中文白话与几何图景

**命题 174.9（零重叠候选的白话表述）。** 在174.1的固定复矩阵关系空间中，候选 (174.2)–(173.5) 可表述为：贝尔配对既能作为原准备，也能测试整个原锥；一个原对象与一个完整对偶测试若读出恰为零，它们的矩阵支撑就必须真正错开，不能靠内部正负抵消装成“没有重叠”。这条二元关系加原三体种子给出174.4的全部有限量子对应。

**证明与图景。** 把任意一条一维方向放在原锥旁边，取它的数学最近点。零重叠条件使这个落点只能是原方向本身或零，不能落成另一个歪斜分支。所有复射线连成一片，最近点又连续，这个“进或不进”的选择就不能跳变；贝尔已经给出一个进来的正方向，于是全部正方向一起进来，完整对偶再把多余方向排出去。二体锥由此锁成正半定锥，任意两条不同纯射线所张的完整归一面仍是一颗实三维球。原三体种子的正性选定奇数层朝向，满维腿和每切口非乘积性再调用已有传播定理，恢复每个有限层的密度矩阵、玻恩概率与完全正过程。反模型则说明为什么要这条零关系：即使贝尔本身不可再分、三体种子也在，整套量子锥仍能在给定矩阵坐标里转歪；所有原概率合法，零概率却可由矩阵正负项抵消。新的条件把这种伪装锁掉。这里的最近点只服务证明；装置可用性、具体测后更新、时间与能量标度仍各按174.8保留条件。$\square$

[Q174M]: https://www.numdam.org/item/BSMF_1965__93__273_0.pdf
[Q174XVI]: https://github.com/the-omega-institute/trureturing/blob/32b36deda4c26d281e6c49bd805b44a1615a5740/docs/develop/theory/QUANTUM_ORIGIN_BINARY_BELL_ORBITS_AND_SINGLE_ATTENUATOR_XVI.md

## 追加锚（本行以下为增补区）
