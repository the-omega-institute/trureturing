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
