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

## 171. 原始 Fourier 字母的定量局部预算与同字分支质量

**定义 171.1（固定字母、时序与辅助乘积集）。** 对每个整数 $n\ge2$ 和每个 $0<\lambda<1$，完整采用[169.2][Q171Native]的矩阵，即

$$
\begin{aligned}
\omega&=e^{2\pi i/n},& F_{jk}&=n^{-1/2}\omega^{jk},& a&=2^{1/(n+1)},\\
G&=F\operatorname{diag}(e^{2\pi ia},\ldots,e^{2\pi ia^n})F^{\ast},&
z&=i\lambda,& R&=\operatorname{diag}(z,1,\ldots,1).
\end{aligned}
$$

指标 $j,k$ 均在 $\{0,\ldots,n-1\}$ 中。记

$$
\begin{aligned}
\mathbb T_F&=\{F\operatorname{diag}(e^{i\theta_0},\ldots,e^{i\theta_{n-1}})F^{\ast}:\theta_j\in\mathbb R\},\\
P&=F\operatorname{diag}(1,\omega^{-1},\ldots,\omega^{-(n-1)})F^{\ast},\\
s&=n^{-1/2}\sum_j e_j,\qquad Q=ss^{\ast},\qquad A=iQ,\\
H&=e^{\pi A/2}=I+(i-1)Q,\qquad R_j=P^jRP^{-j},\\
\mathfrak g&=\{X\in M_n(\mathbb C):\operatorname{Re}\operatorname{Tr}X=0\}.
\end{aligned}
$$

$\mathfrak g$ 取实向量空间结构，范数为 $\|X\|_{\mathrm F}=(\operatorname{Tr}(X^{\ast}X))^{1/2}$；$\|X\|_{\mathrm{op}}$ 表示通常算子范数。对于非负整数 $k$，定义辅助乘积集

$$
\mathscr P_k=\{T_0RT_1\cdots RT_k:T_0,\ldots,T_k\in\mathbb T_F\}.
$$

其中保留所显示的 $k$ 个 $R$ 位置。原始正向时序字为有限列 $w=(B_1,\ldots,B_\ell)$，每个 $B_j\in\{G,R\}$；它先作用 $B_1$，其矩阵为 $W(w)=B_\ell\cdots B_1$，$\#_R(w)$ 按字母位置计数。辅助集合 $\mathscr P_k$ 的环面因子不属于这个原始字母表。

**定义 171.2（有限相似标架与常数）。** 令

$$
\begin{aligned}
\mathcal I&=\{(h,j,k,r,v):h\in\{0,1\},\ j\ne k,\ r\in\{0,1,2,3,4\},\ v\in\{0,1\}\},\\
D_\eta&=R_j^rR_k^v,\qquad
A_\eta=H^hD_\eta A D_\eta^{-1}H^{-h}
\quad(\eta=(h,j,k,r,v)),\\
m&=|\mathcal I|=20n(n-1),\qquad
\Phi(t)=\prod_{\eta\in\mathcal I}^{\longrightarrow}e^{t_\eta A_\eta}
\quad(t\in\mathbb R^{\mathcal I}).
\end{aligned}
$$

箭头表示按五元组的字典序从左到右作矩阵乘法，重复方向仍保留各自位置。这里的相似作用始终是 $\operatorname{Int}_D(X)=DXD^{-1}$。置

$$
\begin{aligned}
\mathsf M&=\frac{4n}{\lambda(1-\lambda^2)},&
\mathsf C&=10n^3\mathsf M=\frac{40n^4}{\lambda(1-\lambda^2)},\\
\mathsf N&=\lambda^{-4},&
\mathsf S&=\mathsf N\mathsf C=\frac{40n^4}{\lambda^5(1-\lambda^2)},\\
r_0&=\frac1{16\mathsf S^2},&
b&=50n(n-1),\qquad k_0=nb.
\end{aligned}
$$

**定理 171.3（带明确原衰减次数的非线性局部包含）。** 对定义171.1—171.2的每个 $n,\lambda$，有

$$
\boxed{
z^b\exp\bigl\{Y\in\mathfrak g:\|Y\|_{\mathrm F}\le r_0/2\bigr\}
\ \subseteq\ \mathscr P_{k_0}.
}
$$

证明。相似变换补足方向再取第二类局部乘积坐标的方法见[D’Alessandro，Lemma 1][Q171DA01]及[Method 1][Q171DA09]；以下对本组相似矩阵给出系数预算、非线性半径和原 $R$ 的支付次数。

先构造实线性合成映射

$$
T:\mathbb R^{\mathcal I}\longrightarrow\mathfrak g,
\qquad Tt=\sum_\eta t_\eta A_\eta
$$

的一个右逆。每个 $A_\eta$ 的迹都是 $i$，且

$$
\|A_\eta\|_{\mathrm F}\le
\|D_\eta\|_{\mathrm{op}}\|D_\eta^{-1}\|_{\mathrm{op}}\|A\|_{\mathrm F}
\le\lambda^{-4}=\mathsf N.
$$

这里 $H$ 酉，$D_\eta$ 对角，其最小对角模长至少为 $\lambda^4$、最大模长至多为一，而 $\|A\|_{\mathrm F}=1$。

称一个表示具有系数预算 $d$，是指它是 $A_\eta$ 的实线性组合且系数绝对值之和不超过 $d$。记 $E_{jk}=e_je_k^{\ast}$、$P_j=E_{jj}$ 及 $\mathcal T_j=\operatorname{Int}_{R_j}$。对于 $j\ne k$，逐项相似作用给

$$
\begin{aligned}
B_{jk}&=(\mathcal T_j-I)(\mathcal T_k-I)A
=\alpha(E_{jk}+E_{kj}),\\
\alpha&=\frac{i}{n}(2-z-z^{-1}),\qquad |\alpha|\ge\frac2n,\\
\Delta&=\lambda^{-2}-\lambda^2>0,\\
C_{jk}&=\frac{(\mathcal T_j^2+\lambda^{-2}I)B_{jk}}{\Delta}
=\alpha E_{jk},\qquad
\mathcal T_jC_{jk}=i\lambda\alpha E_{jk}.
\end{aligned}
$$

确实，$\mathcal T_j^2$ 在 $E_{jk},E_{kj}$ 上的乘数分别为 $-\lambda^2,-\lambda^{-2}$。$B_{jk}$ 的四项展开给预算四；$C_{jk}$ 及 $\mathcal T_jC_{jk}$ 各自的预算不超过

$$
\frac{4(1+\lambda^{-2})}{\Delta}=\frac4{1-\lambda^2}.
$$

这些展开只用 $h=0$、$r\le4$、$v\le1$ 的位置。写 $\alpha=x+iy$，其中 $x,y$ 为实数，则

$$
\begin{aligned}
E_{jk}&=\frac{x}{|\alpha|^2}C_{jk}
-\frac{y}{\lambda|\alpha|^2}\mathcal T_jC_{jk},\\
iE_{jk}&=\frac{y}{|\alpha|^2}C_{jk}
+\frac{x}{\lambda|\alpha|^2}\mathcal T_jC_{jk}.
\end{aligned}
$$

由 $|\alpha|\ge2/n$，这两个实表示各有预算

$$
\frac4{1-\lambda^2}\frac{1+\lambda^{-1}}{|\alpha|}
\le\frac{4n}{\lambda(1-\lambda^2)}=\mathsf M.
$$

因此 $iI=nA-\sum_{j\ne k}iE_{jk}$ 有预算 $n+n(n-1)\mathsf M$。

令 $\Pi_{\mathrm{off}}$ 删除矩阵的对角部分。对 $Y_{jk}=E_{jk}-E_{kj}$，$H=I+(i-1)Q$ 的直接乘法给

$$
\operatorname{diag}(HY_{jk}H^{-1})=-\frac{2i}{n}(P_j-P_k).
$$

所以

$$
\begin{aligned}
i(P_j-P_k)&=-\frac n2\bigl[HY_{jk}H^{-1}-\Pi_{\mathrm{off}}(HY_{jk}H^{-1})\bigr],\\
P_j-P_k&=\frac n2\bigl[H(iY_{jk})H^{-1}-\Pi_{\mathrm{off}}(H(iY_{jk})H^{-1})\bigr].
\end{aligned}
$$

$Y_{jk}$ 和 $iY_{jk}$ 的上述表示各有预算 $2\mathsf M$，并只用 $h=0$；以 $H$ 共轭便使用同样系数的 $h=1$ 位置。酉共轭保持 Frobenius 范数，故这两只共轭矩阵均有范数 $\sqrt2$，其非对角条目的实部和虚部绝对值总和不超过

$$
\sqrt{2n(n-1)}\sqrt2\le2n.
$$

用已得 $E_{jk},iE_{jk}$ 的表示扣除这些非对角部分，每个所显示的对角差方向遂有预算 $n(n+1)\mathsf M$。

对任意 $X\in\mathfrak g$，定义

$$
\tau=\frac{\operatorname{Im}\operatorname{Tr}X}{n},\qquad
d_j=X_{jj}-i\tau.
$$

有 $\sum_jd_j=0$，并且

$$
\operatorname{diag}X=i\tau I+
\sum_{j=1}^{n-1}\bigl[\operatorname{Re}d_j(P_j-P_0)
+\operatorname{Im}d_j\,i(P_j-P_0)\bigr].
$$

实 Cauchy–Schwarz 不等式给

$$
\begin{aligned}
\sum_{j\ne k}(|\operatorname{Re}X_{jk}|+|\operatorname{Im}X_{jk}|)
&\le2n\|X\|_{\mathrm F},\\
\sum_{j=1}^{n-1}(|\operatorname{Re}d_j|+|\operatorname{Im}d_j|)
&\le\sqrt{2(n-1)}\Bigl(\sum_j|d_j|^2\Bigr)^{1/2}
\le n\|X\|_{\mathrm F},\\
|\tau|&\le\|X\|_{\mathrm F}/\sqrt n.
\end{aligned}
$$

第二行还用了 $\sum_j|d_j|^2=\sum_j|X_{jj}|^2-n\tau^2$。在这些式中代入已固定的矩阵单位、对角差及 $iI$ 表示，得到一个实线性映射 $J:\mathfrak g\to\mathbb R^{\mathcal I}$，满足

$$
\begin{aligned}
TJ&=I_{\mathfrak g},\\
\|JX\|_1&\le
\left[2n\mathsf M+n^2(n+1)\mathsf M+
\frac{n+n(n-1)\mathsf M}{\sqrt n}\right]\|X\|_{\mathrm F}
\le\mathsf C\|X\|_{\mathrm F}.
\end{aligned}
\tag{171.1}
$$

最后一个界对所有 $n\ge2$ 成立；这里 $\mathsf M\ge1$，可将中间方括号界为 $(2n+n^2(n+1)+n^{3/2})\mathsf M\le10n^3\mathsf M$。构造只要求存在 $j\ne k$，故包括 $n=2$。

现在令 $E(X)=\Phi(JX)$。矩阵指数的收敛、相似变换、范数界及单参数导数直接采用[Hall，Propositions 3.1、3.3、3.4][Q171Hall]。记 $t=JX$、$B_\ell=e^{t_\ell A_\ell}$，其中 $\ell=1,\ldots,m$ 是固定顺序，并置

$$
u=\mathsf S\|X\|_{\mathrm F},\qquad q=e^u-1.
$$

因为 $\sum_\ell|t_\ell|\|A_\ell\|_{\mathrm F}\le u$，指数级数及逐因子乘积差分解给

$$
\|E(X)-I\|_{\mathrm F}\le q.
$$

具体地，每个因子满足 $\|B_\ell\|_{\mathrm{op}}\le e^{|t_\ell|\|A_\ell\|_{\mathrm F}}$ 和 $\|B_\ell-I\|_{\mathrm F}\le e^{|t_\ell|\|A_\ell\|_{\mathrm F}}-1$；乘积差分解的上界相加正好不超过 $e^u-1$。

对 $Z\in\mathfrak g$，乘积求导给

$$
DE_X[Z]=\sum_{\ell=1}^m(JZ)_\ell
B_1\cdots B_\ell A_\ell B_{\ell+1}\cdots B_m.
$$

令 $L_\ell=B_1\cdots B_\ell$、$D_\ell=B_{\ell+1}\cdots B_m$，并记 $u_\ell=\sum_{j\le\ell}|t_j|\|A_j\|_{\mathrm F}$、$v_\ell=\sum_{j>\ell}|t_j|\|A_j\|_{\mathrm F}$。在 $A_\ell$ 左右分别作乘积差分解，所有未作差的指数因子取算子范数，得到

$$
\begin{aligned}
\|L_\ell A_\ell D_\ell-A_\ell\|_{\mathrm F}
&\le\bigl[(e^{u_\ell}-1)e^{v_\ell}+e^{v_\ell}-1\bigr]\|A_\ell\|_{\mathrm F}\\
&\le q\|A_\ell\|_{\mathrm F}.
\end{aligned}
$$

又 $DE_0[Z]=TJZ=Z$，故

$$
\|DE_X-I\|_{\mathrm F\to\mathrm F}\le\mathsf S q.
\tag{171.2}
$$

所用混合范数不等式为 $\|BCD\|_{\mathrm F}\le\|B\|_{\mathrm{op}}\|C\|_{\mathrm F}\|D\|_{\mathrm{op}}$，其中 $\|I_n\|_{\mathrm{op}}=1$，而 $\|I_n\|_{\mathrm F}=\sqrt n$。

在 $\|X\|_{\mathrm F}\le r_0$ 上，$\mathsf S\ge1$，因而

$$
u\le\frac1{16\mathsf S},\qquad
q\le2u\le\frac1{8\mathsf S}<1.
$$

采用[Hall，Theorem 3.6][Q171Hall]的近单位矩阵对数，定义 $\Psi(X)=\log E(X)$。若 $B=E(X)-I$，其导数是收敛级数

$$
D\log_{I+B}[V]=
\sum_{d=1}^{\infty}\frac{(-1)^{d+1}}d
\sum_{v=0}^{d-1}B^vVB^{d-1-v}.
$$

级数在每个 $\|B\|_{\mathrm{op}}\le q<1$ 的较小邻域上一致可逐项求导。由上述混合范数不等式，

$$
\|D\log_{E(X)}\|_{\mathrm F\to\mathrm F}\le\frac1{1-q},\qquad
\|D\log_{E(X)}-I\|_{\mathrm F\to\mathrm F}\le\frac q{1-q}.
$$

又 $\operatorname{Tr}A_\eta=i$，所以每个 $E(X)$ 的行列式模长是一。由[Hall，Theorem 3.10][Q171Hall]的 $\det e^Z=e^{\operatorname{Tr}Z}$ 及 $e^{\log E(X)}=E(X)$，有

$$
\operatorname{Re}\operatorname{Tr}\Psi(X)=\log|\det E(X)|=0.
$$

因此 $\Psi$ 在所用闭球及其一个开邻域内取值于 $\mathfrak g$。链式法则与(171.2)给

$$
\begin{aligned}
\|D\Psi_X-I\|_{\mathrm F\to\mathrm F}
&\le\frac{(\mathsf S+1)q}{1-q}\\
&\le\frac{\mathsf S+1}{8\mathsf S-1}
\le\frac27<\frac12
\qquad(\|X\|_{\mathrm F}\le r_0).
\end{aligned}
\tag{171.3}
$$

$\mathfrak g$ 是有限维矩阵空间的闭实子空间，所用闭球完备且凸，$\Psi(0)=0$；沿线段积分便给

$$
\|\Psi(X)-\Psi(X')-(X-X')\|_{\mathrm F}
\le\tfrac12\|X-X'\|_{\mathrm F}
\quad(\|X\|_{\mathrm F},\|X'\|_{\mathrm F}\le r_0).
$$

直接使用[定量局部满射原理][Q171IFT]，取近似线性映射为 $I_{\mathfrak g}$、右逆范数为一、误差常数为 $1/2$、定义域为半径 $r_0$ 的闭球，得到

$$
\{Y\in\mathfrak g:\|Y\|_{\mathrm F}\le r_0/2\}
\subseteq\Psi\bigl(\{X\in\mathfrak g:\|X\|_{\mathrm F}\le r_0\}\bigr).
$$

该原理在这里的 Banach 不动点映射是 $X\mapsto Y+X-\Psi(X)$；上式的线段估计同时支付其闭球自映射性和收缩性。于是每个所需 $Y$ 都有 $e^Y=E(X)=\Phi(JX)$，这是有限乘积等式。

最后支付这个有限乘积。指数的相似恒等式给

$$
e^{t_\eta A_\eta}
=H^hD_\eta e^{t_\eta A}D_\eta^{-1}H^{-h}.
$$

[169.3][Q171Native]已经给出 $P,H,e^{tA}\in\mathbb T_F$ 以及精确恒等式

$$
S_0=\prod_{j=1}^{n-1}P^jRP^{-j}=zR^{-1}.
$$

展开 $D_\eta=R_j^rR_k^v$ 及其逆，每个指数因子含 $q_\eta=r+v$ 个原 $R$ 和同样多的原 $R^{-1}$，其余因子全部在 $\mathbb T_F$。将每个原 $R^{-1}$ 用 $S_0$ 替换，使该因子的矩阵乘上中心标量 $z^{q_\eta}$，并留下恰好 $nq_\eta$ 个正向原 $R$。保持全部五元组位置，即使 $t_\eta=0$ 也不取消该位置的展开。于是

$$
\sum_{\eta\in\mathcal I}q_\eta
=2n(n-1)\sum_{r=0}^4\sum_{v=0}^1(r+v)
=50n(n-1)=b.
$$

将相邻环面因子合并，便得到 $V\in\mathscr P_{nb}$ 且

$$
V=z^b\Phi(JX)=z^be^Y.
$$

中心标量没有被实现为额外字母，也没有从矩阵 $V$ 中消去。这证明所需包含。∎

**定理 171.4（精度无关的原 $R$ 次数与同一正向字的质量下界）。** 对每个整数 $n\ge2$、每个 $0<\lambda<1$，定义

$$
\begin{aligned}
L&=\left\lceil32\pi\sqrt n\left[\frac{40n^4}{\lambda^5(1-\lambda^2)}\right]^2\right\rceil,\\
\beta&=50n(n-1)L,\\
K(n,\lambda)&=50n^2(n-1)L=n\beta,\\
c(n,\lambda)&=(i\lambda)^\beta,\qquad
p(n,\lambda)=\lambda^{2K(n,\lambda)}>0.
\end{aligned}
$$

对每个 $U\in U(n)$ 及每个 $\varepsilon>0$，存在一个定义171.1的实际有限正向时序字 $w$，使同一个 $W=W(w)$ 同时满足

$$
\boxed{
\begin{aligned}
\#_R(w)&=K(n,\lambda),\\
\|c(n,\lambda)^{-1}W-U\|_{\mathrm{op}}&\le\varepsilon,\\
\inf_{\rho\succeq0,\ \operatorname{Tr}\rho=1}
\operatorname{Tr}(W\rho W^{\ast})&\ge p(n,\lambda).
\end{aligned}
}
$$

次数 $K$、记账标量 $c\ne0$ 和下界 $p$ 均只依赖 $n,\lambda$。

证明。通常酉谱分解由[Watrous，Theorem 1.3、Corollary 1.4][Q169W1]供应。取本征角 $\theta_j\in[-\pi,\pi]$，得到

$$
U=e^X,\qquad X\in\mathfrak u(n)\subseteq\mathfrak g,
\qquad\|X\|_{\mathrm F}\le\pi\sqrt n.
$$

因 $L=\lceil32\pi\sqrt n\,\mathsf S^2\rceil$，有 $\|X/L\|_{\mathrm F}\le r_0/2$。在酉目标上取根并重复局部乘积，是[D’Alessandro，Method 1、式(7)及(14)][Q171DA09]的步骤；这里由171.3给出的明确半径确定其重复次数。具体地，171.3给出

$$
V_0=z^be^{X/L}\in\mathscr P_{k_0}.
$$

重复同一有限乘积 $L$ 次，合并相邻环面因子，得到

$$
V=V_0^L=z^{bL}e^X=cU
=T_0RT_1\cdots RT_K\in\mathscr P_K.
$$

仅对酉矩阵 $U$ 使用了谱对数；没有使用非紧群的全局指数满射。

置

$$
\delta=\frac{\varepsilon\lambda^\beta}{K+1}>0.
$$

直接消费[169.3的正向幂稠密性][Q171Native]：对每个有限位置 $j=0,\ldots,K$，选取一个非负整数 $a_j$，使

$$
\|G^{a_j}-T_j\|_{\mathrm{op}}<\delta.
$$

令

$$
W=G^{a_0}RG^{a_1}\cdots RG^{a_K}.
$$

将显示的乘积从右到左展开为字母列，即得实际时序字 $w$；零次幂给空段，其余幂由有限个 $G$ 字母组成，全部 $K$ 个 $R$ 位置保留。

所有 $T_j,G^{a_j}$ 都酉，所有 $R$ 都为压缩矩阵。逐因子乘积差分解遂给

$$
\|W-cU\|_{\mathrm{op}}
\le\sum_{j=0}^K\|G^{a_j}-T_j\|_{\mathrm{op}}
<(K+1)\delta=\varepsilon\lambda^\beta.
$$

除以记账模长 $|c|=\lambda^\beta$，得到所述逼近。原字母表内没有加入 $c^{-1}I$。

现在对这个已经选定的同一个 $W$ 计算质量。对任意向量 $v$，有

$$
\lambda\|v\|\le\|Rv\|\le\|v\|,\qquad \|Gv\|=\|v\|.
$$

依时序逐步应用，得到

$$
\lambda^K\|v\|\le\|Wv\|\le\|v\|,
\qquad\lambda^{2K}I\preceq W^{\ast}W\preceq I.
$$

因此对每个 $\rho\succeq0$、$\operatorname{Tr}\rho=1$，迹的循环性及 PSD 迹配对给

$$
\operatorname{Tr}(W\rho W^{\ast})
=\operatorname{Tr}(\rho W^{\ast}W)
\ge\lambda^{2K}\operatorname{Tr}\rho=p(n,\lambda).
$$

这是原矩阵 $W$ 的数学分支质量，而非 $c^{-1}W$ 的质量；其完全正性由[Watrous，Theorem 2.22][Q169W2]的单 Kraus 表示给出，不增迹性由 $W^{\ast}W\preceq I$ 给出。该下界在选取任意精度所需的有限正向幂之后仍成立。

最后，$K=n\beta$ 使

$$
|\det W|=\lambda^K=|c|^n=|\det(cU)|,\qquad 0<|c|<1.
$$

于是精度趋零时所逼近的是 $cU$；[169.7][Q171Native]的未缩放恒等式 $\overline{\mathcal W^+}\cap U(n)=\mathbb T_F$ 保持原义。定理没有给 $\sum_ja_j$ 的上界，也没有将辅助环面因子当作原始字母。∎

[Q171Native]: https://github.com/the-omega-institute/trureturing/blob/74f0816e3a2340d063ad1a7cb5e8a93ffe2d1c9d/docs/develop/theory/QUANTUM_ORIGIN_BINARY_BELL_ORBITS_AND_SINGLE_ATTENUATOR_XVI.md
[Q171DA01]: https://arxiv.org/html/quant-ph/0111133v1
[Q171DA09]: https://arxiv.org/html/0904.2793v1
[Q171Hall]: https://arxiv.org/html/math-ph/0005032v1
[Q171IFT]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean#L143

## 追加锚（本行以下为增补区）
