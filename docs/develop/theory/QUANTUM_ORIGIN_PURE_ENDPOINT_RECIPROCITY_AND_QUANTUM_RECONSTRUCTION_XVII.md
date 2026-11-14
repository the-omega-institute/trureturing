# 原纯端点互易与全部有限量子重建 XVII

本卷引用的170—172均指[卷XVI][Q175XVI]中的对应章节；完整强域由定义175.1给定。

[Q175XVI]: https://github.com/the-omega-institute/trureturing/blob/6f38031ae6b77994ef7ed9db3e4729a6a32daa9d/docs/develop/theory/QUANTUM_ORIGIN_BINARY_BELL_ORBITS_AND_SINGLE_ATTENUATOR_XVI.md

## 175. 原纯端点互易、可逆滤波的退化面与全部有限量子锥

### 175.1 完整原域与端点比较

**定义 175.1（原确认菜单与互易条件）。** 完整采用 [XIII166.1][Q175XIII] 的域。固定整数 $n\ge2$，在同一实际 Kronecker 坐标中令

$$
V=\operatorname{Herm}_n(\mathbb C),\qquad
W_N=V^{\otimes_{\mathbb R}N}=\operatorname{Herm}_{n^N}(\mathbb C).
\tag{175.1}
$$

每个有限 $N\ge1$ 有闭、尖、生成凸锥 $C_N\subset W_N$，普通迹 $u_N=\operatorname{Tr}=u_1^{\otimes N}$ 在非零原正元上严格正，并且在这些实际坐标中

$$
C_1=\operatorname{PSD}_n,\qquad C_2=\operatorname{PSD}_{n^2}.
\tag{175.2}
$$

始终使用整个归一基、全部原极点、完整迹对偶、整个 proper 区间：

$$
\begin{aligned}
K_N&=\{x\in C_N:\operatorname{Tr}x=1\},&P_N&=\operatorname{ext}K_N,\\
C_N^*&=\{f\in W_N:\operatorname{Tr}(fx)\ge0\ \forall x\in C_N\},&
\mathcal E_N&=\{f:f,I_{n^N}-f\in C_N^*\}.
\end{aligned}
\tag{175.3}
$$

有限菜单取全部 $f_\ell\in C_N^*$、$\sum_\ell f_\ell=I_{n^N}$，凸准备和配对使用原实线性结构。对每个有限实际分块，保留

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}
                 \subseteq C_a\otimes_{\max}C_b.
\tag{175.4}
$$

最小锥是正简单张量的闭凸生成锥；最大锥由全部原 $f\otimes g$，$f\in C_a^*,g\in C_b^*$，的非负半空间相交定义。全部实际位置置换及其逆均正，不连续分块由它们运输；重括号使用同一实际空间的规范识别。原配对与单位满足

$$
(f\otimes g)(x\otimes y)=f(x)g(y),\qquad u_{a+b}=u_a\otimes u_b.
\tag{175.5}
$$

空系统为 $W_0=\mathbb R,C_0=\mathbb R_+,u_0=\mathrm{id}$；上述条件包括标量分块和每个有限层。对 $N\ge3$ 不预付 PSD、自对偶、全转置不变性、原纯态分类或全局矩阵操作正性。

以下记 $A,B,C$ 为三个带指定基的 $\mathbb C^n$ 实际因子，$D=n^3$、$I=I_D$、$m=I/D$，以及 $\|H\|_2^2=\operatorname{Tr}(H^2)$（$H=H^*$）。由最小界，$I_n\otimes I_{n^2}\in C_3$，故 $m\in K_3$。对原纯态 $p\in P_3$ 定义

$$
\mathcal F_p=\{f\in\mathcal E_3:\operatorname{Tr}(fp)=1\},\qquad
T_p(x)=\min_{f\in\mathcal F_p}\operatorname{Tr}(fx)\quad(x\in C_3).
\tag{175.6}
$$

引理175.3将证明这些最小值取得。端点互易条件为

$$
\mathsf{Rec}:\qquad T_p(q)=T_q(p)\quad(p,q\in P_3).
\tag{175.7}
$$

它交换两个静态比较端点，不涉及测量的先后执行。记号 $\mathsf R$ 仍专指 §172 的二元资源条件，不用于本章互易。固定一个实际切分 $A|BC$，令

$$
\mathcal A_{A|BC}=\{P_a\otimes Q_v:\|a\|=\|v\|=1,\quad
 P_a=aa^*,\ Q_v=vv^*,\ v\in\mathbb C^n\otimes\mathbb C^n\}.
\tag{175.8}
$$

这里 $v$ 可以二腿纠缠。较弱的单向条件及等参照条件分别为

$$
\begin{aligned}
\mathsf{Rec}_{\mathcal A}^{\le}:&\quad
T_p(q)\le T_q(p)\quad(p\in P_3,\ q\in\mathcal A_{A|BC}),\\
\mathsf E:&\quad T_p(m)=T_q(m)\quad(p,q\in P_3).
\end{aligned}
\tag{175.9}
$$

引理175.3将把整个 $\mathcal A_{A|BC}$ 识别为原暴露纯态。$\mathsf E$ 不指定共同值。两个条件都不预设 $T_p$ 仿射、存在 least 确认效应、原纯态集合闭，或奇异滤波保持原纯性。

**定理 175.2（原纯端点互易的全有限重建）。** 在定义175.1的完整域内，下列条件等价：

1. $\mathsf{Rec}$。
2. 一个固定切分上的 $\mathsf{Rec}_{\mathcal A}^{\le}$。
3. $\mathsf E$。
4. 每个原纯态 $p\in P_3$ 满足 $\operatorname{Tr}(p^2)=1$。
5. 存在一个不预先指定的半径 $r\ge0$，使 $\|p-m\|_2=r$ 对全部 $p\in P_3$ 成立。
6. $C_3=\operatorname{PSD}_D$。
7. $C_N=\operatorname{PSD}_{n^N}$ 对每个有限 $N\ge0$ 成立。

此时共同参照读数为 $1/D$，$r^2=1-1/D$，并且对整个原锥

$$
T_p(x)=\operatorname{Tr}(px),\qquad
T_{vv^*}(ww^*)=|v^*w|^2\quad(\|v\|=\|w\|=1).
\tag{175.10}
$$

每个 $p$ 的唯一 $m$ 处最优确认效应是 $p$，它也是整个原效应锥序下的 least 确认效应。这些是结论，不是互易的隐含前件。本定理为 repo-derived 的重建综合；既有范数界、秩保持分类和全有限传播分别按下述精确接口引用，不把本定理归为 Gurvits–Barnum 或 Marciniak 的原陈述。

### 175.2 统一效应界与真正的原二分锚

**引理 175.3（完整菜单的紧性与暴露锚）。** 在三个实际切分 $A|BC,B|AC,C|AB$ 上，$C_3$ 和 $C_3^*$ 均包含于相应块正锥。因而

$$
\|x\|_2\le\operatorname{Tr}x\quad(x\in C_3),\qquad
\|f\|_2\le\operatorname{Tr}f\quad(f\in C_3^*),\qquad
\|f\|_2\le\operatorname{Tr}f\le D\quad(f\in\mathcal E_3).
\tag{175.11}
$$

$K_3,\mathcal E_3,\mathcal F_p$ 都紧，后两者非空；$\mathcal A_{A|BC}\subset P_3$，且每个 $q\in\mathcal A_{A|BC}$ 都是 proper 自确认效应。对全部原纯态有

$$
T_p(m)\ge\frac1{D\|p\|_2}\ge\frac1D,
\qquad T_q(m)=\frac1D\quad(q\in\mathcal A_{A|BC}).
\tag{175.12}
$$

证明。对复有限维矩形空间 $U,Z$，Hermitian 矩阵 $H$ 块正指 $\langle u\otimes z,H(u\otimes z)\rangle\ge0$ 对全部向量成立。直接复用 [Gurvits–Barnum 的块正对偶范数界][Q175BP]：

$$
H\in\operatorname{BP}(U|Z)\quad\Longrightarrow\quad
0\le\operatorname{Tr}H,\qquad\|H\|_2\le\operatorname{Tr}H.
\tag{175.13}
$$

该供应适用于任意矩形维数，特别是 $(n,n^2)$。[原文 Theorem 1][Q175GB] 的可分离单位球及其 BP 对偶界是既有结果。低层 PSD 的完整自对偶使每个 $1|23$ 最大界正好给 $C_3\subset\operatorname{BP}$；最小界包含该切分的全部可分离 PSD 锥，取对偶给 $C_3^*\subset\operatorname{BP}$。原置换支付另外两个切分。对 $f$ 和 $I-f$ 分别应用(175.13)，得到(175.11)最后一项。这是对整个效应区间统一的界，与被确认的纯态无关。

$K_3$ 闭且由(175.11)有界；$\mathcal E_3$ 同样闭有界。$I\in\mathcal E_3$，因为严格正迹是原正泛函，故 $I\in\mathcal F_p$。确认超平面闭，所以 $\mathcal F_p$ 非空紧，所有(175.6)的最小值均取得。

固定 $q=P_a\otimes Q_v$。最小界给 $q\in K_3$。最大界的正简单对偶使 $q\in C_3^*$，并且

$$
I-q=(I_A-P_a)\otimes I_{BC}+P_a\otimes(I_{BC}-Q_v)\in C_3^*.
\tag{175.14}
$$

这里两个 $BC$ 矩阵均在已知的完整二体 PSD 对偶内，包括纠缠 $v$ 的 $Q_v$。于是 $q\in\mathcal F_q$。若 $x\in K_3$ 且 $\operatorname{Tr}(qx)=1$，则 $\|x\|_2\le1$ 给

$$
\|x-q\|_2^2=\|x\|_2^2+1-2\operatorname{Tr}(qx)\le0.
\tag{175.15}
$$

故 $x=q$；泛函 $q$ 在整个 $K_3$ 上唯一暴露该点。此处证明的是实际二分锚的原极端性，没有把全部未知原纯态替换成矩阵 dyad。

最后，对 $f\in\mathcal F_p$，Cauchy–Schwarz 与(175.11)给

$$
1=\operatorname{Tr}(fp)\le\|f\|_2\|p\|_2
\le(\operatorname{Tr}f)\|p\|_2,\qquad 0<\|p\|_2\le1.
$$

除以 $D$ 并最小化得(175.12)下界；锚自身的 $f=q$ 取得反向上界。$\square$

### 175.3 混合面附近的有限互易缺陷

**引理 175.4（定量混合面不对称）。** 设 $q_j=P_a\otimes Q_j\in\mathcal A_{A|BC}$，$Q_j$ 为两两正交的单位秩一投影，并令

$$
\rho=\sum_{j=1}^r\lambda_jq_j,\qquad
\lambda_j>0,\quad\sum_j\lambda_j=1.
$$

对任意原纯态 $p$，记 $\eta=\|p-\rho\|_2$，则每个 $j$ 满足

$$
\boxed{\ T_p(q_j)-T_{q_j}(p)
\ge1-\lambda_j-\left(\frac D{\lambda_j}+1\right)\eta.\ }
\tag{175.16}
$$

证明。任取整个菜单中的 $f\in\mathcal F_p$，统一效应界给

$$
f(\rho)\ge f(p)-\|f\|_2\eta\ge1-D\eta.
$$

每个原态 $q_i$ 上都有 $0\le f(q_i)\le1$，所以

$$
\lambda_j[1-f(q_j)]\le\sum_i\lambda_i[1-f(q_i)]
=1-f(\rho)\le D\eta.
$$

此式对每个 $f\in\mathcal F_p$ 成立，因而

$$
T_p(q_j)\ge1-\frac{D\eta}{\lambda_j}.
\tag{175.17}
$$

另一方面，锚的 proper 自确认效应给

$$
T_{q_j}(p)\le\operatorname{Tr}(q_jp)
\le\operatorname{Tr}(q_j\rho)+\|q_j\|_2\eta
=\lambda_j+\eta.
\tag{175.18}
$$

两式相减即得。整个论证只在 $p,q_j$ 两个原纯端点上使用 $T$；没有在混合 $\rho$ 上要求互易，也没有交换最小化与求和或使用 $p\mapsto T_p$ 的连续性。特别地，当 $\lambda_j<1$ 且

$$
\eta<\frac{\lambda_j(1-\lambda_j)}{D+\lambda_j},
\tag{175.19}
$$

就有实际有限端点对上的严格反向差 $T_p(q_j)>T_{q_j}(p)$。$\square$

### 175.4 可逆滤波保原纯性，奇异极限只用于选参数

**引理 175.5（互易迫使全部一腿压缩秩至多一）。** 在 $\mathsf{Rec}_{\mathcal A}^{\le}$ 下，每个 $p\in P_3$ 和每个 $a\in A$ 满足

$$
X_a=(\langle a|\otimes I)p(|a\rangle\otimes I)\succeq0,
\qquad\operatorname{rank}X_a\le1.
\tag{175.20}
$$

证明。PSD 性由 $A|BC$ 块正性给出。复用 [XIII166.3、VII102.6–102.7][Q175XIII] 的原一体合同接口：任意单腿矩阵 $H$ 的 $\operatorname{Ad}_H$ 在每个原有限旁观层上正。该供应只需本章完整原域和低层 PSD；它的 Choi dyad 在原 $C_2$，与任意原相关输入作最小张量积，再经原 Bell 帽切片，支付合同正性。取 $s_H=\max\{1,\|H\|_{\rm op}\}$，合同 $\operatorname{Ad}_{H/s_H}$ 还具有全旁观不增迹预算。

若 $H$ 可逆，对 $H^{-1}$ 独立使用同一供应，故 $\operatorname{Ad}_H$ 及其逆都正，成为整个原锥的线性自同构，保持极端射线。严格正迹使其非零像可归一，因而归一可逆滤波保持全部原纯态。此处的数学正逆不声称一个无代价、确定性可实现的物理逆。

只需处理单位 $a$ 且 $X_a\ne0$ 的情形。对每个正实数 $t$ 令

$$
H_t=P_a+t(I_A-P_a),\qquad
p_t=\frac{(H_t\otimes I)p(H_t^*\otimes I)}
 {\operatorname{Tr}[(H_t\otimes I)p(H_t^*\otimes I)]}.
\tag{175.21}
$$

$H_t$ 可逆，故 $p_t\in P_3$。分母对每个 $t>0$ 严格正；在 $t\downarrow0$ 时收敛到 $\operatorname{Tr}X_a>0$，通常矩阵连续性给

$$
p_t\longrightarrow\rho=P_a\otimes\frac{X_a}{\operatorname{Tr}X_a}.
\tag{175.22}
$$

若 $X_a$ 的秩 $r\ge2$，在已知二体 PSD 空间作谱分解

$$
\frac{X_a}{\operatorname{Tr}X_a}=\sum_{j=1}^r\lambda_jQ_j,
\qquad0<\lambda_j<1,\quad\sum_j\lambda_j=1.
$$

全部 $q_j=P_a\otimes Q_j$ 都是引理175.3的原暴露纯态。固定其中一个 $j$，(175.22)允许选择仍严格为正的有限 $t$，使(175.19)成立。引理175.4遂给 $T_{p_t}(q_j)>T_{q_j}(p_t)$，与单向条件矛盾。故秩至多一。零压缩、零向量 $a$ 及非单位 $a$ 分别由直接判断和正比例缩放涵盖。

这个矛盾只使用正参数的原纯态 $p_t$，未把 $t=0$ 的奇异映射当成保纯操作，也未断言极限 $\rho$ 原纯或 $P_3$ 闭。二体谱向量可以纠缠，所以若只保留完全乘积锚，以上谱分解步骤便没有被支付。$\square$

### 175.5 秩保持分类、三切分排负与完整极性

**引理 175.6（压缩秩条件的共同重建尾部）。** 在定义175.1的域中，如果(175.20)对全部原纯态及固定 $A$ 腿的全部向量成立，则全部有限 $C_N$ 为 PSD。

证明。固定 $p\in P_3$，在实际基中写

$$
p=\sum_{i,j=0}^{n-1}E_{ij}\otimes p_{ij},\qquad
\Phi_p:M_n(\mathbb C)\to M_{n^2}(\mathbb C),\quad
\Phi_p(E_{ij})=p_{ij}.
\tag{175.23}
$$

这是复线性映射，且逐项计算给

$$
\Phi_p(zz^*)=\sum_{i,j}z_i\overline z_jp_{ij}=X_{\overline z}.
\tag{175.24}
$$

所以 $\Phi_p$ 正，并把每个一维正交投影映成秩至多一的 PSD 矩阵，允许零输出。其参考—输出 Choi 矩阵恰为 $p$；式中的复共轭由实际坐标决定。

现在直接使用 [Marciniak, Theorem 2.2，0812.2311v3 印刷页9][Q175Marc]，DOI **10.4064/bc89-0-12**。该定理的精确前件是两个任意有限维复 Hilbert 空间间的 rank-1 non-increasing 正线性映射，所指条件正是上述一维投影条件；不要求保迹、单射、极端性或满支撑。其三支分类在本节的矩形 $(n,n^2)$ 上为

$$
\Phi_p(Z)=\omega(Z)Q,\qquad
\Phi_p(Z)=LZL^*,\qquad
\Phi_p(Z)=M'Z^{\mathsf T}(M')^*.
\tag{175.25}
$$

$\omega$ 是正泛函，$Q$ 是一维投影；$L,M':\mathbb C^n\to\mathbb C^{n^2}$ 可有核，$M'$ 与 §172 的固定 $M$ 无关。写 $\omega(Z)=\operatorname{Tr}(SZ)$、$S\succeq0$，三支的 Choi 形式分别为

$$
p=S^{\mathsf T}\otimes Q,\qquad p=vv^*,\qquad
p=\Gamma_A(vv^*).
\tag{175.26}
$$

这里 $\Gamma_A$ 是实际指定基中仅对 $A$ 因子作矩阵转置。第二、三支分别取 $v=\sum_i e_i\otimes Le_i$、$v=\sum_i e_i\otimes M'e_i$。第一支中 $S$ 可以混合，不需先证明其秩一：整个该支已是 PSD。$p$ 迹一排除零 Choi；后两支 $\|v\|=1$。零输出方向和退化矩形算子已包含在分类中。

只余部分转置支路。对任意 $b\in B$ 令 $v_b=(I_A\otimes\langle b|\otimes I_C)v$。$B|AC$ 块正性使

$$
\Gamma_A(v_bv_b^*)\succeq0\quad\text{在 }A\otimes C\text{ 上}.
\tag{175.27}
$$

若 $w=\sum_i s_i a_i\otimes c_i$ 是 Schmidt 展开，则 $\Gamma_A(ww^*)$ 在 $\overline a_i\otimes c_i$ 上的本征值为 $s_i^2$，在每对 $\overline a_i\otimes c_j,\overline a_j\otimes c_i$ 上的块为

$$
\begin{pmatrix}0&s_is_j\\s_is_j&0\end{pmatrix}.
\tag{175.28}
$$

故其 PSD 当且仅当 $w$ 的 Schmidt 秩至多一，零向量也包括在内。这是通常纯态 PPT 判据；[Gurvits–Barnum Theorem 2(1)][Q175GB] 给该谱，块计算保留了这里的矩形维数和所有零特征值。

所以每个 $v_b$ 都是乘积或零。这些切片的全部像构成复线性子空间，虽然参数 $b$ 的进入是反线性的。复用 [XIII166.6][Q175XIII] 的共同因子引理，得到

$$
v=a\otimes z_{BC}\quad\text{或}\quad v=z_{AB}\otimes c.
\tag{175.29}
$$

第一支给 $p=\overline a\,\overline a^*\otimes z_{BC}z_{BC}^*\succeq0$。第二支中 $c\ne0$，沿 $c$ 压缩并使用 $C|AB$ 块正性，得到 $\Gamma_A(z_{AB}z_{AB}^*)\succeq0$。同一个谱判据迫使 $z_{AB}$ 为乘积，故 $p$ 也 PSD。切片空间若为零则 $v=0$，已由迹一排除；一维空间及部分零切片都被共同因子引理涵盖。这里部分转置只是分类记号，没有被用作原正物理操作。

至此全部原极点是 PSD。有限维紧凸生成使整个 $K_3$ 为其极点的凸包，严格正迹再给

$$
C_3\subseteq\operatorname{PSD}_D.
\tag{175.30}
$$

反向包含消费 [VII 式(105.6)][Q175VII] 的全有限 Bell 极性：

$$
C_N^*=\mathsf T_N(C_N)\quad(N\ge1),
\tag{175.31}
$$

$\mathsf T_N$ 是全部实际腿的同时全转置。其接口在这里逐项到位：低层 PSD 使 Bell dyad $B_n$ 同时属于原 $C_2$ 和完整 $C_2^*$；$N$ 份杯的最小积与实际重排属于原 $C_{2N}$，对完整 $f\in C_N^*$ 切片给 $\mathsf T_Nf\in C_N$；对 $x\otimes y\in C_{2N}$ 收缩 $N$ 份原帽给 $\operatorname{Tr}[(\mathsf T_Nx)y]\ge0$，即 $\mathsf T_Nx\in C_N^*$。用 $\mathsf T_N^2=\mathrm{id}$ 即得该供应的原等式。$N=3$ 实际使用六体对象；没有从低阶形状预设高阶自对偶。

由(175.30)和全转置保持通常 PSD，得 $C_3^*\subseteq\operatorname{PSD}_D$；取完整对偶及闭锥双极性，得 $\operatorname{PSD}_D\subseteq C_3$。因此三体整锥相等，而不仅是一个 PSD 子锥。

此时明确向量 $g_n=\sum_{j=0}^{n-1}e_j\otimes e_j\otimes e_j$ 的 dyad 属于原 $C_3$，三个展平秩都是 $n\ge2$。它支付 [166.2][Q175XIII] 的全部种子条件。定义175.1与166.1的对应是同一固定 $n$ 和实际载体、每层闭尖生成锥、严格正乘法迹、整个基及全部原极点、完整对偶与 proper 区间、全部有限单位分解、所有有限 min/max 分块、正置换及正逆、不连续分块运输、规范重括号、原配对及空系统，加上同坐标的两条低层 PSD 等式。故直接消费 [166.12 条件1到条件5][Q175XIII]，得到每个有限 $C_N=\operatorname{PSD}_{n^N}$。该供应的递减支撑归纳、角的完整对偶延拓、有限控制与传播证明均按其原前件保留，不在这里重复构造传播尾部。$\square$

### 175.6 互易主定理与未知半径的等价证明

证明定理175.2。引理175.3使 $\mathsf{Rec}$ 蕴含 $\mathsf{Rec}_{\mathcal A}^{\le}$；引理175.5和175.6使后者推出全部有限 PSD。全部有限等式当然给三体等式。

若 $C_3=\operatorname{PSD}_D$，原纯态正好是全部单位秩一投影。对 $p=vv^*$，$\|v\|=1$，任意原 proper 确认效应满足 $0\preceq f\preceq I$ 和 $\langle v,(I-f)v\rangle=0$，故 $(I-f)v=0$。Hermitian 性消去交叉块，给完整确认集合

$$
f=p+Q,\qquad 0\preceq Q\preceq I-p,\qquad Qv=0.
\tag{175.32}
$$

所以 $f-p\in C_3^*$ 对每个确认效应成立，$p$ 为 least 确认；$p$ 自身取得所有 $x\in C_3$ 上的最小值，得到(175.10)及互易。$\operatorname{Tr}(fm)=(1+\operatorname{Tr}Q)/D$，其最小值为 $1/D$，且当且仅当 $Q=0$ 取得。唯一 $m$ 处最优不表示确认菜单仅有一个元素。

现在假设 $\mathsf E$。一个原二分锚按(175.12)把未知共同值固定为 $1/D$。对任意原纯态，该式的下界和 $\|p\|_2\le1$ 于是迫使 $\|p\|_2=1$。这也说明单独要求全部 $T_p(m)\le1/D$ 就与 $\mathsf E$ 等价。

反过来，只假设全部原纯态范数为一。对任意原纯态 $p$ 和单位向量 $a$ 使用(175.21)的可逆滤波；当 $X_a\ne0$，每个 $p_t$ 仍为原纯态，故 $\|p_t\|_2=1$。矩阵范数连续性在(175.22)的极限给

$$
1=\left\|P_a\otimes\frac{X_a}{\operatorname{Tr}X_a}\right\|_2^2
=\operatorname{Tr}\left[\left(\frac{X_a}{\operatorname{Tr}X_a}\right)^2\right].
\tag{175.33}
$$

PSD 迹一矩阵的非负特征值之和为一，平方和为一当且仅当只有一个非零特征值。因此 $X_a$ 秩一，零压缩另行满足秩条件。再次消费同一个引理175.6，得到全部有限 PSD，继而得到 $\mathsf E$。这里只对矩阵范数取极限，没有假定极限原纯，也无需另一个 Haar 等号分类论证。

对任意迹一 Hermitian 矩阵，

$$
\|p-m\|_2^2=\operatorname{Tr}(p^2)-1/D.
\tag{175.34}
$$

故未知半径条件等价于纯点平方迹为某个常数；一个已证明为原纯点的二分锚把该常数固定为一。所有条件和数值结论均已证明。$\square$

几何结论附于本定理如下。原 $K_3$ 一开始已在以 $m$ 为中心、平方半径 $1-1/D$ 的闭球内。互易最终使全部原极点位于该球面，并识别为 $\mathbb{CP}^{D-1}$。其维数为 $2D-2$，环境球面维数为 $D^2-2$；$D>2$ 时它是球面的真子集。密度矩阵体是这个射影纯态轨迹的凸包，并非整个球。例如 $D\ge3$ 时

$$
\operatorname{diag}(-1/3,2/3,2/3,0,\ldots,0)
\tag{175.35}
$$

迹一、平方迹一，却不是 PSD；按实际乘积基排列，其负对角元已违反块正测试。纯态外接球也不同于 Gurvits–Barnum 的可分离内球。等价的几何表述不自动减少独立假设数，也不证明整套重建描述长度达到全局最小。

### 175.7 二元供应、普通中性选择与有向运输

**推论 175.7（由原二元资源进入互易重建）。** 固定的矩阵始终精确为170.2，即(172.8)：

$$
K=\sum_{j=0}^{n-2}(E_{j,j+1}-E_{j+1,j}),\quad t=\frac1{32n},\quad
O=e^{(1+i)tK},\quad W=e^{\pi i\sqrt2P_0},\quad M=WO.
\tag{175.36}
$$

置 $\Omega=\sum_j e_j\otimes e_j$、$B=\Omega\Omega^*$、$D_M=(M\otimes I)B(M^*\otimes I)$。有以下两个条件应用。

在170.1的普通完整域中，先用170.5的**第一项等价**

$$
\mathsf B\wedge\mathsf M_2
\quad\Longleftrightarrow\quad
C_1=\operatorname{PSD}_n,\quad C_2=\operatorname{PSD}_{n^2},
\tag{175.37}
$$

其中 $\mathsf B$ 是 $B\in C_2\cap C_2^*$，$\mathsf M_2$ 仅是这一个固定 $\operatorname{Ad}_{M\otimes I}(C_2)\subseteq C_2$。随后定义175.1的整个菜单。则

$$
\mathsf B\wedge\mathsf M_2\wedge\mathsf{Rec}
\quad\Longleftrightarrow\quad
C_N=\operatorname{PSD}_{n^N}\quad\text{对每个有限 }N.
\tag{175.38}
$$

在171.1、等同172.1的较弱原域中，不先要求尖性、生成性或正迹。先要求原资源 $\mathsf R$，即 $D_M\in C_2,B\in C_2^*$；再要求普通中性成员关系 $m=I_D/D\in C_3$；最后在由这些前件获得的普通完整菜单上要求 $\mathsf{Rec}$。这个依赖顺序的合取满足

$$
[D_M\in C_2,\ B\in C_2^*]\ \wedge\ [m\in C_3]\ \wedge\ [\mathsf{Rec}]
\quad\Longleftrightarrow\quad
C_N=\operatorname{PSD}_{n^N}\quad\text{对每个有限 }N.
\tag{175.39}
$$

这里互易的原基与菜单在前两组条件支付普通正方向后定义。将首组资源替换为 $\mathsf B\wedge\mathsf M_2$ 也有相同等价。

证明。普通域的(175.37)没有三元种子 $\mathsf T$ 前件；它给低层对齐，其余全部前件原已在170.1中。直接应用定理175.2便得(175.38)。这里互易替代显式 GME 种子，而非先借有种子的全有限结论证明低层。

弱域中先精确消费172.7的二元结论(172.25)–(172.26)，即其引用的171.7–171.9：原资源等价于 $\mathsf B\wedge\mathsf M_2$，给唯一 $\varepsilon\in\{\pm1\}$、$C_1=\varepsilon\operatorname{PSD}_n,C_2=\operatorname{PSD}_{n^2}$，每个原锥尖且生成，$\varepsilon^N\operatorname{Tr}$ 在其非零元上严格正。这一步不使用 $\mathsf T$、普通概率归一化或 proper 菜单。

普通 $m$ 是三体奇数层的非零通常 PSD 元素，171.10遂给 $\varepsilon=+1$。至此才取得每层严格正的普通迹和完整紧基，按(175.3)取全部极点、完整对偶、整个 proper 区间和所有有限单位分解。结构部分原就是172.1的全部实际有限 min/max、置换及正逆、重括号、配对和标量对象；两条低层等式也已获得。因此定义175.1的每一前件都已支付，可以定义(175.6)并消费定理175.2。

反向在全部普通 PSD 层级中，指定 $D_M$ 为 PSD dyad，$B$ 属于完整二体 PSD 对偶，普通 $m$ 合法且(175.32)给互易；指定矩阵合同也给 $\mathsf M_2$。两个等价均成立。证明只消费已有矩阵生成、双轨夹逼和有限投影标架，不重证这些供应。$\square$

**推论 175.8（保留方向的精确有向版本）。** 在上述弱域及二元资源下，用已获得的唯一 $\varepsilon$ 定义

$$
\begin{aligned}
\widehat u_N&=\varepsilon^N\operatorname{Tr},&
\widehat K_N&=\{x\in C_N:\widehat u_N(x)=1\},&
\widehat P_N&=\operatorname{ext}\widehat K_N,\\
\widehat{\mathcal E}_N&=\{f:f,\varepsilon^NI_{n^N}-f\in C_N^*\},&
\widehat m&=\varepsilon I_D/D.
\end{aligned}
\tag{175.40}
$$

以这些整个菜单定义 $\widehat T$ 和全部三体原有向纯端点上的 $\widehat{\mathsf{Rec}}$，则

$$
\widehat{\mathsf{Rec}}\quad\Longleftrightarrow\quad
C_N=\varepsilon^N\operatorname{PSD}_{n^N}\quad\text{对每个有限 }N.
\tag{175.41}
$$

证明。171.9的运输族 $D_N=\varepsilon^NC_N$ 已满足定义175.1的整个强域。锥同构 $\Theta_N(x)=\varepsilon^Nx$ 将完整基和全部极点双射到运输族的迹一对象；完整对偶满足 $D_N^*=\varepsilon^NC_N^*$。效应也按 $f\mapsto\varepsilon^Nf$ 双射，且

$$
\operatorname{Tr}[(\varepsilon^Nf)(\varepsilon^Nx)]=\operatorname{Tr}(fx),
\qquad \widehat T_p(q)=T^{D_3}_{\varepsilon p}(\varepsilon q).
\tag{175.42}
$$

确认约束和菜单每个候选的目标值都逐项保持。因此有向互易正是运输族上的普通互易，定理175.2给 $D_N=\operatorname{PSD}$，再运输回去。反向同理。$\widehat m$ 的成员关系由 $I_n/n\in D_1$ 和最小积给出。运输同时满足

$$
\Theta_{a+b}(x\otimes y)=\Theta_a(x)\otimes\Theta_b(y),\qquad
\Theta_0=\mathrm{id}.
$$

故完整复合、配对与获得单位相容。$\varepsilon=-1$ 的结论是交替定向 PSD，并非普通 PSD；另加 $m\in C_3$ 才选正方向。171.12、172.8的完整交替模型满足二元资源和有向互易，普通奇数层迹一基却为空，不能用该空集使普通互易虚真地替代中性选择。$\square$

### 175.8 全部静态数据与矩形数学过程的量子字典

**推论 175.9（同坐标的完整有限量子对应）。** 在定理175.2或推论175.7的任一普通量子结论下，令 $d_N=n^N,d_0=1$。精确消费 [166.14][Q175XIII]、[VII102.13–102.18][Q175VII] 及172.16的整锥后矩阵证明，得到：

| 整个原对象及量词 | 同一实际坐标中的量子对象 |
| --- | --- |
| $K_N$ 与全部有限凸准备 | 全部密度矩阵 $\rho\succeq0,\operatorname{Tr}\rho=1$，包括混态 |
| $P_N$ 与非零极射线 | 全部单位秩一投影及其正倍数；$\mathbb{CP}^{d_N-1}$ |
| 完整 $C_N^*$、整个 $\mathcal E_N$ | 全部 PSD 迹泛函、全部 $0\preceq E\preceq I_{d_N}$ |
| 全部有限单位分解与原配对 | 全部有限 POVM，含 PVM；$\Pr(\ell\mid\rho)=\operatorname{Tr}(E_\ell\rho)$ |
| Hermitian 可观察量及其谱菜单 | 期望 $\operatorname{Tr}(A\rho)$ |
| 每个实际有限张量分块与联合锥 | 给定 Hilbert 张量积中的全部联合密度矩阵，包含纠缠 |
| 原置换及单位切片 | 普通因子置换及任意相关输入的偏迹 |
| 全部纯态确认读数 | $T_p^{(N)}(x)=\operatorname{Tr}(px)$；纯态重叠 $|v^*w|^2$ |
| 全部原全旁观正的实线性 $F:W_a\to W_b$ | 全部矩形 CP 映射及有限 Kraus 表示 |
| 整个输入及相关旁观者上的 TNI/TP 预算 | Kraus 平方和 $\preceq I_{d_a}$／$=I_{d_a}$ |

证明及矩形接口。所有整锥等式、普通迹和完整菜单已取得，正好满足所引字典的前件。谱分解给密度矩阵、全部极点和有限纯分解；完整 PSD 对偶给全部效应。对每个有限层重复(175.32)的矩阵论证，得 least 确认及全部准备一致性

$$
T_p^{(N)}\left(\sum_j\alpha_jq_j\right)
=\sum_j\alpha_jT_{q_j}^{(N)}(p),\qquad
\alpha_j\ge0,\quad\sum_j\alpha_j=1.
\tag{175.43}
$$

具体地，$a,b$ 为任意有限非负整数，对 $F$ 取唯一复线性保 Hermitian 扩张，即 $F(X+iY)=F(X)+iF(Y)$（$X,Y$ Hermitian）。参考—输出 Choi 次序给

$$
\begin{aligned}
J(F)&=\sum_{i,j=0}^{d_a-1}E_{ij}\otimes F(E_{ij}),\\
(\mathrm{id}_{W_s}\otimes F)C_{s+a}\subseteq C_{s+b}\quad(\forall s\ge0)
&\Longleftrightarrow J(F)\succeq0\\
&\Longleftrightarrow F(X)=\sum_\mu K_\mu XK_\mu^*,\quad
K_\mu:\mathbb C^{d_a}\to\mathbb C^{d_b}.
\end{aligned}
\tag{175.44}
$$

原自身 Choi 判据 VII102.7的杯帽与全部原有限结构已支付；[Watrous Theorem 2.22][Q175W2] 在 $\mathcal X=\mathbb C^{d_a},\mathcal Y=\mathbb C^{d_b}$ 的矩形应用给最后一步，书中输出—参考次序由一次实际 SWAP 转换。非零映射可取 $\operatorname{rank}J(F)$ 个 Kraus 算子；零映射取空族。任意有限矩阵参考维数上的通常 CP 性由该表示成为结论，输入只量化原层级的全部有限旁观者。

令 $Q_F=\sum_\mu K_\mu^*K_\mu$，完整预算为

$$
\begin{aligned}
\operatorname{Tr}F(X)&=\operatorname{Tr}(Q_FX),&
\operatorname{Tr}_{\rm out}J(F)&=Q_F^{\mathsf T},\\
F\text{ TNI}&\Longleftrightarrow Q_F\preceq I_{d_a},&
F\text{ TP}&\Longleftrightarrow Q_F=I_{d_a}.
\end{aligned}
\tag{175.45}
$$

TP 是 Watrous Theorem 2.26 的同一替换；TNI 由同一迹身份测试全部 PSD 输入取得，旁观者版本的差预算是 $I\otimes(I-Q_F)\succeq0$。Choi 总迹不能替代该边缘条件。所有原作用位置由置换给出。$a=0$ 为准备 $q\mapsto q\sigma$，预算是 $\operatorname{Tr}\sigma\le1$／$=1$；$b=0$ 为效应 $X\mapsto\operatorname{Tr}(EX)$；$a=b=0$ 为非负标量乘法，空旁观者始终保留。$\square$

### 175.9 缺陷机制、删域控制与真正的全有限反模型

**命题 175.10（互易的作用范围）。** 下列对照分别说明滤波缺陷、第三切分、全有限域和低层对齐的不同作用；它们不构成定理175.2的同域反例。

证明。若某个原纯态有一个秩至少二的条件压缩，则其可逆滤波轨道按(175.22)逼近 $\rho=\sum_j\lambda_jq_j$。对每个固定谱权重，(175.16)给

$$
\liminf_{t\downarrow0}[T_{p_t}(q_j)-T_{q_j}(p_t)]\ge1-\lambda_j>0.
\tag{175.46}
$$

(175.19)已把这个极限障碍变成实际正参数端点上的严格违例。反之，若全部原纯态的这些压缩秩至多一，引理175.6已给全部有限 PSD。因此同域内任一非量子层级都必须有这种混合压缩和实际互易缺陷。有限抽样、给滤波参数设正下限或额外要求统一成功率，都不等于本章全量词条件。

第三切分不能删除：取 $A,B$ 中指定二维子空间上的交换算子 $F_2$（其余为零），及 $C$ 中单位向量 $0$，则

$$
H=\frac{F_2}{2}\otimes|0\rangle\langle0|,\qquad
\operatorname{Tr}H=\operatorname{Tr}(H^2)=1.
\tag{175.47}
$$

它在 $A|BC$、$B|AC$ 上块正，因为相应压缩期望是两个二维分量的内积模平方的一半。但 $\psi_-=(|01\rangle-|10\rangle)/\sqrt2$ 给 $\langle\psi_-\otimes0,H(\psi_-\otimes0)\rangle=-1/2$，违反 $C|AB$ 块正性。这是矩阵删前件控制，不是原全有限层级。

另一个控制只保留 $N\le3$。令低两层 PSD，三体基为三个切分的全部二可分 dyad 的凸包：

$$
\mathcal S=\bigcup_{X=A,B,C}\{vv^*:\|v\|=1,\ v\text{ 在 }X|X^c\text{ 上乘积}\},
\qquad K_3^{\rm bis}=\operatorname{conv}\mathcal S.
\tag{175.48}
$$

$\mathcal S$ 紧，故其有限维凸包紧；锥闭、尖、生成且迹严格正。每个实际 $1|23$ 最小锥包含于该锥，最大界由该锥为 PSD 子锥给出；置换及其逆置换三个切分。每个 $\mathcal S$ 点在整个 PSD 基中已极端，而极点的有限 $\mathcal S$ 分解只能由自身组成，故全部原极点恰为 $\mathcal S$。

每个这样的 $p$ 满足 $p,I-p$ 对整个前缀锥正，且其完整对偶在任一切分的 BP 内。因此(175.12)同一下界及 $f=p$ 上界给 $T_p(m)=1/D$，$\mathsf E$ 成立。归一 GHZ dyad 却不在该基中：它不在 $\mathcal S$，且其 PSD 秩一性排除不同 $\mathcal S$ 点的凸分解。特别在 $n=2$，对 $g=(|000\rangle+|111\rangle)/\sqrt2$，$I_8-2gg^*$ 在每个二可分 dyad 上非负，因为相应 Schmidt 最大系数平方为 $1/2$；它在 $g$ 上取 $-1$。故完整对偶含非 PSD 元素，而全转置保持二可分锥，(175.31)失效。这个三体有限前缀只证明删去全有限 Bell 极性后 $\mathsf E$ 不足；这里未判定它是否满足 $\mathsf{Rec}$，也未把它延拓为全有限反模型。

一般凸域中互易甚至不必推出等参照。取方锥基

$$
K=\operatorname{conv}\{(\pm1,\pm1,0),(0,0,1)\},\qquad m=(0,0,1/5),
\tag{175.49}
$$

并使用全部取值在 $[0,1]$ 的仿射效应。顶点两两可由二元效应区分：顶点与底面用 $z,1-z$，不同底顶点用 $(1\pm x-z)/2$ 或 $(1\pm y-z)/2$。故 $T_p(q)=\delta_{pq}$，互易成立。顶点 $a=(0,0,1)$ 有 $T_a(m)=1/5$，由 $z$ 取得。对底顶点 $b=(1,1,0)$，四个底值满足 $f_{++}+f_{--}=f_{+-}+f_{-+}$；若 $f_{++}=1$，底值之和至少二，故 $T_b(m)\ge2/5$，由 $(1+x-z)/2$ 取得。这里 $m$ 甚至是全部五个原纯态的等权均值，仍无 $\mathsf E$。该一般仿射模型没有本章复矩阵低层和滤波接口。

真正的全有限删域反模型则可直接消费172.11–172.14：在任意奇素数 $n=p$ 的实际载体上，Wigner 锥族是每一层的完整经典单纯形，普通迹严格正，具有全部有限 min/max、置换、完整对偶及全部菜单，并满足普通 Bell 和原三元种子。在三体层用172.11的顶点 $A_z$，正交关系给 $\operatorname{Tr}[(A_z/p^3)A_w]=\delta_{zw}$，且 $I=\sum_wA_w/p^3$。因此 $A_z/p^3$ 与其补都在完整原对偶内，确认 $A_z$ 而拒绝每个其他顶点，给 $T_{A_z}(A_w)=\delta_{zw}$，从而满足 $\mathsf{Rec}$。但其一体相位点含非 PSD 顶点，且精确 $D_M$ 不属于二体原锥。它因此反驳弱域中删去低层对齐或指定变形资源后的“裸互易重建”，而非本章已对齐域或(175.39)。有向交替 PSD 的全有限方向反模型则已由推论175.8精确说明。$\square$

### 175.10 实际事件、条件更新与时间的额外边界

**命题 175.11（静态互易不规定更新或时间顺序）。** 在普通量子结论下，全部有限数学仪器为

$$
F_\ell(X)=\sum_\mu K_{\ell\mu}XK_{\ell\mu}^*,\qquad
\sum_{\ell,\mu}K_{\ell\mu}^*K_{\ell\mu}=I,
\qquad E_\ell=\sum_\mu K_{\ell\mu}^*K_{\ell\mu}.
\tag{175.50}
$$

它们成为全部实际可用事件需要另给 VII102.14 的事件饱和条件。一个效应不指定唯一条件更新；$\mathsf{Rec}$ 不使有更新的先后操作交换，也不指定物理钟、Hamiltonian 或 $\hbar$。

证明。数学仪器及预算复用推论175.9和172.16，即 Watrous §2.3.2 的同坐标表述。对任意相关输入 $Z$，分支 $Z_\ell=(\mathrm{id}\otimes F_\ell)Z$ 的质量为 $m_\ell=\operatorname{Tr}[(I\otimes E_\ell)Z]$，且 $\sum_\ell m_\ell=\operatorname{Tr}Z$。只有 $m_\ell>0$ 时才定义条件态 $Z_\ell/m_\ell$；零质量时 PSD 输出必为零，不能作归一除法。有限顺序、自适应组合、粗粒化的未归一相加及仪器张量积沿172.16的证明保留。

对全基投影 $P_j$，令 $U$ 交换 $e_0,e_1$。两套数学仪器 $F_j(X)=P_jXP_j$ 和 $G_j(X)=UP_jXP_jU^*$ 的效应均为 $P_j$，但输入 $P_0$、结果零时的条件态分别为 $P_0,P_1$。两者总 Kraus 平方和都是 $I$，故效应和 Born 概率不能选择唯一更新。若另要求 sharp yes 子空间每条纯射线逐点不受扰动，172.17及其161.7.1供应才选出 Lüders 压缩；单独的 repeatability 不足以替代该逐点条件。

具体顺序差异在二维子空间已出现。取

$$
P=|0\rangle\langle0|,\qquad Q=|+\rangle\langle+|,\qquad
|+\rangle=(|0\rangle+|1\rangle)/\sqrt2,
\quad\mathcal L_R(X)=RXR.
$$

静态 $T_P(Q)=T_Q(P)=1/2$，但输入 $P$ 时

$$
(\mathcal L_Q\circ\mathcal L_P)(P)=\tfrac12Q,\qquad
(\mathcal L_P\circ\mathcal L_Q)(P)=\tfrac14P.
\tag{175.51}
$$

所以两次均“是”的分支质量分别为 $1/2$ 和 $1/4$。交换比较端点与交换测量时序是不同命题。

若另给每个固定矩阵系统上的连续、保迹实序自同构时间群，172.17按161.10的矩阵级供应给酉实现的生成元形式。若已给可微酉群 $U_{t+s}=U_tU_s$，则 $K=\dot U_0$ 满足 $K^*=-K$，$U_t=e^{tK}$；再选正尺度 $\hbar$ 并置 $H=i\hbar K$，才有 $U_t=e^{-itH/\hbar}$。这些前件、具体时间作用、物理钟和能量—时间标定不由静态互易产生。$\square$

### 175.11 几何机制与中文释义

**命题 175.12（比较直觉的精确内容与供应边界）。** 本章将“两两比较，交换端点不改变结果”解释为整个原确认菜单下的(175.7)。其承重机制是混合面缺陷和可逆滤波，而不是预设比较函数线性或原纯点已构成球面。

证明及释义。若一个原纯准备在越来越强、每次仍可逆的局部筛选下逼近几个已知端点的真正混合，那么任何对该准备必答“是”的测试，在统一效应界下也必须对混合几乎必答“是”。每个端点都有正权，于是这些测试对每个端点都几乎必答“是”。反向看，一个端点用自己的确定性测试看这个混合，只能看到自己的权重；权重小于一就产生(175.16)的严格差。互易排除了这样的混合压缩。

压缩秩一进入 Marciniak 的矩形分类，另外两个实际切分和共同因子引理去掉非 PSD 部分转置支路。全有限 Bell 杯帽随后从原锥及其完整对偶两面夹逼，补足整个三体 PSD 锥；明确满维 GHZ 再由166.12传播至全部有限层。这解释了为何完整菜单、二腿纠缠锚、三个切分与全有限域各有实质作用。

Gurvits–Barnum 的范数界、Marciniak 的秩保持分类、166.12的传播和既有量子字典均各归其来源。本章补的是端点互易到压缩秩条件的桥梁及其同域等价和条件应用。复数载体、固定 $n$、实际张量识别、完整对偶和全部有限复合仍是前提；证明没有额外加入谱性、投影性或 least 确认条件。本章不据此宣称历史优先权、无前提宇宙本体或独立公理数的最小性。$\square$

[Q175GB]: https://arxiv.org/pdf/quant-ph/0204159v2
[Q175BP]: https://github.com/the-omega-institute/trureturing/blob/59c307b5ef357d66f12d054b023e0a00edd398ff/D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall.lean
[Q175Marc]: https://arxiv.org/pdf/0812.2311v3
[Q175XIII]: https://github.com/the-omega-institute/trureturing/blob/59c307b5ef357d66f12d054b023e0a00edd398ff/docs/develop/theory/QUANTUM_ORIGIN_BINARY_TANGENT_CLOSURE_AND_GLOBAL_NONCOLLAPSE_XIII.md
[Q175VII]: https://github.com/the-omega-institute/trureturing/blob/59c307b5ef357d66f12d054b023e0a00edd398ff/docs/develop/theory/QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md
[Q175W2]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf

## 追加锚（本行以下为增补区）
