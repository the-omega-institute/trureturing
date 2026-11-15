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


## 176. 一个乘积点附近的纯关系闭性与单锚比较

### 176.1 原定义间的关系与精确条件

**定义 176.1（整个原纯集、局部无缺口与固定锚）。** 本章完整采用定义175.1，即 [XIII166.1][Q175XIII] 的同一强域：固定 $n\ge2$、实际复 Hermitian Kronecker 载体、全部有限闭尖生成锥、严格正的乘法普通迹、同坐标 $C_1=\operatorname{PSD}_n,C_2=\operatorname{PSD}_{n^2}$、完整对偶、所有有限 min/max 分块、正置换及正逆、规范重括号、原配对和空系统。$K_N,P_N,\mathcal E_N$ 及全部有限菜单始终是(175.3)的整个原集合，$T$ 精确为(175.6)，不换成选定子集。只在176.6–176.7的条件推论中使用较弱域。

固定单位向量 $a_0,b_0,c_0$，置 $q_0=P_{a_0}\otimes P_{b_0}\otimes P_{c_0}$，其中 $P_v=vv^*$。引理175.3已证明 $q_0$ 是原暴露纯点及 proper 自确认效应；这里不另假定它的原纯性。拓扑取 $W_3$ 上的有限维 Hilbert–Schmidt 范数，或任意等价范数；闭包记为 $\overline{P_3}$。也可在迹一仿射超平面中取相对拓扑，所得条件相同。定义

$$
\begin{aligned}
\mathsf{PClose}:&\quad P_3=\overline{P_3},\\
\mathsf{LPC}(q_0):&\quad \exists\ U\subset W_3\text{ 开},\quad q_0\in U,
 \quad U\cap\overline{P_3}=U\cap P_3,\\
\mathsf S(q_0):&\quad T_p(q_0)\le T_{q_0}(p)\quad\text{对每个 }p\in P_3,\\
\mathsf Q_\infty:&\quad C_N=\operatorname{PSD}_{n^N}\quad\text{对每个有限 }N\ge0.
\end{aligned}
\tag{176.1}
$$

$\mathsf{LPC}(q_0)$ 说整个原纯集在这一个点附近没有非纯极限缺口；它不是单点集 $\{q_0\}$ 闭，也不是附近每个原态都纯。固定锚只限制第二端点；$\mathsf S(q_0)$ 的第一端点仍量化全部原纯态。

原极端性本来就由中点关系定义：$x\in P_3$ 当且仅当 $x\in K_3$ 且 $2x=y+z$、$y,z\in K_3$ 蕴含 $y=z=x$。因此同一原定义的二元关系为

$$
\mathcal I_{K_3}:=\{(y,z)\in K_3^2:(y+z)/2\in P_3\}
 =\{(p,p):p\in P_3\}.
\tag{176.2}
$$

对角映射 $x\mapsto(x,x)$ 是到闭对角集的同胚，故 $\overline{\mathcal I_{K_3}}=\{(r,r):r\in\overline{P_3}\}$。于是 $\mathsf{PClose}$ 恰是这个既有中点关系的闭性，$\mathsf{LPC}(q_0)$ 恰是它在 $(q_0,q_0)$ 附近的相对闭性：把邻域沿对角映射拉回即可，反向可取 $U\times U$。$K_3$ 闭使在 $K_3^2$ 或环境空间中取闭包一致。这是定义对应，不从极端性的定义自动推出关系闭。

**定理 176.2（单点附近、整个纯集与单锚的同域等价）。** 在上述完整强域中，下列条件等价：

1. $\mathsf Q_\infty$。
2. $C_3=\operatorname{PSD}_{n^3}$。
3. $\mathsf{PClose}$。
4. $\mathsf{LPC}(q_0)$。
5. $\mathsf S(q_0)$。

它们也各与定理175.2的原全端点互易、固定二分切口的单向互易、等参照读数和未知半径条件等价；这些条件及其数值结论直接沿用175.2，不改写其量词。以下先分别证明三个新的充分性桥梁，再给出逆向。这里的拓扑条件是显式前件，没有藏在完整强域里。

### 176.2 可逆滤波把任何纯极限缺口送近同一乘积点

**命题 176.3（局部闭性推出整个原纯集闭）。** 定义176.1的强域内，$\mathsf{LPC}(q_0)$ 蕴含 $\mathsf{PClose}$。

证明。直接消费175.5证明中由166.3支付的一腿合同及其可逆版本。对任意可逆局部乘积矩阵 $G=G_A\otimes G_B\otimes G_C$，定义

$$
F_G(x)=\frac{GxG^*}{\operatorname{Tr}(GxG^*)}\quad(x\in K_3).
\tag{176.3}
$$

合同及其逆均保持整个 $C_3$；严格正迹使分母在整个 $K_3$ 上正。故 $F_G$ 连续，逆为 $F_{G^{-1}}$，是整个原基的同胚。合同的线性锥同构保持极端射线，归一基的极点对应这些射线，故 $F_G(P_3)=P_3$。这里不声称 $F_G$ 仿射。引理175.3给 $K_3$ 紧，特别是 $\overline{P_3}\subset K_3$；在 $K_3$ 内取闭包与环境闭包一致。因此

$$
L:=\overline{P_3}\setminus P_3,\qquad F_G(L)=L.
\tag{176.4}
$$

若 $L$ 非空，取 $r\in L$。对任意实际正交乘积基，最大界给全部对角测试非负，它们之和为 $\operatorname{Tr}r=1$。所以其中某个单位乘积向量 $a\otimes b\otimes c$ 满足

$$
\alpha=\langle abc|r|abc\rangle>0.
\tag{176.5}
$$

这一步没有把可能非 PSD 的 $r$ 当成 PSD。对每个 $t>0$ 取

$$
G_t=[P_a+t(I-P_a)]\otimes[P_b+t(I-P_b)]\otimes[P_c+t(I-P_c)].
\tag{176.6}
$$

三个因子均可逆，故 $r_t=F_{G_t}(r)\in L$。普通矩阵极限给分子趋于 $\alpha q$、分母趋于 $\alpha>0$，其中 $q=P_a\otimes P_b\otimes P_c$；于是 $r_t\to q$。选一个固定局部酉 $U=U_A\otimes U_B\otimes U_C$ 把 $q$ 送到 $q_0$。它也是上述锥同构，且保迹，所以 $Ur_tU^*\in L$ 并趋于 $q_0$。

若 $\mathsf{LPC}(q_0)$ 的开邻域为 $U_0$，则充分小的正 $t$ 给 $Ur_tU^*\in U_0\cap(\overline{P_3}\setminus P_3)$，矛盾。故 $L$ 为空。每个有限滤波后的缺口仍非纯；没有用全纯态传递性、奇异滤波保纯、统一成功率下界或比较函数的连续性。反向 $\mathsf{PClose}\Rightarrow\mathsf{LPC}(q_0)$ 可取 $U_0=W_3$。$\square$

### 176.3 闭纯集排除混合压缩

**命题 176.4（整个原纯集闭推出全部有限 PSD）。** 在同一强域内，$\mathsf{PClose}$ 蕴含 $\mathsf Q_\infty$。

证明。任取 $p\in P_3$、单位向量 $a\in A$。由 $A|BC$ 最大界及完整二体 PSD 对偶，

$$
X_a=(\langle a|\otimes I)p(|a\rangle\otimes I)\succeq0
\quad\text{在 }B\otimes C\text{ 上}.
\tag{176.7}
$$

若 $X_a=0$，其秩已为零。否则 $\operatorname{Tr}X_a>0$，直接使用(175.21)的有限正参数可逆滤波，得到 $p_t\in P_3$ 且

$$
p_t\longrightarrow\rho=P_a\otimes X_a/\operatorname{Tr}X_a.
\tag{176.8}
$$

闭性使 $\rho\in P_3$。若 $\operatorname{rank}X_a=r\ge2$，通常二体 PSD 谱分解给

$$
\rho=\sum_{j=1}^r\lambda_jq_j,\qquad
q_j=P_a\otimes P_{v_j},\quad
\lambda_j>0,\quad\sum_j\lambda_j=1,
\tag{176.9}
$$

其中 $v_j$ 两两正交且为单位向量。最小界及 $C_1,C_2$ 的既定 PSD 性已使每个 $q_j$ 属于整个原 $K_3$，彼此不同。取任意 $j$，则 $0<\lambda_j<1$，其余项的归一凸组合也是原态，且与 $q_j$ 不同；故(176.9)是 $\rho$ 的真正非平凡凸分解，违反原极端性。这一步只需这些谱点是原态，不需它们暴露，也不使用效应范数界或 $T$ 的最优化。

因此全部 $p\in P_3$ 的全部 $A$ 腿压缩秩至多一。$a=0$ 的压缩为零，非单位向量由正比例缩放涵盖。现精确消费引理175.6：它在同一强域中把这一条件送入 Marciniak 的矩形 rank-1 non-increasing 正映射分类，保留零输出和退化支路；三个实际切分去掉非 PSD 分支，全有限 Bell 极性及完整对偶给三体整锥等式，再由明确满维 GHZ 和166.12传播到每个有限层。这里不重证分类、极性或传播，也不预付任一高层 PSD。$\square$

### 176.4 固定乘积锚迫使两腿压缩秩一

**命题 176.5（一个乘积锚的单向比较推出全部有限 PSD）。** 在同一强域内，$\mathsf S(q_0)$ 蕴含 $\mathsf Q_\infty$。

证明。首先，局部酉 $U$ 的合同保持原锥、普通迹及其完整对偶，因而双射整个 $\mathcal E_3$ 和所有确认集合。逐项配对不变给

$$
T_{UpU^*}(UxU^*)=T_p(x)\quad(p\in P_3,\ x\in C_3).
\tag{176.10}
$$

任意完全乘积单位 dyad $q$ 都可写成 $Uq_0U^*$。对原纯态 $U^*pU$ 使用固定锚条件并用(176.10)，得

$$
T_p(q)\le T_q(p)\qquad
(p\in P_3,\ q=P_a\otimes P_b\otimes P_c).
\tag{176.11}
$$

这里只移动已知的乘积锚轨道，未声称局部酉在全部原纯点上传递。

任取 $p\in P_3$ 和单位 $a\in A,b\in B$。由原乘积测试非负，普通矩阵

$$
Y_{ab}=(\langle ab|\otimes I_C)p(|ab\rangle\otimes I_C)\succeq0.
\tag{176.12}
$$

零输出无需处理。非零时用同时作用于 $A,B$ 的
$G_t=[P_a+t(I-P_a)]\otimes[P_b+t(I-P_b)]\otimes I_C$，$t>0$，得原纯态

$$
p_t=F_{G_t}(p)\longrightarrow
\rho=P_a\otimes P_b\otimes Y_{ab}/\operatorname{Tr}Y_{ab}.
\tag{176.13}
$$

若 $Y_{ab}$ 秩至少二，普通谱分解把 $\rho$ 写成 $\sum_j\lambda_jq_j$，其中 $q_j=P_a\otimes P_b\otimes P_{c_j}$，$c_j$ 为正交单位向量，$0<\lambda_j<1$。它们是175.3的原纯 proper 自确认锚，而且是175.4所需的同一 $A|BC$ 切口的正交二分锚。对任意固定 $j$，直接用其缺陷估计得

$$
T_{p_t}(q_j)-T_{q_j}(p_t)
\ge1-\lambda_j-\left(\frac D{\lambda_j}+1\right)\|p_t-\rho\|_2>0
\tag{176.14}
$$

只须选择仍为正的有限 $t$，使 $\|p_t-\rho\|_2<\lambda_j(1-\lambda_j)/(D+\lambda_j)$。这与(176.11)矛盾，故全部 $Y_{ab}$ 秩至多一。由实际置换，同一论证适用于 $AC$、$BC$ 任意一对；零向量及非单位向量由零输出和缩放涵盖。没有对混合 $\rho$ 使用比较律，也没有对 $T$ 的第一参数取连续极限。

还需从两腿恢复一腿压缩，所用普通 PSD Gram 事实在此作为中间步骤证明。设 $X\succeq0$ 在 $B\otimes C$ 上，而且其全部 $B$ 腿及全部 $C$ 腿向量压缩秩至多一。若 $X=0$，结论显然。否则取有限 Gram 分解

$$
X=\sum_{i=1}^r v_iv_i^*,\qquad
\Psi=\sum_{i=1}^r v_i\otimes e_i\in B\otimes C\otimes E,
\qquad E=\mathbb C^r.
\tag{176.15}
$$

这里 $e_i$ 是 $E$ 的标准正交基。对每个 $b\in B$，切片 $\Psi_b=(\langle b|\otimes I_C\otimes I_E)\Psi$ 满足普通矩阵身份

$$
\operatorname{Tr}_E(\Psi_b\Psi_b^*)
=\sum_i[(\langle b|\otimes I_C)v_i][(\langle b|\otimes I_C)v_i]^*=X_b.
$$

Gram 矩阵秩等于其列空间维数，所以 $\operatorname{rank}X_b\le1$ 意味着 $\Psi_b$ 在 $C|E$ 上是乘积向量或零。所有这些切片的像是复线性空间，尽管参数 $b$ 反线性进入。精确使用166.6的共同因子结论，有以下两种情形：

$$
\Psi=\psi_{BC}\otimes e
\quad\text{或}\quad
\Psi=\chi_{BE}\otimes c.
\tag{176.16}
$$

第二式按 $B,C,E$ 次序作普通张量重排。第一种给 $X=\|e\|^2\psi\psi^*$，秩至多一。第二种可把 $c$ 归一，得到 $X=R_B\otimes P_c$、$R_B\succeq0$；沿这个 $c$ 的另一侧压缩正好是 $R_B$，故另一组秩条件使 $\operatorname{rank}R_B\le1$，仍得 $\operatorname{rank}X\le1$。非零 $\Psi$ 保证共同因子非零；部分零切片和一维切片空间已由166.6涵盖。$E$ 只是任意有限辅助 Gram 坐标，不是原物理系统；这里未要求它有原锥层级、可用纯化或任何物理操作。

现在对每个原纯态及单位 $a$，(176.7)的 $X_a\succeq0$ 的全部 $B$ 压缩正是 $Y_{ab}$，全部 $C$ 压缩正是 $Y_{ac}$。上述事实遂给 $\operatorname{rank}X_a\le1$，含零情形。再次直接消费175.6的完全相同重建尾部，得 $\mathsf Q_\infty$。$\square$

### 176.5 等价的逆向与全部原对象的量子对应

证明定理176.2。命题176.3给局部闭性到整个纯集闭，命题176.4给闭性到全部有限 PSD，命题176.5给固定锚比较到全部有限 PSD。全部有限 PSD 显然给三体 PSD。若三体 PSD，则整个原纯集恰为

$$
P_3=\{vv^*:\|v\|=1\}\cong\mathbb{CP}^{D-1}.
\tag{176.17}
$$

它是有限维单位球面的连续像，故紧而闭，进而满足局部闭性。(175.32)在整个原 proper 确认集合上给 Born 公式 $T_p(x)=\operatorname{Tr}(px)$，故固定锚不等式成为等式。至此所有条件互相推出；定理175.2把原全端点互易、等参照、球面及三体到全有限的等价一并接上。$\square$

**推论 176.6（以当前二元零关系进入完整候选）。** 在 [XVI定义174.1][Q176XVI] 的弱实际全有限域中，固定同一个普通单位乘积 dyad $q_0$。令 $\mathsf Q_0$ 精确为其(174.2)：$B\in C_2\cap C_2^*$，且对整个 $C_2$ 与完整 $C_2^*$，零迹配对蕴含普通矩阵支撑正交。依次要求 $\mathsf Q_0$、普通成员关系 $q_0\in C_3$，再在由此前件获得的普通整个原基与菜单上要求 $\mathsf{LPC}(q_0)$ 或 $\mathsf S(q_0)$。则分别有

$$
\begin{aligned}
[\mathsf Q_0]\wedge[q_0\in C_3]\wedge[\mathsf{LPC}(q_0)]
&\Longleftrightarrow\mathsf Q_\infty,\\
[\mathsf Q_0]\wedge[q_0\in C_3]\wedge[\mathsf S(q_0)]
&\Longleftrightarrow\mathsf Q_\infty.
\end{aligned}
\tag{176.18}
$$

证明及精确域对应。只消费174.4的**第一项等价**(174.10)，即 $\mathsf Q_0\Longleftrightarrow C_2=\operatorname{PSD}_{n^2}$，不使用有三元种子的(174.11)。再消费173.5中从该二体等式出发的171.8–171.9供应，取得唯一 $\varepsilon\in\{\pm1\}$、$C_1=\varepsilon\operatorname{PSD}_n$、各层尖性生成性和非零原元上严格正的 $\varepsilon^N\operatorname{Tr}$。这一步没有三体 GME 种子，也没有先行普通概率菜单。

普通 $q_0\in C_3$ 非零且 $\operatorname{Tr}q_0=1$，所以171.10的奇数层选择给 $\varepsilon=+1$。现在才取所有层的整个普通迹一基、全部极点、完整对偶区间及全部有限单位分解。弱域本已保留相同的全部实际有限 min/max、置换与正逆、重括号、配对及标量层；已获严格正普通迹和两条低层等式。因此定义175.1每个前件都到位，$q_0$ 的原纯和 proper 性由175.3成为结论，可应用定理176.2。反向普通全 PSD 层级满足二体零支撑关系、Bell 双成员、普通乘积成员关系及两种附加条件。$\mathsf{PClose}$ 也可等价替换(176.18)中的局部条件。整个应用不借用174.11的满腿种子结论。$\square$

### 176.6 不选普通方向时的精确有向条件

**推论 176.7（有向闭性与有向单锚）。** 在上述弱域及 $\mathsf Q_0$ 下，不加普通 $q_0\in C_3$。用已获得的唯一符号 $\varepsilon$ 和推论175.8的完整有向对象 $\widehat K_N,\widehat P_N,\widehat{\mathcal E}_N,\widehat T$，固定 $\widehat q_0=\varepsilon q_0$。则

$$
\begin{aligned}
\widehat P_3\text{ 闭}
&\Longleftrightarrow\widehat{\mathsf{LPC}}(\widehat q_0)
\Longleftrightarrow
[\widehat T_p(\widehat q_0)\le\widehat T_{\widehat q_0}(p)
\quad\forall p\in\widehat P_3]\\
&\Longleftrightarrow C_N=\varepsilon^N\operatorname{PSD}_{n^N}
\quad\text{对每个有限 }N.
\end{aligned}
\tag{176.19}
$$

这里 $\widehat{\mathsf{LPC}}(\widehat q_0)$ 是(176.1)中以 $\widehat P_3,\widehat q_0$ 替换 $P_3,q_0$ 的同一邻域条件，闭包仍取有限维 Hilbert–Schmidt 拓扑。

证明。精确复用171.9及175.8的 $D_N=\varepsilon^NC_N$ 和同胚 $S_N(x)=\varepsilon^Nx$：运输族满足整个定义175.1，$S_{a+b}=S_a\otimes S_b$，完整基及极点双射，闭包和局部闭性保持。原有向乘积点 $\widehat q_0$ 由运输族的一体 PSD 及最小积合法，并由175.3运输回原有向纯点。效应同时运输为 $f\mapsto\varepsilon^Nf$，(175.42)逐项保持完整配对、确认约束和全部最小值。故三个左侧条件分别就是 $D$ 族的定理176.2条件，运输其结论即得(176.19)。这不重证矩阵生成或原域正性供应。

$\varepsilon=-1$ 时结论是交替有向 PSD。175.8已有该全有限方向模型；它的普通奇数层迹一基为空。空普通纯集虽闭，不能借此推出普通 PSD；普通 $q_0\in C_3$（或175.7的普通 $m\in C_3$）必须先选定正方向。$\square$

### 176.7 拓扑机制、来源与仍未支付的桥梁

**命题 176.8（几何内容与条件边界）。** 本章的闭性与固定锚条件在定义175.1下等价于整个原量子结论，但既不把额外拓扑默认为内生，也不把静态端点交换解释为时间顺序交换。

证明及边界。一般紧凸体的极点集未必闭。例如在 $\mathbb R^3$ 中取

$$
K_0=\operatorname{conv}\bigl(\{(x,y,0):x^2+y^2\le1\}
 \cup\{(1,0,1),(1,0,-1)\}\bigr).
\tag{176.20}
$$

这是紧集的有限维凸包，因而紧。对 $\theta\notin2\pi\mathbb Z$，线性泛函 $x\cos\theta+y\sin\theta$ 在整个 $K_0$ 上唯一最大于 $(\cos\theta,\sin\theta,0)$：圆盘上最大值一且唯一，两端点的值均为 $\cos\theta<1$。这些点暴露且趋于 $(1,0,0)$；后者是两个端点的中点，故非极点。因此紧性不能代替 $\mathsf{PClose}$。这里只给普通凸几何控制，不给定义175.1的同域全有限反模型。

在本章强域内，若任何地方存在非纯的原纯极限，(176.3)–(176.6)会把这个缺口沿始终可逆的局部筛选移近任一指定乘积点。闭性又使每个非零一腿条件压缩的极限仍纯，从而排除真正混合。固定锚比较走另一条路：局部酉把一锚条件运到所有乘积锚，有限缺陷排除混合两腿输出，普通辅助 Gram 结构再恢复一腿秩条件。两路随后消费同一个175.6，并保留其三个切分和全有限极性；不能以只有低层前缀的模型代替该域。

新增的承重内容是这些同域桥梁及其弱域条件组合，文献表态为 repo-derived，不作穷尽文献或历史优先权声明。共同因子事实直接用166.6；Marciniak 的矩形分类、全有限 Bell 极性及166.12传播严格保留175.6的来源和前件，效应紧性及定量缺陷直接用175.3–175.4。普通谱分解、Gram 秩与对角拓扑是中间线性代数和拓扑事实，不另立为新重建原理。

较局部的量词不等于在此基底上逻辑严格更弱，也不证明独立公理数更少。本章没有给出同域非 PSD 层级，所以没有证明强域单独不能推出 $\mathsf{PClose}$，也没有证明其独立性；从原 Bell 关系或当前基底内生推出这些闭性条件的桥梁仍未解决。175.10的全有限 Wigner 控制虽有有限闭纯集，却缺低层对齐；[XVI174.6][Q176XVI]的旋转层级缺 $C_2=\operatorname{PSD}$ 与零支撑关系，两者都不能裁决强域闭性问题。复数载体、固定 $n$、实际有限粘合、完整原纯集与效应集以及低层对齐仍在明确前提中。

所有普通量子条件下的完整密度矩阵、POVM、Born 配对、纠缠复合、矩形 CP/Choi/Kraus 和全输入预算，按175.9的同坐标字典逐项复用；其前件是本章已经取得的整锥等式及同一普通迹和全菜单。实际事件饱和、具体条件更新、连续时间作用、物理钟、Hamiltonian 和 $\hbar$ 各保留175.11的独立条件及零质量分支规则。特别是静态 $T_p(q)=T_q(p)$ 不使两次有更新的测量交换；175.11的(175.51)已给明确反例。$\square$

### 176.8 一个清楚的中文图景

**命题 176.9（单个参照点与纯关系无缺口的白话表述）。** 在完整强域及其已对齐的低层结构中，只要求整个原纯集在一个固定乘积点附近没有非纯极限缺口，或者只要求每个原纯点朝这一个参照点的最小确认读数不大于反向读数，就已与全部有限量子锥等价。

证明与释义。“纯”先只表示不能拆成两个不同原态的中点，并没有先说它是矩阵秩一。假如某处的一串纯点逼近了一个可拆的混合点，那么对这个缺口逐腿加强筛选，每次筛选仍可逆，它就仍是缺口，却会越来越靠近一个普通乘积点；再用固定局部旋转便靠近指定参照点。因此这个点附近不许有缺口，就等于处处不许有缺口。另一方面，对一个纯点只留某条腿的一维方向，其条件输出如果真是几个不同原态的混合，闭性就会把这个混合也判成纯，与中点定义矛盾。单锚比较则不用先假定闭性：先让固定参照沿局部旋转覆盖所有乘积参照，再同时筛选两条腿；混合输出会产生严格的双向比较差，故被单向不等式排除，Gram 论证把这种两腿限制补回一腿限制。已有分类、三切分和全有限杯帽随后锁定整个量子锥，而不只是一些选定纯点。这里新增的是明确条件下的更局部表述；闭性为何能从更少关系自动生出仍是问题，“比较端点可交换”也依然不等于“先测哪个都一样”。$\square$

[Q176XVI]: https://github.com/the-omega-institute/trureturing/blob/02e623db8cc5dd8e6b413d337edbe4991f33e178/docs/develop/theory/QUANTUM_ORIGIN_BINARY_BELL_ORBITS_AND_SINGLE_ATTENUATOR_XVI.md

## 追加锚（本行以下为增补区）

## 177. 一个固定混合中心附近的非平凡中点与全部有限量子锥

### 177.1 只用原二元平均关系陈述的条件

**定义 177.1（固定中心的非平凡中点邻域）。** 完整采用定义175.1，即 [XIII166.1][Q175XIII] 的强域：固定 $n\ge2$，同一实际复 Hermitian Kronecker 载体上的全部有限闭尖生成锥，非零原正元上严格正的乘法普通迹，同坐标的 $C_1=\operatorname{PSD}_n,C_2=\operatorname{PSD}_{n^2}$，所有有限实际 min/max 分块、正置换及正逆、规范重括号、原配对和空系统。始终取(175.3)的整个 $K_N$、全部 $P_N=\operatorname{ext}K_N$、完整迹对偶、整个 proper 区间与全部有限单位分解。没有加入高层 PSD、原纯集闭性、奇异滤波保纯或物理纯化。

固定单位向量 $a_0,b_0,c_0,c_1$，其中 $c_0\perp c_1$，令

$$
x_0=P_{a_0}\otimes P_{b_0}\otimes P_{c_0},\qquad
y_0=P_{a_0}\otimes P_{b_0}\otimes P_{c_1},\qquad
r_0=\frac{x_0+y_0}{2}.
\tag{177.1}
$$

最小界使两端点属于整个原 $K_3$；它们不同，所以 $r_0$ 是已知的非平凡平均。对凸集 $K$ 定义其非平凡中点集

$$
\operatorname{Split}_K
=\{z\in K:\exists u,v\in K,\ u\ne v,\ 2z=u+v\}.
\tag{177.2}
$$

本章唯一新增的候选条件是

$$
\boxed{\ \mathsf{Mid}(r_0):\qquad
r_0\in\operatorname{int}_{K_3}
\left\{\frac{u+v}{2}:u,v\in K_3,\ u\ne v\right\}.\ }
\tag{177.3}
$$

等价地，存在包含 $r_0$ 的环境开集 $U\subset W_3$，使每个 $z\in U\cap K_3$ 都有 $u,v\in K_3$、$u\ne v$、$z=(u+v)/2$。相对邻域量化整个原 $K_3$；不限定在含 $r_0$ 的某个面内。条件本身只有原状态、二元平均、固定中心和相对邻域；不要求分解端点接近指定端点、连续选择分解，或整个凸体上的混合映射开放性。

### 177.2 重建之前已经存在的原 Bloch 面

**命题 177.2（整个原凸体中的三维暴露面）。** 仅在定义175.1的强域内，置 $S=\operatorname{span}_{\mathbb C}\{c_0,c_1\}$、$\Pi=P_{c_0}+P_{c_1}$，并定义

$$
\operatorname{dens}(S)=\{\tau\succeq0:\operatorname{Tr}\tau=1,\ \operatorname{ran}\tau\subseteq S\},\qquad
F_0=P_{a_0}\otimes P_{b_0}\otimes\operatorname{dens}(S).
\tag{177.4}
$$

则 $F_0$ 是整个原 $K_3$ 的实际暴露面，实仿射维数为三，仿射同构于闭 Bloch 三球；$r_0$ 为其相对中心，球面上的点都是原纯点。此结论不以整个 $K_3$ 已为 PSD 为前提。

证明。对任意 $z\in K_3$，其普通一体边缘 $z_A,z_B,z_C$ 都是迹一 PSD：最大界用其余因子的单位切片给原一体锥成员关系。三个原 proper 边缘缺陷效应为

$$
\begin{aligned}
D_A&=(I_A-P_{a_0})\otimes I_B\otimes I_C,\\
D_B&=I_A\otimes(I_B-P_{b_0})\otimes I_C,\\
D_C&=I_A\otimes I_B\otimes(I_C-\Pi).
\end{aligned}
\tag{177.5}
$$

每个效应及其相对于 $I$ 的补都由相应 $1|23$ 最大界在整个原锥上非负。故 $d(z)=\operatorname{Tr}[(D_A+D_B+D_C)z]\ge0$，且 $d(z)=0$ 当且仅当三个缺陷分别为零。前两项为零分别给 $z_A=P_{a_0},z_B=P_{b_0}$；这是普通 PSD 边缘的支撑结论。

先只用 $z_A=P_{a_0}$。对每个普通二体效应 $0\preceq e\preceq I_{BC}$，以迹配对作 $BC$ 切片，最大界及其补给

$$
0\preceq(\mathrm{id}_A\otimes e)(z)
\preceq(\mathrm{id}_A\otimes I_{BC})(z)=P_{a_0}.
\tag{177.6}
$$

这里 $C_2$ 及其完整对偶已是通常 PSD，因而所有这些 $e$ 都可用。夹在零与秩一投影之间的 PSD 矩阵只能是该投影的非负倍数。普通效应实线性张成 $\operatorname{Herm}(B\otimes C)$，所以全部这些切片共同迫使 $z=P_{a_0}\otimes\sigma_{BC}$，其中 $\sigma_{BC}=\operatorname{Tr}_A z$。对全部普通正二体效应的非负配对给 $\sigma_{BC}\succeq0$，且其迹为一。此处未对 $z$ 预设 PSD。

若再有 $z_B=P_{b_0}$，则 $\sigma_{BC}$ 的 $B$ 边缘是 $P_{b_0}$。对每个 $b\perp b_0$，非负数 $\langle bc|\sigma_{BC}|bc\rangle$ 沿 $C$ 的任意正交基求和为零，故对全部 $c$ 均为零；PSD 性使 $\sigma_{BC}(b\otimes c)=0$。因此它支撑在 $\mathbb Cb_0\otimes C$，即 $\sigma_{BC}=P_{b_0}\otimes\tau$，$\tau\succeq0$、$\operatorname{Tr}\tau=1$。第三个缺陷为零又使 $\tau$ 消灭 $S^\perp$，故 $z\in F_0$。反过来，最小界使每个(177.4)中的矩阵都是原态，且三个缺陷均为零。于是

$$
F_0=\{z\in K_3:d(z)=0\}.
\tag{177.7}
$$

这正是整个原凸体上非负泛函的零面，故为实际暴露面，而非仅在某个 PSD 子锥里取面。

在有序基 $c_0,c_1$ 上，令 $`\sigma_x=c_0c_1^*+c_1c_0^*`$、$`\sigma_y=-ic_0c_1^*+ic_1c_0^*`$、$\sigma_z=P_{c_0}-P_{c_1}$，在 $S^\perp$ 上均取零。每个 $\tau\in\operatorname{dens}(S)$ 唯一写成

$$
\tau=\tfrac12(\Pi+t_x\sigma_x+t_y\sigma_y+t_z\sigma_z),\qquad
\mathbf t\in\mathbb R^3,\quad |\mathbf t|\le1.
\tag{177.8}
$$

在 $S$ 上的两个特征值是 $(1\pm|\mathbf t|)/2$，所以这是实三维闭球；中心 $\mathbf t=0$ 正好给 $r_0$。球面对应秩一 $\tau$，是 $F_0$ 的极点；面内极点也是整个 $K_3$ 的极点。这里只说明 $r_0$ 在 $F_0$ 中居中，并不把它说成 $K_3$ 的内部点；(177.3)仍要求整个 $K_3$ 的相对邻域。$\square$

### 177.3 固定中心排除全部混合双腿压缩

**定理 177.3（固定非平凡中点邻域的全有限重建）。** 在定义175.1的完整强域中，

$$
\mathsf{Mid}(r_0)
\quad\Longleftrightarrow\quad r_0\notin\overline{P_3}
\quad\Longleftrightarrow\quad C_3=\operatorname{PSD}_{n^3}
\quad\Longleftrightarrow\quad\mathsf Q_\infty.
\tag{177.9}
$$

闭包取整个原纯集在 $W_3$ 中的闭包。它们也各与定理176.2的 $\mathsf{PClose},\mathsf{LPC}(x_0),\mathsf S(x_0)$ 及定理175.2的全部互易、等参照和未知半径条件等价；$x_0$ 正是该定理可选的固定乘积锚。完整量子字典和操作边界分别沿用175.9、175.11。

证明。先处理定义对应。精确复用176.1的中点极端性：对任意凸集，

$$
\operatorname{Split}_K=K\setminus\operatorname{ext}K.
\tag{177.10}
$$

若从一般比例的非平凡线段分解出发，在该线段上以待分解点为中心向两侧取相同的充分小步长，就得到两个仍在 $K$ 内的不同等权端点；反向由极端性直接排除。对本章闭的 $K_3$，$P_3$ 的相对闭包就是环境闭包，且补集的相对内部为闭包的补集。因此

$$
\operatorname{int}_{K_3}\operatorname{Split}_{K_3}
=K_3\setminus\overline{P_3},
\tag{177.11}
$$

得到(177.9)的第一项等价。这是对同一条件的定义改写，既未自动证明邻域存在，也未把证明中使用的纯集另加为候选输入。

现在假设 $\mathsf{Mid}(r_0)$。任取原纯态 $p\in P_3$ 及单位向量 $a\in A,b\in B$，令

$$
Y_{ab}=(\langle ab|\otimes I_C)p(|ab\rangle\otimes I_C).
\tag{177.12}
$$

全部原乘积正测试给 $\langle c|Y_{ab}|c\rangle\ge0$ 对每个 $c$ 成立，故 $Y_{ab}\succeq0$。零输出已满足秩条件。若其秩 $r\ge2$，置 $\tau=Y_{ab}/\operatorname{Tr}Y_{ab}$。对每个 $t>0$ 使用

$$
G_t=[P_a+t(I_A-P_a)]\otimes[P_b+t(I_B-P_b)]\otimes I_C,
\qquad p_t=F_{G_t}(p).
\tag{177.13}
$$

这里 $F_G$ 精确为(176.3)。命题176.3证明中的原域接口已支付每个可逆局部 $G$ 的正合同及正逆；归一后是整个原 $K_3$ 的同胚，保持 $P_3$ 及其闭包。因而 $p_t\in P_3$，分母对每个正 $t$ 严格正，且通常矩阵极限给

$$
p_t\longrightarrow\rho=P_a\otimes P_b\otimes\tau
\in\overline{P_3}.
\tag{177.14}
$$

极限分母是 $\operatorname{Tr}Y_{ab}>0$。这里只把混合的 $\rho$ 放进纯集闭包，没有称它为原纯态。

取一次固定局部酉，把 $a,b$ 送到 $a_0,b_0$，并把 $\tau$ 的正谱方向送到以 $c_0,c_1$ 开头的正交组 $c_0,\ldots,c_{r-1}$。不要求随输入连续选择这些方向。酉变换后的点为 $P_{a_0}\otimes P_{b_0}\otimes\tau'$，其中 $\tau'=\sum_{j=0}^{r-1}\lambda_jP_{c_j}$、$\lambda_j>0$、$\sum_j\lambda_j=1$。在整个 $n$ 维 $C$ 空间上置

$$
\Pi_r=\sum_{j=0}^{r-1}P_{c_j},\qquad
L=\sum_{j=0}^{r-1}\lambda_j^{-1/2}P_{c_j}+(I_C-\Pi_r).
\tag{177.15}
$$

$L$ 在正谱方向白化，在核上为恒等，故在全空间可逆。再次用上述同胚，得

$$
\rho_r=F_{I_A\otimes I_B\otimes L}
 (P_{a_0}\otimes P_{b_0}\otimes\tau')
=P_{a_0}\otimes P_{b_0}\otimes\frac{\Pi_r}{r}
\in\overline{P_3}.
\tag{177.16}
$$

若 $r=2$，这就是 $r_0$。若 $r>2$，对每个 $s>0$ 取全空间可逆的 $J_s=\Pi+s(I_C-\Pi)$。则

$$
F_{I_A\otimes I_B\otimes J_s}(\rho_r)
=P_{a_0}\otimes P_{b_0}\otimes
\frac{\Pi+s^2(\Pi_r-\Pi)}{2+s^2(r-2)}
\in\overline{P_3},\qquad
\lim_{s\downarrow0}F_{I_A\otimes I_B\otimes J_s}(\rho_r)=r_0.
\tag{177.17}
$$

由于 $\overline{P_3}$ 闭，两种情形均给 $r_0\in\overline{P_3}$，与(177.11)矛盾。故每个原纯态、每对 $a,b$ 的 $Y_{ab}$ 均秩至多一。对 $AC$ 或 $BC$ 任意一对，先用实际正置换及其正逆把被压缩的两腿移到前两位，再用同一论证；置换保持整个原基、极点和闭包。因此三对的全部双腿压缩都受此限制，零向量和非单位向量由零输出及缩放涵盖。论证只用闭集 $\overline{P_3}$，没有要求 $\overline{P_3}\setminus P_3$ 闭，也没有把奇异滤波当成保纯操作或假定统一成功率下界。

最后任取同一个原纯态 $p$ 及任意 $a$。由原 $A|BC$ 最大界和完整二体 PSD 对偶，$X_a=(\langle a|\otimes I)p(|a\rangle\otimes I)\succeq0$。它的全部 $B$ 向量压缩正是已受限的 $Y_{ab}$，全部 $C$ 向量压缩正是 $Y_{ac}$。这逐项满足命题176.5证明中双侧普通 PSD Gram 结论的两个输入条件，故直接由(176.15)–(176.16)得 $\operatorname{rank}X_a\le1$。其辅助 $E$ 只是有限 Gram 坐标，未输入物理纯化或新的原系统。于是对全部 $p\in P_3$、全部 $a$，字面上的(175.20)已经成立，包括零输出。定义175.1的全部强域前件也始终保留，可以直接消费175.6，得到每个有限 $C_N=\operatorname{PSD}_{n^N}$；不重证其矩形分类、三切分、Bell 极性或 GHZ 传播尾部。

### 177.4 量子逆向、精确距离与既有等价

继续证明定理177.3。假设 $C_3=\operatorname{PSD}_{n^3}$，此时整个原纯集才识别为全部单位 dyad $P=vv^*$。$x_0,y_0$ 为正交单位 dyad，所以 $\operatorname{Tr}r_0^2=1/2$ 且 $\operatorname{Tr}(Pr_0)\le1/2$。因此

$$
\|P-r_0\|_2^2
=1+\tfrac12-2\operatorname{Tr}(Pr_0)\ge\tfrac12,
\qquad \operatorname{dist}_{\rm HS}(r_0,P_3)=\frac1{\sqrt2}.
\tag{177.18}
$$

等号在 $P=x_0$ 取得。任选 $0<\delta<1/\sqrt2$，整个原相对球 $B_\delta(r_0)\cap K_3$ 内没有秩一态。对其中任意 $z$，取两个正特征值 $\mu_i,\mu_j$ 的正交单位谱向量 $v_i,v_j$，及 $0<\epsilon<\min(\mu_i,\mu_j)$，则

$$
z_\pm=z\pm\epsilon(P_{v_i}-P_{v_j})\in K_3,
\qquad z_+\ne z_-,\qquad z=\frac{z_++z_-}{2}.
\tag{177.19}
$$

这证明 $\mathsf{Mid}(r_0)$；每个态单独取谱方向和步长就够了，不需要分解的连续提升。全有限 PSD 给三体 PSD，而上一节已从候选得到全有限 PSD，故(177.9)全部成立。

至此量子目标及完整强域都已支付，再直接使用定理176.2，得到与 $\mathsf{PClose},\mathsf{LPC}(x_0),\mathsf S(x_0)$ 的精确等价，并由175.2接上原端点互易及其余条件。这些不是新加的独立假设。175.9的前件正是这里取得的同坐标整锥等式、普通迹与完整菜单，所以全部有限密度矩阵、原纯射线、完整效应与 POVM、Born 配对、纠缠张量复合及矩形 CP/Choi/Kraus 和全输入预算逐项沿用。实际事件饱和、唯一条件更新及连续时间仍分别需要175.11所列的额外输入；零质量分支不作归一除法，静态比较端点交换不等于测量时序交换，也不决定物理钟、Hamiltonian 或 $\hbar$。$\square$

### 177.5 条件的几何含义、来源与中文释义

**命题 177.4（固定中心条件的作用与未决边界）。** (177.3)是原二元平均关系在一个已知混合点附近的条件；在完整强域中它与全部有限量子层级等价，但该改写不证明独立公理数减少，也不证明这一邻域条件已由强域自动推出。

证明与释义。普通有限维凸集的中点极端性及可逆局部 $\mathrm{GL}$ 合同几何是成熟工具，分别按176.1、命题176.3证明中的接口使用；谱分解、两维 Bloch 坐标和(177.19)只是中间矩阵事实。本章的 repo-derived 综合是：把任意原纯态的任意混合双腿输出，经全空间可逆白化和浓缩汇到同一个固定混合中心，再接命题176.5的双侧 Gram 桥和175.6的完整重建尾部。对应来源与全部假设各按这些供应保留，不作历史优先权声明。命题176.8已经给出普通紧凸体的非闭极点集控制；它说明不能仅凭凸性、紧性或(177.10)自动宣布邻域存在，并不是定义175.1的同域反模型。

在已知的小球 $F_0$ 里取两个相反端点，它们的平均是中心。只要求这个中心在整个原状态体中稍有扰动时，仍能拆成两份不同状态的平均；不规定这两份必须靠近哪两个端点。若某个原纯态的双腿条件压缩留下真正混合，始终可逆的筛选就会把纯态的极限挤到同一个中心，与这里一小片地方都可拆相冲突。于是双腿压缩都不能留下真正混合；双侧 Gram 论证补回全部一腿秩条件，既有重建尾部锁住全部有限量子锥。小球是整个原凸体中的实际暴露面，但只在小球内检查无法排除从小球外逼近中心的原纯点，所以不能替代(177.3)。

全部明确底座仍保留，新增邻域关系能否从当前基底或更少关系自动生出仍未解决；本章没有给出违反它的同域全有限层级，不主张反模型或独立性。条件自身不提纯点或确认最优化，并不意味着可以删去原域的完整对象、低层对齐或全有限粘合。端点关系的这种简写也不增加175.11之外的事件、更新或时间结论。$\square$

## 追加锚（本行以下为增补区）

## 178. 同源首响应、指定比较群与原锥自对偶

### 178.1 一个完整候选及其精确删项

**定义 178.1（同源响应候选）。** 固定 [C123 定义1.1–1.5][Q178P] 的同一个原签名 $\Omega$、原全语境响应空间、准备、事件及合法性谓词。操作尾部完整采用 [C124 定义10.2][Q178C124]，包括它对整个原指针 $P$、全部实际有限参考幂、联合对象、输出和同记录执行的逐字替换。以下条件对其中每个所需原对象 $A$ 分别成立，特别包括局部、实际联合、原输出、参考及其被消费的联合对象；局部条件不代替联合条件。

原 $E_A$ 非零有限维，原 $C_A$ 是闭凸尖生成锥，原 $u_A\in C_A^\circ$。在整个原 $E_A$ 上给同一来源的有限实值读数 $q_A$，要求全部有限右首响应存在：

$$
D_{q_A}(x;y)=\lim_{t\downarrow0}
 \frac{q_A(x+ty)-q_A(x)}t\in\mathbb R
 \qquad(x,y\in E_A).
\tag{178.1}
$$

这里“有限”指极限值有限，量词是全部带符号的原向量与实比例，不是有限采样。读数直接定义在原响应空间；若起点是另一配方空间，须另给与原 $E_A$ 的线性同构、全部读数及原接口的相容识别，不能用振幅读出零空间商替换原 $E_A$。另要求

$$
\inf_{t\in\mathbb R}q_A(tx)>-\infty\quad(x\in E_A),
\qquad x\ne0\Longrightarrow
 \exists y\in E_A:\ D_{q_A}(x;y)\ne0.
\tag{178.2}
$$

下界只须逐径向存在，不要求统一下界或上界。保留同一个指定闭连通群 $G_A\le\operatorname{Aut}(C_A)$ 及其在 $C_A^\circ$ 上的传递性。在这一个群内定义原比较关系

$$
\Gamma_{q_A}(S,R)\quad\Longleftrightarrow\quad
D_{q_A}(Sx;y)=D_{q_A}(Ry;x)
\quad\text{对所有 }x,y\in E_A,
\qquad S,R\in G_A,
\tag{178.3}
$$

并要求 $\Gamma_{q_A}(I,I)$ 以及 $\forall S\in G_A\ \exists R\in G_A:\Gamma_{q_A}(S,R)$。原比较型取下述恢复式给出的同一个 $g_A^0$；若该型已经命名，要求其数值逐点就是该恢复式，不能事后另选一个自对偶型。

除不再单列假设 P 的等式(1.1)外，原合同逐项保留：

| 保留的原合同 | 本候选的字面要求 |
| --- | --- |
| P 的其余部分 | 原 $E_A,C_A,u_A$、正定对称 $g_A^0$；已命名正准备 $\alpha$ 的原质量 $\alpha(u_A)\le1$；实际准备有限正锥包恰为完整 $C_A^*$，每个实际联合对象也如此；事件次幺不等式、完整装置求和及实际可读子菜单均不变。正定性由下述引理支付。 |
| G | 原指定群的闭性、连通性、原锥自同构性及内点传递性不变；原伴随封闭由 $\Gamma$ 全性等价表达，不扩张群。 |
| 原 D | C123 假设1.5的同一原双线性有向关系、全载体导子律及三元交换子抵消，消费原 $u_A$ 适配的乘法，不消费下文辅助单位的乘法。 |
| X、Xs、$N_u$ | 原含幺嵌入保持该乘法及 D，交叉 D 为零、乘积张成、原乘积准备、结合/交换/经典标签；全部被消费同记录旁接和合法连线；指定单位稳定子每个元素的系数一原完整提升，均按定义10.2保留。 |
| AC、R | 整个实际 $P$ 上定义10.1的非中心极射线效果与原配对概率一；对每个原事件、原细支、失败、标签、遗忘、返回及全部有限合法历史，R 的充分实际参考和完整联合准备锥保正，均保留。 |
| F 及支持双返回 | 假设2.6的全部原有限细记录、原遗忘、单中心输入/输出支持、具名原返回、两条同一正系数的支持等式及反向资料，量化整个原菜单与全部合法有限历史。返回系数仍是原数，以下记为 $q_F>0$ 以免与读数 $q_A$ 混淆。 |

所有未在原合法性谓词中声明的合成仍未供应。此处唯一候选以 C124 的 AC 尾部为准，不另加 C123 的 Q1。拟删除的只是两者共有 P 中单独写出的 $C_A=C_{A,g_A^0}^*$；对保留 Q1 的 C123 合同，同一锥桥也支付这一共有条款，其余 Q1 及全部原接口仍须原样供给。这里没有把新增响应条件与旧条件的字数差算成独立公理数减少。

**引理 178.2（原正定型与群伴随的恢复）。** 定义178.1给出唯一原正定对称双线性型

$$
g_A^0(x,y)=\tfrac12D_{q_A}(x;y),\qquad
q_A(x)=q_A(0)+g_A^0(x,x),
\qquad
\Gamma_{q_A}(S,R)\Longleftrightarrow R=S^{\dagger_0}.
\tag{178.4}
$$

因而 $G_A^{\dagger_0}=G_A$，这正是原 G 的伴随封闭条件。

证明。$\Gamma(I,I)$ 正是 [C139 定理3.3][Q178C139] 的全部有限右首响应互易；直接应用其唯一双线性恢复式，不重新证明。逐径向下界排除 $g_A^0(x,x)<0$，否则 $q_A(tx)=q_A(0)+t^2g_A^0(x,x)$ 无下界。因此该型半正定。若 $g_A^0(x,x)=0$，对全部实数 $s$ 的非负式 $g_A^0(y+sx,y+sx)=g_A^0(y,y)+2s g_A^0(x,y)$ 强制 $g_A^0(x,y)=0$ 对全部 $y$ 成立，探针分离遂给 $x=0$。于是它在原 $E_A$ 上正定，无须取商。将(178.4)代入(178.3)得 $g_A^0(Sx,y)=g_A^0(x,Ry)$；非退化性给所述唯一伴随。$\Gamma$ 全性给每个 $S^{\dagger_0}\in G_A$，伴随的对合性再给群集合等式。只有 $\Gamma(I,I)$ 不会支付这项全性，更不会支付原群的传递性、原 D 或实际调用。$\square$

### 178.2 原锥、原度量及原群的非循环桥梁

**定理 178.3（指定自伴随内迁群强制原型自对偶）。** 设 $E$ 为有限维实空间，$g$ 为给定正定对称双线性型，$C$ 为闭凸尖生成锥，$G\le\operatorname{Aut}(C)$ 为给定闭连通子群，在 $C^\circ$ 上传递且 $G^{\dagger_g}=G$。则

$$
C=C_g^*:=\{z:g(z,c)\ge0\text{ 对每个 }c\in C\}.
\tag{178.5}
$$

结论属于原 $E,g,C,G$，不假设锥锐角性或自对偶，不以 HSD Koecher–Vinberg 定理来推出其自己的自对偶前件。$E=0$ 时立即成立；以下设 $E\ne0$。

证明。先构造辅助单位与度量代数。令 $K=G\cap O(g)$。它紧；对任一原锥内点的 $K$ 轨道取 Haar 平均，得 $K$ 固定的 $e_*\in C^\circ$。紧轨道有共同半径的 $g$ 开球包含于 $C$，凸性及积分保留该半径，故平均仍是内点。这里不把 $e_*$ 认作原 $u$。

令 $H=G_{e_*}$。它在原锥的序单位范数

$$
\|x\|_{e_*}=\inf\{t\ge0:-te_*\le_C x\le_C te_*\}
\tag{178.6}
$$

下等距，且闭，故是有限维范数线性等距群的闭子群，因而紧。伴随封闭把原 Lie 代数分成

$$
\mathfrak g=\mathfrak k\oplus\mathfrak p,
\quad \mathfrak k=\{D\in\mathfrak g:D^{\dagger_g}=-D\}
 =\operatorname{Lie}(K),
\quad \mathfrak p=\{S\in\mathfrak g:S^{\dagger_g}=S\}.
\tag{178.7}
$$

若 $X\in\operatorname{Lie}(H)$，其斜伴随部分属于 $\mathfrak k$，消去 $e_*$；其自伴随部分 $S$ 也消去 $e_*$。于是 $\exp(tS)\in H$ 对全部实数 $t$ 有界，实自伴随谱强制 $S=0$。故 $\operatorname{Lie}(H)=\mathfrak k$。传递 Lie 群作用的轨道映射是浸没，其导数 $X\mapsto Xe_*$ 满射到 $E$，核为 $\mathfrak k$。因此

$$
\mathfrak p\longrightarrow E,\qquad L\longmapsto Le_*
\quad\text{是线性同构}.
\tag{178.8}
$$

对每个 $x$ 取唯一 $L_x\in\mathfrak p$ 满足 $L_xe_*=x$，定义 $x\circ_e y=L_xy$。由 $[\mathfrak p,\mathfrak p]\subset\mathfrak k$，

$$
x\circ_e y-y\circ_e x=[L_x,L_y]e_*=0,
\quad x\circ_e e_*=x,
\quad L_{e_*}=I,
\quad g(x\circ_e y,z)=g(y,x\circ_e z).
\tag{178.9}
$$

最后两项分别由交换性与自伴随性得到，故这是含幺交换且有正 Frobenius 型的实代数，尚须证明 Jordan 恒等式。对 $k\in K$，(178.8)的唯一性给 $kL_xk^{-1}=L_{kx}$；微分得

$$
[D,L_x]=L_{Dx}\qquad(D\in\mathfrak k).
\tag{178.10}
$$

故每个这样的 $D$ 都是 $g$ 斜伴随导子。以下平方均用 $\circ_e$。固定 $a,b,c$，取 $D=[L_a,L_c]\in\mathfrak k$，则

$$
\begin{aligned}
0&=g(D(b^2),b)+g(b^2,Db)=3g(b^2,Db),\\
g([L_{b^2},L_b]a,c)&=-g(b^2,[L_a,L_c]b)=0.
\end{aligned}
\tag{178.11}
$$

第一式用 $D(b^2)=2b\circ_e Db$ 与 Frobenius 性；第二式把两个自伴随乘法算子逐项移到另一槽。非退化性及任意 $a,c$ 给 $[L_b,L_{b^2}]=0$，即 Jordan 恒等式。又若 $\sum_i x_i^2=0$，与 $e_*$ 配对得 $\sum_i g(x_i,x_i)=0$，故所有 $x_i=0$。这个辅助代数因此是有限维含幺形式实 Jordan 代数；这里的 Jordan 性并非由交换性或度量性直接略去。

现在证明平方锥在同一个原 $g$ 下自对偶。记 $Q=\{x^2:x\in E\}$，暂不认定 $Q=C$。由 [Hanche-Olsen–Størmer 引理2.4.5][Q178HS] 的幂结合性，$\mathbb R[a]$ 是有限维含幺交换结合代数；其上乘以 $a$ 的算子关于限制的 $g$ 自伴随。通常实自伴随谱定理给互异实谱值 $\lambda_i$；其谱投影是该算子的实多项式。作用于单位便得到 $\mathbb R[a]$ 中非零幂等元 $c_i$，满足

$$
a=\sum_i\lambda_i c_i,\qquad
\sum_i c_i=e_*,\qquad c_i\circ_e c_j=\delta_{ij}c_i.
\tag{178.12}
$$

这些等式来自同一结合子代数中的多项式谱投影，既不使用 $C$ 的自对偶，也不要求 $c_i$ 已是原操作或物理纯态。对任一幂等元 $c$，在 $c$ 处一阶极化 $[L_x,L_{x^2}]=0$ 并作用于 $c$，得到

$$
2L_c^3-3L_c^2+L_c=0.
\tag{178.13}
$$

所以原 $g$ 自伴随的 $L_c$ 只有 $0,\tfrac12,1$ 三种可能特征值，因而半正定。若 $a=y^2$，对 $y$ 用(178.12)，便有 $L_a=\sum_i\mu_i^2L_{c_i}\ge_g0$。反之若 $L_a\ge_g0$，在 $a$ 的分解中测试 $c_i$，得 $\lambda_i g(c_i,c_i)\ge0$，故 $\lambda_i\ge0$，并有 $a=(\sum_i\sqrt{\lambda_i}c_i)^2$。因此

$$
Q=\{a:L_a\ge_g0\},\qquad
Q_g^*=\{a:g(a,y^2)\ge0\ (y\in E)\}
      =\{a:g(L_ay,y)\ge0\ (y\in E)\}=Q.
\tag{178.14}
$$

这也证明 $Q$ 闭凸。$L_{e_*}=I$ 给 $e_*\in Q^\circ$。其内点恰是(178.12)中全部 $\lambda_i>0$ 的元素：全正时 $L_a\ge(\min_i\lambda_i)I$；某个谱值为零时，与非零 $c_i\in Q=Q_g^*$ 配对为零，故在边界。自对偶正是原 $g$ 的结论，没有换成某个新迹型。

还须支付 $C=Q$ 的两个方向。定义 Jordan 二次算子

$$
P(a)=2L_a^2-L_{a^2}.
\tag{178.15}
$$

上面已证明有限维、含幺、Jordan 恒等式和形式实性，故 [HS 推论3.1.7][Q178HS] 供应其内在谱范数下的 JB 结构；[HS §2.4.16 式(2.39)及命题3.3.6][Q178HS] 给此同一 $P(a)$ 的平方锥正性 $P(a)Q\subseteq Q$。这些供应只消费刚建立的 Jordan 代数，不对原 $C$ 提任何自对偶要求。

对 $x=\sum_i\lambda_i c_i$，正交幂等元的乘法算子彼此交换：Jordan 恒等式在 $c_i$ 沿 $c_j$ 的一阶极化及 $c_i\circ_e c_j=0$ 给 $[L_{c_i},L_{c_j}]=0$。这些算子同时自伴随，特征值各为 $0,\tfrac12,1$ 且相加为一；每个共同特征空间上只能有一个一，或两个二分之一。设

$$
\exp_J(sx)=\sum_i e^{s\lambda_i}c_i.
$$

在前一种空间上，$P(\sum_i a_i c_i)$ 的特征值是 $a_i^2$；在后一种空间上是 $a_i a_j$。逐空间代入 $a_i=e^{t\lambda_i/2}$，得到

$$
\exp(tL_x)=P(\exp_J(tx/2)),\qquad
\exp(tL_x)^{-1}=P(\exp_J(-tx/2)).
\tag{178.16}
$$

二次算子正性遂给 $\exp(tL_x)\in\operatorname{Aut}(Q)$。每个 $D\in\mathfrak k$ 是导子，$\exp(tD)$ 是 Jordan 自同构，也保持 $Q$ 及其逆向。于是(178.7)–(178.8)给 $\mathfrak g\subseteq\operatorname{Lie}(\operatorname{Aut}(Q))$。$\operatorname{Aut}(Q)$ 是 $GL(E)$ 的闭子群；指定 $G$ 连通，故 $G\subseteq\operatorname{Aut}(Q)$。这里证明的是原群保持 $Q$，没有把原群换成更大的可调用群。

现在传递性给 $C^\circ=Ge_*\subseteq Q^\circ$。反向任取 $z\in Q^\circ$，由正谱分解置 $a=\sum_i\log\lambda_i\,c_i$；幂结合性给

$$
z=\exp(L_a)e_*\in Ge_*=C^\circ,
\tag{178.17}
$$

其中 $L_a\in\mathfrak g$ 已由(178.8)取得。故两内点集相等。两个闭凸生成锥各为自己内点的闭包，遂有 $C=Q=Q_g^*=C_g^*$，完成原锥的双向识别。$\square$

### 178.3 原单位、原有向关系及完整量子消费者

**定理 178.4（补回共有 P 条款并接回完整 C124）。** 定义178.1的候选对每个所需原对象给 $C_A=C_{A,g_A^0}^*$，从而完整满足 C124 定义10.2。其对象结论为同一原载体上的有限复矩阵直和及已声明的普通复张量联合；[C124 命题11.1、11.3、定理12.1及命题12.2][Q178Structure] 的完整结论分别适用，不只适用于新选词。

证明。引理178.2给同一个原 $g_A^0$ 及指定群的伴随封闭；定理178.3逐个代入原 $(E_A,g_A^0,C_A,G_A)$，恰好补回共有 P 的(1.1)。不把一个局部锥的结论外推成联合锥结论。其余原条件已在定义178.1逐项保留，故可消费原定理；下面明确其中的单位与类型接口。

辅助 $e_*$ 只用于锥桥，原单位仍为 $u_A$。在每个对象上取原 $h\in G_A$ 满足 $hu_A=e_*$，并写

$$
\widehat g_A(x,y)=g_A^0(hx,hy),\qquad S=h^{\dagger_0}h,\qquad
T^{\dagger_{\widehat g_A}}=S^{-1}T^{\dagger_0}S\in G_A.
\tag{178.18}
$$

这就是 [C123 定理3.1 的(3.3)–(3.4)单位适配][Q178Adapt]，只是将其辅助型 $q_A$ 改记为 $\widehat g_A$，与原读数区别。$hC_A=C_A$ 及刚证的原型自对偶给 $\widehat g_A$ 自对偶；该既有证明随后支付 $(G_A)_{u_A}=G_A\cap O(\widehat g_A)$，构造定义1.4的 $u_A$ 适配乘法 $\circ$。原 D 的导子律与 $[L_a,L_c]+[D_a,D_c]=0$ 逐字作用在这个 $\circ$ 上；不能拿辅助 $\circ_e$ 代替，也没有假设 $h$ 自动交织原 D。

于是 [命题11.1][Q178Structure] 的参数是同一个 $(E_A,u_A,\widehat g_A,\circ,D)$：它直接消费 C123(3.3)–(3.5)和既有 V95 的完整动力对应，得到 $a\cdot b=a\circ b-iD_ab$ 及

$$
\mathcal A_A\cong\bigoplus_sM_{n_s}(\mathbb C),\qquad
E_A=(\mathcal A_A)_{\rm sa},\quad C_A=(\mathcal A_A)_+,
\quad u_A=I_A.
\tag{178.19}
$$

X 的原嵌入、交叉 D、张成及完整原乘积准备恰为该命题引用(3.9)的张量前件，故实际联合对象是这些代数的普通复张量积，原相关态全部保留。复类型选择来自仍保留的原 D 和实际联合合同；单凭对称锥几何不会排除实、四元数、其他 Jordan 类型。

随后按 [命题11.3][Q178CP] 使用整个原 $P$ 的实际有限幂：AC 经既有定理11.2在某个实际指针块给 $r\ge2$ 的系数一纯准备及破坏性读口；$P^{\otimes k}$ 中实际块维数 $r^k$ 无界。R 对所有原事件在完整联合准备锥上保正，正好支付每个输入块所需的充分参考层，取得全部原事件、细记录及合法历史的 CP/TNI，不限于乘积输入或新供应词。每个实际联合对象自身的 P、G、D 又给所需联合内酉群在指定群内的包含；$N_u$ 才把其中每个被消费单位稳定子变成精确原调用。

最后直接使用 [定理12.1][Q178Words]：对每个数学效果 $0\le e\le I_A$，有同一原签名中的新选中完整有限装置 $W_e$，成功支及每个已声明实际相关参考上的作用为

$$
\Phi_{W_e}(\rho)=\sqrt e\,\rho\sqrt e,
\qquad
\Phi_{W_e\mid R}(X)=(\sqrt e\otimes I_R)X(\sqrt e\otimes I_R).
\tag{178.20}
$$

奇异效果、零效果和零中心分量也由其有限构造供应，不需要物理奇异极限。整个实际 $P$、准备、联合比较、测试及其全部原失败输出、原系数、细记录和丢弃仍是原来的装置。再用 [命题12.2][Q178Records] 保留原 F 的实际一算子返回细支、原 $q_F$、细化及遗忘；可访问阶段细口只在原合法连线中相乘，未声明阶段细连线时只调用整个原词自己的全称 F。任意数学 Kraus 指标不因此成为原记录。这样复用的是完整旧历史和全事件等式，并未重建量子尾部或用新词替换旧实现。$\square$

### 178.4 原概率的双运输及真正对称的端点比较

**命题 178.5（密度、效果、Born 配对与纯确认）。** 在定理178.4的同空间坐标内，令 $\tau_A=\sum_s\operatorname{Tr}_{n_s}$，精确使用 C123(3.6)及 C124(11.1)的唯一迹自伴随正定算子 $B_A$：

$$
g_A^0(x,y)=\tau_A((B_Ax)y),\qquad B_A(C_A)=C_A.
\tag{178.21}
$$

对原准备 $\alpha(y)=g_A^0(x_\alpha,y)$ 和原数学效果 $e$，原密度、质量及对称坐标分别为

$$
\begin{aligned}
\rho_\alpha&=B_Ax_\alpha\ge0,
&m_\alpha&=\tau_A(\rho_\alpha)=\alpha(u_A)\le1,\\
v_\alpha&=B_A^{-1/2}\rho_\alpha,
&w_e&=B_A^{-1/2}e,\\
\alpha(e)&=\tau_A(\rho_\alpha e)
            =g_A^0(v_\alpha,w_e).
\end{aligned}
\tag{178.22}
$$

这里 $B_A^{-1/2}$ 是实响应空间上的正自伴随算子的逆平方根，不是将其误作矩阵左乘。数学归一正泛函底与全部密度矩阵一一对应；它不保证每个底点已有质量一的实际准备。

证明。密度、质量及 $B_A(C_A)=C_A$ 直接复用 [命题11.1][Q178Structure]；最后一式由 $B_A$ 的迹自伴随性和正谱演算给出，因而运输的是原概率，不是将原 Riesz 向量直接当成效果。$m_\alpha>0$ 时才可在数学上取 $\rho_\alpha/m_\alpha$ 作条件归一态，原概率仍含 $m_\alpha$；质量零时密度为零，不作除法。P 的实际准备正锥包为完整对偶，只给锥生成，不给系数一全准备供应；AC 支付的是它自己的原端点，不能默默推广成所有底点的实际质量一制备。

完整数学效果是 $0\le e\le I_A$，完整数学 POVM 是任意有限 $e_i\ge0$、$\sum_i e_i=I_A$，其概率是 $\tau_A(\rho e_i)$。若 $p,r$ 是数学归一底的纯态，它们恰为单块秩一投影且 $\tau_A(p)=\tau_A(r)=1$。在整个 proper 数学效果区间上定义纯确认比较

$$
T_p(r)=\min\{\tau_A(re):0\le e\le I_A,\ \tau_A(pe)=1\}.
\tag{178.23}
$$

确认条件与 $0\le e\le I_A$ 给 $ep=pe=p$，因而 $e=p+(I_A-p)e(I_A-p)\ge p$。取 $e=p$ 达到最小，故

$$
T_p(r)=\tau_A(pr)=\tau_A(rp)=T_r(p)
      =g_A^0(v_p,v_r),\qquad
v_p=w_p=B_A^{-1/2}p.
\tag{178.24}
$$

这涵盖不同中心块，彼时读数为零。这里先有完整数学区间；限制到一个旧实际子菜单时，$p$ 未必可读，不能沿用同一个最小值。定理12.1另给每个效果一份选中实际 $W_e$，却不补齐每个纯态的质量一准备，也不单凭这些逐点供应就组装任意指定原 POVM 仪器。原纯准备的 Riesz 向量是 $x_p=B_A^{-1}p$；一般不能把(178.24)写成 $g_A^0(x_p,x_r)=T_p(r)$。

对每个原事件 $f:A\to B$，同一运输仍为

$$
\Phi_f=B_B T_f^{\dagger_0}B_A^{-1},\qquad
\tau_B(\Phi_f(\rho)y)=\tau_A(\rho T_f(y)).
\tag{178.25}
$$

逐次代入便保留全部原合法有限历史的原概率、成功质量、记录和条件分母。对联合系统逐个使用其自身的 $B_{AB}$；不要求 $B_{AB}=B_A\otimes B_B$。效果只固定统计，原有同效果设备的输出不由(178.22)决定；新供应的(178.20)与旧设备相等仍须后者自己的完整输出校准。$\square$

### 178.5 对称锥、复数选择、三球面与全有限范围

**命题 178.6（几何结论及单块全有限的附加量词）。** 定义178.1下，每个原锥在恢复的原 $g_A^0$ 中是齐性自对偶锥；采用定理178.4的原复结构后，它是有限复正矩阵锥的直和。若另保留一个原对象 $A$ 的锥不可约性、原实维数 $\dim E_A=n^2$、固定整数 $n\ge2$，并实际声明全部 $A^{\otimes N}$ 及其所需联合、准备、群、D 与全部原接口，则

$$
C_{A^{\otimes N}}=\operatorname{PSD}_{n^N}
\qquad\text{在相容复坐标中，对每个有限 }N\ge1.
\tag{178.26}
$$

没有这些额外原对象和校准条件时，准确结论仍是(178.19)及实际声明的联合，不是任意全有限单块层级。

证明与几何。齐性来自原群的传递性，自对偶来自定理178.3，故原锥是对称锥；这些是同一原空间中的几何性质。定理178.4的 D 及 X 才把此几何接成复矩阵类型。若原锥不可约，(178.19)不能有两个非零直和块；故为一个 $M_d(\mathbb C)_+$，实维数 $d^2=n^2$ 给 $d=n$。实际全部有限幂再由 X 的既有普通复张量结论逐次给 $M_n^{\otimes N}\cong M_{n^N}$，其正锥就是(178.26)。这里不可约性、$n$ 校准及实际全有限幂各有用途；C124 只为参考声明的 $P^{\otimes k}$ 不自动成为任意 $A$ 的全有限幂。

复结构取得后，在任一大小至少二的简单块选二维复子空间 $S$，令 $\Pi_S$ 为其投影。数学归一底中的暴露面 $\{\rho:\operatorname{ran}\rho\subseteq S\}$ 精确写成

$$
\rho=\tfrac12(\Pi_S+\mathbf r\cdot\boldsymbol\sigma),
\quad \mathbf r\in\mathbb R^3,\quad |\mathbf r|\le1,
\qquad T_{p_{\mathbf r}}(p_{\mathbf s})
       =\tfrac12(1+\mathbf r\cdot\mathbf s)
\quad(|\mathbf r|=|\mathbf s|=1).
\tag{178.27}
$$

正性等价于两个特征值 $(1\pm|\mathbf r|)/2$ 非负；$\tau(\rho(I-\Pi_S))=0$ 暴露这个支撑面。故几何是闭 Bloch 三球，球面是该面及整个数学底的纯点，端点交换保持点积。这是复重建之后的数学面，不要求它是单独可附接的原 $M_2$ 对象；C124 的实际指针可以根本没有 $M_2$ 简单块。也不把面上每点的数学存在变成系数一实际准备。

时间仍只按 [C123 命题4.1][Q178Time] 的额外合同取得：原连续、确定、可逆一参数动态群和物理时钟标定才给逐块 $\rho_s(t)=e^{-itH_s/\hbar}\rho_s(0)e^{itH_s/\hbar}$。静态(178.24)交换的是比较端点，不交换两个有更新事件的操作次序；它不选 $H_s$、$\hbar$ 或物理钟，也不把探针比例 $t$ 认作时间。全部数学 POVM/CP、选中 $W_e$、指定原仪器组装、旧支更新和连续时间仍分别处在各自合同范围内。$\square$

### 178.6 来源职责、仍存条件与中文图景

本章的经典供应与新增综合分开承担：C139 定理3.3支付同源首响应到唯一对称型的恢复式；HS 的幂结合性、有限形式实 Jordan 到 JB 及二次算子正性分别在定理178.3已具备其全部代数前件后使用。HS 的对应位置是引理2.4.5（印刷页32/PDF页42）、§2.4.16式(2.39)（35/45）、推论3.1.7（77/87）、命题3.3.6（83/93）；其二次算子记号 $U_a$ 对应本章 $P(a)$，正锥对应已经独立建立的平方锥 $Q$，不对应一个预先自对偶的原 $C$。这些成熟 Jordan 事实为 literature-attested，不赋予原调用或物理实例化。

原型中的 Jordan 恒等式、平方锥自对偶及 $C=Q$ 两向识别由定理178.3的显式论证承担；对称锥几何不作新颖性声明。本章 repo-derived 的综合是：同源 $q$ 与原群内 $\Gamma$ 接成同一原型，自对偶从单列输入移到结论，再以原 $u$、原 D 及全部实际接口接回 C123/C124。C123 的单位适配、C124 的结构/CP/完整有限词/原记录结果均按上列精确所有者复用；不重证其分类、膨胀或量子过程尾部。这里不声称穷尽文献检索、历史优先权、全部剩余条件相互独立，或宇宙已经满足这些来源条件。

仍存的简化缺口是具体的：全部原有限右响应、径向下界、探针分离、原群内 $\Gamma$ 全性、闭连通内迁性、原 $u$ 适配 D、完整准备锥及真实对象/记录/参考/调用合同都仍须供应；本章没有把它们从一个无额外关系的共同宇宙中推出。删除的是共有 P(1.1)这一冗余明列条款，不是少一个独立公理的证明。这里的域也不是175.1预先对齐的复 Hermitian 全有限域：两者保留不同来源和接口，没有逐坐标弱支配结论。没有(178.26)的附加前件时也不借用175的单块全有限结算。

用普通中文说，先让两份原响应互相轻推，要求同一读数的最初变化在交换两端后相等；每条径向不能向下无限透支，每个非零原响应又都能被某个探针分辨，这才恢复原空间里的一把正尺子。还要原先指定的比较群内部总能找到反向配对，并能搬动任意两个锥内点。把这群的旋转平均出一个临时中心，用自伴随微小变化定义乘法，导子抵消证明它确是 Jordan 乘法；谱与二次算子再证明原来的正锥恰好是平方锥，而不是另画一个相似的锥。于是“正响应恰是对一切正响应读出非负的那些向量”不必另假定。

临时中心只是证明用的脚手架，原设备的单位没有换掉。回到原单位后，仍由原有向三元关系选复数类型，由真实联合和参考合同接通相关态与 CP，由原系数一端点和精确调用供应完整有限滤波词。正确运输后的纯确认比较就是两条量子射线的重叠：交换两端数值不变，二维复支撑面上画成三球的点积。数学球上的全部点不等于都能无损准备，某个效果也不指定旧设备怎样更新；记录、失败系数和时间仍各守自己的原条件。这是一个删除明列自对偶输入的完整条件候选，不是把所有剩余来源一并消去的结论。

[Q178P]: https://github.com/the-omega-institute/trureturing/blob/1ce2944a218087efcb6c57e6d886645eaa7712e0/docs/develop/theory/AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md#L5
[Q178C124]: https://github.com/the-omega-institute/trureturing/blob/1ce2944a218087efcb6c57e6d886645eaa7712e0/docs/develop/theory/AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md#L646
[Q178C139]: https://github.com/the-omega-institute/trureturing/blob/1ce2944a218087efcb6c57e6d886645eaa7712e0/docs/develop/theory/AURIC_C139_MUTUAL_PROBES_AND_INTRINSIC_RECOVERY_OF_SQUARE_GEOMETRY.md#L186
[Q178HS]: https://hanche.folk.ntnu.no/joa/joa-m.pdf
[Q178Adapt]: https://github.com/the-omega-institute/trureturing/blob/1ce2944a218087efcb6c57e6d886645eaa7712e0/docs/develop/theory/AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md#L133
[Q178Structure]: https://github.com/the-omega-institute/trureturing/blob/1ce2944a218087efcb6c57e6d886645eaa7712e0/docs/develop/theory/AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md#L662
[Q178CP]: https://github.com/the-omega-institute/trureturing/blob/1ce2944a218087efcb6c57e6d886645eaa7712e0/docs/develop/theory/AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md#L698
[Q178Words]: https://github.com/the-omega-institute/trureturing/blob/1ce2944a218087efcb6c57e6d886645eaa7712e0/docs/develop/theory/AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md#L706
[Q178Records]: https://github.com/the-omega-institute/trureturing/blob/1ce2944a218087efcb6c57e6d886645eaa7712e0/docs/develop/theory/AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md#L785
[Q178Time]: https://github.com/the-omega-institute/trureturing/blob/1ce2944a218087efcb6c57e6d886645eaa7712e0/docs/develop/theory/AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md#L341

## 追加锚（本行以下为增补区）

## 179. 原锥的典范比较群与同数据唯一扩张

### 179.1 不另给群参数的完整候选

**定义 179.1（典范比较候选）。** 固定定义178.1的同一个原签名 $\Omega$ 及其完整原资料：对象、全语境响应商、准备、事件、装置身份、端口、细记录及可访问关系、丢弃、经典标签、具名支持返回和全部有限接续的合法性谓词。每个所需原对象 $A$ 保留同一个非零有限维实空间 $E_A$、闭凸尖生成锥 $C_A$、内点单位 $u_A$、有限实值读数 $q_A$、已命名比较型及原双线性有向关系 $D$。所需对象逐字包括定义178.1/C124定义10.2的局部、实际联合、整个实际指针 $P$ 及其每个原有限幂、原输出、被消费的参考及其已声明联合；不由局部条件代替联合条件。

只从原线性锥定义

$$
G_C(A):=\operatorname{Aut}(C_A)^\circ,
\qquad \operatorname{Aut}(C_A)
=\{S\in GL(E_A):SC_A=C_A\},
\qquad (G_C(A))_{u_A}=\{S\in G_C(A):Su_A=u_A\}.
\tag{179.1}
$$

上标 $\circ$ 在群上表示恒等连通分支，在锥上仍表示内点集。此群不依赖 $q_A,g_A^0,u_A$ 或 $D$；$u_A$ 只参与稳定子。不给另一份指定群数据，也不另列闭性、连通性条件。

对全部带符号的原 $x,y\in E_A$，要求

$$
\begin{gathered}
D_{q_A}(x;y)=\lim_{t\downarrow0}
\frac{q_A(x+ty)-q_A(x)}t\in\mathbb R,
\qquad \inf_{t\in\mathbb R}q_A(tx)>-\infty,\\
x\ne0\ \Longrightarrow\ \exists y\in E_A:\ D_{q_A}(x;y)\ne0.
\end{gathered}
\tag{179.2}
$$

在唯一的域 $S,R\in G_C(A)$ 内定义并要求

$$
\begin{aligned}
\Gamma_{q_A}(S,R)&\ \Longleftrightarrow\quad
 \forall x,y\in E_A:\ D_{q_A}(Sx;y)=D_{q_A}(Ry;x),\\
\Gamma_{q_A}(I,I)&,\qquad
 \forall S\in G_C(A)\ \exists R\in G_C(A):\Gamma_{q_A}(S,R),\\
G_C(A)\curvearrowright C_A^\circ&\text{ 传递，即 }
 \forall a,b\in C_A^\circ\ \exists S\in G_C(A):Sa=b.
\end{aligned}
\tag{179.3}
$$

最后一行的群作用即通常的线性作用。逐径向下界无须一致，响应量词不是有限探针抽样。若原比较型已命名，必须逐点等于 $g_A^0(x,y)=\tfrac12D_{q_A}(x;y)$；其双线性与正定性由引理178.2支付，不重新选择度量或取商。除178.1已经不单列的共有P自对偶等式外，全部原合同如下保留；每处旧 $G_A$ 均以(179.1)代入。

| 原接口 | 典范候选中的完整保留 |
| --- | --- |
| P 与全原菜单 | 每个已命名正准备 $\alpha$ 的原质量 $\alpha(u_A)\le1$，实际准备的有限正锥包恰为完整 $C_A^*$；每个实际联合也如此。每个原事件 $f:A\to B$ 的正 Heisenberg 映射满足 $T_f(u_B)\le u_A$，完整装置求和等于 $u_A$。实际可读子菜单、补事件和装置身份照旧，完整数学效果区间不等于原子菜单。 |
| 原单位适配与 D | 按178.4及C123定义1.4，在原 $u_A$ 上作同一单位适配；保留其选择资料。原 $D_ab$ 在该乘法上对全部 $a,b,c\in E_A$ 满足导子律及 $([L_a,L_c]+[D_a,D_c])b=0$。不把辅助单位的乘法或后来矩阵交换子当作原 D。 |
| X、Xs 与联合控制 | 原含幺嵌入保持上述乘法和原 D，交叉 D 为零、乘积张成，有原乘积准备及原结合、交换、标量和经典标签接口。实际 $AP$ 自身满足全部对象条件。所有被消费旁接、准备—联合比较—测试及失败输出丢弃，均为同装置、同记录的原合法执行；全部相关输入由原乘积张成覆盖，未声明连线不变合法。 |
| $N_u$ | 对每个所需原对象和每个 $T\in(G_C(A))_{u_A}$，有同一原签名内系数一、Heisenberg响应恰为 $T$ 的完整有限装置指定事件，连同其原细记录、零响应补事件、失败端与输出。此为实际供应要求，不由(179.1)定义支付。 |
| AC 与整个实际 $P$ | 原完整准备装置、原破坏性成功事件 $m:P\to I$ 及完整测试都保留；$d=T_m(u_I)\ne0$ 张成整个 $C_P$ 的极射线，原 $\alpha(d)=1$，且存在 $h\in E_P$ 使 $[L_d,L_h]\ne0$。全部原准备、失败输出 $B_\ell$、细记录与实际丢弃保留。不另加Q1或假定可附接支持角。 |
| R 的全事件量词 | 每个原事件、细支、失败、标签、遗忘、具名返回及全部有限合法接续，在充分大的实际 $P^{\otimes k}$ 参考上有同记录执行，满足原乘积律并对完整原联合准备锥保正。参考幂任意大；不是只验乘积准备或新选词。 |
| F、原遗忘与支持双返回 | 同一原实现有原有限联合细记录及原遗忘求和；每个非零指定细支保留单中心输入、输出支持角 $P_a,Q_a$、原返回 $U_a$、同一个原 $q_{F,a}>0$，满足 $U_aS_a=q_{F,a}\mathrm{id}$ 于输入角、$S_aU_a=q_{F,a}\mathrm{id}$ 于输出角，及C123(2.5)的原返回支持约束。反向资料使用同一系数；零支保留标签。量词覆盖整个原菜单、联合标签、遗忘、所有返回及全部有限合法历史。 |

此表连同原定义178.1/C124定义10.2的逐字合同是一个候选，采用AC版本，不另换成Q1版本。保留原端口、全语境等价、可访问性与合法性；没有任何仅因锥闭包、锥自同构或指数存在而新增的原操作。

### 179.2 同数据忘却与唯一补回的等价证明

**定理 179.2（完整候选的典范下降）。** 定义179.1成立，当且仅当在同一份原资料上存在定义178.1的扩张。扩张中的指定群逐对象唯一，并在原 $GL(E_A)$ 中满足字面等式

$$
G_A=G_C(A)=\operatorname{Aut}(C_A)^\circ.
\tag{179.4}
$$

忘去群参数再按(179.1)补回，对全部原资料及其已给见证为恒等；这不声称其他辅助选择或某个变换的装置见证只有一个。原 $\Gamma$ 的两个域、原单位稳定子及 $N_u$ 见证逐点不变，原 $u$ 适配、原 D、原联合和完整C124量子消费者均保留。群等式在原 D 选择复类型之前成立，包括任意有限EJA直和、标量块和例外块。

证明。先核对典范定义自动具有的拓扑性质。若 $S_j\in\operatorname{Aut}(C)$ 在 $GL(E)$ 中收敛于 $S$，则 $S_j^{-1}\to S^{-1}$。由原锥闭性，$SC\subseteq C$ 且 $S^{-1}C\subseteq C$，故 $SC=C$。所以 $\operatorname{Aut}(C)$ 是 $GL(E)$ 的闭子群；闭子群定理使它成为矩阵Lie群。其恒等连通分支闭且连通，故 $G_C$ 自动是闭连通Lie子群。这里的闭性相对于 $GL(E)$，不声称可逆群在全部 $\operatorname{End}(E)$ 中闭。

现在从任意旧候选出发，省略对象下标。引理178.2先在原指定 $G$ 的原域内给出

$$
g(x,y)=g^0(x,y)=\tfrac12D_q(x;y),\qquad
q(x)=q(0)+g(x,x),\qquad
\Gamma_q(S,R)\Longleftrightarrow R=S^{\dagger_g}.
\tag{179.5}
$$

旧候选的闭性、连通性、锥自同构性、原内点传递性和此伴随封闭，正好是定理178.3的全部同源前件。此时才应用178.3，沿用其同一原 $E,g,C$ 上的辅助单位 $e_*$ 与乘法 $\circ_e$。该证明已完整支付EJA、正Frobenius型及原锥的两向识别；直接取其(178.8)–(178.10)、(178.14)–(178.17)：

$$
(E,\circ_e,e_*,g)\text{ 为有限维Euclidean Jordan代数},\qquad
C=Q:=\{x\circ_e x:x\in E\},
\qquad L(E)=\mathfrak p\subseteq\mathfrak g:=\operatorname{Lie}G.
\tag{179.6}
$$

故全部 $[L_a,L_b]$ 已属于这个原 $\mathfrak g$，不是从一个新大群借来。原群内乘法及交换子归属亦见C123定理22.1证明的(22.3)、(22.6a)；这里只复用这些归属片段，不添该处其余前件。

到(179.6)之后，才消费成熟供应：Gowda–Tao–Ravindran，*On the P-property of Z and Lyapunov-like transformations on Euclidean Jordan algebras*，LAA436(2012)2201–2209，[原文§4定理4(iv)⇔(v)][Q179GTR]（[DOI][Q179DOI]），给这个同一有限EJA平方锥的

$$
\operatorname{Lie}\operatorname{Aut}(Q)
=L(E)+\operatorname{innerDer}(E),\qquad
\operatorname{innerDer}(E)
=\operatorname{span}_{\mathbb R}\{[L_a,L_b]:a,b\in E\}.
\tag{179.7}
$$

右侧的span指有限实线性组合。供应中的代数是(179.6)的 $\circ_e$，单位是 $e_*$，内积是原 $g$，锥是刚独立证明等于 $C$ 的 $Q$；不是以该分解反向假定EJA或自对偶。原文§2允许任意正Frobenius型：在简单理想分解 $E=\bigoplus_iE_i$ 上，$g(x,y)=\sum_i c_i\operatorname{tr}_i(x_i\circ_e y_i)$，各 $c_i>0$ 可不等；§5后续才另作统一迹型归一。定理4不要求代数简单，也不限于复矩阵可实现类型。因此(179.7)涵盖有限直和、实/复/四元数块、spin因子及例外Albert块；一维块导子为零，连续正缩放方向已在 $L(E)$。有限EJA导子皆内的相同范围，亦由C123(36.6)–(36.7)的纯EJA片段核定；不调用带原Z等前件的整个定理36.1。相同块的离散置换不因此进入恒等分支。

由已赚得的 $C=Q$ 和全部原Lie归属，

$$
\operatorname{Lie}\operatorname{Aut}(C)
=L(E)+\operatorname{innerDer}(E)
\subseteq\mathfrak g
\subseteq\operatorname{Lie}\operatorname{Aut}(C).
\tag{179.8}
$$

最后一个包含只用旧 $G\le\operatorname{Aut}(C)$。所以两Lie代数作为同一个 $\operatorname{End}(E)$ 的子空间相等。旧 $G$ 连通且含恒等元，故 $G\subseteq\operatorname{Aut}(C)^\circ$。反向，连通矩阵Lie群由其Lie代数的指数生成；$\operatorname{Aut}(C)^\circ$ 的每个元素是有限个 $\exp X$ 的乘积，而每个这样的 $X$ 已在原 $\mathfrak g$，故各 $\exp X\in G$。取得(179.4)的反包含。这是实际线性算子集合的相等，不是抽象群同构；至此未消费原 D、复分类、AC或任何实际调用。

因此旧候选的每个 $\Gamma_q(S,R)$ 及其全称/存在域不变，并有

$$
(G_A)_{u_A}=(G_C(A))_{u_A},\qquad
\{(S,R)\in G_A^2:\Gamma_q(S,R)\}
=\{(S,R)\in G_C(A)^2:\Gamma_q(S,R)\}.
\tag{179.9}
$$

对右侧任意稳定子元 $T$，左侧就是同一个 $T$；照用原 $N_u$ 完整装置、指定支、系数及所有记录，而非从 $T$ 的锥自同构性制造控制。沿用178.4的同一个 $e_*$、同一个 $h\in G_A$ 满足 $hu_A=e_*$，同一个 $\widehat g_A(x,y)=g_A^0(hx,hy)$，便得到同一个原 $u_A$ 适配乘法。群及其Lie代数相等，自伴随部分与 $L_au_A=a$ 的唯一解也相等。因此原 D 的两条全载体律、X的乘法/D保持及AC非中心性逐字不变；无需另证Jordan乘法唯一，也不假设 $h$ 交织原 D。其余原接口和见证均未变，旧候选下降为179.1。

反向，给定179.1，令旧群参数 $G_A:=G_C(A)$。第一段已经支付旧群的闭性、连通性；(179.2)–(179.3)及保留的全部合同逐条就是178.1。引理178.2恢复原型与伴随封闭，178.3据此支付锥桥，178.4按同一选择支付原单位适配；不是在使用178.3之前借它补缺失前件。所有实际供应都用新候选已经给出的原见证，不加装置或事件。任意另一旧扩张的群也由(179.8)被强制为(179.1)，所以扩张群参数唯一，两向复合在其余原资料与已给见证上都是恒等。

### 179.3 等价保留的量子字典与几何

继续定理179.2的证明。由上述完整同数据等价，直接消费178.4–178.6及其所引C124命题11.1、11.3、定理12.1、命题12.2，不重做Jordan锥桥、复分类或过程尾部。在原 $u$ 适配乘法及原 D 上，仍为

$$
a\cdot b=a\circ b-iD_ab,\qquad
\mathcal A_A\cong\bigoplus_sM_{n_s}(\mathbb C),\quad
E_A=(\mathcal A_A)_{\rm sa},\quad C_A=(\mathcal A_A)_+,\quad u_A=I_A.
\tag{179.10}
$$

复类型来自原 D；X给已声明联合的普通复张量积及全部中心对。每个实际 $AP$ 自身的条件给联合块内酉比较，再由同一个 $N_u$ 给原精确调用，不能以局部控制替代联合控制。AC仍在整个实际 $P$ 的某块给质量一纯准备及系数一破坏性读口，该块维数 $r\ge2$，参考 $P^{\otimes k}$ 的实际块维数 $r^k$ 无界。原全事件R因此给每个原事件、细记录、返回及合法有限历史CP/TNI，原完整装置求和TP；CP结论不限新选词。

Born配对精确沿用178.5的同一个 $B_A$ 和 $\tau_A=\sum_s\operatorname{Tr}_{n_s}$：

$$
\begin{aligned}
g_A^0(x,y)&=\tau_A((B_Ax)y),& B_A(C_A)&=C_A,\\
\alpha&=g_A^0(x_\alpha,\cdot),& \rho_\alpha&=B_Ax_\alpha,\\
v_\alpha&=B_A^{-1/2}\rho_\alpha,& w_e&=B_A^{-1/2}e,\\
\alpha(e)&=\tau_A(\rho_\alpha e)=g_A^0(v_\alpha,w_e),&
m_\alpha&=\tau_A(\rho_\alpha)=\alpha(u_A),\\
\Phi_f&=B_BT_f^{\dagger_0}B_A^{-1}\quad(f:A\to B).
\end{aligned}
\tag{179.11}
$$

$B_A^{-1/2}$ 是原实响应空间上正自伴随算子的逆平方根，不是矩阵左乘。每个原联合使用自己的 $B_{AB}$，不假设它分解为 $B_A\otimes B_B$。正质量才可条件归一，零质量保留为零，全部原成功因素仍在原概率里。完整数学效果为 $[0,I_A]$，数学POVM为有限正效果和等于 $I_A$；原可读子菜单及任意指定仪器供应各守原域。完整准备正锥包不把全部数学密度矩阵变成质量一实际准备。

对数学归一底的任意两纯点 $p,r$，即各在一个简单块的迹一秩一投影，178.5在完整数学效果区间上精确给

$$
T_p(r):=\min_{0\le e\le I_A,\ \tau_A(pe)=1}\tau_A(re)
=\tau_A(pr)=\tau_A(rp)=T_r(p)
=g_A^0(B_A^{-1/2}p,B_A^{-1/2}r).
\tag{179.12}
$$

不同中心块的读数为零；这是运输后的对称比较，不是原Riesz向量 $x_p=B_A^{-1}p$ 的裸重叠，也不是旧子菜单上的同一个最小值。178.6同时保留同原型的齐性自对偶，即对称锥几何。复结构取得之后，在任一大小至少二的简单块的二维复支撑面上，数学归一底为 $\rho=(\Pi_S+\mathbf r\cdot\boldsymbol\sigma)/2$、$|\mathbf r|\le1$ 的闭Bloch三球，球面纯点比较为 $(1+\mathbf r\cdot\mathbf s)/2$。这是数学暴露面，不自动是一只可附接原 $M_2$ 对象或满质量实际准备集。

全有限单块结论仍严格限于178.6的附加前件：原 $C_A$ 不可约、$\dim_{\mathbb R}E_A=n^2$、固定整数 $n\ge2$，并实际声明所有 $A^{\otimes N}$ 及其所需联合、准备、D和全部原接口（比较群均按(179.1)定义）。此时才对每个有限 $N\ge1$ 有 $C_{A^{\otimes N}}=\operatorname{PSD}_{n^N}$；否则只有(179.10)和实际声明联合。$P$ 的全部参考幂不替任意 $A$ 声明全部幂。

操作、更新、返回和时间也逐项沿用原界限。对每个 $0\le e\le I_A$，包括奇异、零及部分中心分量为零的效果，178.4给同一原签名内一份选中完整有限词 $W_e$，成功作用为 $\operatorname{Ad}_{\sqrt e}$，每个被声明实际相关参考上为 $\operatorname{Ad}_{\sqrt e\otimes I_R}$。原失败端在丢弃前的算子输出、实际系数、补事件、细记录和原丢弃全保留；这不把旧同效果器件变成该平方根更新。F给原非零返回细支 $S_a=\operatorname{Ad}_{K_a}$、$U_a=q_{F,a}\operatorname{Ad}_{K_a^+}$，支持角、原正系数及反向资料照旧。全部原合法历史按(179.11)逐次运输；阶段细口只在原连线合法时相乘，否则用整个原词自己的全称F，任意Kraus分解不替代原记录。旧支更新仍须其自身完整输出校准，任意指定仪器组装仍须原供应。

逐块时间律 $\rho_s(t)=e^{-itH_s/\hbar}\rho_s(0)e^{itH_s/\hbar}$ 仍以C123命题4.1的原连续、确定、可逆一参数动态和物理时钟标定为前件；静态交换(179.12)的比较端点不交换两个更新操作的先后，也不选择Hamiltonian、$\hbar$或物理钟。由此全部原量子消费者及其量词范围保持，完成证明。$\square$

### 179.4 简化的范围与中文图景

定理179.2的新增综合为repo-derived：在178.1的全部同源资料上，赚得原群的逐元素唯一性，并使整个候选连同实际见证下降。经典供应(179.7)、有限EJA分解及Lie群拓扑事实为literature-attested的中间工具，不单列为本章新增经典结果；其中GTR只在178.3已支付EJA和 $C=Q$ 后使用。C128 §83.2所引Tao–Gowda Proposition1亦将GTR定理4用于同类有限EJA范围，本章不重证该供应，不作穷尽检索或历史优先权声明。

删去的是一份由原线性锥唯一恢复的群参数及其另列闭性、连通性要求。原锥仍是原线性序的数据，$q$不单独选择 $C$；全部响应、径向下界、探针分离、$\Gamma$全性、内点传递、原 D、实际准备和原调用供应均保留。等价不证明这些条件独立，也不证明独立公理总数减少或物理原签名已经满足它们。群的数学存在、固定原单位的实际控制、某个旧器件的输出校准和物理时间仍是不同关系。

用普通中文说，原正锥已经规定了哪些线性变化能保住全部正响应。取其中能从恒等变化连续走到的那些，得到一张完全由原锥写出的名单。旧候选还另交了一张名单；定理说明，只要闭连通的旧名单能搬动任意两个内点，又对原比较尺子的伴随封闭，它就已经包含平方锥的全部连续微小方向，所以两张名单逐项相同，不只是画出的轨道相像。有限直和、经典标量方向和例外块都在这一步里，复数类型尚未使用。

这省掉的是重复提供名单，不是省掉实验资源。每个固定原单位的变换仍须指出原来哪台完整装置、哪个端口以系数一实现；因名单相等，原装置及其失败记录、返回系数才能原样沿用。原单位和原有向关系继续选择复量子结构，完整联合与参考保证相关输入上的CP，原端点及合法连线才供应选中的有限滤波词。正确运输后的两条纯射线交换比较端点给同一个重叠数，在二维复支撑面上就是球面点积；先做哪次操作、保留什么输出与记录，仍由原历史决定。

[Q179GTR]: https://userpages.umbc.edu/~gowda/papers/trGOW10-01.pdf
[Q179DOI]: https://doi.org/10.1016/j.laa.2011.10.019

## 追加锚（本行以下为增补区）

## 180. 群内全性自动恢复恒等互易的同数据量子候选

### 180.1 完整典范候选与唯一删项

**定义 180.1（只由全性要求伙伴的典范候选）。** 将定义179.1连同它完整纳入的定义178.1、[C124定义10.2][Q178C124]作为本定义的一部分，唯一删除(179.3)中单列的合取项 $\Gamma_{q_A}(I,I)$。记所得候选为 $\mathcal C_{180}$，原定义179.1为 $\mathcal C_{179}$。以下明确其数据、响应条件和完整合同的保留范围；这些说明不截短被引用原条款的任何量词。

同一个原签名 $\Omega$、原全语境响应空间、全部对象、准备、事件、装置身份、端口、细记录、可访问关系、丢弃、经典标签、具名支持返回和合法有限接续谓词全部保留。每个所需原对象 $A$ 仍有原非零有限维实空间 $E_A$、闭凸尖生成锥 $C_A$、内点单位 $u_A$、有限实值读数 $q_A$、已命名比较读数和原双线性有向关系 $D$。对象集包括全部局部、实际联合、整个实际指针 $P$ 及每个原有限幂、原输出、被消费参考及其已声明联合。每个对象分别满足条件，不能由局部对象替代联合对象。

典范群、稳定子、原响应及比较域仍是

$$
\begin{gathered}
G_C(A)=\operatorname{Aut}(C_A)^\circ,
\qquad \operatorname{Aut}(C_A)=\{S\in GL(E_A):SC_A=C_A\},\qquad
(G_C(A))_{u_A}=\{S\in G_C(A):Su_A=u_A\},\\
F_A(x;y):=D_{q_A}(x;y)
=\lim_{t\downarrow0}\frac{q_A(x+ty)-q_A(x)}t\in\mathbb R
\quad(x,y\in E_A),\\
\inf_{t\in\mathbb R}q_A(tx)>-\infty\quad(x\in E_A),\qquad
x\ne0\Longrightarrow\exists y\in E_A:\ F_A(x;y)\ne0,\\
\Gamma_{q_A}(S,R)\Longleftrightarrow
 \forall x,y\in E_A:\ F_A(Sx;y)=F_A(Ry;x)
\quad(S,R\in G_C(A)),\\
\forall S\in G_C(A)\ \exists R\in G_C(A):\Gamma_{q_A}(S,R),\qquad
\forall a,b\in C_A^\circ\ \exists S\in G_C(A):Sa=b.
\end{gathered}
\tag{180.1}
$$

群上的 $\circ$ 是恒等连通分支；锥上的 $\circ$ 是内点。响应存在性量化全部带符号原向量，不是有限抽样；下界仍只逐径向要求。已命名原比较读数逐点等于 $g_A^0(x,y)=F_A(x;y)/2$，其正定对称双线性性质由下述定理恢复，不能在消扭入口预用。原 $q_A(0)$ 保留为原数据。不另加读数的凸性、全空间连续性、双侧可微、探针负齐次、范数或Hessian条件。

| 完整保留的原接口 | 同一原资料及见证的范围 |
| --- | --- |
| P及原菜单 | 每个已命名正准备的原质量 $\alpha(u_A)\le1$，实际准备的有限正锥包恰为完整 $C_A^*$，每个实际联合亦然；每个原事件 $f:A\to B$ 的正映射 $T_f$ 满足 $T_f(u_B)\le u_A$，完整装置求和等于 $u_A$。原可读子菜单、补事件及身份保留。178已经移为结论的共有P自对偶等式不重新输入。 |
| 原单位适配及D | 保留178.4/C123定义1.4的原 $u_A$ 适配与全部选择资料；原 $D_ab$ 在该乘法上对全部 $a,b,c$ 满足导子律和 $([L_a,L_c]+[D_a,D_c])b=0$。不改成辅助单位的乘法或后来矩阵交换子。 |
| X、Xs及联合 | 原含幺嵌入保持该乘法和原D，交叉D为零、乘积张成、原乘积准备、结合/交换/标量/经典标签均保留。实际 $AP$ 自身满足全部对象条件。所有被消费旁接、准备—联合比较—测试、失败输出丢弃均是同装置、同记录的原合法执行；未声明连线仍不合法。 |
| $N_u$ | 对每个所需对象和每个 $T\in(G_C(A))_{u_A}$，原签名内有系数一、响应恰为 $T$ 的完整有限装置指定事件及其细记录、零响应补事件、失败端和输出；该实际供应不由群的数学定义支付。 |
| AC及整个实际P | 原完整准备装置和破坏性成功事件 $m:P\to I$、完整测试、全部失败输出 $B_\ell$、记录和实际丢弃不变。$d=T_m(u_I)\ne0$ 张成整个 $C_P$ 的极射线，原 $\alpha(d)=1$，且存在 $h\in E_P$ 使 $[L_d,L_h]\ne0$。不另加Q1或可附接支持角。 |
| R及全部原事件 | 对每个原事件、细支、失败、标签、遗忘、具名返回及全部有限合法历史，在充分大的实际 $P^{\otimes k}$ 参考上有同记录执行、原乘积律和完整原联合准备锥保正；参考幂任意大，不限乘积准备或新选词。 |
| 原F及支持双返回 | 原有限联合细记录、原遗忘求和、每个非零细支的单中心输入/输出支持角 $P_a,Q_a$、具名原返回 $U_a$、同一个原 $q_{F,a}>0$、$U_aS_a=q_{F,a}\mathrm{id}$ 于输入角及 $S_aU_a=q_{F,a}\mathrm{id}$ 于输出角、C123(2.5)支持约束和同系数反向资料全保留。零支保留标签；量词覆盖整个原菜单、联合标签、遗忘、全部返回及有限合法历史。此处合同F不是响应记号 $F_A$。 |

这仍是完整AC版本的一个候选。典范群的闭性、连通性沿用179.2证明首段的闭子群事实，不另给群参数；其余群全性和内点传递仍是(180.1)的输入。全部原准备锥、原质量、原调用与记录合同均未由本定义推导或删去。

### 180.2 同一标量的消扭与候选等价

**定理 180.2（恒等互易删项的完整同数据等价）。** 在同一份原资料及全部已给见证上，

$$
\mathcal C_{180}\quad\Longleftrightarrow\quad
\mathcal C_{179}\quad\Longleftrightarrow\quad
\text{存在定义178.1的扩张}.
\tag{180.2}
$$

对每个所需原对象，全性在 $S=I$ 给出的任意伙伴 $R_{0,A}$ 必为 $I$。唯一恢复的正定对称实双线性型、原读数及全部伙伴满足

$$
\begin{gathered}
g_A^0(x,y)=\tfrac12F_A(x;y)
=\frac{q_A(x+y)-q_A(x-y)}4,
\qquad q_A(x)=q_A(0)+g_A^0(x,x),\\
\Gamma_{q_A}(S,R)\Longleftrightarrow R=S^{\dagger_0}
\quad(S,R\in G_C(A)),\qquad G_C(A)^{\dagger_0}=G_C(A).
\end{gathered}
\tag{180.3}
$$

178扩张的群参数逐对象唯一且字面等于 $G_C(A)$；两向对应在其余全部原资料、已给伙伴、比较数值及实际见证上都是恒等。178.3–178.6及完整C124的量子结论在下述原单位、原D、参考和历史范围内原样适用。

证明。先固定任一原对象，暂省下标。由 $I\in G_C$ 取全性给出的某个伙伴 $R:=R_0\in G_C$，只知道

$$
F(x;y)=F(Ry;x)\qquad(x,y\in E).
\tag{180.4}
$$

以下在证明 $R=I$ 以前只用原 $q$、(180.4)、有限右响应、径向下界与原分离条件。不使用正双线性型、伴随、C139定理3.3、锥自对偶或179的群唯一性。

*仿射线连续性和一元工具。* 对每个 $a,b\in E$，函数 $t\mapsto q(a+tb)$ 在每个 $t_0$ 连续：方向 $b$ 的有限右响应给右连续，方向 $-b$ 的有限右响应给左连续；尚未认定两个响应互为相反数。下文右导恒零或等于多项式导数时，直接复用 [C139引理3.2][Q180C139Unique] 的连续函数积分唯一性。

还需要其单侧极值论证的非负版本，作为本证明内部工具：连续 $h$ 在区间各非右端点有有限 $h'_+\ge0$，则 $h$ 单调不减。若有 $a<b$ 而 $h(a)>h(b)$，取 $0<\varepsilon<(h(a)-h(b))/(b-a)$。$k(t)=h(t)+\varepsilon t$ 仍有 $k(a)>k(b)$，故其区间最大值在某个 $c<b$ 取得，给 $k'_+(c)\le0$，却又有 $k'_+(c)\ge\varepsilon>0$，矛盾。在每个闭子区间应用即得所需单调性。这里只证明后面双向单调性所需的工具，不预设双侧导数。

*正径向尺度、原下界和原R的不变性。* 原右极限的重参数化给 $F(x;\lambda y)=\lambda F(x;y)$，$\lambda\ge0$；$\lambda=0$ 时两边为零。(180.4)遂给

$$
F(\lambda x;y)=F(Ry;\lambda x)=\lambda F(x;y),\qquad
F(0;y)=F(Ry;0)=0.
\tag{180.5}
$$

连续函数 $s\mapsto q(sx)$ 在 $s\ge0$ 的右导数为 $sF(x;x)$。对任意 $[0,T]$ 用C139引理3.2并取 $s=1$，得到

$$
F(x;x)=2(q(x)-q(0)),\qquad
q(sx)=q(0)+s^2(q(x)-q(0))\quad(s\ge0).
\tag{180.6}
$$

若 $q(x)<q(0)$，令 $s\to+\infty$ 就违反该原方向的径向下界。因此 $q(x)\ge q(0)$ 对所有 $x$ 成立；这是从逐径向下界推出的结论，不是另添统一下界。将(180.4)连续使用两次，$F(x;y)=F(Ry;x)=F(Rx;Ry)$；令 $y=x$，由(180.6)得 $q(Rx)=q(x)$。

*同源剪切和精确矩形差分。* 对固定 $a,b\in E$、$c\in\mathbb R$，令 $t>0$ 足够小使 $1+ct>0$，再令 $\tau=t/(1+ct)>0$。正径向式给原标量的精确恒等式

$$
\begin{aligned}
q(a+t(b+ca))-q(0)
 &=(1+ct)^2\bigl(q(a+\tau b)-q(0)\bigr),\\
\frac{q(a+t(b+ca))-q(a)}t
 &=\frac{(1+ct)^2-1}{t}\bigl(q(a)-q(0)\bigr)
 +(1+ct)\frac{q(a+\tau b)-q(a)}\tau.
\end{aligned}
\tag{180.7}
$$

这里只沿固定方向 $b$ 取一次原右极限，$\tau\to0^+$，得到 $F(a;b+ca)=F(a;b)+2c(q(a)-q(0))$。没有方向变量的可加、连续或负齐次假设，也没有交换两个极限。结合(180.4)与 $q(Ry)=q(y)$，

$$
\begin{aligned}
F(x+cRy;y)&=F(Ry;x+cRy)\\
 &=F(Ry;x)+2c(q(Ry)-q(0))\\
 &=F(x;y)+2c(q(y)-q(0)).
\end{aligned}
\tag{180.8}
$$

固定 $x,y,s$，连续函数 $H(t)=q(x+sRy+ty)-q(x+ty)$ 在每个实数 $t$ 的右导数为 $2s(q(y)-q(0))$。在包含 $0,t$ 的闭区间复用C139引理3.2，故对全部实 $s,t$，

$$
q(x+sRy+ty)-q(x+sRy)-q(x+ty)+q(x)
=2st\bigl(q(y)-q(0)\bigr).
\tag{180.9}
$$

四角都是同一原 $q$ 的数值，没有新读数。将 $(y,s,t)$ 同时换成 $(-y,-s,-t)$，由 $R$ 的线性，左边逐项不变。取 $s=t=1$ 得 $q(-y)=q(y)$。再在(180.9)取 $x=0,s=1,t=-1$，结合 $q(Ry)=q(y)$，得到

$$
q((R-I)y)-q(Ry)-q(-y)+q(0)
=-2(q(y)-q(0)),\qquad
q((R-I)y)=q(0).
\tag{180.10}
$$

*零读数先传播至全部基点，再用原分离。* 设任意原 $v$ 满足 $q(v)=q(0)$。已证 $q(Rv)=q(-Rv)=q(0)$，且 $q\ge q(0)$，故这两个点为原 $q$ 的全局最小点。对每个 $a$，原有限右响应只先给 $F(Rv;a)\ge0$、$F(-Rv;a)\ge0$；不能把最小点的单侧响应直接宣告为零。(180.4)和 $R(-v)=-Rv$ 给

$$
F(a;v)=F(Rv;a)\ge0,\qquad
F(a;-v)=F(-Rv;a)\ge0\qquad(a\in E).
\tag{180.11}
$$

固定任意基点 $a$。上一元工具说明 $t\mapsto q(a+tv)$ 和 $t\mapsto q(a-tv)$ 都单调不减。对 $t_1<t_2$，第一项给 $q(a+t_1v)\le q(a+t_2v)$，第二项在 $-t_2<-t_1$ 给反向不等式。于是

$$
q(a+tv)=q(a)\quad(a\in E,\ t\in\mathbb R),\qquad
F(a;v)=0\quad(a\in E).
\tag{180.12}
$$

这才建立该位移在所有原基点上的不可见性。再由(180.4)，$F(v;z)=F(Rz;v)=0$ 对所有 $z$ 成立；原分离条件的逆否式给 $v=0$。因此 $q(v)=q(0)$ 仅在 $v=0$ 发生。将此结论用于(180.10)中的 $v=(R-I)y$，得到 $Ry=y$ 对全部 $y$ 成立，即原来选到的 $R_0=I$。没有取零空间商或替换伙伴见证。

*赚得无扭互易后复用原恢复与原等价。* 现在(180.4)才成为 $F(x;y)=F(y;x)$，其全部有限右响应前件正是 [C139定理3.3][Q178C139]。直接复用其唯一恢复式，即引理178.2的对称双线性恢复入口，取得 $g^0=F/2$、$q(x)=q(0)+g^0(x,x)$ 及极化式；不另证经典极化定理。刚证的 $q(x)\ge q(0)$ 且等号只在零点给 $g^0$ 正定。已命名原比较型逐点等于它，而非换成另一把自对偶尺子。此时再用引理178.2的群伙伴部分：

$$
\Gamma_q(S,R)\Longleftrightarrow
 \forall x,y:\ g^0(Sx,y)=g^0(x,Ry)
\Longleftrightarrow R=S^{\dagger_0}.
\tag{180.13}
$$

非退化性保证伙伴唯一；保留的群内全性及伴随对合给 $G_C^{\dagger_0}=G_C$。这识别每个已给伙伴本来是什么，不把它换成群逆；一般 $S^{\dagger_0}\ne S^{-1}$。对每个原对象重复上述论证，补回唯一删除的 $\Gamma_{q_A}(I,I)$，其余条款和见证原已相同，遂得 $\mathcal C_{180}\Rightarrow\mathcal C_{179}$。反向只是忘去这条推得的合取项，不改任何数据或见证。最后完整复用定理179.2，得到(180.2)的第三项及扩张群参数的唯一性，不重证179的Lie代数或群等式。

### 180.3 原单位、原D及完整量子字典的接回

继续定理180.2的证明。每个对象的原 $(E_A,g_A^0,C_A,G_C(A))$ 已有正定型、伴随封闭、闭连通锥自同构群和保留的内点传递性，正好满足定理178.3，故原锥 $C_A=C_{A,g_A^0}^*$。逐对象取得该结论后才用178.4；不以局部锥结论代替联合锥前件。178.4–178.6和179.3的完整消费者现在逐项适用，以下明确原数值和原接口的交接。

沿用原辅助 $e_*$ 及原选择 $h_A\in G_C(A)$，$h_Au_A=e_*$，精确用178.18/C123(3.3)–(3.4)的 $\widehat g_A(x,y)=g_A^0(h_Ax,h_Ay)$ 构造原 $u_A$ 适配乘法 $\circ$。$\widehat g_A$ 是该单位适配的辅助型，不替换原 $q_A$ 或原比较型。原D仍在此乘法上满足全载体导子律与交换子抵消；不假设 $h_A$ 交织原D。由178.4/C124命题11.1，

$$
a\cdot b=a\circ b-iD_ab,\qquad
\mathcal A_A\cong\bigoplus_sM_{n_s}(\mathbb C),\qquad
E_A=(\mathcal A_A)_{\rm sa},\quad C_A=(\mathcal A_A)_+,\quad u_A=I_A.
\tag{180.14}
$$

复类型由保留的原D选择，X的原嵌入、交叉D、张成及乘积准备给全部已声明联合的普通复张量积和中心对；单凭消扭不选择复类型。典范群、原单位稳定子及 $N_u$ 的逐元素域从未改变，故原系数一完整调用见证照用，尤其实际 $AP$ 的联合控制不由局部控制替代。

精确复用178.5及179.11的同一个 $\tau_A=\sum_s\operatorname{Tr}_{n_s}$ 和唯一迹自伴随正定算子 $B_A$。对每个原准备、效果和事件，

$$
\begin{aligned}
g_A^0(x,y)&=\tau_A((B_Ax)y),& B_A(C_A)&=C_A,\\
\alpha&=g_A^0(x_\alpha,\cdot),& \rho_\alpha&=B_Ax_\alpha\ge0,\\
v_\alpha&=B_A^{-1/2}\rho_\alpha,& w_e&=B_A^{-1/2}e,\\
\alpha(e)&=\tau_A(\rho_\alpha e)=g_A^0(v_\alpha,w_e),&
m_\alpha&=\tau_A(\rho_\alpha)=\alpha(u_A)\le1,\\
\Phi_f&=B_BT_f^{\dagger_0}B_A^{-1}\quad(f:A\to B),&
\tau_B(\Phi_f(\rho)y)&=\tau_A(\rho T_f(y)).
\end{aligned}
\tag{180.15}
$$

这里 $T_f:E_B\to E_A$，故其原比较型伴随的类型是 $E_A\to E_B$。$B_A^{-1/2}$ 是原实响应空间上算子的逆平方根，不是矩阵左乘；每个联合使用原 $B_{AB}$，不要求 $B_{AB}=B_A\otimes B_B$。既不将 $g_A^0$ 限缩为中心加权迹型，也不作两种比较型之间的额外等距改换。原质量和所有历史成功因子保持；只有 $m_\alpha>0$ 才条件归一，质量零仍为零。

数学归一正泛函底是全部密度矩阵，数学效果为 $[0,I_A]$，数学POVM为有限正效果之和等于 $I_A$。完整实际准备正锥包不供应每个密度点的质量一准备，数学效果区间也不等于旧可读子菜单。对该数学底任意两纯点 $p,r$，即各在一个中心块的迹一秩一投影，178.23–178.24/179.12直接给

$$
T_p(r):=\min_{0\le e\le I_A,\ \tau_A(pe)=1}\tau_A(re)
=\tau_A(pr)=\tau_A(rp)=T_r(p)
=g_A^0(B_A^{-1/2}p,B_A^{-1/2}r).
\tag{180.16}
$$

不同块时读数为零。这是原型中双运输后的数值，不是原Riesz向量 $x_p=B_A^{-1}p$ 与 $x_r$ 的裸重叠。最小值取完整数学效果区间；旧子菜单未含 $p$ 时不能直接沿用其最小值。交换比较端点保持数值的结论不附带任何交换执行次序的断言。

### 180.4 几何、全事件、原记录及时间的精确范围

继续定理180.2的证明。178.6给同一原型中的齐性自对偶，即对称锥几何；(180.14)的复结构取得后，任一大小至少二的简单块的二维复支撑面为

$$
\rho=\tfrac12(\Pi_S+\mathbf r\cdot\boldsymbol\sigma),\qquad
|\mathbf r|\le1,\qquad
T_{p_{\mathbf r}}(p_{\mathbf s})=\tfrac12(1+\mathbf r\cdot\mathbf s)
\quad(|\mathbf r|=|\mathbf s|=1).
\tag{180.17}
$$

这是数学归一底的闭Bloch三球及其纯点球面，不自动是单独可附接原 $M_2$ 对象，也不供应面上全部点的质量一准备。只有另有原锥 $C_A$ 不可约、$\dim_{\mathbb R}E_A=n^2$、固定整数 $n\ge2$，并实际声明全部 $A^{\otimes N}$ 及其所需联合、准备、D、典范群和完整原接口，才由178.26对每个有限 $N\ge1$ 得 $C_{A^{\otimes N}}=\operatorname{PSD}_{n^N}$。否则准确结论仅为(180.14)及已声明联合；实际 $P$ 的全部参考幂不替任意 $A$ 供应全部幂。

全事件CP继续由178.4/C124命题11.3承担：AC在整个实际 $P$ 的某块给质量一纯准备及系数一破坏性读口，块维数 $r\ge2$；实际 $P^{\otimes k}$ 有维数 $r^k$ 无界的参考块。R对完整联合准备锥的保正及同记录执行，为每个原事件、细记录、失败、标签、遗忘、返回和全部原有限合法历史支付充分参考层，因此其(180.15)的状态映射全部CP/TNI，完整装置求和TP。这不是只对新选中的滤波词或乘积输入的结论。

直接复用178.20/C124定理12.1：每个数学 $0\le e\le I_A$，包括奇异、零和部分中心分量为零的效果，都有同一原签名内的选中完整有限装置 $W_e$，沿用其实际见证，满足

$$
\Phi_{W_e}(\rho)=\sqrt e\,\rho\sqrt e,\qquad
\Phi_{W_e\mid R}(X)=(\sqrt e\otimes I_R)X(\sqrt e\otimes I_R)
\quad\text{对每个已声明实际相关参考}.
\tag{180.18}
$$

原准备、实际系数、补事件、失败端丢弃前的算子输出、细记录和原丢弃全部保留。C124命题12.2对原F及支持双返回给每个原非零指定细支 $S_a=\operatorname{Ad}_{K_a}$、$U_a=q_{F,a}\operatorname{Ad}_{K_a^+}$，输入/输出支持角、同一个原 $q_{F,a}>0$ 及反向资料均照旧；零支不丢标签。原遗忘仍是原细支求和。阶段细口只在原连线合法时相乘，否则使用整个原词自己的全称F；任意Kraus分解的指标不成为原记录。按(180.15)逐次运输全部原合法历史，保持原概率、输出、返回系数、记录和条件分母。

选中 $W_e$ 的成功质量严格正时，才有条件态 $\sqrt e\rho\sqrt e/\tau_A(\rho e)$。旧同效果装置仍用自己的原状态映射；要等于这个更新须另有其完整输出校准。逐效果供应 $W_e$ 也不自动组装任意指定原POVM仪器。逐块时间律 $\rho_s(t)=e^{-itH_s/\hbar}\rho_s(0)e^{itH_s/\hbar}$ 仍只在C123命题4.1的原连续、确定、可逆一参数动态及物理时钟标定下取得；(180.16)的静态端点交换不交换有更新操作的先后，不指定 $H_s,\hbar$ 或钟，右响应的探针比例也不因此成为时间。

由此全部原量子消费者已接回，完成(180.2)的完整同数据证明。其新增综合为repo-derived的候选删项及原接口衔接；C139的一元唯一性和对称型恢复、178.3的原锥桥、179.2的典范下降、178.4–178.6/C124的量子消费者均按上述精确入口复用，单侧分析与经典极化只是其中的中间工具。不声称穷尽文献或历史优先权。删去的是一条冗余的明列合取项，不是独立公理数减少的证明；全部有限同源右响应、径向下界、原分离、群内全性、内点传递、原D和实际接口仍须供应，其余条件的独立性及物理原资料是否满足它们均不由此判定。

用中文看这段证明：“每个变化都有伙伴”先只说“不做变化”也有某个伙伴，不能直接指定它就是自己。把同一个原读数放在沿 $y$ 和 $R_0y$ 移动的矩形四角，四笔差量必须一致；正反向重写同一矩形先给相同读数，再使 $R_0y-y$ 具有与零点相同的读数。下界让这成为真正的最低读数，不能靠正负透支抵消。然而最低点的单侧变化还只能说非负；互易把这项非负性搬到每个基点的两个相反行走方向，两个方向都不下降才迫使整条线完全不变。这样先证明该位移在所有地方都看不见，再用“每个非零原响应总有探针看得见”排除它，便有 $R_0y=y$。没有把“某处为零”偷换成“处处不可见”。

于是“不变的伙伴仍是不变”不用再单列，原尺子随之按既有恢复式赚得，而非预先借来。后面的正锥、原单位、有向关系、准备质量、参考、装置、失败、返回和合法记录各仍留在原位。正确运输后的两条纯射线交换端点读出同一重叠，在复二维支撑面上就是球面点积；这幅几何画面没有把数学球上所有点变成可无损准备的原资源，也没有把同一效果变成旧设备唯一的更新或物理时间律。$\square$

[Q180C139Unique]: https://github.com/the-omega-institute/trureturing/blob/1ce2944a218087efcb6c57e6d886645eaa7712e0/docs/develop/theory/AURIC_C139_MUTUAL_PROBES_AND_INTRINSIC_RECOVERY_OF_SQUARE_GEOMETRY.md#L176

## 追加锚（本行以下为增补区）

## 181. 原单位处自伴方向满射的同数据量子候选

### 181.1 完整候选与原单位局部条件

**定义 181.1（恒等伙伴与原单位自伴方向候选）。** 完整采用定义180.1及其纳入的定义179.1、178.1、C124定义10.2，只作如下两项替换：把全群伙伴全性换成恒等元存在一个伙伴，把全部内点传递性换成原单位处自伴Lie方向的评价满射。记这一个候选为 $\mathcal C_{181}$。

具体地，同一原签名 $\Omega$ 的原非零有限维实空间 $E_A$、闭凸尖生成锥 $C_A$、原内点单位 $u_A$、有限实值 $q_A$、已命名比较数值 $g_A^0$ 及原双线性有向关系 $D$ 均保留。全部带符号原向量上的响应条件仍为

$$
\begin{gathered}
F_A(x;y)=\lim_{t\downarrow0}\frac{q_A(x+ty)-q_A(x)}t\in\mathbb R
\quad(x,y\in E_A),\qquad
\inf_{t\in\mathbb R}q_A(tx)>-\infty\quad(x\in E_A),\\
x\ne0\Longrightarrow\exists y\in E_A:\ F_A(x;y)\ne0,
\qquad g_A^0(x,y)=\tfrac12F_A(x;y).
\end{gathered}
\tag{181.1}
$$

原比较数值的正定对称双线性性质由下述恒等伙伴入口恢复，不在入口预用。只从原锥定义同一个 $G_C(A)=\operatorname{Aut}(C_A)^\circ$，并在原域 $S,R\in G_C(A)$ 上沿用 $\Gamma_{q_A}$ 的定义。第一项新要求为

$$
\exists R_{0,A}\in G_C(A)\ \forall x,y\in E_A:
F_A(x;y)=F_A(R_{0,A}y;x).
\tag{181.2}
$$

在(181.1)–(181.2)恢复的原型上，定义并要求

$$
\begin{gathered}
\mathfrak g_A=\operatorname{Lie}(G_C(A)),\qquad
\mathfrak p_A^0=\mathfrak g_A\cap\operatorname{Sym}(E_A,g_A^0),\\
\operatorname{ev}_{u_A}:\mathfrak p_A^0\longrightarrow E_A,
\qquad X\longmapsto Xu_A\quad\text{满射}.
\end{gathered}
\tag{181.3}
$$

这里 $\operatorname{Sym}(E_A,g_A^0)$ 是关于该原正定型自伴随的实线性算子空间；(181.3)在其前件恢复该型后解释，不再输入一把度量。下述证明给出完全等价、不添参数的维数形式

$$
\operatorname{ev}_{u_A}\text{ 满射}
\quad\Longleftrightarrow\quad\dim\mathfrak p_A^0=\dim E_A
\quad\Longleftrightarrow\quad
\dim\mathfrak p_A^0\ge\dim E_A.
\tag{181.4}
$$

定义180.1的完整合同表仍逐字是本定义的一部分，只有上述两个条款被替换，仍为AC版本，不另加Q1。对象量词仍覆盖局部、实际联合、整个实际指针 $P$ 及每个原有限幂、原输出、被消费参考和其已声明联合；每个对象分别满足(181.1)–(181.3)及自己的全部原接口。保留每个实际准备的原质量及其有限正锥包恰为完整 $C_A^*$ 的要求、原单位适配的选择资料和原D、X/Xs、$N_u$、AC、全事件R、原F、具名支持双返回及其原 $q_{F,a}>0$。原装置、事件、补事件、失败输出、细记录、可访问性、标签、遗忘、丢弃、支持角、反向资料和全部有限合法历史不变，未声明连线仍未声明。共有P自对偶等式仍为待推结论；不加入预先齐性、自对偶或伴随封闭，不加入全空间正则性、商空间、自由群或中心参数。

### 181.2 完整同数据等价及恒等伙伴入口

**定理 181.2（原单位局部方向替代两个全局输入）。** 在同一份原资料及共有的全部实际见证上，

$$
\mathcal C_{181}\quad\Longleftrightarrow\quad
\mathcal C_{180}\quad\Longleftrightarrow\quad
\mathcal C_{179}\quad\Longleftrightarrow\quad
\text{存在定义178.1的扩张}.
\tag{181.5}
$$

对每个所需原对象，(181.2)的任意伙伴必为 $R_{0,A}=I$，原数值满足

$$
\begin{gathered}
g_A^0(x,y)=\tfrac12F_A(x;y)
=\frac{q_A(x+y)-q_A(x-y)}4,\qquad
q_A(x)=q_A(0)+g_A^0(x,x),\\
C_A=C_{A,g_A^0}^*,\qquad
G_C(A)^{\dagger_0}=G_C(A),\qquad
G_C(A)\curvearrowright C_A^\circ\ \text{传递},\\
\Gamma_{q_A}(S,R)\Longleftrightarrow R=S^{\dagger_0}
\quad(S,R\in G_C(A)).
\end{gathered}
\tag{181.6}
$$

178扩张的群逐对象唯一且字面等于 $G_C(A)$。遗忘与补回在原数值、原D、原单位适配选择及全部共有实际见证上为恒等；被删去的伙伴族有唯一可补回的算子值，不声称装置见证唯一。完整量子结论按180.3–180.4的全部参数、量词和资格保留。

证明。先固定一个原对象，省略下标。这里只从(181.2)取一个原 $R_0$，不取其他群元的伙伴。在取得正定型前，精确复用180.2证明中从(180.4)到(180.12)的原 $q$ 片段：其输入只有可逆线性 $R_0$、$F(x;y)=F(R_0y;x)$、全部有限右响应、逐径向下界和探针分离，没有全群伙伴或内点传递性。以下列出这段应用的全部承重接口。

有限的正、负方向右响应使每条仿射线上的 $q$ 连续；原右极限的正重参数化给 $F(x;\lambda y)=\lambda F(x;y)$（$\lambda\ge0$）。恒等伙伴把正齐次性搬到第一槽。应用C139引理3.2的一元唯一性，正好得到(180.5)–(180.6)：

$$
\begin{gathered}
F(\lambda x;y)=\lambda F(x;y),\quad F(0;y)=0,\\
F(x;x)=2(q(x)-q(0)),\qquad
q(sx)=q(0)+s^2(q(x)-q(0))\quad(s\ge0).
\end{gathered}
\tag{181.7}
$$

径向下界遂给 $q\ge q(0)$；将恒等伙伴等式用两次给 $F(x;y)=F(R_0x;R_0y)$，故 $q(R_0x)=q(x)$。180.7的精确正径向剪切只沿一个固定探针取右极限；再用180.8–180.9的一元唯一性，得同一原标量的四角等式

$$
q(x+sR_0y+ty)-q(x+sR_0y)-q(x+ty)+q(x)
=2st(q(y)-q(0))\quad(s,t\in\mathbb R).
\tag{181.8}
$$

同时换 $(y,s,t)$ 为 $(-y,-s,-t)$，左边不变，故 $q(-y)=q(y)$；再取 $x=0,s=1,t=-1$，得 $q((R_0-I)y)=q(0)$。此处尚不能以最小点的单侧响应为零。若 $q(v)=q(0)$，则 $\pm R_0v$ 都是全局最小点，恒等伙伴只先给

$$
F(a;v)=F(R_0v;a)\ge0,\qquad
F(a;-v)=F(-R_0v;a)\ge0\quad(a\in E).
\tag{181.9}
$$

180.2证明中的单侧单调性工具只需仿射线连续和有限非负右导数，故两条反向直线都不下降。这正是(180.11)–(180.12)的入口，得到 $q(a+tv)=q(a)$ 对全部原 $a,t$ 成立，因而 $F(a;v)=0$。再用恒等伙伴得 $F(v;z)=F(R_0z;v)=0$ 对全部 $z$ 成立；原探针分离给 $v=0$。应用于 $v=(R_0-I)y$，取得 $R_0=I$。上述片段既未使用伴随，也未用整个定理180.2的结论。

现在才有 $F(x;y)=F(y;x)$，其全部右响应前件正好支付C139定理3.3。直接应用该定理得(181.6)第一行的唯一对称双线性恢复式。刚证的 $q\ge q(0)$ 且仅在零点取等号，使它正定；已命名数值逐点就是 $g=g^0=F/2$。这才允许下面使用其伴随、正交群及自伴随谱，不替换原 $q$ 或原比较型。

### 181.3 从原单位满射到原锥的两向识别

继续证明。典范 $G=\operatorname{Aut}(C)^\circ$ 是闭连通矩阵Lie群，精确复用179.2证明首段的闭子群论证；该论证只需 $C$ 闭以及 $GL(E)$ 中逆映射连续。记 $\mathfrak g=\operatorname{Lie}G$、$\mathfrak p=\mathfrak g\cap\operatorname{Sym}(E,g)$。

先对任意 $v\in C^\circ$ 支付评价的单射性。原序单位范数

$$
\|x\|_v=\inf\{r\ge0:-rv\le_C x\le_C rv\}
\tag{181.10}
$$

是有限维真范数：内点性给吸收性，闭凸性给闭的绝对凸单位球，尖性排除非零零范数方向。每个 $S\in G_v$ 连同其逆保序且固定 $v$，故保持此范数；有限维范数等距群紧，$G_v$ 是其闭子群。若 $X\in\mathfrak p$ 且 $Xv=0$，则 $\exp(tX)\in G_v$ 对所有实 $t$ 成立，因而整条指数族有界。原 $g$ 自伴随谱全实，有界性排除每个非零特征值，于是 $X=0$。这证明

$$
\operatorname{ev}_v\text{ 对每个 }v\in C^\circ\text{ 单射},\qquad
\dim\mathfrak p\le\dim E.
\tag{181.11}
$$

因此原 $u$ 处满射、(181.4)两种维数形式严格等价；一旦成立，每个内点处的评价都是线性同构。这个结论没有使用齐性或伴随封闭，也不适用于任意边界点。

只在证明中令 $K=G\cap O(g)$，$\mathfrak k=\operatorname{Lie}K=\mathfrak g\cap\mathfrak{so}(g)$。$K$ 紧，故可取

$$
e=\int_Kku\,dk.
\tag{181.12}
$$

选 $r>0$ 使 $u+B_g(0,r)\subset C$；每个 $k\in K$ 正交且保锥，同一个半径对全部 $ku$ 成立，凸平均后仍有 $e+B_g(0,r)\subset C$。故 $e\in C^\circ$ 且 $Ke=e$。这是证明用内点，不是新增输入或替换原 $u$。(181.11)和原单位满射给 $\operatorname{ev}_e:\mathfrak p\to E$ 同构，无须先找将 $u$ 搬到 $e$ 的群元。

对每个 $x$ 取唯一 $L_x\in\mathfrak p$ 使 $L_xe=x$，置 $x\circ_e y=L_xy$。此乘法双线性。正标量伸缩保持原锥，其指数路径给 $I\in\mathfrak p$，所以 $L_e=I$。两个自伴随Lie元的交换子属于 $\mathfrak k$，而 $\mathfrak k e=0$，故

$$
[L_x,L_y]e=0,\qquad x\circ_e y=y\circ_e x,
\qquad g(x\circ_e y,z)=g(y,x\circ_e z).
\tag{181.13}
$$

这一步只用交换子的斜伴随性，不假设尚未取得的分解 $\mathfrak g=\mathfrak k\oplus\mathfrak p$。对 $k\in K$，共轭保持 $\mathfrak p$ 且固定 $e$，评价唯一性给 $kL_xk^{-1}=L_{kx}$。微分得 $[\delta,L_x]=L_{\delta x}$（$\delta\in\mathfrak k$），即每个 $\delta$ 为 $\circ_e$ 的斜伴随导子。于是(178.10)–(178.11)的纯代数前件已逐项具备：取 $\delta=[L_a,L_c]$，

$$
0=g(\delta(b^2),b)+g(b^2,\delta b)=3g(b^2,\delta b),
\qquad
g([L_{b^2},L_b]a,c)=-g(b^2,[L_a,L_c]b)=0.
\tag{181.14}
$$

任意 $a,c$ 及非退化性给 $[L_{b^2},L_b]=0$，即Jordan恒等式；没有断言某个这样的导子自动消去 $b$。若 $\sum_jx_j^2=0$，与 $e$ 配对得 $\sum_jg(x_j,x_j)=0$，所以形式实。至此才有同一 $E,g$ 上以 $e$ 为单位的有限维Euclidean Jordan代数。

现在精确复用178.12–178.14的纯Jordan谱论片段，代入刚构造的 $(E,\circ_e,e,g,L)$。其幂结合性供应为HS引理2.4.5；实自伴随谱及幂等元处的Jordan极化给

$$
\begin{gathered}
a=\sum_i\lambda_ic_i,\quad \sum_ic_i=e,\quad
c_i\circ_e c_j=\delta_{ij}c_i,\quad c_i\ne0,\quad\lambda_i\in\mathbb R,\\
Q:=\{x\circ_e x:x\in E\}
=\{a:L_a\ge_g0\}=Q_g^*.
\end{gathered}
\tag{181.15}
$$

该片段只消费刚支付的有限维含幺Jordan代数和原正Frobenius型，不消费原锥的自对偶或传递性；特别地，$2L_c^3-3L_c^2+L_c=0$ 给幂等元乘法算子的非负谱。故 $Q$ 闭凸且 $e\in Q^\circ$，其内点恰为全部谱值严格正的元素。

还须证明原 $C$ 恰为这个 $Q$，不能用传递性反推。对 $z=\sum_i\mu_i^2c_i\in Q$ 和 $\varepsilon>0$，令 $a_\varepsilon=\sum_i\log(\mu_i^2+\varepsilon)c_i$。由于 $L_{a_\varepsilon}\in\mathfrak g$，在同一原空间内有

$$
\exp(L_{a_\varepsilon})e
=\sum_i(\mu_i^2+\varepsilon)c_i=z+\varepsilon e\in C^\circ.
\tag{181.16}
$$

令 $\varepsilon\downarrow0$，原闭性给 $Q\subseteq C$。反向，任取 $z\in C$，用(181.15)对这个同一原向量写 $z=\sum_i\lambda_ic_i$。因 $L_{c_i}\in\mathfrak g$，对每个 $t>0$ 有

$$
e^{-t}\exp(tL_{c_i})z
=\lambda_ic_i+e^{-t}\sum_{j\ne i}\lambda_jc_j\in C,
\qquad \lambda_ic_i\in C\quad(t\to+\infty).
\tag{181.17}
$$

若 $\lambda_i<0$，则非零 $c_i=c_i^2\in Q\subseteq C$，同时 $-c_i\in C$，违反原尖性。故所有 $\lambda_i\ge0$，$z=(\sum_i\sqrt{\lambda_i}c_i)^2\in Q$。这样独立取得两个包含和 $C=Q=Q_g^*=C_g^*$，而非一个抽象同构。

对任意 $z\in C^\circ=Q^\circ$，置 $a_z=\sum_i\log\lambda_i\,c_i$，则 $S_z:=\exp(L_{a_z})\in G$ 且 $S_ze=z$。所以对任意原内点 $a,b$，同一原 $S_bS_a^{-1}\in G$ 将 $a$ 送到 $b$，恢复全局传递性。又对 $S\in\operatorname{Aut}(C)$、$x,y\in C$，$g(S^{\dagger_g}x,y)=g(x,Sy)\ge0$，自对偶给 $S^{\dagger_g}C\subseteq C$；对 $S^{-1}$ 同样应用便得等号。伴随是连续对合且固定 $I$，故保持恒等分支，$G^{\dagger_g}=G$。最后 $F=2g$ 给

$$
\Gamma_q(S,R)\Longleftrightarrow
\forall x,y:\ g(Sx,y)=g(x,Ry)
\Longleftrightarrow R=S^{\dagger_g}.
\tag{181.18}
$$

全部伙伴因此在精确原 $G$ 内存在且唯一；一般不是群逆。所用平均、Jordan乘法和谱事实均为证明中间对象，没有增添原可调用变换。

### 181.4 反向、原单位适配及完整消费者

继续证明。逐个原对象应用以上论证，恢复定义180.1仅被替换的两个条款，得到 $\mathcal C_{181}\Rightarrow\mathcal C_{180}$。此后才完整使用180.2和179.2，接上(181.5)后两项及178扩张群的字面唯一性。

反向从 $\mathcal C_{180}$ 出发，180.2已合法支付 $R_0=I$、原 $g$、全群伴随封闭和原传递性。此时定理178.3的全部原 $(E,g,C,G_C)$ 前件成立；只取其178.8的 $\mathfrak p\to E$ 在辅助 $e_*$ 处同构，得到 $\dim\mathfrak p=\dim E$。本证明(181.11)对原 $u$ 的单射性遂给 $\operatorname{ev}_u$ 满射。没有把 $e_*$ 当作 $u$，也没有假设共轭保持原 $g$ 的自伴随空间。保留所有原资料和见证就得到181.1；179及178扩张的反向通过既有等价取得。

下面精确接回整个消费者。临时(181.12)的 $e$ 和 $\circ_e$ 不用来检验原D；仍沿用180.3/178.18及C123(3.3)–(3.4)中的原选择 $e_*\in C_A^\circ$、$h_A\in G_C(A)$、$h_Au_A=e_*$，以

$$
\widehat g_A(x,y)=g_A^0(h_Ax,h_Ay)
\tag{181.19}
$$

构造同一个原 $u_A$ 适配乘法 $\circ$。全部全局前件现已恢复，原选择仍然可用；不需将它等同于本证明的临时平均选择，不假设 $h_A$ 交织原D。原D的全载体导子律及三元交换子抵消仍作用在这个 $\circ$ 上。180.14/178.4/C124命题11.1的参数因而逐项相同：

$$
a\cdot b=a\circ b-iD_ab,\qquad
\mathcal A_A\cong\bigoplus_sM_{n_s}(\mathbb C),\qquad
(E_A,C_A,u_A)=((\mathcal A_A)_{\rm sa},(\mathcal A_A)_+,I_A).
\tag{181.20}
$$

复类型仍由原D选择，X的原嵌入、乘法/D保持、交叉D为零、乘积张成和原乘积准备供应全部已声明联合的普通复张量积及中心对。每个实际联合自身的条件和 $N_u$ 仍分别承担联合内酉的数学包含与系数一完整原调用；没有从局部满射推出实际联合控制。

180.15–180.16/178.5给同一个 $\tau_A=\sum_s\operatorname{Tr}_{n_s}$ 及唯一迹自伴随正定算子 $B_A$。对原准备、效果及 $f:A\to B$，精确沿用

$$
\begin{aligned}
g_A^0(x,y)&=\tau_A((B_Ax)y),&B_A(C_A)&=C_A,\\
\rho_\alpha&=B_Ax_\alpha,&m_\alpha&=\tau_A(\rho_\alpha)=\alpha(u_A),\\
v_\alpha&=B_A^{-1/2}\rho_\alpha,&w_e&=B_A^{-1/2}e,\\
\alpha(e)&=\tau_A(\rho_\alpha e)=g_A^0(v_\alpha,w_e),&
\Phi_f&=B_BT_f^{\dagger_0}B_A^{-1},\\
T_p(r)&=\tau_A(pr)=\tau_A(rp)=T_r(p)
&&=g_A^0(B_A^{-1/2}p,B_A^{-1/2}r).
\end{aligned}
\tag{181.21}
$$

这里 $\alpha=g_A^0(x_\alpha,\cdot)$，$T_f:E_B\to E_A$；$B_A^{-1/2}$ 是实响应空间算子的逆平方根。每个联合使用自己的 $B_{AB}$，不假设张量因子化。$p,r$ 是数学归一底中任意单块迹一秩一投影；$T_p(r)$ 是180.16在完整数学效果区间上的确认最小值，不同块为零，不是旧子菜单上的同一个最小值或原Riesz向量的裸重叠。数学底、效果和POVM的完整范围仍为全部密度矩阵、$[0,I_A]$ 及有限正效果的单位分解；实际准备的完整正锥包仍不供应每个底点的质量一准备。原 $m_\alpha\le1$ 和全部历史成功因子保留，正质量才可条件归一，零质量不除法。

180.4/178.6的几何资格不变：复结构取得后，大小至少二的块中二维复支撑面的数学底是 $\rho=(\Pi_S+\mathbf r\cdot\boldsymbol\sigma)/2$、$|\mathbf r|\le1$ 的闭Bloch三球，其球面比较为 $(1+\mathbf r\cdot\mathbf s)/2$。它不自动是一只原可附接 $M_2$ 对象或满质量实际准备集。只有另保留原 $C_A$ 不可约、$\dim E_A=n^2$、固定整数 $n\ge2$，并实际声明全部 $A^{\otimes N}$ 及各自全部联合、准备、D和原接口，才对每个有限 $N$ 得 $C_{A^{\otimes N}}=\operatorname{PSD}_{n^N}$；$P$ 的所有参考幂不替任意 $A$ 声明这些对象。

全事件结论精确复用180.4/178.4/C124命题11.3：整个实际 $P$ 的AC给某块维数 $r\ge2$ 的原质量一纯准备和系数一破坏性读口，实际 $P^{\otimes k}$ 的参考块 $r^k$ 无界。R的同记录执行及每个完整原联合准备锥上的保正，对每个输入块支付充分参考层，故(181.21)的每个原事件、细支、失败、标签、遗忘、返回及全部有限合法历史均CP/TNI，完整装置求和TP。不将此量词缩成新选词或乘积输入。

180.18/178.20/C124定理12.1的选中原完整有限装置 $W_e$ 及其全部见证照用：每个数学 $0\le e\le I_A$，包括奇异、零和零中心分量，都有成功作用 $\operatorname{Ad}_{\sqrt e}$，每个已声明实际相关参考上为 $\operatorname{Ad}_{\sqrt e\otimes I_R}$。整个原 $P$、实际准备、比较、测试、补事件、失败端丢弃前的算子输出、系数、细记录及实际丢弃均原样保留，具体输出按C124(12.5)–(12.8)，不先取迹替代。C124命题12.2仍对原F给每个非零指定返回细支

$$
S_a=\operatorname{Ad}_{K_a},\qquad
U_a=q_{F,a}\operatorname{Ad}_{K_a^+},\qquad q_{F,a}>0,
\tag{181.22}
$$

连同原单中心输入/输出支持角、原同系数双返回等式和反向资料；零支保留标签，原遗忘仍是原细支求和。阶段细口只在原连线合法时相乘，否则用整个原词自己的全称F；任意数学Kraus指标不成为原记录。按180.15/178.25的迹对偶等式逐次运输每段原合法历史，原概率、输出、成功质量、记录、返回数和正条件分母均不变。

选中 $W_e$ 的正成功质量才给条件态 $\sqrt e\rho\sqrt e/\tau_A(\rho e)$。旧同效果设备仍须自己的完整输出校准才能认作此更新；逐效果 $W_e$ 供应不自动组装任意指定原POVM仪器。时间仍只在C123命题4.1的原连续、确定、可逆一参数动态及物理钟标定下给逐块 $\rho_s(t)=e^{-itH_s/\hbar}\rho_s(0)e^{itH_s/\hbar}$，不由(181.3)指定Hamiltonian、$\hbar$ 或钟。至此完整180.3–180.4的消费者、量词和实际见证全部接回。

### 181.5 生成元的含义及中文几何解释

继续证明中的范围说明。$X\in\mathfrak p_A^0$ 的含义是原型自伴随且 $\exp(tX)$ 对全部实 $t$ 保持原锥，不是 $X$ 本身保正，也不要求 $I+tX$ 保正。此区别可在复矩阵锥的迹型几何中直接核算：在一个二维支撑上取 $H=\operatorname{diag}(1,-1)$、$X(z)=(Hz+zH)/2$。它迹自伴随且 $\exp(tX)z=e^{tH/2}ze^{tH/2}$ 保锥，但 $X(E_{22})=-E_{22}$ 不保正；对 $z=\left(\begin{smallmatrix}1&1\\1&1\end{smallmatrix}\right)\ge0$，

$$
(I+tX)z=\begin{pmatrix}1+t&1\\1&1-t\end{pmatrix},
\qquad \det((I+tX)z)=-t^2<0\quad(t\ne0).
\tag{181.23}
$$

故连任意小的非零Euler步也不必保锥；这种数学核算不供应一台原可控装置。

用中文读(181.5)：先只要求“不做变化”有一个反向伙伴；同一读数的四角差量、下界和探针分离会迫使这个伙伴仍是不做变化，并恢复原尺子。然后只在原单位 $u$ 看全部关于这把尺子自伴随的无穷小锥变形，要求它们作用在 $u$ 上的方向铺满原空间。固定任一内点的保序变化都受序单位范数约束，自伴随变形若不移动该内点就只能为零，所以方向既无缺口也无多余。这个维数事实可搬到证明用的旋转平均点，在那里把方向组织成含幺Jordan乘法；谱分解和原锥的尖性迫使原来的正锥恰好是平方锥。于是全部内点可互达、全部伙伴为原伴随，都是结论。平均点从未替换原设备的单位；原D仍在原单位适配的乘法上选出复类型。

这种静态几何也容纳经典标量直和；复结构、AC的非经典实际指针以及联合、参考和调用条件各有自己的职责。正确运输后的纯确认比较是两条射线的重叠，交换比较端点数值不变；顺序历史却逐次复合状态映射，交换执行先后并不由此保持输出或概率。数学三球上的点、保锥指数的存在、实际质量一准备、原装置的精确控制、旧设备的更新和物理时间各守上述资源范围。

本结论是完整候选在同一原数值和实际见证上的等价，不是独立物理公理数减少、任意锥呈示的有限判定算法、实际可控性或物理资料满足性的证明。幂结合、自伴随谱和Lie群事实只作上述中间供应；没有以预设EJA的Lie代数分解反向赚取Jordan前件，也不以这里的综合推导主张文献优先权。$\square$

## 追加锚（本行以下为增补区）
