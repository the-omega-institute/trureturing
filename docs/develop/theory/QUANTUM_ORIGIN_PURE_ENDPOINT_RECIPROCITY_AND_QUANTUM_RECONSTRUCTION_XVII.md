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
