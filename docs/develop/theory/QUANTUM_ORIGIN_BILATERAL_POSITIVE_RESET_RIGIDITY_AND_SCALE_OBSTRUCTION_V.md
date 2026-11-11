# QUANTUM ORIGIN: BILATERAL POSITIVE RESET RIGIDITY AND SCALE OBSTRUCTION V

本卷续接[第四卷](QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_IV.md)。章节编号延续第四卷；第 65–72 章的全部章节、条目与公式引用，以及第 64 章的引用，均指第四卷；第 73 章及其内部编号引用均指本卷。

## 73. 双侧正重置补全的标量刚性与原接口的精确余尺度

本节研究同一个实际二元接合在两个输入位置上的概率补全。交叉方向先由定义 71.1 的完整 PRE 与定义 71.8 的 NB 处理；定理 71.6、命题 71.8a 及推论 66.10 已供应同时普通乘积方向。这里不重新证明该入口，不用重置推出 C13，也不把已获 Born 几何、69.8 的第一位置行一致或标准振幅收缩计算为新增数学内容。要确定的是：同一实际接合的两个位置都允许正份额共同重置时，究竟消去哪些原滤子，还有什么读数不能被这种关系看见。

### 73.1 从同一实际数据进入普通方向

**约定 73.1（前件、原对象与复用顺序）。** 完整保留定义 71.1 的 PRE：三个非零有限实全态全效应系统、完整有限混合比较律 $S$ 及其所引忠实规范迹 Jordan 条件纸面桥，实际全锥正 $L:D\times A\to E$、$p:E\to D$，原比较单位及 $\omega=1_D/\tau_D1_D$，同一个实际 $p$ 两次定义的

$$
M(a,b)=pL(pL(\omega,a),b),\quad J(a)=M(a,1_A),\quad
H(d)=L(d,1_A),\quad B_1=pH,
$$

两条实际实张成，以及覆盖原有全部量词的 $D_J,D_H,Z$。其中 $D_H$ 测试整个实际 $D_+$，$Z$ 测试全部实方向，不只测试准备样本。保留定义 64.3、65.1、66.1、71.1 明列的二元接口、有限 Jordan 分类、秩一乘积保持及完整 $S$ 的条件纸面来源，不另行假定一套 Jordan 或复矩阵输入。

采用 NB 时，$\mathfrak E(F)$ 严格指定义 71.4 的完整关系：每个两端非标量的活跃有序块有任意严格正质量，条件态联合纯而 $F$ 内在边缘混；非活跃块是任意 PSD 分量，包括零，总迹为一；无活跃块时是整个态基。NB 是其中存在一个原态经原始 $I^{\rm raw}$ 插入仍正。其非空性、每个成员检测 C13、无须预选 Bell 基或运输原态，全部复用 71.5–71.6；71.6a 的无统一负隙与 71.7 的全类自然单点障碍同样保留。NB 不供应这些态的物理制备。

只有在这一步得到原 C13 后，才依 66.10、65.10 写同一实际映射为

$$
\begin{gathered}
A=\bigoplus_i H_{n_i},\quad D=\bigoplus_{i,j}H_{n_in_j},\quad
E=\bigoplus_{i,j,k}H_{n_in_jn_k},\qquad n=\sum_i n_i,\\
M(a,b)_{ij}=a_i\otimes\sqrt{u_{ij}}b_j\sqrt{u_{ij}},\qquad
L(d,a)_{ijk}=d_{ij}\otimes\sqrt{g_{ijk}}a_k\sqrt{g_{ijk}},\\
u_{ij}>0,\quad g_{ijk}>0,\qquad
\sum_{i,j}n_i\operatorname{Tr}(u_{ij}^{-1})=n^2.
\tag{73.1}
\end{gathered}
$$

全部有序块、重复标签、标量和不等维扇区均保留。这里的矩阵坐标保持原态、效应、迹和比较；$M$ 不是独立供应的准备，$L$ 的第一输入仍是整个实际 $D$，包括纠缠正元。以下先对任意这样的二元接口证明，再分别代入这两个原接口。

### 73.2 两个位置的延拓必须属于同一个接合

**定义 73.2（一般正滤波接合及正补全）。** 取有限非空标签集，记 $H_r=\operatorname{Herm}_r(\mathbb C)$，令

$$
\begin{gathered}
B=\bigoplus_b H_{d_b},\qquad C=\bigoplus_k H_{n_k},\qquad
J=\bigoplus_{b,k}H_{d_bn_k},\quad d_b,n_k\ge1,\\
S_{bk}=I_{d_b}\otimes\sqrt{w_{bk}},\quad w_{bk}>0,\qquad
(C_wZ)_{bk}=S_{bk}Z_{bk}S_{bk},\\
m_w(x,y)_{bk}=x_b\otimes\sqrt{w_{bk}}y_k\sqrt{w_{bk}}.
\tag{73.2}
\end{gathered}
$$

$\tau_B,\tau_C,\tau_J$ 均为所有实际块的普通迹之和，伴随取其迹内积。$C_w$ 及其逆是整个 $J_+$ 的序同构，通常不保迹。所有映射先定义在实 Hermitian 空间；谈放大时用其唯一复线性保 Hermitian 延拓。

对任一局部实线性 $\Phi:B\to B$ 或 $\Theta:C\to C$，其联合延拓必须满足全部实输入的原乘积律

$$
\widehat\Phi m_w(x,y)=m_w(\Phi x,y),\qquad
\widehat\Theta m_w(x,y)=m_w(x,\Theta y).
\tag{73.3}
$$

在一个位置，固定任意输出块及该块内任意密度 $\sigma$，允许秩亏，定义总迹重置

$$
R_\sigma(z)=\tau(z)\sigma,
\tag{73.4}
$$

其余输出块为零。固定 $0<c\le1$。该位置的“正重置补全”指存在有限个局部正实线性分支 $\Gamma_s$，使

$$
T=cR_\sigma+\sum_s\Gamma_s
\tag{73.5}
$$

在局部保总迹，且按 (73.3) 唯一确定的每个联合分支 $c\widehat R_\sigma,\widehat\Gamma_s$ 在整个 $J_+$ 上正，其总和 $\widehat T$ 在整个联合锥上保总迹。局部与联合的每支 TNI 随正性及各自总和 TP 自动成立。$c=1$ 可不列零失败分支。两位置可以固定不同的输出块、重置态、正份额和失败分支，不要求两套总过程相同或交换。

这个定义没有假定局部分支 CP。它量化的是相同原对象、相同原迹、相同接合与其实际实张成上的映射存在性；任意另给一个联合正 TP 映射，如果不满足 (73.3)，不构成本定义的补全。也没有把数学存在量词改写成原装置、菜单、记录或控制的供应断言。

**定理 73.3（两个唯一延拓与非交换双预算）。** 以 $\Phi_{ab}$ 表示输入块 $b$ 到输出块 $a$，以 $\Theta_{\ell k}$ 表示输入块 $k$ 到输出块 $\ell$。置

$$
(T^B_\Phi Z)_{ak}=\sum_b(\Phi_{ab}\otimes\operatorname{id}_{n_k})Z_{bk},\qquad
(T^C_\Theta Z)_{b\ell}=\sum_k(\operatorname{id}_{d_b}\otimes\Theta_{\ell k})Z_{bk}.
$$

(73.3) 的唯一实线性解分别为

$$
\widehat\Phi=C_wT^B_\Phi C_w^{-1},\qquad
\widehat\Theta=C_wT^C_\Theta C_w^{-1}.
\tag{73.6}
$$

特别地，右位置的完整公式是

$$
(\widehat\Theta Z)_{b\ell}
 =S_{b\ell}\left[\sum_k(\operatorname{id}_{d_b}\otimes\Theta_{\ell k})
 (S_{bk}^{-1}Z_{bk}S_{bk}^{-1})\right]S_{b\ell}.
\tag{73.7}
$$

若 $\Phi,\widehat\Phi$ 都正，记 $F_{ab}=\Phi_{ab}^*(I_a)\ge0$。其局部 TNI／TP 预算与联合 TNI／TP 预算分别为

$$
\sum_aF_{ab}\le I_b,\qquad
\sum_aF_{ab}\otimes w_{ak}\le I_b\otimes w_{bk}
\quad(\forall b,k),
\tag{73.8}
$$

其中分别把 $\le$ 换成 $=$ 就得到对应 TP 条件。若 $\Theta,\widehat\Theta$ 都正，右位置的两预算分别为

$$
\sum_\ell\Theta_{\ell k}^*(I_\ell)\le I_k,\qquad
\sum_\ell\Theta_{\ell k}^*(w_{b\ell})\le w_{bk}
\quad(\forall b,k).
\tag{73.9}
$$

等号同样分别刻画 TP。特别地，对任一右局部总映射 $T:C\to C$，其联合延拓 TP 当且仅当

$$
T^*w_b=w_b\quad(\forall b),\qquad w_b=(w_{bk})_k\in C.
\tag{73.10}
$$

**证明。** 每个完整 Hermitian 块由实 Hermitian 简单张量张成，按输入中心标签可单独支撑任意 $(b,k)$；$C_w$ 可逆，故 $m_w(B,C)$ 实张满整个 $J$。两式 (73.6) 在全部乘积上满足 (73.3)，从而存在且唯一。这没有断言乘积正元生成整个联合正锥；正性仍须测试纠缠输入。

左式取迹伴随作用于联合单位，在输入 $(b,k)$ 得

$$
(\widehat\Phi^*1_J)_{bk}
 =\sum_a F_{ab}\otimes
       w_{bk}^{-1/2}w_{ak}w_{bk}^{-1/2}.
\tag{73.11}
$$

其推导仅用 $T^B_\Phi$ 的迹伴随，不用 Kraus 表示。对该效应作 $S_{bk}$ 合同得到 (73.8)。局部预算是相同的迹对偶论证。右式则给

$$
(\widehat\Theta^*1_J)_{bk}
 =I_b\otimes w_{bk}^{-1/2}
 \left[\sum_\ell\Theta_{\ell k}^*(w_{b\ell})\right]w_{bk}^{-1/2}.
\tag{73.12}
$$

正映射 TNI 等价于效应不超过单位，TP 等价于效应为单位，故得到 (73.9)–(73.10)。这里先去输入滤子，作用局部映射，再放回输出滤子；伴随把输出权重放入 $\Theta_{\ell k}^*$ 内。不能将它交换到映射外，也没有假定不同行权重同时对角化。TP 的迹恒等式本身对任意实线性映射也成立；TNI 的正分支解释另需已述正性。$\square$

左式是 69.2、69.4 在一般两个载体上的直接复用，(73.8) 的效应论证明确说明其必要性没有用 CP。右式把右槽实际滤波及块间迁移的对偶预算补齐，不能由把 (73.8) 的标签对调得到。

### 73.3 共同正份额所能固定的全部读数

**证明工具 73.4（正重置的整直和固定点）。** 在任一非零有限 Hermitian 直和 $V$ 上，若 $T=cR_\sigma+\Gamma$ 局部 TP、$\Gamma\ge0$、$\tau\sigma=1$、$\sigma\ge0$、$0<c\le1$，则

$$
\operatorname{Fix}(T^*)=\mathbb R1_V.
\tag{73.13}
$$

具体地，对任意 Hermitian $h$，定义整个直和的谱振幅

$$
\operatorname{osc}(h)
 =\max_k\lambda_{\max}(h_k)-\min_k\lambda_{\min}(h_k).
$$

有

$$
\operatorname{osc}(T^*h)\le(1-c)\operatorname{osc}(h).
\tag{73.14}
$$

这是正保单位映射的标准序单位／Hopf 振幅方法的共同重置特例，见文末 Gaubert–Qu §6；不将它计为新的振幅或遍历定理。

**证明。** 局部 TP 给 $\Gamma^*1=(1-c)1$，而

$$
R_\sigma^*h=\tau(\sigma h)1.
$$

设 $a=\min_k\lambda_{\min}(h_k)$、$b=\max_k\lambda_{\max}(h_k)$。正性给

$$
(1-c)a1\le\Gamma^*h\le(1-c)b1.
$$

加上同一个标量 $c\tau(\sigma h)1$ 只平移谱区间，故得 (73.14)。固定点振幅必为零，即每块都是相同标量，反向由 $T^*1=1$ 得到。$c=1$ 时上述两界都为零，直接给 $\Gamma^*h=0$，无需除以 $1-c$。证明只用 $\sigma$ 正且迹一，允许它仅支撑一个块及该块任意秩；不要求它是内点。若存在非标量方向，取 $\Gamma=(1-c)\operatorname{id}$ 即达到系数 $1-c$。$\square$

只在每个块内部计算振幅是不够的：它不能区分不同块上的不同标量。(73.13) 针对整个直和的同一单位，正是下面跨右标签校准所需的结论。

**命题 73.5（第一位置的正性范围与已获行一致）。** 定义 73.2 的第一位置正补全存在，当且仅当

$$
w_{bk}=v_k>0\qquad(\forall b,k).
\tag{73.15}
$$

这里行一致结论及其共同锚点证明复用定理 69.8；将局部分支从 CP 放宽为正，必要性仍成立，逆向也仍有全锥正构造。

**证明。** 对补全的局部总映射 $P$，正性给 $F_{ab}\ge0$，重置成功分支给 $F_{b_0b}\ge cI_b$，局部 TP 与联合 TP 分别给 (73.8) 的两条等式。这恰是 (69.18) 的全部输入；对首腿除以实际 $d_b$ 的归一偏迹，得到 (69.19) 的行随机共同锚点关系。69.8 后续的有限凸包收缩只用这些正效应，不用 CP，亦不用等维或 $\sigma$ 满秩，故原证明原样适用。

也可把同一关系写成 73.4 的固定点，以显示左右证法的共同结构。对每个实 $y\in C$，令

$$
(h_y)_b=\left[\sum_k\operatorname{Tr}(w_{bk}y_k)\right]I_b,
\qquad \tau_Jm_w(x,y)=\tau_B(xh_y).
\tag{73.16}
$$

由总延拓 TP 和 (73.3) 得 $P^*h_y=h_y$。73.4 迫使括号内的数对全部 $b$ 相等。让 $y$ 仅支撑任意一个块并遍历该块全部 Hermitian 矩阵，迹配对非退化即给 (73.15)。这是同一个已获左位置条件的另一证明，不是第二项独立新校准。反向的整锥构造见定理 73.7。$\square$

**定理 73.6（右位置补全的精确标量固定效应）。** 对定义 73.2 中任意固定输出块、任意秩的固定密度 $\sigma_C$ 及任意固定 $0<c_C\le1$，第二位置正补全存在，当且仅当

$$
w_{bk}=\lambda_b I_{n_k}\qquad(\forall b,k),\qquad\lambda_b>0.
\tag{73.17}
$$

同一行的 $\lambda_b$ 必须跨所有右标签相同；本结论不只给出每个块内的中心性。

**证明。** 对补全取 $T=c_CR_{\sigma_C}+\sum_s\Gamma_s$。联合 TP 由 (73.10) 使每个原行元组 $w_b$ 成为 $T^*$ 的固定点；局部 TP 和正剩余映射使 73.4 适用。因此 $w_b=\lambda_b1_C$。严格正定性给 $\lambda_b>0$。这里 $w_b$ 是迹权重，谱可大于一；若用效应语言，可把整行除以一个共同的足够大正数，不改变固定点结论。

这一论证涵盖 $c_C=1$、秩一重置、标量扇区和不等维扇区，未用 CP、不可约性或各权重交换。反向由 (73.17)，$C_w$ 在每个固定左行是标量倍恒等，右槽跨 $k$ 的输入、输出倍率相消；对重置及恒等的实际正延拓作 (73.19) 的构造，即得到指定正份额的补全。$\square$

### 73.4 双侧分类的逆向必须测试完整联合锥

**定理 73.7（双侧精确分类及显式逆向）。** 对同一个 $m_w$，两位置各自有定义 73.2 的正补全，当且仅当存在同一个 $\lambda>0$，使

$$
\boxed{\quad w_{bk}=\lambda I_{n_k}\quad\text{对全部 }b,k.\quad}
\tag{73.18}
$$

在相应单侧条件下也有逆向：左侧恰要求 (73.15)，右侧恰要求 (73.17)。对每侧任意预先指定的合法重置输出、密度和正份额，都能构造补全。

**证明。** 必要性由 73.5 与 73.6 相交：$v_k=\lambda_bI_{n_k}$ 对任意 $b,k$ 成立，有限非空标签集使所有 $\lambda_b$ 相同。没有等维、非标量或满秩重置前提。

为证明各单侧的充分性，设输出块分别为 $b_0,k_0$。在各自单侧条件下，原联合重置的非零输出块是

$$
\begin{aligned}
(\widehat R_BZ)_{b_0k}
 &=\sigma_B\otimes\sum_b\operatorname{Tr}_{B_b}Z_{bk},\\
(\widehat R_CZ)_{bk_0}
 &=\left(\sum_k\operatorname{Tr}_{C_k}Z_{bk}\right)\otimes\sigma_C.
\tag{73.19}
\end{aligned}
$$

第一式的 $v_k$ 在偏迹前后作互逆合同而相消；第二式的同一行标量 $\lambda_b$ 在输入与输出相消。两式可先在简单张量核对 (73.3)，由 73.3 唯一性得到整个实 $J$ 上的等式。

对任意联合 PSD 输入，每个偏迹、求和、与固定正密度的张量积都保持正性，故 (73.19) 在整个联合锥上正，包括纠缠输入。输出总迹恰为输入总迹。再取局部分支

$$
cR,\qquad (1-c)\operatorname{id},
$$

对应联合分支为 $c\widehat R,(1-c)\operatorname{id}_J$。两层各支正且 TNI，两层总和 TP。$c=1$ 省去零分支即可；任意秩的 $\sigma$ 都适用。这完成单侧及双侧充分性。$\square$

等价分类可直接从原联合质量读出：双侧补全恰使

$$
\tau_Jm_w(x,y)=\lambda\tau_B(x)\tau_C(y)
\quad(\forall x,y).
\tag{73.20}
$$

反向由独立块支持和全部 Hermitian 测试恢复 (73.18)，所以它不是仅在选定参考态上的等式。但没有任何预算在此固定 $\lambda=1$。

以上只构造所需重置及恒等，绝不声称任意局部正映射都有正联合延拓。由 $C_w$ 及其逆全锥正，某个指定分支的联合正性等价于其 $T^B$ 或 $T^C$ 放大正性；这是实际旁观者尺寸上的条件，须单独核对。

### 73.5 回到原 M、L：第一尺度被迫为一，第二尺度恰好保留

**定理 73.8（两个实际接口的残余分类）。** 在约定 73.1 的完整 PRE+NB 上，对实际 $M$ 的两个输入位置、实际 $L$ 的两个输入位置分别施加定义 73.2 的补全，共四项。则在已经由 NB 付出的同时普通方向中，恰有

$$
\boxed{
M(a,b)_{ij}=a_i\otimes b_j,\qquad
L(d,a)_{ijk}=\kappa\,d_{ij}\otimes a_k,\qquad
(pz)_{jk}=\kappa^{-1}\sum_i\operatorname{Tr}_i z_{ijk},\quad \kappa>0.}
\tag{73.21}
$$

反向，每个正 $\kappa$ 的这组同一实际数据都满足 PRE+NB 和四项补全。

**证明。** 对 $M$ 代入 $B=C=A,w_{ik}=u_{ik}$。73.7 给 $u_{ik}=\lambda I_k$，原已获逆迹平衡立即给

$$
n^2=\sum_{i,k}n_i\operatorname{Tr}(u_{ik}^{-1})
 =\lambda^{-1}\sum_{i,k}n_in_k=\lambda^{-1}n^2.
\tag{73.22}
$$

因 $n>0$，$\lambda=1$。所以原 $U=1_D$，此处没有调用 $C_{\rm joint}$。

对 $L$ 必须代入 $B=D$，其左标签是整个有序对 $(i,j)$、维数为 $n_in_j$，右载体是 $A$。73.7 因而给 $g_{ijk}=\kappa I_k$，其中同一个 $\kappa$ 跨全部三重标签。没有关于 $g$ 的逆迹平衡可再用；不能把第一接口的 (73.22) 重用到第二接口。

剩下的原 $p$ 由已发表 (65.11)、(71.6a) 的全实恒等式

$$
pQ(a,b,c)=\tau_A(a)M(b,c),\qquad Q(a,b,c)=L(M(a,b),c)
\tag{73.23}
$$

及实际实张成唯一确定。现在 $Q=\kappa(a_i\otimes b_j\otimes c_k)_{ijk}$。每个块的实 Hermitian 简单三张量张满整个 $E$，故 (73.23) 给且只给 (73.21) 的首腿偏迹。这是在同一原 $p$ 上使用全实恢复律，不是任意正读回在一个参考上取对值就获得的唯一性。反向可直接取 65.11 的 $u=I,g=\kappa I$；73.9 还逐项核对同一 $p$ 两次的关键尺度抵消。四项全锥正补全由 73.19 给出。$\square$

**命题 73.9（同一 p 两次的尺度反例与精确共轭不变性）。** 对每个 $\kappa>0$，(73.21) 的数据都满足保留的静态原定义；四项补全的存在性及每个指定局部映射的联合延拓均不依赖 $\kappa$。因此这些关系不可能单独固定第二尺度。

**证明。** 记原双份首腿读回

$$
(sd)_j=\sum_i\operatorname{Tr}_i d_{ij},\qquad
\omega=1_D/n^2,\qquad e=1_A/n.
$$

在 $L_\kappa(d,a)=\kappa d\otimes a$、$p_\kappa=\kappa^{-1}\operatorname{Tr}_1$ 中，直接从原定义计算

$$
\begin{aligned}
p_\kappa L_\kappa(d,a)&=s(d)\otimes a,\\
K_\kappa(a)&=e\otimes a,\qquad sK_\kappa(a)=a,\\
p_\kappa L_\kappa\bigl(p_\kappa L_\kappa(\omega,a),b\bigr)
 &=a\otimes b.
\tag{73.24}
\end{aligned}
$$

两次都是同一个 $p_\kappa$，中间没有换读回或参考。正性、实张成保留；$J$、$p_\kappa H_\kappa$ 与全实 $Z$ 不变；$H_\kappa=\kappa H_1$ 将 $D_H$ 的配对乘以正数 $\kappa^2$，保持其零关系。原插入 $I^{\rm raw}_\kappa=\kappa I^{\rm raw}_1$，所以 C13 与 NB 均保留；三载体的比较律、全态全效应也没有改变。这是 65.11、66.7、67.6、67.12 的已获尺度族在当前问题上的实际控制，不另计一项旧尺度分类。

对 $L_\kappa$，其滤波 $C_G=\kappa\operatorname{id}_E$，因此对任一槽的任一实线性局部映射，完整实空间上的延拓严格满足

$$
C_GT C_G^{-1}=T.
\tag{73.25}
$$

等价地，$\widetilde L_\kappa=\kappa\widetilde L_1$，所以其与局部张量作用的共轭不变。输入、输出两个尺度逐项抵消，正性、全部谱、局部与联合预算均完全相同；反复要求这种相同的共轭关系也无从区分 $\kappa$。这并非近似不可见性。最小实例已是 $A=D=E=\mathbb R$：$L(d,a)=2da,p(z)=z/2$，同一 $p$ 两次仍给 $M(a,b)=ab$，双侧补全和 C13 都成立。$\square$

### 73.6 一次原迹读数恰好消去最后的尺度

**定义 73.10（标量锚）。** 在同一个原迹与原比较单位下要求

$$
\mathrm A_0:\qquad
 a_0:=\tau_E L(\omega,e)=1,\qquad
 \omega=1_D/n^2,\quad e=1_A/n.
\tag{73.26}
$$

$\omega,e$ 是已给比较几何中的正迹一元；本等式是对实际 $L$ 的额外标量关系，不是已经推出的准备、测量装置或物理操作。若来源已经给定任意一对正迹一 $d_*,a_*$，在 73.8 的分类后用 $\tau_EL(d_*,a_*)=1$ 也固定同一个尺度；它不授权新增制备。

**定理 73.11（同一实际数据上的精确校准替换）。** 在完整 PRE+NB 上，四项正重置补全加 $\mathrm A_0$ 与原联合校准 $C_{\rm joint}$ 逐模型等价。记

$$
R=n^3,\qquad\delta=\tau_E L(1_D,1_A),\qquad
\gamma=\tau_D(p1_E),\qquad
C_{\rm joint}:\ \delta+\gamma\le2R.
\tag{73.27}
$$

有

$$
\boxed{\quad C_{\rm joint}
\quad\Longleftrightarrow\quad
\bigl[\mathrm{RC}_M^B\land\mathrm{RC}_M^C
\land\mathrm{RC}_L^B\land\mathrm{RC}_L^C\bigr]\land\mathrm A_0 .\quad}
\tag{73.28}
$$

每个 RC 指定义 73.2 在该实际位置的数学存在量词，允许任意预定合法输出、重置态及正份额。

**证明。** 从右侧出发，73.8 给 $u=I,g=\kappa I$ 及原 $p=\kappa^{-1}\operatorname{Tr}_1$，故

$$
a_0=\kappa,\qquad (\delta,\gamma)=(\kappa R,R/\kappa).
\tag{73.29}
$$

$\mathrm A_0$ 迫使 $\kappa=1$，从而满足 $C_{\rm joint}$；在这条分类族内，$\kappa+\kappa^{-1}\ge2$ 的等号也说明 $C_{\rm joint}$ 恰好选择 $\kappa=1$。

反向不预设补全。完整 PRE 包含定理 67.7 所需的 $\mathcal B+D_H$，故原 $C_{\rm joint}$ 直接给原 $U=1_D,H1_D=1_E$、原 $p$ TP。NB 独立给 C13 后，66.10 允许同时普通方向，65.10 的实际参数因而是 $u=I,g=I$。四个指定重置的延拓都由 (73.19) 构造为整个原联合锥上的正 TP 映射，再加恒等失败分支；$a_0=1$ 直接成立。所有原 $A,D,E,L,p,\omega$ 和内部定义保持不变，没有以缩放后的辅助模型替换实际模型。$\square$

73.28 的新内容不是重命名一条已经成立的校准：在不输入 $C_{\rm joint}$ 的方向，73.6–73.8 从正补全本身严格排除了全部矩阵滤波自由度；73.9 则证明剩下的一维尺度恰好不能再由同类关系检测，73.26 才补足它。与旧校准的比较是同数据等价，不是独立公理数量、量词数量或资源成本降低的结论。

### 73.7 不能删去的单侧、预算、参考和方向控制

**命题 73.12（单侧不足、标量锚不足及零成功份额）。** 下列控制均在有限实际矩阵类内，未删除任何标量或不等维边界。

1. 对 $A=\mathbb R^2$，取 $u$ 两行都为 $(2,2/3)$，并取 $g=I$。逆迹和为 $4=n^2$，65.11 给完整 PRE+NB 的实际模型。$M$ 左侧补全存在，右侧因每行不是同一标量而失败。
2. 取 $u=\left(\begin{smallmatrix}2&2\\2/3&2/3\end{smallmatrix}\right),g=I$，逆迹和仍为 $4$。右侧补全存在，左侧因两行不同而失败。两例表明任一单侧不能替代双侧；不是宣称整个候选各前件独立。
3. 取 $A=H_2$ 的单扇区、$u=I_2,g=\operatorname{diag}(1/2,3/2)$。65.11 给 PRE+NB，且 $a_0=\operatorname{Tr}g/2=1$；但 $L$ 的右侧补全由 73.6 排除。因此标量锚单独不能消去非标量滤子。反之 $u=I,g=2I$ 满足四项补全却有 $a_0=2$。
4. 若允许成功份额 $c=0$，零重置分支加恒等对任意 $w$ 都同时满足两层 TP，不提供校准。$c>1$ 则与正剩余映射及局部 TP 矛盾，因为 $\Gamma^*1=(1-c)1$ 不能为正；$c=1$ 已由 73.4 和 73.19 直接处理。

**证明。** 前两例各自的逆迹和为 $1/2+3/2+1/2+3/2$ 和 $1/2+1/2+3/2+3/2$，行一致与行标量条件分别直接代入 73.5–73.7。第三例 $\tau_D\omega=1$、$e=I_2/2$，故 $a_0=\tau_D\omega\operatorname{Tr}(ge)=1$；$g$ 两个特征值不同，违反 (73.17)。第四例由恒等的乘积律及正映射伴随保序性直接成立。$\square$

**命题 73.13（两层 TP 与 CP 的不同义务）。** 联合 TP 不能代替局部 TP，局部 TP 不能代替联合 TP；实际小旁观者上的全锥正性也不能冒称 CP。

**证明。** 取 $B=\mathbb R,C=\mathbb R^2,w=(2,1)$，$R(y)=(y_1+y_2,0)$，令

$$
c=1/2,\qquad\Gamma(y)=(y_1/2,0),\qquad
T(y)=(y_1+y_2/2,0).
\tag{73.30}
$$

$T$ 保持加权质量 $2y_1+y_2$，故其原联合延拓 TP。两个局部分支正且 TNI；以 $Z=(2y_1,y_2)$ 书写，联合分支质量分别是 $Z_1/2+Z_2$ 和 $Z_1/2$，都正且 TNI，和为原总质量。但局部输入 $(0,1)$ 的总质量变为 $1/2$，所以欠缺的正是局部 TP，非标量行得以存留。反过来，取总映射 $T=R$ 并分为 $R/2,R/2$，局部 TP，两支联合 TNI；同一局部输入的加权质量却从 $1$ 变成 $2$，联合总和不 TP。

再取 $B=\mathbb R,C=H_2,w=I$、任意 $0<c<1$，令失败分支为 $(1-c)\Theta$，其中 $\Theta(y)=y^T$。局部及实际联合载体此时都是 $H_2$，因此 $cR+(1-c)\Theta$ 及两支满足定义 73.2 的全部正性、TNI 和总 TP。失败分支却不是 CP：在另一个二维参考上，$\operatorname{id}_2\otimes\Theta$ 把 Bell 投影送到 $\operatorname{Swap}/2$，反对称方向值为 $-1/2$。这只用一个显式矩阵方向，未假定转置是物理操作。若实际旁观者本身已有二维块，同一转置的联合正性就会失败。故双侧刚性可仅用正性，任意操作 CP 的消费者仍须另有足够参考。$\square$

**命题 73.14（四项补全及标量锚仍不检测接合方向）。** 已获命题 66.11 的实际 qubit 数据通过四项正补全和 $\mathrm A_0$，却不满足 NB／C13；因此 73.1 的交叉入口不能由这些补全替代。

**证明。** 原数据为 $A=H_2,D=H_4,E=H_8$，$L(d,c)=d\otimes c$，$p(z)=(\operatorname{Tr}_1z)^T$，其中最后转置作用于保留的整个 $4\times4$ 块。66.11 已逐项核对其全部 PRE，包括同一 $p$ 两次实际给

$$
K(a)=(I_2/2)\otimes a^T,\qquad M(a,b)=a\otimes b^T,
\tag{73.31}
$$

两条实张成、$D_J,D_H,Z$ 和原全锥正保迹 $p$。这里不在 NB 之前冒用普通方向分类。直接按实际乘积律核对 $M$ 两位置的联合重置为

$$
Z\longmapsto\sigma_B\otimes\operatorname{Tr}_1Z,\qquad
Z\longmapsto(\operatorname{Tr}_2Z)\otimes\sigma_C^T.
\tag{73.32}
$$

它们都在整个 $D_+$ 上正保迹。$L$ 的两个联合重置分别是 $Z\mapsto\sigma_D\otimes\operatorname{Tr}_{D}Z$ 和 $Z\mapsto(\operatorname{Tr}_A Z)\otimes\sigma_A$，同样全锥正保迹。与各自恒等失败分支配对，即得到任意指定 $0<c\le1$ 的四项补全。$\tau_E L(I_4/4,I_2/2)=1$，故标量锚成立。

但原实际插入为

$$
I^{\rm raw}Z=\operatorname{ins}_2[(\operatorname{id}\otimes\Theta)Z].
$$

端点 Bell 投影的部分转置在反对称向量上为 $-1/2$，中间任意单位向量保持该负值，故 C13 失败，71.6 随即给 NB 失败。整个论证只使用全块转置的正性及显式重置，未把坐标转置当作 CP 操作。$\square$

### 73.8 完整候选与同数据的归一化结论

**定义 73.15（内在方向、双侧补全及标量锚的完整候选）。** 候选由约定 73.1 的全部 PRE、定义 71.8 的 NB、实际 $M,L$ 各自两个输入位置的正重置补全，以及 $\mathrm A_0$ 构成。四项补全直接按 (73.3)–(73.5) 在原实载体、原正锥和原迹上表述，不以一个外供的联合映射或独立 $M$ 代替。每个位置固定一个输出块、任意密度和严格正成功份额；定理保证任何这样的固定选择给同一数学模型类，不要求在一个菜单内同时实现所有选择。

其完整原比较前件仍是：$K_X=\{x\in C_X:u_X(x)=1\}$ 是全部态基，效应是整个 $[0,u_X]$，纯态为其极点，$T_\xi(x)$ 由确定接受纯 $\xi$ 的效应下确界定义；对每个有限纯态族和每组概率权重要求 $T_\xi(\sum_rv_r\eta_r)=\sum_rv_rT_{\eta_r}(\xi)$。只供应全域正 $L,p$，由原 $\omega$、同一 $p$ 连续两次内部生成 $M$，保留 $M(A,A)$、$L(D,A)$ 的实际实张成、全部正输入的 $D_J,D_H$ 与全实 $Z$。这些未删关系的全量词为

$$
\begin{aligned}
D_J:\quad &a,b\in A_+,\ \langle a,b\rangle_A=0
 \Rightarrow\langle Ja,Jb\rangle_D=0,\\
D_H:\quad &d,d'\in D_+,\ \langle d,d'\rangle_D=0
 \Rightarrow\langle Hd,Hd'\rangle_E=0,\\
Z:\quad &B_1M(a,b)=\tau_A(a)Jb\qquad(a,b\in A).
\end{aligned}
$$

NB 先用第一接口的内在纯—混关系补回原整锥交叉方向，再讨论本节正滤波校准。

相对于定义 67.10、70.11，只把交叉测试换成已证等价的 NB，并把 $C_{\rm joint}$ 换成四项补全和 $\mathrm A_0$；其余前件、条件纸面工具及原对象一项不删。原来的探针可用 71.6 的任何关系成员，不增加已付 71.8a 的成果计数。

**定理 73.16（归一化候选的同原模型等价）。** 定义 73.15 与定义 67.10、定义 70.11 的两个版本具有完全相同的实际 $(A,D,E,C_X,u_X,L,p)$ 模型类，因而得到 67.11 的原有限静态结论，特别是

$$
\begin{aligned}
M(a,b)_{ij}&=a_i\otimes b_j,&L(d,c)_{ijk}&=d_{ij}\otimes c_k,\\
(pz)_{jk}&=\sum_i\operatorname{Tr}_i z_{ijk},&
(p_{13}z)_{ik}&=\sum_j\operatorname{Tr}_j z_{ijk},\\
p_{13}&=(I^{\rm raw})^*,&p_{13}Q(a,b,c)&=\tau_A(b)M(a,c).
\tag{73.33}
\end{aligned}
$$

这里 $p$ 保留末两腿有序标签，$p_{13}$ 丢弃中腿；满足这些全实读回律的线性映射分别在整个原 $E$ 上唯一。

**证明。** 71.6、71.8a 在 PRE 上给 NB 与 C13 的逐模型等价，不先输入校准；73.11 给同一原数据上的校准替换。定义 67.10 的探针在其已校准前件下等价于 C13，定义 70.11 两版本由 70.12 同样等价；故完整候选逐点互推。正向也可直接由 73.8 与 $a_0=1$ 得 $u=g=I$，再取 65.31 和 67.27–67.28 得 (73.33)。$M$、$Q$ 的实际实张成确保上述唯一性；不在乘积外另留未定读回项。反向在归一化实际数据上，73.19 给四项补全，原迹给锚。全过程保持同一 $L,p,\omega$，没有把辅助归一化代表当作原数据。$\square$

此等价以数学映射存在性为准。若把 RC 改为“指定原程序、装置、同一菜单和完整记录实际供应这些成功／失败分支”，那是更强的来源条件。旧归一化候选只推出 (73.19) 的数学构造，未自动推出这些物理供应，故不能把 73.16 的逆向无条件搬给该更强解释。

### 73.9 量子消费者的精确前件

原完整比较桥及 66.3、66.8 已在 NB 与校准之前给出复矩阵直和的全部密度、全部效应及实际 Born 配对：

$$
\rho_i\ge0,\quad\sum_i\operatorname{Tr}\rho_i=1,\quad
0\le f_i\le I_i,\qquad
\Pr(f\mid\rho)=\sum_i\operatorname{Tr}(f_i\rho_i).
\tag{73.34}
$$

各块质量可以为零或不相等；候选没有把整个输入域缩成 NB 的见证态。73.16 的新增消费是指定原二份、三份接口及读回的归一化，不是再次推导 Born 几何。独立给定的另一括号载体、高份组合及其来源相容性仍须另行识别。

对另给的实际事件或分支，只有当同一原操作、记录和后续读数确实满足相应原乘积延拓律，并且在足够大的实际参考上全锥正，才可消费标准 CP／Kraus 结论。具体地，对每个输入块 $H_{n_i}$，若供应一个至少 $n_i$ 维的参考块及该同一事件在该整个联合锥上的正延拓，便可测试嵌入的 $n_i$ 维 Bell 投影，由 69.3 所用 Choi 判据逐输入输出块得到 CP 与矩形 Kraus 形式。数学 Bell 矩阵的存在不代表物理参考已供应；只有很小旁观者的情况有 73.13 的转置控制。

若进一步保留局部分支的原 TNI 预算和同一完整菜单总 TP，则各分支 $\Phi_s(\rho)=\sum_\ell K_{s\ell}\rho K_{s\ell}^*$ 满足相应块预算，完整仪器给总完备式；结果概率为 $q_s=\tau\Phi_s(\rho)$，仅在 $q_s>0$ 时条件输出才定义为 $\Phi_s(\rho)/q_s$。这些是 69.3–69.4、69.11 的条件消费者，对全部原扇区、参考、结果及其失败、停止、破坏、返回记录保持原范围，不由四个重置见证推断所有实际操作已 CP 或已物理可实现。效应本身只指定概率，不唯一决定更新；锐效应 $P$ 的 Lüders 压缩另需该实际 CP 分支的效应恰为 $P$，并在每个确定接受的归一态上逐点不变，再复用 71.8 所引锐中性唯一性接口。

若还另给以原物理时间为参数的连续、时间齐次、可逆动力学群，并使其在这些有限复代数上为 $*$ 自同构，则连续性固定离散中心标签，每块连续一参数自同构群由内推导实现，得到

$$
\dot\rho_i=-\frac{i}{\hbar}[H_i,\rho_i].
\tag{73.35}
$$

每块 $H_i$ 有加标量自由度；时间单位、能量单位及 $\hbar$ 的识别须来自原时钟与动力学来源。静态正补全不供应该群、时间参数、相位或 Hamiltonian；一般不可逆过程也不能由这个群结论覆盖。

### 73.10 直观、来源与原目标边界

**普通解释。** 一个接合原先可对不同标签和不同矩阵方向给不同增益。固定正份额的重置把所有输入的一部分送到同一个地方。若局部和联合两边都完整守恒，那么能一直保留的加权读数不能继续区分这些被共同遗忘的方向。遗忘左边迫使各行一致；遗忘右边迫使同一行内所有方向、所有右标签共用一个标量。两边一起要求，全部矩阵增益只剩一个共同倍率。第一接口已有原参考留下的逆迹平衡，因此倍率为一。第二接口每次放大后紧跟同一个读回的反向缩小，连续用两次也看不见这个尺度；在接合后、读回前取一次原总迹，才恰好固定它。接合方向有没有翻错由 NB 的联合纯—边缘混关系另行检查，概率补全本身不代替这项方向检查。

**既有结果与本节增量。** 71.1–71.8a 的 PRE、内在关系、原态逐成员检测和自然单点障碍，66.3–66.10 的全态几何、滤波、有序方向、全实唯一读回与同时方向消除，65.10–65.11 的完整正滤波逆向及同一 $p$ 两次恢复，67.6–67.7、67.11–67.12 的尺度族、旧联合校准和静态消费者，全部按原范围复用。69.2、69.4、69.8 的左位置延拓、预算与行一致也是已付结果；73.5 明确核对其必要性只依赖正效应。本节补足右位置的非交换对偶预算及整个直和固定效应，把它与左位置接到同一实际双侧分类，并在两个原接口上给出精确矩阵刚性、不可见的一维余尺度、一次标量锚及同数据完整候选等价。没有把标准收缩或已付校准重新计数。

所用成熟正算子工具可直接对照 Stéphane Gaubert、Zheng Qu，[Dobrushin’s Ergodicity Coefficient for Markov Operators on Cones，arXiv:1307.4649v3，§6 的 Markov 算子定义与 Theorem 6.1](https://arxiv.org/html/1307.4649v3#S6)：该节在带内点序单位的实序锥空间上，只要求算子正且保序单位；严格 Hopf 振幅收缩给出到标量共识的收敛。这里施于 $T^*$，整直和单位在内点，(73.14) 是共同重置特例的完整初等证明；重置态本身不必内点。该文 §7 的 Kraus 特化不是本节刚性的前件。部分转置及 Schmidt/Bell 计算按 66.11、71.3、71.6 已引原文范围复用，负值在本节控制中已直接列出。CP、Kraus 和锐中性消费者沿 69.3、69.11、71.8 所引 [Watrous 原文接口](../../../Library/Quantum/watrous2018theory.md#one-actual-self-reference-for-finite-sector-operations) 使用，不把未给参考或设备藏入标准定理。这里不作全球新颖性、优先权、独立公理缩减、资源减少或 Lean 核验声明。

**原来源成果及未付桥。** [原观察卷 §§23–24](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ORIGINAL_INTERFACE_EXPOSURE_AND_RECOVERY.md#23-an-acquired-pending-operand-fibre-at-the-original-plan-entry) 已在同一原 $G_V$ 的明示进展域内取得：实际获取的有序操作数与独立 guard、真实拒绝及完整绑定、既有 Plan/Send 对已获取操作数的消费、无新增外部 IN 的不同下一原源和真实下一 Entry、实际服务返回、历史批次、HandbackResume、原 Stop／验证／消费及共同 INITIAL 终端答案；24 的逐分支实际账目也保留。不能把这些已构造的原续接、返回或全部原 incidence 一概说成缺失。此前已获条件下降、参考、递归支撑、原 $D$ 恢复、原 $G_V$ 服务及其返回合同同样各按其原域成立。

本节未构造的是[固定来源卷 (23.7)](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md)要求的原分析器当前接受证书与[有限返回卷 164.1](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md)要求的原 $B_r$ 到 active-ready 连接；这两个位置不同于上述原观察卷的定理 23.7。数学延拓、矩阵相等、存在菜单、操作逆字、纯态校准或矩阵综合都不自动填入这些来源关系，也不生成新的原准备，或把同一密度当作同一历史与全部允许未来。

完整原 $\Omega$ 的全部准备、事件、过程、参考、副本、实际相关联合、零与不等质量、时钟与单位、控制、ready 与 flags、完整记录、失败、停止、销毁、返回及未来，连同全部原全菜单、固定支撑和每个已量化中间切口义务，都在其原域保留。没有免费相干控制、复制、参考、重置或滤波。数学存在性候选没有取代原 analyzer/menu/source 与过程合同；原全目标仍未完成，也没有缩成矩阵校准目标。本节全部是条件范围内的纸面定义、定理和手工证明，不包含形式内核验证或物理实现。

## 追加锚（本行以下为增补区）

## 74. 有限张成局部框架的两层零关系与完整原态候选

本章的第 65—72 章引用仍指第四卷，74 编号属于本卷。本章在第 72 章完整 PRE 的同一实际数据上，以同一个有限局部框架族的两层二元零比较，精确替换全锥 $D_J,D_H$；其余前件及原混态 H13 全部保留。一般 EJA 的平方不等式、支撑归一化和谱分解是成熟中间工具，本章的综合是有限关系在原 PRE 中的同数据替换及其完整消费者，不另主张一般正交保持分类的新意。既有条件纸面接口按 [1]—[3] 的范围使用。

### 74.1 完整保留的原系统与删除两条零关系后的基底

**定义 74.1（$\mathrm{PRE}_0$）。** 对每个 $X=A,D,E$，保留非零有限维实空间、闭尖生成锥 $C_X$、在非零正元上严格正的线性泛函 $u_X$、紧全态基 $K_X=\{x\in C_X:u_X(x)=1\}$、全部效应 $[0,u_X]$ 及 $P_X=\operatorname{ext}K_X$。仅在纯第一端点定义比较，并要求完整有限混合律：
$$
T^X_\xi(x)=\inf\{f(x):0\le f\le u_X,\ f(\xi)=1\},\quad \xi\in P_X,\ x\in K_X,\qquad
T^X_\xi\!\left(\sum_\ell v_\ell\eta_\ell\right)=\sum_\ell v_\ell T^X_{\eta_\ell}(\xi). \tag{74.1}
$$
最后一式量化每个有限纯态族、每组概率权重及每个纯 $\xi$，不是仅要求纯端点互反。完整复用 65.1、66.1、72.1 及 [2] 的 $S$ 到一般有限 EJA 条件纸面桥，包括正对偶生成、共同框架、面投影、项目性及滤波纯性推导；不另加 Jordan 公理，也不把仓内综合归给一个前件较强的外文定理。其忠实坐标满足 $\tau_X\Phi_X=u_X$、$\Phi_XU_X=1_X$、$B_X(x,y)=\tau_X(\Phi_Xx\circ\Phi_Xy)$ 及 $T^X_\xi(x)=B_X(\xi,x)$，双射整个原态基与整个原效应区间。此后就在该坐标中书写，原对象不变。
规范迹 $\tau_X$ 令每个简单理想的每个本原幂等元迹一；写 $\langle x,y\rangle_X=\tau_X(x\circ y)$、$\ell_xy=x\circ y$、$P_x=2\ell_x^2-\ell_{x^2}$。对正元，$x\perp y$ 指零迹配对，等价于 $x\circ y=0$ 及支撑正交。$x>0$ 表示正可逆内点；一般 EJA 始终允许 Albert、直和与秩一因子。
令 $n=\tau_A1_A$、$m=\tau_D1_D$。唯一供应的映射及原参考为
$$
L:D\times A\to E\ \text{实双线性},\quad p:E\to D\ \text{实线性},\quad
L(D_+,A_+)\subseteq E_+,\quad p(E_+)\subseteq D_+,\quad \omega=1_D/m. \tag{74.2}
$$
内部对象全部由同一个原 $p$ 定义，两次调用不能独立供应：
$$
\begin{aligned}
\mathcal B(d,c)&=pL(d,c),& K(a)&=pL(\omega,a),&M(a,b)&=pL(K(a),b),\\
J(a)&=M(a,1_A),&H_{\mathrm s}(d)&=L(d,1_A),&B_1&=pH_{\mathrm s},\\
Q(a,b,c)&=L(M(a,b),c),&U&=M(1_A,1_A),&G&=H_{\mathrm s}1_D.
\end{aligned} \tag{74.3}
$$
要求两条实张成和全部实输入上的 $Z$：
$$
\operatorname{span}_{\mathbb R}M(A,A)=D,\qquad \operatorname{span}_{\mathbb R}L(D,A)=E,\qquad
B_1M(a,b)=\tau_A(a)Jb\quad(a,b\in A). \tag{74.4}
$$
$\mathrm{PRE}_0$ 正是 72.1 的 PRE 只删除 $D_J,D_H$。被删的两条分别是 $a,b\in A_+,a\perp b\Rightarrow Ja\perp Jb$ 与 $d,d'\in D_+,d\perp d'\Rightarrow H_{\mathrm s}d\perp H_{\mathrm s}d'$。原 $L,p$ 的正性仍遍及整个锥，包括双份、三份全部纠缠方向；实张成不表示正乘积生成正锥。此时没有 C13、校准、原保单位或保迹、CP 或物理滤波输入。

### 74.2 定理 74.7 的平方缺陷与支撑中间步骤

以下两步只作为定理 74.7 的证明工具，复用一般 EJA 的成熟结构事实，不单列为新增定理。

**证明中间步骤（一般 EJA 的平方缺陷）。** 若 $\Phi:X\to Y$ 全锥正且保单位，则 $\Delta(a)=\Phi(a^2)-(\Phi a)^2\ge0$。若 $\Delta(a)=0$，则 $\Phi(a\circ x)=\Phi a\circ\Phi x$ 对全部实 $x\in X$ 成立。
**证明。** 在完整谱框架中写 $a=\sum_i\lambda_i e_i$，令 $z_i=\Phi e_i\ge0$、$b=\Phi a$。二次表示的定义直接给
$$
P_{\lambda1-b}=\lambda^2\mathrm{id}-2\lambda\ell_b+P_b,\qquad
\Phi(a^2)-b^2=\sum_iP_{\lambda_i1-b}z_i\ge0. \tag{74.5}
$$
等式由 $\sum_i z_i=1$、$\sum_i\lambda_i z_i=b$、$P_b1=b^2$ 得到。每一项正，是因为一般 EJA 的 $P_v$ 对任意实 $v$ 都保锥；这里绝不要求 $\lambda_i1-b\ge0$。此成熟二次表示事实及下用的谱、Peirce 支撑事实沿 65.4 的一般 EJA 范围复用，不经矩阵表示或复 Schwarz 不等式。
当 $\Delta(a)=0$ 时，对任意实 $t$，
$$
0\le\Delta(a+tx)=2t\,[\Phi(a\circ x)-\Phi a\circ\Phi x]+t^2\Delta(x). \tag{74.6}
$$
分别取两侧符号的 $t$，除以 $|t|$ 并趋于零；闭尖锥迫使一次系数为零。特别地，若 $e$ 与 $\Phi e$ 均幂等，则 $\Delta(e)=0$，得到该幂等元的乘法交织。∎

**证明中间步骤（有限张成框架工具）。** 设非零有限 EJA 间的实线性 $T:X\to Y$ 全锥正，$h=T1_X>0$。固定完整本原框架族，其并实张成 $X$。则每个指定框架内不同成员的像正交，当且仅当 $T$ 保持全部正元对的正交；等价地，$\varphi=P_{h^{-1/2}}T$ 为保单位 Jordan 同态且 $[\ell_h,\ell_{\varphi x}]=0$ 对全部 $x\in X$ 成立。
**证明。** 在任一指定框架 $(e_i)$ 内，$x_i=Te_i\ge0$ 的支撑 $q_i$ 两两正交；$\sum_i x_i=h>0$ 给 $\sum_iq_i=1_Y$。相对于每个 $q_i$，$h$ 无 Peirce 半空间分量，其 $Y_1(q_i)$ 分量恰为 $x_i$。角内谱演算遂给
$$
\varphi e_i=P_{h^{-1/2}}x_i=q_i,\qquad [\ell_h,\ell_{q_i}]=0. \tag{74.7}
$$
允许 $x_i=0,q_i=0$，逆仅施于全局 $h$；不对零像求逆。二次表示及此处的逆全锥正，所以 $\varphi$ 正且保单位。本节平方缺陷步骤 给 $\varphi(e_i\circ x)=\varphi e_i\circ\varphi x$；框架并集张成使之随第一变量线性延拓，故 $\varphi$ 保全部 Jordan 乘积。同一张成将 (74.7) 的交换子延拓到全部 $\varphi x$。
反之，若有上述同态及交换性，$T=P_{\sqrt h}\varphi$。令 $z=\varphi y$，将 $[\ell_h,\ell_z]=0$ 作用于 $h$，得 $\ell_h^2z=\ell_{h^2}z$，所以 $P_hz=h^2\circ z$。利用二次表示自伴随、$P_{\sqrt h}^2=P_h$ 及迹的结合性，
$$
\langle Tx,Ty\rangle_Y=\langle\varphi x,P_h\varphi y\rangle_Y
=\langle\varphi x\circ\varphi y,h^2\rangle_Y
=\langle\varphi(x\circ y),h^2\rangle_Y. \tag{74.8}
$$
于是 $x,y\ge0,x\perp y$ 给像配对为零；全域正交保持当然包含指定框架情形。权重交换在此不可省，任意正可逆滤波本身不保持零配对。∎
不从 $h>0$ 推断单射：例如 $T:\mathbb R^2\to\mathbb R,(a,b)\mapsto a$ 消去一个本原元。若一般工具中 $h\ge0$ 奇异，由 $-c1\le x\le c1$ 得 $-ch\le Tx\le ch$，全像在 $Y_1(\operatorname{supp}h)$ 内；在该角用相对单位作同一证明即可。$h=0$ 时 $T=0$。本章实际应用的 $U,G$ 则如下独立证明为内点。

### 74.3 非循环归一化与有限框架见证

**命题 74.4（先有内点）。** 在 $\mathrm{PRE}_0$ 中，不使用 $D_J,D_H$ 即有 $U>0,G>0$，故可预先定义 $C_D=P_{\sqrt U}$、$F=C_D^{-1}M=P_{U^{-1/2}}M$。
**证明。** (74.2) 使实际 $M$ 在正乘积上正。若 $0\le a\le r1_A,0\le b\le t1_A$，双线性正性给 $0\le M(a,b)\le rtU$，所以全部正乘积像在 $U$ 的支撑面中。锥生成、双线性及第一条实张成迫使该面的实张成为整个 $D$，即 $\operatorname{supp}U=1_D$。同理 $0\le L(d,c)\le rtG$ 与第二条实张成给 $\operatorname{supp}G=1_E$。此步连 $Z$ 都未使用。∎

**定义与存在命题 74.5。** 取同一个有限完整本原框架族 $\mathfrak B=(\mathsf B_1,\ldots,\mathsf B_s)$，要求 $\operatorname{span}_{\mathbb R}\bigcup_r\mathsf B_r=A$。框架符号 $\mathsf B_r$ 不同于映射 $B_1=pH_{\mathrm s}$。令 $d=\dim_{\mathbb R}A$、$n=\operatorname{rank}A=\tau_A1_A$，这样的族总存在且可取
$$
1\le s\le d-n+1. \tag{74.9}
$$
**证明。** 先取一套完整本原框架，其 $n$ 个成员线性无关，已张成 $n$ 维。若累计张成仍为真子空间，谱分解所给的本原元张成性保证存在其外的本原元；将它补成完整框架，至少增加一维。至多再补 $d-n$ 套便结束。直和中按全部简单理想补框架；$d=n$ 的经典情形一套即足。此为存在上界，不主张最少、自然选法、物理可制备性或跨无界维数的统一有限表。∎

### 74.4 两层有限关系逐原数据恢复全部零关系

**定义 74.6（$\mathrm{FJ},\mathrm{FH}$）。** 对上述实际 $J,H_{\mathrm s},F$ 和同一个族要求
$$
\mathrm{FJ}:\quad\langle Je,Jf\rangle_D=0\quad(e\ne f\in\mathsf B_r;\ 1\le r\le s), \tag{74.10}
$$
$$
\mathrm{FH}:\quad\langle H_{\mathrm s}F(e,f),H_{\mathrm s}F(e',f')\rangle_E=0
\quad\substack{e,e'\in\mathsf B_r,\ f,f'\in\mathsf B_t,\ (e,f)\ne(e',f');\\1\le r,t\le s}. \tag{74.11}
$$
只比较每个框架内部，不要求不同框架之间交叉正交，也不预设 $F(e,f)$ 本原。$F$ 已由命题 74.4 定义，未借用 $D_H$ 或 C13。

**定理 74.7（精确替换）。** 对每个 $\mathrm{PRE}_0$ 实际元组及每个预先固定的完整张成族，
$$
D_J\land D_H\quad\Longleftrightarrow\quad\mathrm{FJ}\land\mathrm{FH}. \tag{74.12}
$$
**证明。** $J$ 全锥正且 $J1_A=U>0$；对 $J$ 应用74.2 节的有限框架步骤，第一层先恢复整个 $A_+$ 上的 $D_J$。此时才调用定理 65.3：其第一接口明确不使用 $D_H$ 或 C13，给满规范迹等距同构 $\widetilde F:A\otimes_{\mathbb R}A\to D$、$m=n^2$、$F(1,1)=1_D$、正乘积的正性及本原对的本原性。
对每个 $r,t$ 令 $\mathsf C_{rt}=F(\mathsf B_r\times\mathsf B_t)$。由第一接口，
$$
\langle F(e,f),F(e',f')\rangle_D=\langle e,e'\rangle_A\langle f,f'\rangle_A. \tag{74.13}
$$
所以不同输入对的像正交、各像本原、和为 $1_D$；$\mathsf C_{rt}$ 确为含 $n^2$ 个成员的完整本原框架。又因 $\bigcup_r\mathsf B_r$ 实张成 $A$，全部 $e\otimes f$ 实张成 $A\otimes_{\mathbb R}A$；$\widetilde F$ 满射使全部 $\mathsf C_{rt}$ 的并实张成整个 $D$。
现在 $H_{\mathrm s}:D\to E$ 在整个 $D_+$ 上正且 $H_{\mathrm s}1_D=G>0$；再用74.2 节的有限框架步骤，第二层恢复整个 $D_+$ 上的 $D_H$，包括所有纠缠正元及本原元。此时未预设 $E$ 为复矩阵，故没有用 CP、复 Schwarz 或复型分类循环证明 $D_H$。
反向，$D_J$ 给第一层；65.3 和 (74.13) 给上述完整框架，$D_H$ 即给第二层。每一步均作用于原映射和原参考。∎
故“存在一个完整张成族通过”与“每个完整张成族通过”均等价于原 PRE；忘掉框架见证后是相同实际 $(A,D,E,L,p)$ 模型类。两层至多分别列出
$$
s\binom n2,\qquad s^2\binom{n^2}2,\qquad s\le\dim_{\mathbb R}A-\operatorname{rank}A+1 \tag{74.14}
$$
个无序零等式，重复可保留。这只有限化两条零关系；完整 $S$、全锥正性、两条实张成与全实 $Z$ 没有因此有限化，也不是实验次数或误差稳定性界。

### 74.5 完整候选仍测试同一个原混态

**定义 74.8（$\mathrm{PRE}_{\rm fin}+\mathrm H13$）。** $\mathrm{PRE}_{\rm fin}$ 是全部 $\mathrm{PRE}_0$ 加一个定义 74.5 的族及两层关系。恢复 PRE 后，沿 66.2—66.3 取 $A_i$ 的中心单位 $c_i$、秩 $n_i$，原块 $D_{ik}=\operatorname{span}_{\mathbb R}F(A_i,A_k)$ 及中心投影 $\pi_{ik}$。原规范迹伴随给
$$
\alpha_{ik}(a)=F(a,c_k),\quad\beta_{ik}(b)=F(c_i,b),\quad\mathcal Q=\{(i,k):n_i,n_k\ge2\},\quad
R_i(x)=\alpha_{ik}\alpha_{ik}^*x-x,\quad R_k(x)=\beta_{ik}\beta_{ik}^*x-x.
$$
完整保留 72.3 的关系与 72.17 的原态条件：
$$
\mathcal H(F)=\{\rho\in K_D:\ \forall(i,k)\in\mathcal Q,\ R_i(\pi_{ik}\rho)\not\succeq0\ \text{或}\ R_k(\pi_{ik}\rho)\not\succeq0\}, \tag{74.15}
$$
$$
T_{\rm raw}(a,c)=L(Ja,c),\quad I^{\rm raw}=\widetilde T_{\rm raw}\widetilde M^{-1},\qquad
\mathrm H13:\ \exists\rho\in\mathcal H(F),\ I^{\rm raw}\rho\in E_+. \tag{74.16}
$$
$\widetilde M$ 的逆只在第一接口建立后使用。资格只读第一接口、中心限制、原序与原伴随，不读插入或输出；$\not\succeq0$ 指不在正锥中。$R_i,R_k$ 分别标记左右槽，即使 $i=k$ 仍是两种边缘扩张。非活跃块任意正且可为零，无活跃块时为整个 $K_D$；不加活跃块纯性、固定谱、质量下界或先按块条件化，块非零及正质量由严格违例推出。边缘铺回使用单位，不能改成单位除以维数。测试始终是同一原 $\rho$ 的完整输出，不能换成 $C_D^{-1}\rho$ 或仅看选定输出面。

**定理 74.9（完整同数据等价）。** 忘掉框架见证后，
$$
\mathrm{PRE}_{\rm fin}+\mathrm H13\ \equiv\ \mathrm{PRE}+\mathrm H13\ \equiv\ \mathrm{PRE}+\mathrm{C13},\qquad
\mathrm{C13}:I^{\rm raw}(D_+)\subseteq E_+. \tag{74.17}
$$
H13 改成每个合格原态都通过仍给同一类；全部原 $\omega,p,\rho$ 和权重数据不换。
**证明。** 第一个等价由定理 74.7，且没有改变 $F,\mathcal H(F),I^{\rm raw}$。命题 72.7 给非空性，定理 72.8 给每个原成员的通过与 C13 等价，故得到第二个及全称版本。其依赖的关键几何仍是：任一活跃原块的边缘非支配蕴含 NPT；证明用 $\mathrm{Red}_d=\Psi_d\circ T$，其中 $\Psi_d(Y)=\sum_{a<b}(E_{ab}-E_{ba})Y(E_{ab}-E_{ba})^\dagger$。所以 PPT 会使两种边缘差都正，逆否即得 NPT。
在 72.2 的真实恢复接口中，证明内的 $C_D^{-1}$ 只对原块施加可逆局部合同，保持 NPT，未必保持 reduction 资格；坏相对方向的单腿转置因而仍有负值，插入未经归一化的中间单位（包括标量中间扇区）保留负值，$C_E$ 的序同构不能消除它。不同中心块不能抵消，所以每个合格原态都拒绝坏插入。这里直接复用实际 65.6、66.2、72.2 的 $C_E$ 与精确恢复式，不以另一不完整滤波公式替代。∎

### 74.6 原量子几何与全部未校准权重

**推论 74.10（原静态消费者及逆向）。** 恢复 PRE 后，66.3、66.8 在 C13 之前已给保原迹 Jordan 坐标中的
$$
A=\bigoplus_iH_{n_i}(\mathbb C),\quad D=\bigoplus_{i,j}H_{n_in_j}(\mathbb C),\quad E=\bigoplus_{i,j,k}H_{n_in_jn_k}(\mathbb C),\quad n=\sum_i n_i,
$$
$$
\Pr(f\mid\rho)=\sum_\lambda\operatorname{Tr}(f_\lambda\rho_\lambda),\qquad
\rho_\lambda\ge0,\quad\sum_\lambda\operatorname{Tr}\rho_\lambda=1,\quad0\le f_\lambda\le I_\lambda. \tag{74.18}
$$
扇区集有限非空，$n_i\ge1$；全部有序块、重复标签、经典标量及混合扇区都保留。纯态是单扇区射影纯态，同区比较为平方重叠、异区为零；全部纠缠态仍在原态基。H13 只补组合的相对方向相容性。
**证明与参数。** C13 前必须保留 66.4—66.7 的有序转置位及全锥正读回的完整方向限制；不能提前取共同普通方向。由定理 74.9 恢复 C13 后，才按 66.10、65.9—65.11 同时取辅助 $F(a,b)_{ij}=a_i\otimes b_j$、$N(d,c)_{ijk}=d_{ij}\otimes c_k$。全部原始模型恰是
$$
M(a,b)_{ij}=a_i\otimes\sqrt{u_{ij}}b_j\sqrt{u_{ij}},\qquad
L(d,c)_{ijk}=d_{ij}\otimes\sqrt{g_{ijk}}c_k\sqrt{g_{ijk}},\qquad
u_{ij},g_{ijk}>0,\quad\sum_{i,j}n_i\operatorname{Tr}(u_{ij}^{-1})=n^2. \tag{74.19}
$$
置 $A_{jk}=I_j\otimes\sqrt{u_{jk}}$、$W_{ijk}=I_i\otimes u_{ij}^{-1/2}\otimes g_{ijk}^{-1/2}$，同一个原读回在整个 $E$ 上唯一为
$$
(pz)_{jk}=A_{jk}\left[\sum_i\operatorname{Tr}_1(W_{ijk}z_{ijk}W_{ijk})\right]A_{jk},\qquad \omega_{ij}=I_{n_in_j}/n^2. \tag{74.20}
$$
65.11 的逆向从这些 $L,p$、原 $\omega$ 重算同一个 $p$ 两次，给实际 $M$ 及所有原前件；定理 74.7 与 72.8 再给有限关系和 H13，故双向闭合。唯一权重约束是所列逆迹平衡，不另要求跨块对称、共同对角化或同腿的 $u,g$ 交换。辅助归一化一般不保原迹一截面，不能删去权重或转送为原 $M,H_{\mathrm s}$ 保单位、原 $p$ 保迹；其精确边界仍按 65.12、66.8—66.9，原插入伴随也一般不保迹。∎

### 74.7 操作消费者与可选的同读回校准

有限候选本身不供应标准仪器。若另按 69.1—69.4 固定同一旁观者族 $\Psi_\Phi=C_DT_\Phi C_D^{-1}$、$(T_\Phi X)_{jk}=\sum_i(\Phi_{ji}\otimes\mathrm{id}_k)X_{ik}$，分支限定为块 CP，则有限分支的 Kraus 效应 $F^a_{ji}=\sum_\ell K_{a,ji,\ell}^\dagger K_{a,ji,\ell}$ 必须满足双预算
$$
\sum_{a,j}F^a_{ji}\le I_i,\qquad
\sum_{a,j}F^a_{ji}\otimes u_{jk}\le I_i\otimes u_{ik}\quad(\forall i,k). \tag{74.21}
$$
部分仪器用聚合预算，完整仪器要求两式均等号，即局部及原始联合总映射都 TP；单分支可容许不等于可共同补全。原始 Choi/Kraus、顺序复合、粗粒化及条件更新仅在此固定族内沿 69.3—69.11 复用。
具体地，固定输出扇区 $j_0$、其中任意密度 $\sigma$、同一个 $0<c\le1$，令 $R(a)_j=\delta_{j,j_0}(\sum_i\operatorname{Tr}a_i)\sigma$。69.8 的精确附加条件是正权弱共同重置 $cR$ 可按同族补成两边均 TP 的有限 CP 仪器；它等价于 $u_{ik}=v_k$ 与输入行 $i$ 无关。此时 $\Psi_\Phi=T_\Phi$，双预算合为普通 Kraus 预算，才取得整个标准有限局部 CP 仪器菜单。充分小的 $c>0$ 仅保证分支双预算，不能代替共同补全。概率用原分支输出迹，正概率时除以该迹给条件态；行一致不迫使 $v_k=I_k$，也不校准 $g$ 或保证每对原制备迹一。
另一项可选附加校准是 [3] 定理 1.3，绝非有限判据前提：预先固定任意上述局部全重置 $R$，由 $R_2M(a,b)=M(Ra,Rb)$、$R_3Q(a,b,c)=Q(Ra,Rb,Rc)$ 唯一线性延拓到整个 $D,E$，则在恢复的完整 PRE 上
$$
(p\text{ 全域 TP 且 }R_2\text{ 全域 TP})\ \Longleftrightarrow\
(p\text{ 全域 TP 且 }R_3\text{ 全域 TP})\ \Longleftrightarrow\ u_{ij}=I_j,\ g_{ijk}=I_k\ \text{对全部块}. \tag{74.22}
$$
这是同一原 $p$ 与实际并行全重置的联合条件，允许任意秩的 $\sigma$；另一重置也随之 TP。该定理使用原 $pQ(a,b,c)=\tau_A(a)M(b,c)$、实张成与逆迹平衡，不用 C13，也不自动推出 C13，不能与弱重置补全混同。
数学框架、正滤波和 CP 映射的存在均不供应装置可用性、制备成本或鲁棒性。效应本身不唯一决定更新，唯一 Lüders 压缩还需“确定接受的态逐点不变”等锐中性前件。一般操作重建、动力学、Hamiltonian、物理钟、$\hbar$、独立右载体、四份或更高份兼容组合及无限维一致性仍不由此得到；比较互反不等于实际测量次序交换。

### 74.8 删除边界与自然选择障碍

**命题 74.11（两个 $H_2$ 纸面控制）。** 张成与全锥正性都不能从74.2 节的有限框架步骤 的前件中删去。
**证明。** 取 $H_2(\mathbb C)$ 的 Pauli 矩阵 $X,Y,Z$ 及本原框架 $\{(I\pm V)/2\}$。删张成时，$\Phi(x)=(x+x^T)/2$ 正且保单位，固定 $X,Z$ 两套完整框架；它们的并只张成 $I,X,Z$。$Y$ 框架的两个正交本原元却都映成 $I/2$，像配对为 $\operatorname{Tr}(I/4)=1/2$，所以有限通过不推出全域零关系。
删全锥正性时，实线性规定 $T(I)=I,T(X)=T(Y)=T(Z)=Z$。三套 Pauli 框架的并张成 $H_2$，每套均映成完整正交 $Z$ 框架；但正交纯投影 $p_\pm=(I\pm(X+Y+Z)/\sqrt3)/2$ 的像为 $(I\pm\sqrt3Z)/2$，有特征值 $(1-\sqrt3)/2<0$，且像配对为 $-1$。这些是中间工具的删项反例，不冒充满足其余 PRE 的完整反模型。∎
这也说明有限框架上看见正输出不能替代 (74.2) 的全锥量词。全部产品框架实张成 $D$，其正包一般仍小于 $D_+$；纠缠方向的控制依靠 $H_{\mathrm s}$ 已有的全锥正性及上述步骤的代数刚性。作为权重边界，$h=\left(\begin{smallmatrix}2&1\\1&2\end{smallmatrix}\right)$、$T=P_{\sqrt h}$ 的归一化虽是恒等同态，却有 $\langle TE_{11},TE_{22}\rangle=|h_{12}|^2=1$，再次说明交换性不可漏。
定理 72.16 仍有效：第一接口自然、集合等变的非空有限原态选集，不能靠逐成员完整插入输出正性在全 PRE 中完备检测 C13。本章另付一个完整张成框架族见证，测试的是 $J,H_{\mathrm s}$ 的二元零关系，且仍保留完整 H13，没有构造该定理禁止的选集。即使在 $H_2$，有限本原元集若在连通酉共轭群下集合不变，每个轨道也只能是单点；全酉固定矩阵仅为标量，故不存在这样的本原框架自然选择。任一固定有效族都可用，不表示可以自然选出一个族。关系成员的平均还可能丢失 72.14 的负方向；本章没有将 H13 换成平均点。

### 74.9 完整中文候选与几何图像

在三个非零有限实际系统中，保留全部状态、全部效应与完整随机纯制备比较律，只沿既有条件桥取得规范迹 Jordan 几何。供应整个双份正锥上的原正接合和整个三份正锥上的同一个正读回，以原参考连续调用它两次；保留两条实张成及所有实方向的 $Z$。选择有限多套完整局部本原框架，使它们共同覆盖全部实方向：第一层要求每套框架经原第一切片后仍互不混淆；恢复第一接口后，用同一族的全部两两产品形成双份框架，第二层要求它们经原第二切片后仍互不混淆。这精确恢复原来的两条全锥零关系。随后在每个两端非标量有序块，要求原联合态的至少一种边缘铺回盖不住原块；保留混态、任意谱和全部原归一化，要求一个这样的原态经实际逆准备所定义的原插入后完整为正。所得恰是原 PRE+C13 的实际模型类，原 $\omega,p$ 与所有正权重都在。
几何上，每套框架像一组把空间分开的面单位。正交正像先占据互不重叠的支撑面；单位输出是内点，保证这些面合起来铺满目标单位。除去面内厚度后，它们成为幂等元；平方缺陷沿正负两向的扰动不能留下线性偏差，因而锁定与这些方向的全部 Jordan 交叉乘积。框架共同张成后，剩余方向也随之锁定。两层框架并未把纠缠浮雕变成产品平板的概率混合，而是利用全锥正性排除映射扭坏剩余零关系的自由。最后 H13 仍在每个活跃端点寻找边缘铺不开的纹理，用同一个原态抓住坏相对翻转。真正缩短的是 DJ、DH 的零比较列表；全态效应、正性、实张成、$Z$、见证成本和完整原态输出判据仍在，不主张公理最少、全球新颖或完整物理量子起源。

**数学引文及复用范围。** [1] [固定 dev db6fde5df77，Atlas IV §§65—72](https://github.com/the-omega-institute/trureturing/blob/db6fde5df77b82e4c869ee075d04f786708f5e18/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_IV.md)：65.1、66.1、72.1 的完整忠实入口；65.3 不含 DH/C13 的第一接口；65.4 的一般 EJA 谱、Peirce 与二次表示工具；65.6、66.2、72.2 的真实恢复接口；66.3—66.10 的复载体、有序方向及 C13 后同时定向；65.9—65.12 的完整原权重及逆向；69 的固定 CP 族、双预算与弱共同重置补全；72.3、72.7—72.8、72.14、72.16—72.18 的原混态资格、非空性、逐成员等价及边界。
[2] [同版本 Library，Complete conditional candidate and its scope](https://github.com/the-omega-institute/trureturing/blob/db6fde5df77b82e4c869ee075d04f786708f5e18/Library/QuantumStates/mullerududec2012selfduality.md#complete-conditional-candidate-and-its-scope)：完整 $S$ 的仓内条件纸面桥及逆向；其 Barnum–Müller–Ududec Theorem 16 的前件按该桥供应，单独的纯端点互反或正对偶结论不代替它。
[3] [dev 77c459c3513，同读回与并行重置校准 §1.3](https://github.com/the-omega-institute/trureturing/blob/77c459c351371a4d05cc4f2f148d1b8b883b5967/docs/develop/theory/QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md)：仅作 (74.22) 的可选同数据联合校准，沿其完整 PRE、预固定重置、全空间 TP 及实际同读回范围使用，不添加为有限零关系判据前提。

## 追加锚（本行以下为增补区）

## 75. 纯制备元数的精确障碍、回路平衡与混合余项二元入口

本章的第 65—72 章引用均指[第四卷](QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_IV.md)，第 73—74 章引用指本卷。完整比较律到一般有限 EJA 的纸面桥已经由 [Library 的完整条件候选](../../../Library/QuantumStates/mullerududec2012selfduality.md#complete-conditional-candidate-and-its-scope)供应，包括正对偶剥离、共同框架、带符号谱性、自对偶、正面投影及最大杂质论证的滤波纯性，再明确调用 Barnum–Müller–Ududec 的 Theorem 16。本章直接复用这条链及其逆向，不重证、不把它列成未付桥，也不将它计作本章增量。要解决的是比较入口究竟约束哪些已有制备关系：只检验少量纯项，和允许二元式的一端带任意混合余项，逻辑内容不同。

### 75.1 全载体、达到的比较与元数定义

**定义 75.1（载体与 $S_k$）。** 取非零有限维实向量空间 $A$，$d=\dim_{\mathbb R}A$，闭、尖、生成的锥 $C$，以及在 $C\setminus\{0\}$ 上严格正的线性泛函 $u$。始终使用整个态基 $K=\{x\in C:u(x)=1\}$、$P=\operatorname{ext}K$ 及整个 proper 效应区间

$$
[0,u]=\{f\in A^*: f(C)\ge0,\ (u-f)(C)\ge0\}.
$$

对纯 $p$，定义确认集与比较

$$
F_p=\{f\in[0,u]:f(p)=1\},\qquad
T_p(x)=\min_{f\in F_p}f(x)\quad(x\in K).
\tag{75.1}
$$

$S_k$ 对每个 $p\in P$、每个 $1\le r\le k$、所有 $q_1,\ldots,q_r\in P$ 及所有 $w_j\ge0,\sum_jw_j=1$ 要求

$$
T_p\!\left(\sum_{j=1}^r w_jq_j\right)
 =\sum_{j=1}^r w_jT_{q_j}(p).
\tag{75.2}
$$

零权、重复纯态和不等正权都在量词中。完整 $S$ 要求每个有限 $r$；$S_1$ 恰为纯端点互反 $T_p(q)=T_q(p)$。这里元数数的是制备纯项，不是参照 $p$ 加上这些项的总标签数，更不是 Hilbert 维数。固定参照版本 $S_k(p)$ 仅固定 (75.2) 的第一端点，其余量词不动。

**命题 75.2（紧性、达到与有限纯分解）。** $K$、$[0,u]$、$F_p$ 均非空紧凸，$\operatorname{aff}K$ 的维数为 $d-1$，$P$ 张成 $A$；每个 $x\in K$ 有有限纯分解。(75.1) 的最小值达到，$0\le T_p(x)\le1$、$T_p(p)=1$，且 $T_p$ 在 $K$ 上连续、凹。

**证明。** 任取实范数。在紧集 $C\cap\{\|x\|=1\}$ 上，$u$ 有严格正最小值；故 $u(x)=1$ 的正元有统一范数上界。$K$ 闭而有界，因 $C$ 非零而非空。每个非零正元可除以其 $u$ 值，故 $C=\operatorname{cone}K$，生成性给 $\operatorname{span}K=A$，从而 $\operatorname{aff}K=\{u=1\}$。有限维紧凸集的极点分解定理给 $K=\operatorname{conv}P$，其中凸包指有限凸组合；亦可取至多 $d$ 个纯项。它不要求纯态 exposed，不要求原世界实际生成这些准备。

取 $K$ 中一组线性基 $x_1,\ldots,x_d$。任一 $f\in[0,u]$ 的基读数均在 $[0,1]$，所以整个效应区间有界；由对偶锥闭性它亦闭。$0,u$ 在区间内，$u\in F_p$，而 $F_p$ 是其闭仿射截面。连续线性评价在紧 $F_p$ 上取最小值。所有效应的对偶范数有统一上界，故它们的下包络满足同一 Lipschitz 界，特别地连续；线性函数下包络是凹函数。余下读数范围直接由定义得出。∎

### 75.2 任意整数条带载体与全 proper 效应

**定义 75.3（行列条带）。** 对每个整数 $q\ge2$，在 $\mathbb R^{q\times q}$ 中令 $r_i$ 是第 $i$ 行的指示阵除以 $q$，$c_j$ 是第 $j$ 列的指示阵除以 $q$。置

$$
A_q=\operatorname{span}_{\mathbb R}\{r_i,c_j:1\le i,j\le q\},\quad
C_q=\operatorname{cone}\{r_i,c_j\},\quad u(x)=\sum_{i,j}x_{ij}.
\tag{75.3}
$$

此处 $q$ 不必是素数或素数幂。$u(r_i)=u(c_j)=1$，$C_q$ 是有限生成闭锥，因它包含于非负坐标锥而尖，按定义在 $A_q$ 中生成，$u$ 在非零正元上严格正。其整个 $K_q$ 正是这 $2q$ 点的凸包。

**命题 75.4（唯一关系、全部极点与全部效应）。** 这 $2q$ 点均为 exposed 纯态，唯一线性关系生成元为

$$
\sum_i r_i=\sum_j c_j,\qquad
\dim A_q=2q-1,\qquad \dim\operatorname{aff}K_q=2q-2.
\tag{75.4}
$$

一个线性效应由 $a_i=f(r_i),b_j=f(c_j)$ 唯一决定，其为 proper 的充要条件恰是

$$
0\le a_i,b_j\le1,\qquad \sum_i a_i=\sum_j b_j.
\tag{75.5}
$$

特别地 $e_{ij}(x)=q x_{ij}$ 都是全锥上的 proper 效应。

**证明。** 行总量泛函在 $r_i$ 的值为一，在其他行态为零，在每个列态为 $1/q<1$，故唯一最大于 $r_i$；列总量对称地暴露 $c_j$。有限凸包没有其他极点。若 $\sum_i s_ir_i+\sum_jt_jc_j=0$，逐坐标给 $s_i+t_j=0$，故全部 $s_i$ 是同一个 $t$，全部 $t_j=-t$。这证明唯一关系及维数。赋值能下降为 $A_q$ 上的线性泛函，当且仅当它保持这一关系；锥由上述顶点生成，$f\ge0$ 与 $u-f\ge0$ 恰可在全部生成元上检验，故得到整个区间 (75.5)，并非只允许坐标效应。$e_{ij}$ 的行值只在 $i$ 为一，列值只在 $j$ 为一，满足 (75.5)。∎

用原坐标 Euclidean 内积，公共中心 $x_*=\sum_i r_i/q=\sum_jc_j/q$ 的每格是 $1/q^2$。直接内积给

$$
\begin{aligned}
\langle r_i,r_k\rangle&=\delta_{ik}/q,&
\langle c_j,c_\ell\rangle&=\delta_{j\ell}/q,&
\langle r_i,c_j\rangle&=1/q^2,\\
\langle r_i-x_*,r_k-x_*\rangle&=\delta_{ik}/q-1/q^2,&
\langle c_j-x_*,c_\ell-x_*\rangle&=\delta_{j\ell}/q-1/q^2,&
\langle r_i-x_*,c_j-x_*\rangle&=0.
\end{aligned}
\tag{75.6}
$$

所以减去中心后，行、列分别是两个正则 $(q-1)$-单纯形，各自中心为零，所在 $(q-1)$ 维空间互相正交；$K_q-x_*$ 是它们的 free sum，即直接和空间中两者并集的凸包。这一几何已有文献，准确归属见 75.12；这里的内积只解释条带坐标，不预置量子自对偶或比较配对。

### 75.3 精确比较公式与没有最小确认者

**定理 75.5（所有准备的最小读数）。** 任一准备

$$
x=\sum_i\alpha_ir_i+\sum_j\beta_jc_j,\qquad
\alpha_i,\beta_j\ge0,\quad \sum_i\alpha_i+\sum_j\beta_j=1
$$

在全效应区间下恰有

$$
\boxed{\quad T_{r_i}(x)=\alpha_i+\min_j\beta_j,\qquad
T_{c_j}(x)=\beta_j+\min_i\alpha_i.\quad}
\tag{75.7}
$$

所有纯态之间的比较为 $\delta$ 表。

**证明。** 确认 $r_i$ 的效应有 $a_i=1$，(75.5) 给 $\sum_jb_j=\sum_ka_k\ge1$。因此

$$
f(x)=\sum_k\alpha_ka_k+\sum_j\beta_jb_j
 \ge\alpha_i+(\min_j\beta_j)\sum_jb_j
 \ge\alpha_i+\min_j\beta_j.
$$

在最小 $\beta_j$ 的位置取 $e_{ij}$，其读数恰为右侧，故达到。列情形对称。若两套系数表示同一 $x$，唯一关系使它们相差 $\alpha'_i=\alpha_i+t,\beta'_j=\beta_j-t$，故 $\alpha'_i+\min_j\beta'_j=\alpha_i+\min_j\beta_j$；列式亦然。因此公式是 $x$ 的函数，不依赖选定表示。代入任一顶点即得同点一、异点零。∎

**命题 75.6（极小确认单纯形）。** $r_i$ 的序极小确认效应恰为：$a_i=1$、其余 $a_k=0$，而 $(b_j)$ 是概率向量。它们组成一个 $(q-1)$-单纯形，任意两个不同成员互不可比，$r_i$ 因而没有最小 proper 确认效应。这里不声称整个 $F_{r_i}$ 的仿射维数是 $q-1$。

**证明。** 对任一确认效应，令 $B=\sum_jb_j\ge1$，取 $b'_j=b_j/B$、$a'_i=1,a'_k=0$。这些值定义一个 proper 确认效应，且在所有生成元上不超过原效应，所以原效应支配这个概率向量成员。若某个确认效应不超过一个这样的成员，则其他行值必须零，列值逐项不超过该概率向量，同时列值和必须一，故逐项相等。这证明这些成员极小，也穷尽极小成员。不同概率向量不可能逐项同向比较，因为它们总和相同。若存在最小确认者，它必须同时等于全部这些极小成员，矛盾。列情形完全对称。∎

### 75.4 精确元数层级、最大缺陷与联合区分

**定理 75.7（$S_{q-1}$ 成立而 $S_q$ 失败）。** 对任意整数 $q\ge2$，条带载体满足 $S_{q-1}$，不满足 $S_q$。对指定准备，把重复条带的权重合并为 $\alpha,\beta$ 后，行参照的 (75.2) 左减右缺陷精确是 $\min_j\beta_j$，列参照精确是 $\min_i\alpha_i$。在所有参照及所有有限指定准备上最大缺陷恰为 $1/q$。

**证明。** 纯表为 $\delta$，故行参照的右侧就是该行在指定准备中的总权重 $\alpha_i$，(75.7) 给所列缺陷。至多 $q-1$ 个纯项，无论是否重复、有零权或权重不等，都不可能给 $q$ 条对侧条带各自正权；至少一个对应系数零，所以全部这些等式成立。

在同一个中心，取全列准备 $x_*=\sum_jc_j/q$ 与参照 $r_1$。其右侧零而 $T_{r_1}(x_*)=1/q$，故 $S_q$ 失败。又 $\min\beta\le(\sum\beta)/q\le1/q$，列式对称，中心实例达到上界。这只是该比较等式的精确缺陷，不是任何范数中的距量子空间或一般稳定性估计。∎

特别地，$q=3$ 有六个纯态、载体维数五、态基仿射维数四：所有纯二项混合都通过，三项列混合失败。三项制备标签并不表示三维 Hilbert 空间。给任意固定 $k$ 取 $q=k+1$，就否定在无统一维数限制时以固定纯元数 $S_k$ 代替完整 $S$；此为载体比较反例，不是满足全部原复合、PRE 或来源条件的 $\Omega$ 反模型。

**命题 75.8（全部 $q$ 元子集可联合区分仍不足）。** 任意至多 $q$ 个不同纯条带，都有一个数学上的归一化共同区分效应表；不存在区分 $q+1$ 个条带的这种表。因此“每个 $q$ 元子集都可共同区分”仍不蕴含 $S_q$。

**证明。** 先取恰好 $q$ 个，其中选中行集 $R$ 大小 $a$，选中列集 $B$ 大小 $q-a$。把 $R$ 双射匹配到未选列 $B^c$，把未选行 $R^c$ 双射匹配到 $B$，合成一个排列 $\pi$。$q$ 个效应 $e_{i,\pi(i)}$ 在每个顶点上恰有一个值一，故其和在整个 $A_q$ 上为 $u$。每个选中条带的唯一一值效应不同：一个配对不同时包含选中行与选中列。所以该表共同区分全部选中态。较小非空子集先扩成 $q$ 元，再把多余效应粗粒化并入保留结果，得到所需归一表。

反向，每个确认条带的效应在 $x_*$ 上至少 $1/q$。若 $(f_s)_{s=1}^n$ 是共同区分表，$\sum_sf_s=u$，则 $1=\sum_sf_s(x_*)\ge n/q$，所以 $n\le q$。定理 75.7 的失败需要对侧 $q$ 个标签再加参照端点，共 $q+1$ 个不同标签；已有的 $q$ 元联合区分没有覆盖这个关系。这些是全效应模型中的数学表，不供应原实际菜单或 analyzer。∎

### 75.5 $\delta$ 纯表类的锐维数阈值

**定理 75.9（仅在 $\delta$ 类中的锐阈值）。** 在定义 75.1 的载体上，另假设 $T_p(r)=\delta_{pr}$ 对全部纯对成立。令 $m=\lfloor(d+1)/2\rfloor$。则

$$
S_m\quad\Longleftrightarrow\quad K\text{ 是单纯形}
\quad\Longleftrightarrow\quad S.
\tag{75.8}
$$

$d=1,2$ 的载体自动是单纯形。此阈值不适用于具有非零异纯态过渡值的一般量子表。

**证明。** 若纯态多于 $d$ 个，取不超过 $d+1$ 个不同纯态中的一个最小线性依赖集。将其关系 $\sum_ic_iq_i=0$ 施以 $u$，得 $\sum_ic_i=0$；所有系数非零且正负两边均存在。除以共同正总和，把关系分成两套不交、各权严格正的凸准备，具有同一状态 $x$。每一侧至少两个成员，否则一纯态是其他不同纯态的真凸组合，与极性矛盾。

较短一侧至多 $\lfloor(d+1)/2\rfloor=m$ 个。取另一侧某成员为参照 $p$，其在该侧正权为 $\lambda>0$。每个确认 $p$ 的正效应在共同 $x$ 上都至少读出 $\lambda$，所以 $T_p(x)\ge\lambda$。但较短侧不含 $p$，$S_m$ 与 $\delta$ 表给 $T_p(x)=0$，矛盾。因此 $|P|\le d$。命题 75.2 的张成性迫使恰有 $d$ 个线性无关纯态，$K$ 是其单纯形。

反向，在单纯形中，取顶点基的坐标效应，确认一个顶点并在其他顶点取零。任何确认者在准备上的值至少是该顶点权重，坐标效应达到它，故对任意有限准备满足完整 $S$。完整 $S$ 当然给 $S_m$。$d=1$ 时态基为一点，$d=2$ 时非退化紧凸基为线段，直接得到末句。∎

**推论 75.10（奇偶维数的达到与最小反例维数）。** 奇维 $d=2q-1\ge3$ 的条带模型达到阈值：$S_{q-1}$ 不能迫使单纯形，$S_q$ 可以。偶维 $d=2q\ge4$ 也有同样反例。等价地，对每个 $k\ge1$，非单纯形、$\delta$ 表且满足 $S_k$ 的载体最小维数恰为 $2k+1$。

**证明。** 奇维已由定理 75.7。偶维取 $A'=A_q\oplus\mathbb R$、$C'=C_q\oplus\mathbb R_+$、$u'(x,s)=u(x)+s$。其全基是原条带基与新经典顶点 $z=(0,1)$ 的凸包，纯态恰为这些点，维数 $2q$。整个 proper 效应区间恰是 $[0,u]\times[0,1]$：这由两个直和锥分量独立测试得到。

对条带参照，确认者为 $(f,t)$，$f\in F_p,0\le t\le1$；取 $t=0$ 最小化经典部分。若一份全基准备的条带总质量 $\mu>0$，比较就是 $\mu T_p(x/\mu)$；$\mu=0$ 时直接为零，不作除法。其条带系数仍给 (75.7) 的齐次式 $\alpha_i+\min\beta$ 或 $\beta_j+\min\alpha$。对 $z$ 的参照，取 $(0,1)$ 得比较恰为经典质量 $s$，其他确认者不能更低。因此全纯表仍为 $\delta$，$S_{q-1}$ 仍成立，而原中心的 $q$ 列准备仍使 $S_q$ 失败。

最后若 $d\le2k$，则 $m\le k$，定理 75.9 排除非单纯形 $S_k$ 模型；$q=k+1$ 的条带维数 $2k+1$ 给达到。所有直和零质量与边界均已包含。∎

### 75.6 共同极小者、标准 Helly 界及其范围

**引理 75.11（同一确认者的交集判据）。** 固定 $p$，令 $h_p=\dim\operatorname{aff}F_p\le d-1$，并对每个纯 $r$ 定义非空紧 exposed 面

$$
A_{pr}=\{f\in F_p:f(r)=T_p(r)\}.
\tag{75.9}
$$

在纯互反成立的范围内，对任一正权有限准备，(75.2) 成立，当且仅当其支持上的 $A_{pr}$ 有共同点。对每个固定有限支持，仅测试其均匀混合即足以判定共同点；共同点一旦存在，所有不等正权、补零权和重复标签都自动满足等式。

**证明。** $F_p$ 位于 $f(p)=1$ 的仿射超平面，故有维数界。最小值达到给各面非空，线性评价的最小层是紧 exposed 面，允许它等于整个 $F_p$。任何 $f\in F_p$ 都满足各非负超额 $f(r)-T_p(r)\ge0$。由互反，准备等式要求最小加权超额为零；其最小值由同一 $f$ 达到。各权严格正时，加权和为零恰要求全部超额为零。这就是交集条件，也证明均匀权测试的充分性。零权先去掉，重复先合并，不删原量词。∎

**命题 75.12（标准 Helly 充分界）。** 固定参照处的 $S_{h_p+1}(p)$ 蕴含该参照处全部有限等式，并给一个同时达到所有纯读数的最小确认效应。因此统一 $S_d$ 或 $S_{1+\max_ph_p}$ 足以推出完整 $S$。此处只把标准有限维 Helly 定理应用到 $\operatorname{aff}F_p$，不主张该界锐或定理新颖。

**证明。** 单项给该参照与每个纯态的互反。引理 75.11 使任意至多 $h_p+1$ 个面都有共同点。有限 Helly 定理于是使每个有限面族交非空；$h_p=0$ 时 $F_p$ 是一点，结论直接成立。$F_p$ 紧，闭面族的有限交性质使 $\bigcap_{r\in P}A_{pr}$ 非空，即使 $P$ 无限或含非 exposed 极点。取交中 $e_p$，则 $e_p(r)=T_p(r)\le f(r)$ 对每个纯 $r$ 及每个确认者 $f$ 成立。纯态生成锥，故 $e_p\le f$ 于整个 $C$。它本身是确认者，故为最小者并在所有 $x\in K$ 上等于 $T_p(x)$，得到所有有限等式。$h_p\le d-1$ 给统一界。Helly 的引用范围见 75.12 节文献说明。∎

### 75.7 全确认区间带来的更强局部界

**定理 75.13（固定参照的 $\max(1,h_p)$ 界）。** 定义 75.1 的全效应载体具有更强结论：$S_{\max(1,h_p)}(p)$ 已足以得到该参照处完整等式和最小确认者。仅要求所有至多该大小的不同纯支持之均匀混合等式也足够。因此 $S_{\max(1,d-1)}$ 在任一载体上都足以推出完整 $S$；这里没有断言一般最优阈值。

**证明。** 关键是：这些共同极小面若有一个有限极小空交族 $A_{pq_1},\ldots,A_{pq_n}$，则

$$
2\le n\le h_p.
\tag{75.10}
$$

每个单面非空，故 $n\ge2$。记 $t_i=T_p(q_i)$。若 $t_i=1$，因全部 proper 效应不超过一，该面为 $F_p$，不能出现在极小空交族中。所以 $t_i<1$。$u\in F_p$，在 $V=\operatorname{span}(F_p-u)$ 上定义线性函数

$$
g_i(v)=-\frac{v(q_i)}{1-t_i},\qquad
G_i(f)=g_i(f-u)=\frac{1-f(q_i)}{1-t_i}.
\tag{75.11}
$$

$\dim V=h_p$，$0\le G_i\le1$ 于 $F_p$，$G_i(u)=0$，且 $A_{pq_i}=\{G_i=1\}$。极小性允许为每个 $j$ 选 $f_j\in\bigcap_{i\ne j}A_{pq_i}$，但 $f_j\notin A_{pq_j}$。故 $\delta_j=1-G_j(f_j)\in(0,1]$。

若 $\sum_i c_ig_i=0$，记 $C_0=\sum_ic_i$。在 $f_j-u$ 上评价给

$$
C_0-c_j\delta_j=0,\qquad
C_0=\sum_jc_j=C_0\sum_j\delta_j^{-1}.
\tag{75.12}
$$

因 $\sum_j\delta_j^{-1}\ge n\ge2$，只能 $C_0=0$，进而所有 $c_j=0$。所以这 $n$ 个线性函数独立，$n\le\dim V=h_p$，证明 (75.10)。这一步使用 $u$ 属于同一全确认集、读数上界一，以及所有面都来自最小读数；任意凸集的任意面族不具有这个改进。

现在单项等式给互反。若某有限支持空交，取其中一个极小空交子族，它的大小至多 $h_p$，与引理 75.11 及假设的均匀混合测试矛盾。$h_p=0,1$ 时 (75.10) 本身排除有限空交；单项仍保留互反义务。最后用紧性有限交性质及命题 75.12 后半段，得到所有纯态共同的最小确认者和完整等式。补零、不等权及重复由引理 75.11 恢复。∎

### 75.8 关系的关系：回路平衡的完整刻画

**定义 75.14（纯态回路与平衡）。** 一个回路是不同纯态的有限最小线性依赖集 $Q=\{q_1,\ldots,q_n\}$。其非零关系 $\sum_ic_iq_i=0$ 唯一到非零实倍数，所有 $c_i\ne0$。回路平衡要求对每个纯参照 $p$ 和每个这样的关系

$$
\sum_i c_iT_{q_i}(p)=0.
\tag{75.13}
$$

这是对已有准备恒等式的比较值守恒，不把负系数当作负物理质量：施以 $u$ 后 $\sum_ic_i=0$，正负分开再归一，才是两套非负准备。

**引理 75.15（有限关系由支撑内回路生成）。** 不同纯态的任一有限线性关系均是其原支持内回路关系的实线性组合。每个回路有至多 $d+1$ 个标签；按正负分成凸准备后，每一侧至少两项，因而每一侧至多 $d-1$ 项。

**证明。** 对关系非零系数的支持大小归纳。若支持本身最小依赖，它已经是回路。否则在支持内选一个最小依赖子集及其关系 $v$；选其中某个 $j$，从原关系 $c$ 减去 $(c_j/v_j)v$。所得仍为关系，支持不增且至少去掉 $j$，归纳即可；这里不要求消元过程保持系数符号。最小依赖集删去任何一点即独立，所以大小不超过 $d+1$，其关系空间一维且无零系数。$u$ 给两侧相同正系数和；单项侧会把一个极点写成其他不同纯态的真凸组合，不可能。因此 $n\ge4$、两侧各至少两项，较长侧也至多 $d-1$。这些是实际线性恒等式的证明操作，不是新准备的生成程序。∎

**定理 75.16（完整 $S$ 当且仅当互反加回路平衡）。** 在同一全态全效应载体上，以下条件逐模型等价：完整 $S$；纯互反加 (75.13)；每个纯 $p$ 有一个最小 proper 确认效应 $e_p$ 且 $e_p(q)=e_q(p)$。其线性效应均作用于原 $A$，不引入另一份状态或另选准备表示。

**证明。** 完整 $S$ 含互反。把任意关系分成同一态的两份凸准备，对两份使用 $S$，即得到回路平衡，事实上得到所有有限关系的平衡。

反向固定 $p$。引理 75.15 使赋值 $q\mapsto T_q(p)$ 保持每个有限线性关系。因此它从纯态自由线性组合下降为 $A$ 上唯一的线性泛函 $e_p$；唯一性由 $P$ 张成 $A$。全部纯值在 $[0,1]$，故 $0\le e_p\le u$ 于生成锥，且 $e_p(p)=1$。纯互反使

$$
e_p(q)=T_q(p)=T_p(q)\le f(q)\quad(q\in P,\ f\in F_p).
$$

所以 $e_p\le f$ 于整个 $C$。$e_p$ 自身属于 $F_p$，故 $T_p(x)=e_p(x)$ 对全部归一态成立，线性性立刻给完整 $S$。最后若直接给最小确认者与互反，它在每个 $x$ 达到最小值，线性性又给 $S$；完整 $S$ 的方向也已构造了这些最小确认者。∎

**推论 75.17（一般有限界及仍未确定的最优元数）。** 任一 $d$ 维载体的 $S_{\max(1,d-1)}$ 蕴含完整 $S$。令 $b(d)$ 为保证所有该维载体之完整 $S$ 所需的最小正纯元数，则

$$
\left\lfloor\frac{d+1}{2}\right\rfloor\le b(d)\le d-1\quad(d\ge3),
\qquad b(3)=2,\qquad b(1)=b(2)=1.
\tag{75.14}
$$

$d\ge4$ 的一般最优值本章未定；$\delta$ 类的锐值不冒充一般答案。

**证明。** 当 $d\ge3$，每个回路的两份凸准备各至多 $d-1$ 项。分别用 $S_{d-1}$ 读同一个共享态，就得到 (75.13)；单项给互反，定理 75.16 给 $S$。$d\le2$ 时基为单纯形，直接成立。下界由定理 75.7 及推论 75.10 的奇偶维反例，上界由刚证结论；$d=3$ 两界相合。另一条充分性证明已经由定理 75.13 给出，它额外保留固定参照的 $h_p$ 信息。∎

### 75.9 任意混合余项的二元律恰好保留完整关系

**定义 75.18（混合余项二元律 $\mathrm B_{\rm mix}$）。** 对每个纯 $p,q\in P$、每个原基中的任意 $x\in K$ 和每个 $0\le t\le1$，要求

$$
\boxed{\quad
T_p(tq+(1-t)x)=tT_q(p)+(1-t)T_p(x).
\quad}
\tag{75.15}
$$

第一参照仍纯，余项 $x$ 不限于纯态，也不被改成一套特选制备。该式只约束已有数学态与其混合恒等式；将数学混合解释成某个原程序的实际彩票时，仍需原来源本已供应那项混合。

**定理 75.19（完整入口等价与三列诊断）。** $\mathrm B_{\rm mix}\Longleftrightarrow S\Longleftrightarrow$ 纯互反加回路平衡。它不是纯二项测试 $S_2$，也没有减少独立公理或资源需求的结论。

**证明。** $t=1$ 给互反。对正权纯准备按支持大小归纳：取第一项权重 $t<1$，把其余项除以 $1-t$ 形成余项 $x\in K$，用 (75.15) 再对余项用归纳假设，得到完整 $S$；单项、$t=1$ 直接处理，零权删除、重复合并后恢复原量词。反向用命题 75.2 将任意混合余项 $x$ 有限纯分解，对组合准备及余项分别用 $S$，就得到 (75.15)，包括 $t=0,1$。第三个等价由定理 75.16。

在 $q=3$ 条带中，取 $p=r_1,q=c_3,x=(c_1+c_2)/2,t=1/3$。右侧的 $T_{c_3}(r_1)=0$ 且 $T_{r_1}(x)=0$；但 $tq+(1-t)x=x_*$，左侧 $1/3$。所以混合余项二元律精确查出纯二项测试漏掉的那条关系。所漏的不是单个比较数的精度，而是“全列均匀准备等于全行均匀准备”这一原仿射恒等式。∎

### 75.10 保留全部原对象的完整候选

**定义 75.20（回路／混合余项完整候选）。** 对每个原系统 $X=A,D,E$，保留定义 73.15 的全部全态基、全效应区间和原始有序载体，只把其比较入口的完整 $S$ 换成 (75.15) 的 $\mathrm B_{\rm mix}$；等价版本使用纯互反加全部回路平衡。先由定理 75.19 恢复每个系统的完整 $S$，然后直接复用本章开头的既有 Library 纸面桥，取得忠实的规范迹 EJA 坐标。它不假定已有 Born 或 CP 来证明这个入口，也不再加入一条独立 Jordan 或滤波纯性公理。

其余承重对象与量词逐项保留。令 $n=\tau_A1_A,m=\tau_D1_D,\omega=1_D/m$；只供应同一个实际全锥正实双线性 $L:D\times A\to E$ 与同一个实际全锥正实线性 $p:E\to D$，所有内部映射仍为

$$
\begin{aligned}
K(a)&=pL(\omega,a),& M(a,b)&=pL(K(a),b),& J(a)&=M(a,1_A),\\
H(d)&=L(d,1_A),&B_1&=pH,&Q(a,b,c)&=L(M(a,b),c).
\end{aligned}
\tag{75.16}
$$

$K(a)$ 是沿原记号的线性映射，和态基 $K_X$ 区分；$M$ 必须由同一 $p$ 连续用两次生成，不得独立供应。保留两条实际实张成和全量词关系

$$
\begin{aligned}
\operatorname{span}_{\mathbb R}M(A,A)&=D,&
\operatorname{span}_{\mathbb R}L(D,A)&=E,\\
D_J:\quad a,b\in A_+,\ \langle a,b\rangle_A=0
 &\Rightarrow\langle Ja,Jb\rangle_D=0,\\
D_H:\quad d,d'\in D_+,\ \langle d,d'\rangle_D=0
 &\Rightarrow\langle Hd,Hd'\rangle_E=0,\\
Z:\quad B_1M(a,b)&=\tau_A(a)Jb\qquad(a,b\in A).
\end{aligned}
\tag{75.17}
$$

特别地，$D_H$ 遍及整个实际双份正锥，$Z$ 遍及全部实方向。第 74 节已经付清的有限张成框架版本可以按定理 74.7 等价复用，但这里不借它删除任何全锥正性、实张成或原菜单量词。

方向入口仍是定义 71.8 的 NB：从第一接口 $F=C_D^{-1}M$ 及其内在中心块形成完整 $\mathfrak E(F)$，每个两端非标量活跃有序块的条件态联合纯而 $F$ 内在边缘混，块质量任意严格正；非活跃块任意正，包括零，无活跃块时取整个态基。要求存在一个这样的同一原态 $\rho$，经由 $T_{\rm raw}(a,c)=L(Ja,c)$、$I^{\rm raw}=\widetilde T_{\rm raw}\widetilde M^{-1}$ 定义的原插入后仍在 $E_+$。第一接口可逆性建立后才取逆，不先运输或更换 $\rho$，不按输出反选资格。其每个成员检测 C13、非空性和全部边界沿 71.4—71.8a；也可完整使用第 72 节原混态非支配 H13 的已证等价版本。

最后，实际 $M:A\times A\to D$ 的两位置和实际 $L:D\times A\to E$ 的两位置，各保留定义 73.2 的严格正份额重置补全，共四项。每位置固定合法输出块、任意秩密度 $\sigma$ 和 $0<c\le1$；成功为 $cR_\sigma$，$R_\sigma(z)=\tau(z)\sigma$，其余有限局部分支正。联合分支须在整个原联合锥上正、满足同一个实际接合的全部实乘积延拓律，两层总和各自 TP。它们不是四个独立任意联合映射，也不先假定所有局部分支 CP。保留原标量锚

$$
\mathrm A_0:\qquad \tau_E L(\omega,1_A/n)=1.
\tag{75.18}
$$

这份候选的“重置补全”是原空间、原迹上的数学映射存在性；指定装置、程序、同菜单、成功失败记录实际供应这些分支，是另一个更强的来源条件，不能由存在量词自动获得。

**定理 75.21（同一原模型类与完整静态消费者）。** 定义 75.20 与定义 73.15 具有完全相同的实际 $(A,D,E,C_X,u_X,L,p)$ 模型类；其结论恰复用定理 73.16 及 (73.33)—(73.34)。存在有限非空扇区集及 $n_i\ge1$，在保持原迹、全部原态、全部原效应的坐标中

$$
\begin{gathered}
A=\bigoplus_iH_{n_i}(\mathbb C),\quad
D=\bigoplus_{i,j}H_{n_in_j}(\mathbb C),\quad
E=\bigoplus_{i,j,k}H_{n_in_jn_k}(\mathbb C),\\
M(a,b)_{ij}=a_i\otimes b_j,\qquad
L(d,c)_{ijk}=d_{ij}\otimes c_k,\\
(pz)_{jk}=\sum_i\operatorname{Tr}_i z_{ijk},\qquad
(p_{13}z)_{ik}=\sum_j\operatorname{Tr}_jz_{ijk},\qquad
p_{13}=(I^{\rm raw})^*,\\
\Pr(f\mid\rho)=\sum_\lambda\operatorname{Tr}(f_\lambda\rho_\lambda),\quad
\rho_\lambda\ge0,\quad\sum_\lambda\operatorname{Tr}\rho_\lambda=1,\quad
0\le f_\lambda\le I_\lambda.
\end{gathered}
\tag{75.19}
$$

全部有序标签、重复标签、经典标量扇区、不等和零中心质量、实际相关与纠缠输入均保留。上述二份、三份与偏迹属于这些指定的原接口，不自动识别独立另一括号或四份以上组合。

**证明。** 在同一 $A,D,E$ 上逐个使用定理 75.19，恢复且仅恢复原完整 $S$，故全部未改前件给定义 73.15。其既有 Library 桥在这个顺序后使用，不把矩阵概率预置到比较定义中。71.6 与 71.8a 先从 NB 得原 C13；73.8 从四个正补全得原 $M$ 的滤子为单位、原 $L$ 仅剩一个共同正标量；73.10—73.11 的原锚消去该标量。于是 73.16 给实际普通乘积与两个唯一全实读回。原 Born 配对则已经由完整比较桥和 66.3、66.8 获得，73.9 明确它不是重置的新后果。逆向，定义 73.15 的完整 $S$ 给 $\mathrm B_{\rm mix}$ 与回路平衡，其他对象原封不动；所以这是同模型类等价，而非另造一个兼容量子模型。∎

### 75.11 操作、张量与时间消费者逐项保留来源

定义 75.20 的静态结论不能把数学重置存在性升级为全实际菜单供应。操作消费者严格沿 73.9：对每个原事件、分支、结果和记录，先要其同一实际操作满足原乘积延拓律，并在足够大的实际参考的整个联合正锥上为正。对每个输入块 $H_{n_i}$，若实际供应一个至少 $n_i$ 维的参考块及该同一事件的整个正延拓，才以嵌入的 $n_i$ 维 Bell 投影消费 Choi 判据，逐输入输出块取得 CP 及矩形 Kraus 形式。数学 Bell 态或原有限张量坐标的存在，都不供应所需参考、事件或菜单；73.13 的小旁观者转置控制继续有效。

若再保留原局部分支 TNI、相应联合预算，以及同一完整实际菜单的总 TP，则写输入块 $i$ 到输出块 $j$ 的分支为

$$
\Phi_{s,ji}(\rho_i)=\sum_\ell K_{s,ji,\ell}\rho_iK_{s,ji,\ell}^\dagger,
\qquad
\sum_{s,j,\ell}K_{s,ji,\ell}^\dagger K_{s,ji,\ell}=I_i
\tag{75.20}
$$

得到完整仪器；部分菜单的聚合预算用 $\le I_i$。结果概率是原未归一输出总迹 $q_s=\tau\Phi_s(\rho)$，只在 $q_s>0$ 才用 $\Phi_s(\rho)/q_s$ 条件化，零支保留其标签、记录和后续权限。顺序复合与真实粗粒化沿 69.3—69.4、69.11 的同族合同消费，不以一个 effect 唯一决定更新。锐投影效应 $P$ 的 Lüders 更新还须该实际 CP 分支效应恰为 $P$，且对每个确定接受的归一态逐点不变，才复用 71.8 所引锐中性唯一性；重复性、CP 或完整性各自不能代替这一条件。

(75.19) 给指定原二份、三份的普通有序乘积和相应偏迹，不意味着不同历史具有相同允许未来，也不从两份分别可得推断真实相关联合已供应。其他原参考、副本、另一括号、更高份联合及其来源相容性均保留原合同；没有免费复制、控制、相干叠加或准备生成。

仅当另有以原物理时间为参数的连续、时间齐次、可逆动力学群，且在这些有限复代数上为 $*$ 自同构，才沿 73.9 取得各块内推导及

$$
\dot\rho_i=-\frac{i}{\hbar}[H_i,\rho_i].
\tag{75.21}
$$

连续性固定离散中心标签；$H_i$ 仍有加标量自由度。原时钟、时间及能量单位、$\hbar$ 的识别都要其实际动力学来源。本章比较关系不供应该群，也不把失败、停止、销毁、返回或一般不可逆过程改成可逆运动。

### 75.12 成熟来源、已有固定元数先例与增量范围

**文献归属。** 条带的 free-sum 几何不是本章发明。Baumeister–Haase–Nill–Paffenholz，[Polytopes associated to Dihedral Groups，arXiv:1212.4442v1，Definition 3.1 与 Theorem 3.3，PDF 第 3—4 页](https://arxiv.org/pdf/1212.4442v1)，对每个整数 $n$ 描述 $Q_n$ 为两个 $(n-1)$-单纯形的 free sum，并归功 Collins–Perkinson。其 $W$ 的上部是重复 $I$，下部是 $I,R,\ldots,R^{n-1}$：每个坐标恰入一条上行、一条下行，且每对恰出现一次。依这个关联重排坐标并缩放 $1/q$，即得定义 75.3 的精确条带模型；这是此处说明的坐标对应，不把本文比较公式归成该文已述定理，也不主张先前 Collins–Perkinson 原文已被独立阅读。$q=3$ 还可与全部六个 $S_3$ 排列矩阵的 Birkhoff 多面体作数学识别，但无量子 Hilbert 维数含义。

75.6 节的标准 Helly 引用是 Amenta–De Loera–Soberón，[Helly's Theorem: New Variations and Applications，arXiv:1508.07606v2，Theorem 1.1，PDF 第 1 页](https://arxiv.org/pdf/1508.07606v2)。所用仅是有限仿射维数中每个至多 $h+1$ 子族有交则全部有限族有交；无限纯态族额外使用本章已证的紧性有限交性质。该引用的直接阅读范围是 PDF 第 1—2 页，不声称通读该综述；改进到 $h_p$ 的 (75.10)—(75.12) 在本章给出完整证明，不归给普通 Helly 定理。

**命题 75.22（已发表共同测量结果给出的固定纯元数先例）。** 无维数上界时，固定纯元数不足的广义概率理论现象已有发表来源。具体地，Lami–Goldwater–Adesso，[A Post-Quantum Associative Memory，arXiv:2201.12305v3，Definitions 2、8、9、11，Theorem 17、§4.2 的 (14)—(15) 及证明](https://arxiv.org/pdf/2201.12305v3)，给固定 $N$ 的共同归一化 $N$ 元测量构造；限制其选定纯顶点到凸包，再配备该凸包的全 proper 效应，就能推出非单纯形 $\delta$ 表的 $S_k$ 载体，取 $N=k+1$。这一限制和到 $S_k$ 的推论由下面证明承担，不是该文定理原句。

**证明。** 所引 Theorem 17 在 product-simplex GPT 中选出 $2^m$ 个纯顶点，使每个至多 $N$ 元子集有共同归一化区分测量，维数上界为 $d(N,m)\le m^{1+o_N(1)}$，$N$ 固定。取这些选中顶点的整个凸包与其锥的实张成。原顶点仍极端，有限凸包也没有其他纯态；原效应限制后 proper，所以给出的共同测量仍在新模型的全效应区间。全效应区间还可能增大，不能据此假设所有最小值不变；以下逐项确定所需最小值。

两个不同顶点有一个确认前者、在后者零值的测量效应，正性下界为零，故新纯表确为 $\delta$。给至多 $k$ 纯项的准备和参照 $p$，参照加准备的不同标签数至多 $k+1=N$，有共同区分表。其 $p$ 结果效应读出准备中 $p$ 的总权重；若 $p$ 不在准备中则读零。每个确认 $p$ 的正效应都不能低于这份权重，故下界达到，$S_k$ 成立，涵盖零权、不等权和重复。充分大 $m$ 时 $2^m>d(N,m)$，限制后维数不增而全部选中点仍纯，所以不是单纯形；定理 75.9 因而排除完整 $S$。

这证明宽泛的无维数统一固定元数失败已有文献先例。该来源的可靠准备、no-restriction 模型及数学测量没有供应原 $\Omega$ 的准备、菜单或复合接头。上述维数只使用所引渐近定理，不运行其程序、不复算数值，也不把其上界当成条带锐阈值。∎

该文直接阅读范围是 PDF 第 3—8、11—15 页；这里不声称阅读全篇。Library 的完整 $S$ 桥、第四卷的原恢复及第 73—74 节的结果均按原范围复用。本章集中给出全效应条带的达到公式、极小确认者与精确缺陷、$\delta$ 类锐维数阈值、共同极小面的局部改进、回路平衡与混合余项的完整同数据接口。这些是纸面综合及其手工推导，不声明全球新颖、优先权、独立公理或资源严格减少，更不声明 Lean 认证或新物理理论已完成。

### 75.13 普通解释、实际原来源成果与剩余目标

把一张方格纸上的每整行、每整列各看作一种纯准备。所有行平均与所有列平均是同一张均匀纸。确认某一行的测试，必须在那一行完全接受；由于行和列共享同一总量关系，它在全部列上的接受值总和至少一。给少于 $q$ 条列时，总能把不得不接受的那一份挪到没出现的列上，因此少项测试全过；所有列都出现后，再无地方可藏，最小读数就等于最小列权。两两纯比较表完全没有记录这个集体恒等式。正交的两个单纯形画出了同一个障碍：缺失的是两套铺满中心的方法之间的关系。

回路就是不能再拆小的制备恒等式。让比较值保持这些回路，消元便保证它保持所有有限恒等式；互反再把这个一致赋值锁成原全效应中的最小确认者。也可以每次只剥出一个纯项，但余下整块必须允许是任意混合态：这样二元式每次都带着前面累积的关系，归纳才没有丢信息。只让两端都是纯态，就没有携带这块余项。有限维界说明需要看的支持大小受载体维数约束；它不是跨无界维数的一张固定有限验收表，更不是从三个标签直接制造三维量子系统。

原来源方面，[原观察卷 §§23—24](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ORIGINAL_INTERFACE_EXPOSURE_AND_RECOVERY.md#23-an-acquired-pending-operand-fibre-at-the-original-plan-entry)已经在明示原 $G_V$ 进展域上完成实际获取的有序操作数与独立 guard、真实拒绝和绑定、既有 Plan/Send 消费、无新增外部 IN 的不同下一原源及真实下一 Entry、实际服务返回、历史批次、HandbackResume、原 Stop／验证／消费和共同 INITIAL 终端答案；逐分支账目仍按原定理成立。新 DEV 的[续卷 §9](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ORIGINAL_INTERFACE_EXPOSURE_AND_RECOVERY_II.md#9-attribution-and-the-remaining-recovery-problem)还明确取得其新安装中 finitely attained completed canonical GuardAcquired 边界的当前四份交付与收到后 Plan 续接，其自身的 Busy、非规范输入和未改安装运输边界仍保留。这里不将这些已构造来源结果统称缺失，也不把新安装扩大成全部原域。既有下降、参考、递归支撑、原 $D$ 恢复及各有限返回合同继续按各自证明域成立。

本章没有构造[固定来源卷 (23.7)](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md)的原具名 analyzer 当前接受接口证书，也没有构造[有限返回卷定义 164.1](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md)所区分的原 $B_r$ 到 active-ready 接头。它们不是原观察卷已经证明的定理 23.7。矩阵相等、可逆字、纯态校准、数学效应表、存在菜单、矩阵综合和数学重置补全均不能自动填入这些实际来源。数学有限纯分解也不把全原准备改成实际纯态彩票生成，不把同一密度或同一比较表认作同一历史、记录与全部合法未来。

完整原 $\Omega$ 的全部准备、事件、过程、参考、副本、实际相关联合、零与不等质量、时钟与单位、控制、ready 与 flags、完整记录、失败、停止、销毁、返回及未来，连同所有原全菜单、固定支撑和每个已量化中间切口义务，均在其原域不变。定义 75.20 只等价重写比较入口，其他实际 PRE、NB／H13、四位置补全、锚及各量子消费者前件都保留。条带是这个入口的实质关系障碍，不是整个原世界的反模型；完整候选也没有完成实际 analyzer/menu/source、一般过程、物理时钟或严格简化的原总目标。原总目标仍未完成，没有以本章已完成的元数问题取代。

## 追加锚（本行以下为增补区）
