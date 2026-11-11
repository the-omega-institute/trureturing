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

## 75. Jordan 生成局部框架的两层有限零关系与统一三框架候选

### 75.1 同一原数据与完整保留的比较入口

**定义 75.1（$\mathrm{PRE}_0$）。** 采用定义 74.1 [P]，即定义 72.1 [R] 的 PRE 只删除 $D_J,D_H$。完整量词如下：对每个 $X=A,D,E$，取非零有限维实空间、闭尖生成锥 $C_X$、在非零正元上严格正的线性泛函 $u_X$、整个紧态基 $K_X=\{x\in C_X:u_X(x)=1\}$、全部效应 $[0,u_X]$ 及纯态集 $P_X=\operatorname{ext}K_X$。只在纯第一端点定义
$$
T^X_\xi(x)=\inf\{f(x):0\le f\le u_X,\ f(\xi)=1\},\qquad
T^X_\xi\!\left(\sum_\ell v_\ell\eta_\ell\right)=\sum_\ell v_\ell T^X_{\eta_\ell}(\xi). \tag{75.1}
$$
第二式遍及每个纯 $\xi$、每个有限纯态族 $(\eta_\ell)$ 及每组概率权重 $(v_\ell)$。沿 65.1、66.1、72.1 及 [S] 完整复用 $S$ 到一般有限 Euclidean Jordan 代数（EJA）的条件纸面桥，包括正对偶剥离与生成、共同框架、忠实配对、面投影、项目性及滤波纯性的推导义务。纯端点互反不代替完整有限混合律；不另加独立 Jordan 公理，也不将整条桥归给前件较强的单个外文定理。
其忠实坐标满足 $\tau_X\Phi_X=u_X$、$\Phi_XU_X=1_X$、$B_X(x,y)=\tau_X(\Phi_Xx\circ\Phi_Xy)$、$T^X_\xi(x)=B_X(\xi,x)$，双射整个原态基与原效应区间。以下在该坐标中书写，正锥为完整平方锥，$\tau_X$ 在每个简单因子的每个本原幂等元上为一；允许直和、秩一因子和 Albert 代数，尚未预选复型。
记 $\langle x,y\rangle_X=\tau_X(x\circ y)$、$\ell_xy=x\circ y$、$P_x=2\ell_x^2-\ell_{x^2}$。正元的 $x\perp y$ 指零迹配对，等价于 $x\circ y=0$ 及支撑正交；$x>0$ 指正可逆内点。二次表示对任意实元保正且自伴随，可逆时 $P_x^{-1}=P_{x^{-1}}$。
令 $n=\tau_A1_A$、$m=\tau_D1_D$。唯一供应的映射和参考为
$$
L:D\times A\to E\ \text{实双线性},\quad p:E\to D\ \text{实线性},\quad
L(D_+,A_+)\subseteq E_+,\quad p(E_+)\subseteq D_+,\quad \omega=1_D/m. \tag{75.2}
$$
全部内部对象由此定义：
$$
\begin{aligned}
\mathcal B(d,c)&=pL(d,c),&K(a)&=pL(\omega,a),&M(a,b)&=pL(K(a),b),\\
J(a)&=M(a,1_A),&H_{\mathrm s}(d)&=L(d,1_A),&B_1&=pH_{\mathrm s},\\
Q(a,b,c)&=L(M(a,b),c),&U&=M(1_A,1_A),&G&=H_{\mathrm s}1_D.
\end{aligned} \tag{75.3}
$$
两次调用的是同一个实际 $p$，不得另供独立 $M$、更换 $\omega$ 或独立选择第二次读回。完整保留两条实张成及全实 $Z$：
$$
\operatorname{span}_{\mathbb R}M(A,A)=D,\qquad
\operatorname{span}_{\mathbb R}L(D,A)=E,\qquad
B_1M(a,b)=\tau_A(a)Jb\quad(a,b\in A). \tag{75.4}
$$
被删两条的原量词是 $a,b\in A_+,a\perp b\Rightarrow Ja\perp Jb$（$D_J$），以及 $d,d'\in D_+,d\perp d'\Rightarrow H_{\mathrm s}d\perp H_{\mathrm s}d'$（$D_H$）。$L,p$ 的正性仍覆盖整个实际锥，包括全部纠缠方向；实张成不表示正乘积生成正锥。原保单位、保迹、CP、校准及物理滤波均非此基底的输入。

### 75.2 生成见证、先行内点与两张有限表

**定义 75.2（$\mathsf{JG}_3$ 与有限关系）。** 完整本原框架是两两正交、和为单位的本原幂等元族。有限框架族 $\mathfrak B=(B_r)_{r=1}^s$ **Jordan 生成** $A$，指含其全部成员、闭实线性组合与 Jordan 乘积的最小子代数为 $A$；不要求并集线性张成。$\mathsf{JG}_3$ 指存在这样的族且 $1\le s\le3$，允许重复框架。下述候选对该族使用存在量词，成员取自原比较几何，并非独立供应另一套制备或读回；是否可自然或物理选取不由存在量词保证。
在定义有限表之前，$\mathrm{PRE}_0$ 已保证 $U>0,G>0$：对任意正 $a\le r1_A,b\le t1_A$，正双线性性给 $0\le M(a,b)\le rtU$。若 $z\ge0$ 与 $U$ 零配对，它消去全部正乘积，锥生成性及第一实张成遂使它消去整个 $D$，故 $z=0$；自对偶性给 $U$ 内点。同理，$0\le L(d,a)\le rtG$ 与第二实张成给 $G$ 内点。这一论证未用 $D_J,D_H$ 或任何有限零表。
故可先定义 $C_D=P_{\sqrt U}$ 及 $F=C_D^{-1}M=P_{U^{-1/2}}M$。对同一个生成族要求
$$
\mathsf J_{\mathfrak B}:\quad \langle Je,Je'\rangle_D=0
\quad(e\ne e'\in B_r;\ 1\le r\le s), \tag{75.5}
$$
$$
\mathsf H_{\mathfrak B}:\quad
\langle H_{\mathrm s}F(e,f),H_{\mathrm s}F(e',f')\rangle_E=0
\quad((e,f)\ne(e',f')\in B_r\times B_t;\ 1\le r,t\le s). \tag{75.6}
$$
第二表取全部有序框架对；只比较各套列表内部不同成员，不要求跨框架的非正交原子也零配对。此时公式已有意义，产品列表的完整本原框架性质须在证明中建立。

### 75.3 保持原资格、原输入和原输出的混态 H13

**定义 75.3（原混态关系）。** 对恢复 PRE 的数据，采用 72.2—72.3、72.17 的原接口 [R]。令 $c_i$ 为 $A$ 的简单中心单位，$n_i=\tau_Ac_i$、$A_i$ 为其因子，$D_{ik}=\operatorname{span}_{\mathbb R}F(A_i,A_k)$，$\pi_{ik}$ 为相应中心块投影。置
$$
\alpha_{ik}=F(-,c_k)|_{A_i},\quad\beta_{ik}=F(c_i,-)|_{A_k},\quad
\mathcal Q=\{(i,k):n_i,n_k\ge2\},\qquad
R_i(x)=\alpha_{ik}\alpha_{ik}^*x-x,\quad R_k(x)=\beta_{ik}\beta_{ik}^*x-x, \tag{75.7}
$$
其中伴随取原规范迹内积，并定义
$$
\mathcal H(F)=\{\rho\in K_D:\ \forall(i,k)\in\mathcal Q,
\ R_i(\pi_{ik}\rho)\not\succeq0\ \text{或}\ R_k(\pi_{ik}\rho)\not\succeq0\}. \tag{75.8}
$$
至少一差不正指存在严格负方向，不指负定，也不改为两差皆不正。活跃块由此自动非零、具有正迹；非活跃块任取正元含零，只受原总迹一约束；$\mathcal Q=\varnothing$ 时取整个 $K_D$。在第一接口坐标中，两差恰是 $(\operatorname{Tr}_k x)\otimes I_{n_k}-x$ 与 $I_{n_i}\otimes(\operatorname{Tr}_i x)-x$，使用未经维数归一化的单位。资格不要求纯性、固定 Schmidt 谱或逐块条件化，只读取第一接口与原序，不读取插入输出。
由 65.3 已证可逆的 $\widetilde M:A\otimes_{\mathbb R}A\to D$，定义
$$
T_{\rm raw}(a,c)=L(Ja,c),\quad I^{\rm raw}=\widetilde T_{\rm raw}\widetilde M^{-1},\qquad
\mathrm H13:\ \exists\rho\in\mathcal H(F),\ I^{\rm raw}\rho\in E_+,
\qquad \mathrm{C13}:I^{\rm raw}(D_+)\subseteq E_+. \tag{75.9}
$$
本候选按“两表恢复 PRE，再读取此关系”解释；资格所用信息仍仅属第一接口。检测输入是同一个原总迹一 $\rho$，检测整个原输出锥，不换成运输态、固定效应或总迹读数。

### 75.4 两层恢复与统一三框架的同数据等价定理

**定理 75.4。** 在定义 75.1 的同一实际数据上，对任意固定的有限 Jordan 生成完整框架族，
$$
\mathsf J_{\mathfrak B}+\mathsf H_{\mathfrak B}\quad\Longleftrightarrow\quad D_J+D_H. \tag{75.10}
$$
而且，存在同一见证族使
$$
\boxed{\mathrm{PRE}_0+\mathsf{JG}_3+\mathsf J_{\mathfrak B}+\mathsf H_{\mathfrak B}+\mathrm H13}
\quad\Longleftrightarrow\quad \mathrm{PRE}+\mathrm{C13}. \tag{75.11}
$$
这里比较的是遗忘框架见证后的实际 $(A,D,E,C_X,u_X,L,p)$ 模型类。删去两边的 H13、C13，仍有相同的 PRE 等价。对 $\operatorname{rank}A=n$，两张表分别至多 $3\binom n2$、$9\binom{n^2}2$ 条零比较。

**证明。** 以下平方缺陷域、交换子、谱和矩阵单位计算仅是本定理的内部步骤；其一般结构归属见 [D]、[C]、[F]。
**（一）零平方缺陷的 Jordan 闭包。** 暂取一般有限 EJA $X,Y$，正保单位实线性映射 $\Phi:X\to Y$。对 $a=\sum_i\lambda_ie_i$ 的完整谱框架，置 $z_i=\Phi e_i\ge0,b=\Phi a$。由 $\sum_i z_i=1,\sum_i\lambda_i z_i=b$ 及二次表示保正，
$$
P_{\lambda1-b}=\lambda^2\mathrm{id}-2\lambda\ell_b+P_b,\qquad
\Delta(a):=\Phi(a^2)-b^2=\sum_iP_{\lambda_i1-b}z_i\ge0. \tag{75.12}
$$
求和三项分别为 $\Phi(a^2),-2b^2,b^2$；不要求 $\lambda_i1-b\ge0$，所以此证包含 Albert。若 $\Delta(a)=0$，对任意实 $t$、任意 $x$，
$$
0\le\Delta(a+tx)=2t[\Phi(a\circ x)-\Phi a\circ\Phi x]+t^2\Delta(x). \tag{75.13}
$$
分别令 $t$ 从正、负两侧趋零，锥闭且尖即得 $\Phi(a\circ x)=\Phi a\circ\Phi x$。若 $a,c$ 均零缺陷，展开 $\Delta(a+c)$ 并用此混合恒等式得零；$\Delta(ta)=t^2\Delta(a)$，故 $\mathcal D_\Phi=\{a:\Delta(a)=0\}$ 是含单位的实线性空间。还需闭平方：幂结合性与混合恒等式依次给 $\Phi(a^2)=b^2,\Phi(a^3)=b^3,\Phi(a^4)=b^4$，从而 $\Delta(a^2)=b^4-(b^2)^2=0$。极化遂使 $\mathcal D_\Phi$ 成为 Jordan 子代数；仅有线性闭包尚不足以得到这点。
**（二）权重交换域的 Jordan 闭包。** 对任意实 $h\in Y$，取完整本原谱细化 $h=\sum_i\lambda_ic_i$，写同时 Peirce 分解 $y=\sum_i y_{ii}+\sum_{i<j}y_{ij}$。直接作用于 $c_i$ 得
$$
[\ell_h,\ell_y]c_i=\frac14\sum_{j\ne i}(\lambda_j-\lambda_i)y_{ij},\qquad
\mathcal C_h:=\{y:[\ell_h,\ell_y]=0\}
=\bigoplus_{\lambda\in\operatorname{spec}h}Y_1(e_\lambda),\quad
e_\lambda=\sum_{\lambda_i=\lambda}c_i. \tag{75.14}
$$
第一式及 Peirce 空间直和强迫不同谱值之间的分量消失。反向，右侧的 $y$ 对每个 $e_\lambda$ 都在 $Y_1(e_\lambda)\oplus Y_0(e_\lambda)$ 中；Peirce 规则使 $\ell_y$ 保持该幂等元的 $1,1/2,0$ 空间，故与 $\ell_{e_\lambda}$、进而与 $\ell_h$ 交换。各 $Y_1(e_\lambda)$ 闭乘积，异块乘积为零，单位和为一，故 $\mathcal C_h$ 是 Jordan 子代数。这些 Peirce-one 代数是交换子子代数的块，并非一般都为整个 $Y$ 的理想。重谱必须合块；标量 $h$ 给整个 $Y$。直和中的零 Peirce 空间与 Albert 的非结合 Peirce 空间均在论证内。
**（三）支撑归一化推广有限保零。** 仍在一般 EJA 中，设 $T:X\to Y$ 正实线性，$h=T1>0$，且在某个 Jordan 生成完整框架族的每套内部保零。固定其中一套，写 $x_i=Te_i$、$q_i=\operatorname{supp}x_i$，零像规定 $q_i=0$。支撑两两正交；$\sum_i x_i=h>0$ 蕴含 $\sum_iq_i=1$，非零 $x_i$ 在其 $Y_1(q_i)$ 角内正可逆。块内谱计算遂给
$$
\Phi=P_{h^{-1/2}}T,\qquad \Phi1=1,\qquad
\Phi e_i=q_i,\qquad [\ell_h,\ell_{q_i}]=0. \tag{75.15}
$$
逆只施于全局 $h$；零像不求逆，也不要求 $q_i$ 本原。$\Phi$ 正且每个选定 $e_i$ 零平方缺陷，故（一）与源生成性给 $\mathcal D_\Phi=X$，$\Phi$ 为保单位 Jordan 同态。由（二），$\Phi^{-1}(\mathcal C_h)$ 是含全部选定原子的 Jordan 子代数；再次用生成性得 $\Phi(X)\subseteq\mathcal C_h$。两个闭包分别负责同态性与权重交换，不能省略后者。
对 $z\in\Phi(X)$，把 $[\ell_h,\ell_z]=0$ 作用于 $h$，得 $\ell_h^2z=\ell_{h^2}z$，从而 $P_hz=h^2\circ z$。自伴随性、$P_{\sqrt h}^2=P_h$ 及迹内积结合性给全部实 $x,y$ 的
$$
\langle Tx,Ty\rangle_Y
=\langle\Phi x,P_h\Phi y\rangle_Y
=\langle\Phi x\circ\Phi y,h^2\rangle_Y
=\langle\Phi(x\circ y),h^2\rangle_Y. \tag{75.16}
$$
因此正交正元的像正交；反向，全域保零当然给每套框架内保零。此步骤无单射、无非零像、无结合矩阵表示或 CP 前件。
**（四）先第一接口、后整个双份锥。** 对 $J$ 用（三）：$J$ 正，$J1=U>0$ 已在两表之前证明，故第一表恢复整个 $D_J$。此后才调用不使用 $D_H$、C13 的定理 65.3 [R]，得到
$$
F(a,b)=\alpha(a)\circ\beta(b),\quad\alpha=F(-,1),\quad\beta=F(1,-),\qquad
\widetilde F\text{ 为满规范迹等距},\quad m=n^2, \tag{75.17}
$$
其中 $\alpha,\beta$ 是保单位 Jordan 嵌入，两个像的乘法算子在环境 $D$ 上交换。于是每个 $F(B_r\times B_t)$ 都是完整本原框架：交换幂等元之积是幂等元，等距性给其范数平方一、故迹一而本原；不同成员零配对，双重求和为 $F(1,1)=1_D$。
令 $W$ 为这些产品成员的 Jordan 闭包。固定一边求和，$W$ 含所有选定的 $\alpha(e)=\sum_{f\in B_t}F(e,f)$ 和 $\beta(f)=\sum_{e\in B_r}F(e,f)$。源生成性及同态性给 $\alpha(A),\beta(A)\subseteq W$，故 $F(A,A)\subseteq W$；原第一实张成经可逆 $C_D^{-1}$ 给 $\operatorname{span}_{\mathbb R}F(A,A)=D$，所以 $W=D$。所选产品成员自身并不必线性张成 $D$。
现在 $H_{\mathrm s}$ 在整个 $D_+$ 上正，$H_{\mathrm s}1=G>0$；对这些完整生成框架用（三），第二表恢复整个 $D_H$，包括全部纠缠正元。反向，$D_J$ 给第一表，65.3 给产品框架性质，$D_H$ 给第二表，证明 (75.10)。
**（五）至多三套的逆向存在构造。** 从旧 PRE 出发，先由 66.3 [R] 得 $A=\bigoplus_iH_{n_i}(\mathbb C)$；此分类不使用 C13。对每个 $N\ge3$ 因子，取对角框架 $e_j=E_{jj}$ 及下述 Hermitian $B$ 的任意完整本原谱框架：
$$
B_{12}=B_{23}=1,\quad B_{13}=i,\quad B_{k,k+1}=1\ (3\le k<N),\quad
B_{ji}=\overline{B_{ij}},\qquad\text{其余项为零}. \tag{75.18}
$$
生成代数含 $B$ 及全部 $e_j$。重谱时在每个谱空间任取正交秩一细化即可，因为 $B$ 仍为该框架的实加权和，不要求细化投影都是 $B$ 的多项式。记 $R_{jk}=E_{jk}+E_{kj}$、$I_{jk}=iE_{jk}-iE_{kj}$（$j<k$）。$4e_j\circ(e_k\circ B)$ 提取 $jk$ 边，故已有 $R_{12},R_{23},I_{13}$ 及实尾边。矩阵单位乘法给
$$
2R_{12}\circ R_{23}=R_{13},\quad
2R_{12}\circ I_{13}=I_{23},\quad
2R_{23}\circ I_{13}=I_{12}. \tag{75.19}
$$
连同前三个对角元即得整个 $H_3$ 角。若已有 $H_k$ 角，令 $\ell=k+1$，对任意 $j<k$，
$$
2R_{jk}\circ R_{k\ell}=R_{j\ell},\quad
2I_{jk}\circ R_{k\ell}=I_{j\ell},\quad
2R_{jk}\circ I_{j\ell}=I_{k\ell}. \tag{75.20}
$$
因此得到全部新实、虚边及 $e_\ell$，归纳得到 $H_N$ 的整个实基。这两套完整框架 Jordan 生成该因子。
对 $H_2$，写 $H_2=\mathbb RI\oplus\{u\cdot\sigma:u\in\mathbb R^3\}$，$(u\cdot\sigma)\circ(v\cdot\sigma)=(u\cdot v)I$。任意两套完整框架的 Bloch 轴为 $u,v$，其生成代数包含于闭乘积空间 $\operatorname{span}_{\mathbb R}\{I,u\cdot\sigma,v\cdot\sigma\}$，维数至多三而 $\dim H_2=4$；三个 Pauli 轴的谱框架则线性张成整个 $H_2$。标量因子只需一套。
各因子的列表以重复补到三槽，逐槽把各因子的嵌入原子并成全直和的一套框架。每个中心单位是该因子原子之和，各局部生成运算都留在对应嵌入角内，故三槽生成整个直和；同构因子也不会被锁成对角副本。于是旧 PRE 给 $\mathsf{JG}_3$，原 $D_J,D_H$ 给两表。结合（四），也证明删去 H13、C13 的同数据等价。
**（六）原混态方向条件。** （四）恢复 PRE 后，原命题 72.7 给 $\mathcal H(F)\ne\varnothing$，总含全秩态，有活跃块时还含非纯混态；原定理 72.8 给每个 $\rho\in\mathcal H(F)$ 的 $I^{\rm raw}\rho\in E_+\Longleftrightarrow\mathrm{C13}$。其准确机制是：两边缘差至少一项不正蕴含原活跃块 NPT；原 $C_D^{-1}$ 是可逆局部合同，保持 NPT；错误单腿转置后插入未经归一化的中间单位仍有负方向，输出中心块直和与可逆 $C_E$ 不能消去它。此处只复用 NPT 的合同不变性，不声称 reduction 资格本身被滤波保持。
因此前向由一般 EJA 的（一）至（四）先得 PRE，再由 H13 得 C13；逆向由旧 PRE 分类和（五）选框架，再以 C13 与 72.7—72.8 得同一原 H13，证明 (75.11)，也给“全部合格成员通过”的等价版本。前向未预设复数，逆向未用新候选证明旧分类。每套局部框架有 $n$ 个成员、每套产品框架有 $n^2$ 个成员，分别数无序不同成员对即得所列条目上界。证毕。

### 75.5 严格放宽的见证与三套的准确尖锐范围

**命题 75.5（见证放宽与统一上界）。** 对同一选定框架族，Jordan 生成严格弱于第 74 章的线性张成要求；三套是本章完整局部框架／Jordan 生成签名在全部有限复直和上的统一尖锐上界。
**证明。** 在 $H_3$ 中，(75.18) 具体为
$$
B=\begin{pmatrix}0&1&i\\1&0&1\\-i&1&0\end{pmatrix},\qquad
B^2=2I+R_{13}+I_{12}+I_{23},\quad B^3=3B,\qquad
q_\pm=(B^2\pm\sqrt3B)/6,\quad q_0=I-B^2/3. \tag{75.21}
$$
由 $B^3=3B,B^4=3B^2$，这些自伴随元平方等于自身、两两乘积零且和为 $I$；$\operatorname{Tr}B=0,\operatorname{Tr}B^2=6$ 给各迹一，故为对应 $\sqrt3,-\sqrt3,0$ 的完整本原谱框架。它与对角框架 Jordan 生成九维 $H_3$，但两套线性张成都含同一单位，故并集线性维数至多 $3+3-1=5<9$。
取标准原模型 $A=H_3,D=H_9,E=H_{27}$，$L(d,c)=d\otimes c,p=\operatorname{Tr}_1,\omega=I_9/9$。同一 $p$ 两次给 $K(a)=I_3/3\otimes a$、$M(a,b)=F(a,b)=a\otimes b$。上述两套框架产生四套产品框架；其全部成员的线性张成包含于 $V\otimes_{\mathbb R}V$（$\dim V\le5$），故维数至多 $25<81$，却由定理证明（四）Jordan 生成全部 $H_9$。它们满足两表。
因此 Jordan 生成对同一个选定见证严格弱于线性张成；完整候选遗忘见证后的实际模型类仍为 PRE+C13。旧类含标准 qubit 模型，而任何两套 qubit 完整框架都不能 Jordan 生成，故“三”是本**完整局部框架／Jordan 生成签名**的统一尖锐上界。它不表示三个标量比较或三个实验，不是一般有限检测方案、量子公理数或物理资源的最优性；条目总数仍随维数增长。∎

### 75.6 删除控制与自然有限选态障碍

**命题 75.6（内部推广的必要边界）。** 下述前三个单映射控制分别说明：生成性、全锥正性和权重交换不能从定理证明（三）的推广步骤中无条件删去；它们不主张 PRE 其他保留项相互独立。
在 $H_2$ 上，正保单位 $T(a)=(a+a^T)/2$ 固定 $\sigma_x,\sigma_z$ 的两套谱框架，故各框架内部像保零；但 $\sigma_y$ 的两个谱原子都映成 $I/2$，配对为 $1/2$。这两套非生成框架不能控制全部正交方向。
定义实线性 $T1=1,T\sigma_x=\sigma_x,T\sigma_y=\sigma_x,T\sigma_z=\sigma_z$。三个 Pauli 框架生成且各套原子像均为正交投影；但对 $v=(\sigma_x+\sigma_y)/\sqrt2$、$e_\pm=(I\pm v)/2$，有 $Te_\pm=(I\pm\sqrt2\sigma_x)/2$、$\langle Te_+,Te_-\rangle=-1/2$。$T$ 非正，故有限表不能替代完整源锥上的正性；PRE 的整个纠缠锥量词仍必保留。
取 $S=\operatorname{diag}(2,1)$、$T(a)=SaS$，则 $h=T1=S^2>0$，$P_{h^{-1/2}}T=\mathrm{id}$ 是同态，却对 $\sigma_x$ 谱原子给 $\langle Te_+,Te_-\rangle=(4-1)^2/4=9/4$。同态性不能替代像与权重 $h$ 的算子交换。
H13 的必要性保留原定理 72.16 [R] 的同一坏模型：$A=H_2^r\oplus H_2^t\oplus\mathbb R^s$，全有序块、单位权重、普通 $F$，仅 $rst$ 槽的末腿转置异常，原 $L,p$ 精确按 (72.17)，原 $\omega$ 与同 $p$ 两次按 (72.18)。该模型满足全部 PRE，故存在三帧且全部合法族的两表都通过；但 $rt\to rst$ 将 Bell 投影单腿转置，反对称方向为 $-1/2$，C13 失败。两表不能替代相对方向条件。∎
定理 72.16 的自然选择障碍也完整保留：仅由第一接口与原比较几何决定、在第一接口同构下集合等变的非空有限态集，不能逐成员完整输出检测全 PRE 的 C13，也不能自然选出 $\mathcal H(F)$ 的非空有限子集；其大小允许依赖接口。外部框架见证不满足这种无参照自然选态要求，本章仍使用原 H13，未绕过该障碍。
完整框架的单位和、$h>0$ 及完整正锥都是上述归一化的范围。零像已经允许；不额外假设单射或本原像。奇异 $h$ 的支撑角问题不在本定理全目标单位归一化的断言内。

### 75.7 原量子几何、可选归一化与操作前件

**推论 75.7（保持原消费者）。** 完整 $S$ 桥与恢复的既有组合接口经 66.3、66.8 [R]，在 C13 之前已给
$$
A=\bigoplus_iH_{n_i}(\mathbb C),\quad D=\bigoplus_{i,k}H_{n_in_k}(\mathbb C),\quad
E=\bigoplus_{i,j,k}H_{n_in_jn_k}(\mathbb C),\qquad
\Pr(f\mid\rho)=\sum_\lambda\operatorname{Tr}(f_\lambda\rho_\lambda), \tag{75.22}
$$
其中 $\rho_\lambda\ge0,\sum_\lambda\operatorname{Tr}\rho_\lambda=1,0\le f_\lambda\le I_\lambda$ 是整个原态与原效应域；单份纯态空间为 $\bigsqcup_i\mathbb{CP}^{n_i-1}$，同区纯比较为模方 Born、异区为零。允许经典及多个量子扇区。H13 只补相对方向相容性，此后才沿 66.10、65.9—65.12 同时取普通二份、三份辅助张量，并接回原 $L,p,M$ 的完整正滤波族与逆向。
全部 $u_{ik},g_{ijk}>0$ 及唯一逆迹平衡 $\sum_{i,k}n_i\operatorname{Tr}(u_{ik}^{-1})=n^2$ 保留；原 $\omega$ 不变。辅助归一化一般不保原迹一截面，不能据此宣布原 $M,H_{\mathrm s}$ 保单位或原 $p$ 保迹，亦不强迫跨块对称或 $u,g$ 交换。若另要标准原归一化，可在已恢复方向后沿第五卷定义 73.2、73.10 与定理 73.11、73.16 [V] 加两个实际接口各自双侧的四项正重置补全及 $\mathrm A_0:\tau_E L(\omega,1_A/n)=1$。按其完整全锥、同接合与固定重置量词，恰得 $u=g=I$、原张量准备和原偏迹读回；校准不是本章候选前提，数学补全不等同装置供应。
操作仍按 69.1—69.11 [R] 的额外前件：先固定同一旁观者族 $\Psi_\Phi=C_DT_\Phi C_D^{-1}$、$(T_\Phi X)_{jk}=\sum_i(\Phi_{ji}\otimes\mathrm{id}_k)X_{ik}$，分支另限块 CP；若 Kraus 效应为 $F^a_{ji}=\sum_\ell K_{a,ji,\ell}^\dagger K_{a,ji,\ell}$，有限分支须满足两预算
$$
\sum_{a,j}F^a_{ji}\le I_i,\qquad
\sum_{a,j}F^a_{ji}\otimes u_{jk}\le I_i\otimes u_{ik}\quad(\forall i,k). \tag{75.23}
$$
部分仪器用聚合预算；完整仪器两式都等号，即局部及原始联合总映射都 TP。固定输出扇区 $j_0$、其中任意密度 $\sigma$ 与同一个 $0<c\le1$，令 $R(a)_j=\delta_{j,j_0}(\sum_i\operatorname{Tr}a_i)\sigma$。正权弱共同重置 $cR$ 能在同族补成两边均 TP 的有限 CP 仪器，当且仅当 $u_{ik}=v_k$ 与输入行无关。充分小的 $c$ 仅使分支满足双预算，不保证共同补全；行一致时两预算才合为普通 Kraus 预算，取得整个标准有限局部 CP 仪器菜单，仍不校准 $g$ 或迫使 $v_k=I_k$。
Born 分支概率为原输出迹，只有正概率才除以该迹定义条件态；顺序复合与粗粒化仅在上述固定族内复用。若从实际事件导出 CP，还须供应同一事件的乘积延拓及足够大实际参考上的全锥正性，逐输入块至少其维数的参考才支持 Choi/Bell 判据。效应不唯一指定更新；唯一 Lüders 压缩还须该实际 CP 分支效应为相应锐投影，并在每个确定接受的归一态上逐点不变。源识别、共同重置、参考及数学滤波的物理可用性均另有前件。
若另给以原物理时间为参数的连续、时间齐次、可逆 $*$ 自同构群，才有逐复块的内 Hamiltonian 演化；时间、能量单位和 $\hbar$ 的识别仍来自原动力学来源。一般不可逆过程、独立右载体、四份以上组合及无限维一致性不由本章供应。比较端点互反不表示实际顺序测量交换。∎

### 75.8 完整候选的直观表述与数学来源

**直观白话。** 先保留全部状态与全部测试，用“确定接受纯参照的所有测试，对另一态至少接受多少”定义比较；任意随机纯制备都满足交换端点后平均的规则。完整旧桥先给一般 Jordan 几何。准备与同一个读回在整个正锥上可用，以原参考连续读回两次，并保留两条实张成和全实切片等式。现在只选至多三套完整互斥方向，要求每套内部经 $J$ 后仍零比较，同族形成的每套双份产品方向经 $H_{\mathrm s}$ 后也仍零比较。归一化把这些像变成支撑投影；零平方缺陷域与权重交换域对加法、平方、Jordan 乘积都封闭，于是有限方向生成的全部局部几何都被锁住。双份空间再由两个边缘嵌入及其乘积生成，所以第二层也覆盖纠缠方向。
最后保留原混态 H13：每个两端非标量块，至少有一张边缘影像铺回后盖不住联合原块；存在一个这样的原总迹一态，其整个原插入输出为正。边缘盖不住保证错误单腿转置会留下负方向，可逆局部拉伸与中间插单位都不能消去它。两表负责全域零关系，H13 负责剩余相对方向。所得是同一实际模型类的完整条件候选；框架和关系的数学存在性不指定自然选择或物理制备，也不构成最少量子公理、全球新意、形式核验或完整量子起源结论。

**数学引文及适用范围。**

[R] [Atlas IV，固定文本版本 64c88225，§§65—72](https://github.com/the-omega-institute/trureturing/blob/64c88225fe7cafc77ec95ef1cfea1e12afcdc706/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_IV.md)：定义 72.1 的 PRE；定理 65.3 的无 $D_H$/C13 第一接口；66.2—66.10 的前交叉复型、权重、原态 Born 几何及方向恢复；72.3、72.7—72.8、72.16—72.18 的原混态资格、非空性、逐成员同原输出检测及有限自然选择障碍。69 的操作、双预算与共同补全仅在其固定旁观者 CP 族和原迹等额外前件下使用；65.10—65.11 的原始滤波逆向保持同 $p$ 两次和原参考。
[S] [Library 完整 $S$ 桥，同版本](https://github.com/the-omega-institute/trureturing/blob/64c88225fe7cafc77ec95ef1cfea1e12afcdc706/Library/QuantumStates/mullerududec2012selfduality.md#reciprocal-least-confirmation-and-the-spectrality-bridge)：从“Reciprocal least confirmation and the spectrality bridge”至“Complete conditional candidate and its scope”；保留全文载体、正对偶、项目性和纯滤波证明链。其外文接口为 Niestegge [2312.13213v2，Lemma 3(iv)、Lemma 5、Theorems 2—3](https://arxiv.org/abs/2312.13213v2) 的 proper-effect 范围，及 Barnum–Müller–Ududec [1403.4147v4，Theorem 16](https://arxiv.org/abs/1403.4147v4) 的项目性、对称转移和纯滤波条件；不将 bit symmetry 或仅自对偶性当作整条分类桥。
[P] [第五卷第 74 章，指定文本版本 75eb0961](https://github.com/the-omega-institute/trureturing/blob/75eb0961a70894fe335bdc3d29fa62eafd049d12/docs/develop/theory/QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md)：定义 74.1 的同原 $\mathrm{PRE}_0$ 与符号；本章的生成闭包与两层推广由定理 75.4 自行证明。
[V] [第五卷第 73 章，固定文本版本 64c88225](https://github.com/the-omega-institute/trureturing/blob/64c88225fe7cafc77ec95ef1cfea1e12afcdc706/docs/develop/theory/QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md)：定义 73.2 的两个实际位置补全、定义 73.10 的标量锚、定理 73.11 与 73.16 的同数据校准；仅作方向恢复后的可选消费者。
[D] E. Størmer，[*Multiplicative properties of positive maps*，math/0607090v1，§1 (1)—(2) 后 definite set 段](https://arxiv.org/abs/math/0607090v1)，期刊版 Math. Scand. 100 (2007), 184—192，[DOI](https://doi.org/10.7146/math.scand.a-15020)：正保单位 C* 映射的 Jordan definite domain 与混合乘积工具；该文 C*/JC 范围本身不包含 Albert，本章 (75.12)—(75.13) 给所需有限 EJA 证明。
[C] J. van de Wetering，[*Commutativity in Jordan Operator Algebras*，1912.01903v1，Definitions 2.6—2.7，Propositions 2.13、2.21、2.25、2.34，Theorem 3.13](https://arxiv.org/abs/1912.01903v1)：算子交换、幂等元交换子、二次表示保正、有限 JB/EJA 范围及交换子闭包；(75.14) 明确给出本章所需重谱和 Peirce 块公式，不借结合嵌入处理例外因子。
[F] H. Barnum、J. Hilgert，[*Strongly symmetric spectral convex bodies are Jordan algebra state spaces*，1904.03753v1，§4 Definition 4.1、Theorem 4.2](https://arxiv.org/abs/1904.03753v1)：完整本原谱框架与按不同谱值合并的谱幂等元；其定位 Faraut–Korányi, *Analysis on Symmetric Cones* (1994), III.1.1、III.1.3。本章只用有限 EJA 谱工具，不以强对称分类替换 [S]。矩阵单位归纳 (75.19)—(75.20) 属于复矩阵中的直接 Jordan 乘法计算。

## 追加锚（本行以下为增补区）

## 76. 同标框架的同步提升与生成性不可由两点表代替

本章第 65—72 章仍指第四卷，第 73—75 章指本卷。一般 EJA 的支撑归一化与 Jordan 闭包沿定理 75.4 的证明使用；本章把两层有限关系限制到同标产品框架，给出同一实际模型类的完整候选，并在整个原接口上分离有限两点读数、生成性与全域保零。

### 76.1 同一原系统与同标零关系

**定义 76.1（保留的基底与生成族）。** $\mathrm{PRE}_0$ 精确取定义 75.1：每个 $X=A,D,E$ 保留非零有限维实空间、闭尖生成锥、非零正元上严格正的 $u_X$、整个紧态基 $K_X$、全部效应 $[0,u_X]$、纯态 $P_X=\operatorname{ext}K_X$，以及只以纯态为第一端点的比较和全部有限混合律
$$
T^X_\xi(x)=\inf\{f(x):0\le f\le u_X,\ f(\xi)=1\},\qquad
T^X_\xi\!\left(\sum_\ell v_\ell\eta_\ell\right)=\sum_\ell v_\ell T^X_{\eta_\ell}(\xi). \tag{76.1}
$$
量词遍及每个纯 $\xi$、每个有限纯态族和每组概率权重。保留 75.1 与其 [S] 引用的完整一般 EJA 条件桥，包括正对偶生成、忠实配对、共同框架、面投影、项目性和滤波纯性；纯端点互反不替代该混合律。在忠实坐标中，原态与效应区间均完整保留，比较为规范迹配对；仍允许一般 EJA、Albert、直和和秩一因子，尚未取得复型。
令 $n=\tau_A1_A$、$m=\tau_D1_D$，唯一供应的映射与参考仍是全锥正的实双线性 $L:D\times A\to E$、全锥正的实线性 $p:E\to D$ 及 $\omega=1_D/m$。内部量由同一个实际 $p$ 定义：
$$
\begin{aligned}
K(a)&=pL(\omega,a),& M(a,b)&=pL(K(a),b),& J(a)&=M(a,1_A),\\
H_{\mathrm s}(d)&=L(d,1_A),&B_1&=pH_{\mathrm s},&U&=M(1_A,1_A),\quad G=H_{\mathrm s}1_D.
\end{aligned} \tag{76.2}
$$
保留 $\operatorname{span}_{\mathbb R}M(A,A)=D$、$\operatorname{span}_{\mathbb R}L(D,A)=E$ 及全实 $Z:B_1M(a,b)=\tau_A(a)Jb$。正性覆盖第一输入的全部纠缠正元和全部原输出锥；两次读回、原参考、原迹和原 $L,p$ 不变。定义 75.2 已仅由这些前件证明 $U,G>0$，因此可先于零表定义 $F=P_{U^{-1/2}}M$。
取同一原比较几何中的完整本原框架族 $\mathfrak B=(B_r)_{r=1}^s$；$\mathsf{JG}_3$ 表示存在 $1\le s\le3$ 的这种族，其全部成员的最小实 Jordan 子代数为整个 $A$。允许重复框架，不要求这些成员线性张满；存在见证不供应独立制备、读回、自然选择或物理装置。第一表保持 (75.5)，第二表只取同标配对：
$$
\mathsf J_{\mathfrak B}:\quad \langle Je,Je'\rangle_D=0\quad(e\ne e'\in B_r), \tag{76.3}
$$
$$
\mathsf H^{\mathrm{diag}}_{\mathfrak B}:\quad
\langle H_{\mathrm s}F(e,f),H_{\mathrm s}F(e',f')\rangle_E=0
\quad((e,f)\ne(e',f')\in B_r\times B_r). \tag{76.4}
$$
两式量化所有 $r$，不要求 $r\ne t$ 的 $B_r\times B_t$ 列表，也不要求不同框架间本来非正交的原子零比较。$F(B_r\times B_r)$ 的完整本原框架性质是下述证明的结论。

**定义 76.2（保留原混态方向条件）。** 两表恢复 PRE 后，完全按定义 75.3 读取 H13。写 $A=\bigoplus_iA_i$ 的中心单位为 $c_i$、秩为 $n_i$，$D_{ik}=\operatorname{span}_{\mathbb R}F(A_i,A_k)$ 的中心投影为 $\pi_{ik}$，并令
$$
\alpha_{ik}=F(-,c_k)|_{A_i},\quad\beta_{ik}=F(c_i,-)|_{A_k},\quad
\mathcal Q=\{(i,k):n_i,n_k\ge2\},\qquad
\mathcal H(F)=\{\rho\in K_D:\ \forall(i,k)\in\mathcal Q,
\ \alpha_{ik}\alpha_{ik}^*x-x\not\succeq0\ \text{或}\ \beta_{ik}\beta_{ik}^*x-x\not\succeq0,\ x=\pi_{ik}\rho\}. \tag{76.5}
$$
伴随取原规范迹内积；每个活跃块至少一差有严格负方向，不要求两差都不正或负定。非活跃块任取正元含零，只受同一原总迹一约束；$\mathcal Q$ 空时资格为整个 $K_D$。这里的边缘铺回使用未经维数归一化的单位，不要求纯态、固定 Schmidt 谱或逐块条件化。
以原 $\widetilde M$ 和 $T_{\rm raw}(a,c)=L(Ja,c)$ 定义
$$
I^{\rm raw}=\widetilde T_{\rm raw}\widetilde M^{-1},\qquad
\mathrm H13:\ \exists\rho\in\mathcal H(F),\ I^{\rm raw}\rho\in E_+,\qquad
\mathrm{C13}:\ I^{\rm raw}(D_+)\subseteq E_+. \tag{76.6}
$$
检测同一个原 $\rho$ 的整个原输出，不以滤波后的态、固定效应、总迹或校准后的输出替代。这个分阶段定义不把尚未恢复 PRE 的对象自动视作具有其结构。

### 76.2 同标提升的完整等价与计数

**定理 76.3（只需同标产品框架）。** 在定义 76.1 的同一实际数据上，对任意有限 Jordan 生成完整框架族，
$$
\mathsf J_{\mathfrak B}+\mathsf H^{\mathrm{diag}}_{\mathfrak B}\quad\Longleftrightarrow\quad D_J+D_H. \tag{76.7}
$$
其中 $D_J,D_H$ 分别保持全部 $A_+$、$D_+$ 上的正交正元对。特别地，遗忘框架见证后，
$$
\boxed{\mathrm{PRE}_0+\mathsf{JG}_3+\mathsf J_{\mathfrak B}+\mathsf H^{\mathrm{diag}}_{\mathfrak B}+\mathrm H13}
\quad\Longleftrightarrow\quad\mathrm{PRE}+\mathrm{C13}. \tag{76.8}
$$
删去两边的 H13、C13 仍为同实际模型类的等价。两张表分别不超过
$$
s\binom n2\le3\binom n2,\qquad s\binom{n^2}2\le3\binom{n^2}2. \tag{76.9}
$$

**证明。** 第一步仅在一般 EJA 中应用 75.4（三）的生成框架工具于 $J$。其前件是全锥正性、$J1=U>0$ 和第一表，因此取得整个 $D_J$，未使用复型、第二表或 H13。该工具的证明同时使用零平方缺陷域和权重算子交换域的 Jordan 闭包；两者的前件与 Albert、重谱、直和、零像范围完整保留。
第二步才用不依赖 $D_H$/C13 的第四卷定理 65.3，取得保单位 Jordan 嵌入 $\alpha=F(-,1)$、$\beta=F(1,-)$，其像的乘法算子在 $D$ 中交换，且
$$
F(a,b)=\alpha(a)\circ\beta(b),\qquad \widetilde F\text{ 是满规范迹等距},\quad m=n^2. \tag{76.10}
$$
所以 $\mathsf C_r=F(B_r\times B_r)$ 是完整本原框架：交换幂等元之积幂等，等距性给每个像范数平方一、迹一，故本原；不同成员正交，双重求和为单位。
令 $W$ 为全部 $\mathsf C_r$ 成员的 Jordan 闭包。对每个 $e\in B_r$，仅在同一 $r$ 中求行和与列和就得
$$
\alpha(e)=\sum_{f\in B_r}F(e,f)\in W,\qquad
\beta(e)=\sum_{f\in B_r}F(f,e)\in W. \tag{76.11}
$$
因此源生成性和同态性分别给 $\alpha(A),\beta(A)\subseteq W$。$W$ 闭 Jordan 乘积，遂含全部 $F(A,A)$；第一条实张成经可逆 $P_{U^{-1/2}}$ 给 $\operatorname{span}_{\mathbb R}F(A,A)=D$，所以 $W=D$。这里不声称有限所选产品成员本身线性张满。不同框架的交叉产品没有参与此生成证明。
第三步对全锥正的 $H_{\mathrm s}$ 使用同一个工具：$H_{\mathrm s}1=G>0$，而这些同标产品框架已经 Jordan 生成整个 $D$；第二表遂恢复整个 $D_H$，包括纠缠正元。反向，$D_J$ 给第一表和 (76.10)，$D_H$ 给第二表，证明 (76.7)。
从旧 PRE 出发，第四卷 66.3 先给复 Hermitian 直和；75.4（五）在这个已取得的环境中构造至多三套完整生成框架，包含 qubit 的三个 Pauli 框架、较高秩的非实三角加实尾谱框架及保中心的直和合并。因此前向无需预选复数，逆向不循环使用新候选；也得删去 H13/C13 的等价。恢复 PRE 后，75.4（六）所引 72.7—72.8 保证资格非空及每个合格原态的全输出正性等价 C13，给 (76.8)。最后每套局部框架有 $n$ 个成员，同标产品框架有 $n^2$ 个成员，数各自无序不同成员对即得 (76.9)。证毕。

相对 (75.6) 的 $s^2$ 套产品框架，本定理只保留 $s$ 套；统一上界由 $9\binom{n^2}2$ 降至 $3\binom{n^2}2$。这是同实际模型类内的关系冗余删除，不是三个实验，不保证每套都不可再删，也不证明最少公理。局部三框架的统一尖锐性仍只在 75.4 的完整框架/Jordan 生成签名内成立。

### 76.3 相同十二原子两点表的不同生成闭包

**命题 76.4（生成性不是所选两点表的后处理）。** 在同一个 $A=H_4(\mathbb C)$ 中，令 $X,Y,Z$ 为 Pauli 矩阵、$I=I_2$，省略张量符号。对 $s,t\in\{\pm1\}$ 定义
$$
\begin{aligned}
E_{st}&=(I_4+sZI+tIZ+stZZ)/4,&F_{st}&=(I_4+sXI+tIX+stXX)/4,\\
G^{\mathrm r}_{st}&=(I_4+sXZ+tZX+stYY)/4,&G^{\mathrm c}_{st}&=(I_4+sYI+tIY+stYY)/4.
\end{aligned} \tag{76.12}
$$
两个有标签框架三元组 $(E,F,G^{\mathrm r})$ 与 $(E,F,G^{\mathrm c})$ 的全部十二原子两点表 $\operatorname{Tr}(pq)$ 完全相同：同框架为 Kronecker delta，异框架恒为 $1/4$。前者 Jordan 闭包为 $H_4(\mathbb R)$，实维数十；后者闭包为 $H_4(\mathbb C)$，实维数十六。

**证明。** 每套使用两个可交换自伴随对合 $A_0,B_0$，而 $A_0,B_0,A_0B_0$ 均迹零。因此 $(I_4+sA_0)(I_4+tB_0)/4$ 是四个和为单位的正交迹一投影，故完整本原。第三套用 $(XZ)(ZX)=(-iY)(iY)=YY$。Pauli 张量迹正交；每个三元组中，各套使用的三个非单位 Pauli 张量集合不相交，故跨套配对只剩 $\operatorname{Tr}I_4/16=1/4$。
把 $E$ 记为对角投影 $e_j$；$F_{++}=q=\mathbf1\mathbf1^*/4$。对 $j\ne k$，$4e_j\circ(e_k\circ q)=(E_{jk}+E_{kj})/4$。所以 $E,F$ 生成全部实对称矩阵单位，又都实，闭包恰为 $H_4(\mathbb R)$。$G^{\mathrm r}$ 也实，因为 $YY$ 实，加入它不扩大闭包。
另一方面，$\sum_{s,t}sG^{\mathrm c}_{st}=YI$，其一个非零虚 Peirce 分量给 $I_{13}=iE_{13}-iE_{31}$，差一个非零实因子。已有全部 $R_{jk}=E_{jk}+E_{kj}$；三个不同指标的矩阵单位乘法给
$$
2R_{12}\circ I_{13}=I_{23},\quad 2R_{23}\circ I_{13}=I_{12},\qquad
2I_{jk}\circ R_{k\ell}=I_{j\ell},\quad 2R_{jk}\circ I_{j\ell}=I_{k\ell}\quad(j<k<\ell). \tag{76.13}
$$
先得前三点的全部虚边，再经第四点得 $I_{14},I_{24},I_{34}$，与全部实边、对角元组成 $H_4(\mathbb C)$ 的实基。证毕。

该命题比较同一环境内的两个框架见证，不是两个完整 PRE 模型。它分离的是生成见证的充分性；不反驳保留生成性时的定理 76.3，也不反驳全部原态上的 $S$。相同有限两点表的任何后处理都无法分开这两个见证；需要原空间内 Jordan 乘积及其闭包所保留的关系。

### 76.4 全原接口中的删生成性反模型

**命题 76.5（完整插入正性不能补回遗漏的生成性）。** 固定 $0<\lambda<1$，取完整标准矩阵态、效应、迹和比较，并令
$$
A=H_4(\mathbb C),\quad D=H_{16}(\mathbb C),\quad E=H_{64}(\mathbb C),\qquad
T_\lambda a=\frac{1+\lambda}{2}a+\frac{1-\lambda}{2}a^T,\quad
L_\lambda(d,a)=d\otimes T_\lambda a,\quad p=\operatorname{Tr}_1,\quad\omega=I_{16}/16. \tag{76.14}
$$
这里 $p$ 始终为同一个四维首腿偏迹。上述数据满足整个 $\mathrm{PRE}_0$、完整 $D_H$ 和完整 C13；对 $(E,F,G^{\mathrm r})$ 两张有限零表均成立，所选原子及其 $J,F,H_{\mathrm s}F$ 像与 $T=\mathrm{id}$ 的标准模型逐项相同，但 $D_J$ 失败。

**证明。** $T_\lambda$ 为恒等与转置的凸组合，所以全锥正、保单位、保迹且对迹配对自伴随。它在实对称部分恒等，在纯虚反对称 Hermitian 部分乘 $\lambda$，故实线性可逆，不要求逆正。$L_\lambda$ 因而对全部 $d\in D_+,a\in A_+$ 正，包括纠缠的 $d$；$p$ 在整个 $E_+$ 上正。标准全态效应满足 (76.1)。原参考经同一个 $p$ 两次直接给
$$
\begin{aligned}
K(a)&=I_4/4\otimes T_\lambda a,&M(a,b)&=T_\lambda a\otimes T_\lambda b,&J(a)&=T_\lambda a\otimes I_4,\\
H_{\mathrm s}(d)&=d\otimes I_4,&U&=I_{16},&G&=I_{64},\quad F=M.
\end{aligned} \tag{76.15}
$$
$T_\lambda$ 可逆给两条实张成，且全部实输入上
$$
B_1M(a,b)=\operatorname{Tr}(T_\lambda a)\,T_\lambda b\otimes I_4=\operatorname{Tr}(a)Jb. \tag{76.16}
$$
$H_{\mathrm s}$ 保持整个 $D_+$ 上的正交，给完整 $D_H$。三套实框架的每个成员被 $T_\lambda$ 固定，因此 $Je=e\otimes I_4$、$F(e,f)=e\otimes f$、$H_{\mathrm s}F(e,f)=e\otimes f\otimes I_4$。全部所列读数与标准模型相同，两表成立，甚至所有 $B_r\times B_t$ 的旧第二表也成立。
在标准实张量识别下，$\widetilde M=T_\lambda\otimes T_\lambda$ 可逆，而 $T_{\rm raw}(a,c)=T_\lambda a\otimes I_4\otimes T_\lambda c$。因此逆映射消去两端的 $T_\lambda$，$I^{\rm raw}$ 在整个 $D$ 上恰为通常的中间插单位映射，是 $d\mapsto d\otimes I_4$ 的腿置换；它保整个正锥，给完整 C13，所有原输入的插入输出都与标准模型相同。此处可逆性由显式公式给出，未借尚未取得的 65.3。
最后在前两维角取 $p_\pm=(I_2\pm Y)/2$，其余两维补零。这两个本原投影正交，但
$$
\operatorname{Tr}(T_\lambda p_+T_\lambda p_-)=\frac{1-\lambda^2}{2},\qquad
\langle Jp_+,Jp_-\rangle_D=2(1-\lambda^2)>0. \tag{76.17}
$$
所以 $D_J$ 失败，且失败来自同一个原 $p$、原参考和整个原正锥。证毕。

本例只是否定“删去生成性仍能恢复 $D_J$”：指定的 $(E,F,G^{\mathrm r})$ 不生成 $A$。$A=H_4(\mathbb C)$ 本身仍存在其他至多三套生成框架，但它们不能同时通过第一表，否则 75.4（三）会推出与 (76.17) 矛盾的 $D_J$。完整 C13 不表示已经恢复 PRE。若将 (76.5) 的单块边缘公式明确延拓到本例，令 $\alpha(a)=T_\lambda a\otimes I$、$\beta(a)=I\otimes T_\lambda a$，则四维归一 Bell 投影 $\rho_\Omega$ 的两边缘均为 $I_4/4$，两种铺回差都为 $I_{16}/4-\rho_\Omega$，在 Bell 方向为 $-3/4$；其原插入输出仍正。这只是该单块公式延拓的通过，不是定义 76.2 的前序结构已经成立，也不能据以替代生成性。

### 76.5 量子公理对应、几何与完整白话

**推论 76.6（同标候选的消费者与范围）。** 在 (76.8) 的全部前件下，75.7 的原消费者完整保留：完整 $S$ 与组合桥给复 Hermitian 直和、全密度态与全效应、$\Pr(f\mid\rho)=\sum_\lambda\operatorname{Tr}(f_\lambda\rho_\lambda)$，以及单份纯态几何 $\bigsqcup_i\mathbb{CP}^{n_i-1}$；H13 选定相对方向后才可同时取普通二份、三份辅助张量。正滤波权重 $u,g$、唯一逆迹平衡及原参考仍按原式保留，不由有限零表自动成为标准归一化。
若另满足 73.2、73.10—73.16 的两个原接口双侧正重置补全与一次原总迹锚 $\mathrm A_0$，才得原 $u=g=I$、标准张量准备与偏迹。有限 CP 仪器仍须 69.1—69.11／75.7 的固定旁观者族、局部和原联合两预算；弱共同重置可同时补全两预算当且仅当权重输入行一致。事件的 CP 来源、足够大实际参考、锐效应和确定接受态逐点不变所需的 Lüders 前件、连续时间齐次可逆 $*$ 自同构群所需的 Hamiltonian 前件均不从本章静态零表取得。

**证明与入口边界。** 定理 76.3 先恢复同一 PRE+C13，遂可直接代入 75.7，原量词与尺度均不变。最新 Library [L] 的无序可区分纯对传递性结果提供另一条有条件入口：在完整有限维态效应和紧保序群下先得自对偶，另加每个纯态存在最小确认效应才识别内在比较并得完整 $S$。该群条件不自动给最小性，也不提供复型或组合；它只是充分入口，不是本章对 $S$ 的无条件替换或同模型类缩减。第四卷 72.16 的自然有限选态障碍及 75.6 的全锥正性、权重交换控制仍有效；本章并未给出无参照自然选框架。四份以上组合、无限维一致性、完整原来源与全部过程合同仍不由这些有限维关系供应。∎

**直观白话。** 先保留所有状态、所有测试、随机制备的完整比较规则，以及一个准备和同一个读回连续用两次的原系统。局部只选至多三套能生成全部空间的互斥方向；每套经过第一接口后仍互斥。提升到双份时，两边只使用同一套方向，不再把三套左右交叉成九套。一张同标方格的行和留下左边缘，列和留下右边缘；三张方格已经同时带回两边全部生成方向，它们的乘积再铺满整个双份空间，所以只检查三张方格也能锁住整个纠缠锥的零关系。随后仍用同一个原混态的边缘盖不住联合块、整个原插入输出为正，排除错误相对转置方向。为什么不能只看几张两点概率表？两套十二方向表可以逐项相同，却一套永远留在实矩阵平面，另一套生成全部复方向；转置平均还能把没看见的虚方向缩短，使所有已选表和完整插入都通过，却破坏遗漏方向的互斥。因而保留下来的关键是这些方向之间反复组合的关系，而不只是方向两两之间已经列出的数字。

本章简洁几何是同一局部 Jordan 生成族的同步产品提升；它没有预先在一般 EJA 中指定复相位图。Pauli 张量、互补框架、Peirce 提取、正映射和矩阵单位运算是成熟工具；本章只在其上给同原接口的约束删除及明确反模型，不作工具原创、全球优先权、最少量子公理、物理实现或形式核验声明。

**数学来源。** [V] [本卷第 73—75 章，固定文本 5555e728](https://github.com/the-omega-institute/trureturing/blob/5555e728b62ed8a7c5aea520bd396cf2c11b08d4/docs/develop/theory/QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md)：定义 75.1—75.3、定理 75.4 的一般 EJA 闭包和三框架存在、75.6 的控制、75.7 的消费者与其中明确归属的成熟来源；本章新同标生成论证为 (76.11)，不把旧闭包重算为新内容。[R] [第四卷，同固定文本](https://github.com/the-omega-institute/trureturing/blob/5555e728b62ed8a7c5aea520bd396cf2c11b08d4/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_IV.md)：65.3 第一接口不依赖 $D_H$/C13；66 的分类和方向、69 的操作前件、72.7—72.8 的原混态逐成员检测及 72.16 的自然选择障碍，各按原范围使用。[L] [Library 完整比较桥及“Appendix: unordered distinguishable-pair transitivity”，同固定文本](https://github.com/the-omega-institute/trureturing/blob/5555e728b62ed8a7c5aea520bd396cf2c11b08d4/Library/QuantumStates/mullerududec2012selfduality.md)：无序对称到自对偶的原文证明、最小确认效应的独立前件及其低维例外；不以该附录替代 [V] 中完整一般 EJA 桥。

## 追加锚（本行以下为增补区）

## 77. 纯制备元数的精确障碍、回路平衡与混合余项二元入口

本章的第 65—72 章引用均指[第四卷](QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_IV.md)，第 73—74 章引用指本卷。完整比较律到一般有限 EJA 的纸面桥已经由 [Library 的完整条件候选](../../../Library/QuantumStates/mullerududec2012selfduality.md#complete-conditional-candidate-and-its-scope)供应，包括正对偶剥离、共同框架、带符号谱性、自对偶、正面投影及最大杂质论证的滤波纯性，再明确调用 Barnum–Müller–Ududec 的 Theorem 16。本章直接复用这条链及其逆向，不重证、不把它列成未付桥，也不将它计作本章增量。要解决的是比较入口究竟约束哪些已有制备关系：只检验少量纯项，和允许二元式的一端带任意混合余项，逻辑内容不同。

### 77.1 全载体、达到的比较与元数定义

**定义 77.1（载体与 $S_k$）。** 取非零有限维实向量空间 $A$，$d=\dim_{\mathbb R}A$，闭、尖、生成的锥 $C$，以及在 $C\setminus\{0\}$ 上严格正的线性泛函 $u$。始终使用整个态基 $K=\{x\in C:u(x)=1\}$、$P=\operatorname{ext}K$ 及整个 proper 效应区间

$$
[0,u]=\{f\in A^*: f(C)\ge0,\ (u-f)(C)\ge0\}.
$$

对纯 $p$，定义确认集与比较

$$
F_p=\{f\in[0,u]:f(p)=1\},\qquad
T_p(x)=\min_{f\in F_p}f(x)\quad(x\in K).
\tag{77.1}
$$

$S_k$ 对每个 $p\in P$、每个 $1\le r\le k$、所有 $q_1,\ldots,q_r\in P$ 及所有 $w_j\ge0,\sum_jw_j=1$ 要求

$$
T_p\!\left(\sum_{j=1}^r w_jq_j\right)
 =\sum_{j=1}^r w_jT_{q_j}(p).
\tag{77.2}
$$

零权、重复纯态和不等正权都在量词中。完整 $S$ 要求每个有限 $r$；$S_1$ 恰为纯端点互反 $T_p(q)=T_q(p)$。这里元数数的是制备纯项，不是参照 $p$ 加上这些项的总标签数，更不是 Hilbert 维数。固定参照版本 $S_k(p)$ 仅固定 (77.2) 的第一端点，其余量词不动。

**命题 77.2（紧性、达到与有限纯分解）。** $K$、$[0,u]$、$F_p$ 均非空紧凸，$\operatorname{aff}K$ 的维数为 $d-1$，$P$ 张成 $A$；每个 $x\in K$ 有有限纯分解。(77.1) 的最小值达到，$0\le T_p(x)\le1$、$T_p(p)=1$，且 $T_p$ 在 $K$ 上连续、凹。

**证明。** 任取实范数。在紧集 $C\cap\{\|x\|=1\}$ 上，$u$ 有严格正最小值；故 $u(x)=1$ 的正元有统一范数上界。$K$ 闭而有界，因 $C$ 非零而非空。每个非零正元可除以其 $u$ 值，故 $C=\operatorname{cone}K$，生成性给 $\operatorname{span}K=A$，从而 $\operatorname{aff}K=\{u=1\}$。有限维紧凸集的极点分解定理给 $K=\operatorname{conv}P$，其中凸包指有限凸组合；亦可取至多 $d$ 个纯项。它不要求纯态 exposed，不要求原世界实际生成这些准备。

取 $K$ 中一组线性基 $x_1,\ldots,x_d$。任一 $f\in[0,u]$ 的基读数均在 $[0,1]$，所以整个效应区间有界；由对偶锥闭性它亦闭。$0,u$ 在区间内，$u\in F_p$，而 $F_p$ 是其闭仿射截面。连续线性评价在紧 $F_p$ 上取最小值。所有效应的对偶范数有统一上界，故它们的下包络满足同一 Lipschitz 界，特别地连续；线性函数下包络是凹函数。余下读数范围直接由定义得出。∎

### 77.2 任意整数条带载体与全 proper 效应

**定义 77.3（行列条带）。** 对每个整数 $q\ge2$，在 $\mathbb R^{q\times q}$ 中令 $r_i$ 是第 $i$ 行的指示阵除以 $q$，$c_j$ 是第 $j$ 列的指示阵除以 $q$。置

$$
A_q=\operatorname{span}_{\mathbb R}\{r_i,c_j:1\le i,j\le q\},\quad
C_q=\operatorname{cone}\{r_i,c_j\},\quad u(x)=\sum_{i,j}x_{ij}.
\tag{77.3}
$$

此处 $q$ 不必是素数或素数幂。$u(r_i)=u(c_j)=1$，$C_q$ 是有限生成闭锥，因它包含于非负坐标锥而尖，按定义在 $A_q$ 中生成，$u$ 在非零正元上严格正。其整个 $K_q$ 正是这 $2q$ 点的凸包。

**命题 77.4（唯一关系、全部极点与全部效应）。** 这 $2q$ 点均为 exposed 纯态，唯一线性关系生成元为

$$
\sum_i r_i=\sum_j c_j,\qquad
\dim A_q=2q-1,\qquad \dim\operatorname{aff}K_q=2q-2.
\tag{77.4}
$$

一个线性效应由 $a_i=f(r_i),b_j=f(c_j)$ 唯一决定，其为 proper 的充要条件恰是

$$
0\le a_i,b_j\le1,\qquad \sum_i a_i=\sum_j b_j.
\tag{77.5}
$$

特别地 $e_{ij}(x)=q x_{ij}$ 都是全锥上的 proper 效应。

**证明。** 行总量泛函在 $r_i$ 的值为一，在其他行态为零，在每个列态为 $1/q<1$，故唯一最大于 $r_i$；列总量对称地暴露 $c_j$。有限凸包没有其他极点。若 $\sum_i s_ir_i+\sum_jt_jc_j=0$，逐坐标给 $s_i+t_j=0$，故全部 $s_i$ 是同一个 $t$，全部 $t_j=-t$。这证明唯一关系及维数。赋值能下降为 $A_q$ 上的线性泛函，当且仅当它保持这一关系；锥由上述顶点生成，$f\ge0$ 与 $u-f\ge0$ 恰可在全部生成元上检验，故得到整个区间 (77.5)，并非只允许坐标效应。$e_{ij}$ 的行值只在 $i$ 为一，列值只在 $j$ 为一，满足 (77.5)。∎

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
\tag{77.6}
$$

所以减去中心后，行、列分别是两个正则 $(q-1)$-单纯形，各自中心为零，所在 $(q-1)$ 维空间互相正交；$K_q-x_*$ 是它们的 free sum，即直接和空间中两者并集的凸包。这一几何已有文献，准确归属见 77.12；这里的内积只解释条带坐标，不预置量子自对偶或比较配对。

### 77.3 精确比较公式与没有最小确认者

**定理 77.5（所有准备的最小读数）。** 任一准备

$$
x=\sum_i\alpha_ir_i+\sum_j\beta_jc_j,\qquad
\alpha_i,\beta_j\ge0,\quad \sum_i\alpha_i+\sum_j\beta_j=1
$$

在全效应区间下恰有

$$
\boxed{\quad T_{r_i}(x)=\alpha_i+\min_j\beta_j,\qquad
T_{c_j}(x)=\beta_j+\min_i\alpha_i.\quad}
\tag{77.7}
$$

所有纯态之间的比较为 $\delta$ 表。

**证明。** 确认 $r_i$ 的效应有 $a_i=1$，(77.5) 给 $\sum_jb_j=\sum_ka_k\ge1$。因此

$$
f(x)=\sum_k\alpha_ka_k+\sum_j\beta_jb_j
 \ge\alpha_i+(\min_j\beta_j)\sum_jb_j
 \ge\alpha_i+\min_j\beta_j.
$$

在最小 $\beta_j$ 的位置取 $e_{ij}$，其读数恰为右侧，故达到。列情形对称。若两套系数表示同一 $x$，唯一关系使它们相差 $\alpha'_i=\alpha_i+t,\beta'_j=\beta_j-t$，故 $\alpha'_i+\min_j\beta'_j=\alpha_i+\min_j\beta_j$；列式亦然。因此公式是 $x$ 的函数，不依赖选定表示。代入任一顶点即得同点一、异点零。∎

**命题 77.6（极小确认单纯形）。** $r_i$ 的序极小确认效应恰为：$a_i=1$、其余 $a_k=0$，而 $(b_j)$ 是概率向量。它们组成一个 $(q-1)$-单纯形，任意两个不同成员互不可比，$r_i$ 因而没有最小 proper 确认效应。这里不声称整个 $F_{r_i}$ 的仿射维数是 $q-1$。

**证明。** 对任一确认效应，令 $B=\sum_jb_j\ge1$，取 $b'_j=b_j/B$、$a'_i=1,a'_k=0$。这些值定义一个 proper 确认效应，且在所有生成元上不超过原效应，所以原效应支配这个概率向量成员。若某个确认效应不超过一个这样的成员，则其他行值必须零，列值逐项不超过该概率向量，同时列值和必须一，故逐项相等。这证明这些成员极小，也穷尽极小成员。不同概率向量不可能逐项同向比较，因为它们总和相同。若存在最小确认者，它必须同时等于全部这些极小成员，矛盾。列情形完全对称。∎

### 77.4 精确元数层级、最大缺陷与联合区分

**定理 77.7（$S_{q-1}$ 成立而 $S_q$ 失败）。** 对任意整数 $q\ge2$，条带载体满足 $S_{q-1}$，不满足 $S_q$。对指定准备，把重复条带的权重合并为 $\alpha,\beta$ 后，行参照的 (77.2) 左减右缺陷精确是 $\min_j\beta_j$，列参照精确是 $\min_i\alpha_i$。在所有参照及所有有限指定准备上最大缺陷恰为 $1/q$。

**证明。** 纯表为 $\delta$，故行参照的右侧就是该行在指定准备中的总权重 $\alpha_i$，(77.7) 给所列缺陷。至多 $q-1$ 个纯项，无论是否重复、有零权或权重不等，都不可能给 $q$ 条对侧条带各自正权；至少一个对应系数零，所以全部这些等式成立。

在同一个中心，取全列准备 $x_*=\sum_jc_j/q$ 与参照 $r_1$。其右侧零而 $T_{r_1}(x_*)=1/q$，故 $S_q$ 失败。又 $\min\beta\le(\sum\beta)/q\le1/q$，列式对称，中心实例达到上界。这只是该比较等式的精确缺陷，不是任何范数中的距量子空间或一般稳定性估计。∎

特别地，$q=3$ 有六个纯态、载体维数五、态基仿射维数四：所有纯二项混合都通过，三项列混合失败。三项制备标签并不表示三维 Hilbert 空间。给任意固定 $k$ 取 $q=k+1$，就否定在无统一维数限制时以固定纯元数 $S_k$ 代替完整 $S$；此为载体比较反例，不是满足全部原复合、PRE 或来源条件的 $\Omega$ 反模型。

**命题 77.8（全部 $q$ 元子集可联合区分仍不足）。** 任意至多 $q$ 个不同纯条带，都有一个数学上的归一化共同区分效应表；不存在区分 $q+1$ 个条带的这种表。因此“每个 $q$ 元子集都可共同区分”仍不蕴含 $S_q$。

**证明。** 先取恰好 $q$ 个，其中选中行集 $R$ 大小 $a$，选中列集 $B$ 大小 $q-a$。把 $R$ 双射匹配到未选列 $B^c$，把未选行 $R^c$ 双射匹配到 $B$，合成一个排列 $\pi$。$q$ 个效应 $e_{i,\pi(i)}$ 在每个顶点上恰有一个值一，故其和在整个 $A_q$ 上为 $u$。每个选中条带的唯一一值效应不同：一个配对不同时包含选中行与选中列。所以该表共同区分全部选中态。较小非空子集先扩成 $q$ 元，再把多余效应粗粒化并入保留结果，得到所需归一表。

反向，每个确认条带的效应在 $x_*$ 上至少 $1/q$。若 $(f_s)_{s=1}^n$ 是共同区分表，$\sum_sf_s=u$，则 $1=\sum_sf_s(x_*)\ge n/q$，所以 $n\le q$。定理 77.7 的失败需要对侧 $q$ 个标签再加参照端点，共 $q+1$ 个不同标签；已有的 $q$ 元联合区分没有覆盖这个关系。这些是全效应模型中的数学表，不供应原实际菜单或 analyzer。∎

### 77.5 $\delta$ 纯表类的锐维数阈值

**定理 77.9（仅在 $\delta$ 类中的锐阈值）。** 在定义 77.1 的载体上，另假设 $T_p(r)=\delta_{pr}$ 对全部纯对成立。令 $m=\lfloor(d+1)/2\rfloor$。则

$$
S_m\quad\Longleftrightarrow\quad K\text{ 是单纯形}
\quad\Longleftrightarrow\quad S.
\tag{77.8}
$$

$d=1,2$ 的载体自动是单纯形。此阈值不适用于具有非零异纯态过渡值的一般量子表。

**证明。** 若纯态多于 $d$ 个，取不超过 $d+1$ 个不同纯态中的一个最小线性依赖集。将其关系 $\sum_ic_iq_i=0$ 施以 $u$，得 $\sum_ic_i=0$；所有系数非零且正负两边均存在。除以共同正总和，把关系分成两套不交、各权严格正的凸准备，具有同一状态 $x$。每一侧至少两个成员，否则一纯态是其他不同纯态的真凸组合，与极性矛盾。

较短一侧至多 $\lfloor(d+1)/2\rfloor=m$ 个。取另一侧某成员为参照 $p$，其在该侧正权为 $\lambda>0$。每个确认 $p$ 的正效应在共同 $x$ 上都至少读出 $\lambda$，所以 $T_p(x)\ge\lambda$。但较短侧不含 $p$，$S_m$ 与 $\delta$ 表给 $T_p(x)=0$，矛盾。因此 $|P|\le d$。命题 77.2 的张成性迫使恰有 $d$ 个线性无关纯态，$K$ 是其单纯形。

反向，在单纯形中，取顶点基的坐标效应，确认一个顶点并在其他顶点取零。任何确认者在准备上的值至少是该顶点权重，坐标效应达到它，故对任意有限准备满足完整 $S$。完整 $S$ 当然给 $S_m$。$d=1$ 时态基为一点，$d=2$ 时非退化紧凸基为线段，直接得到末句。∎

**推论 77.10（奇偶维数的达到与最小反例维数）。** 奇维 $d=2q-1\ge3$ 的条带模型达到阈值：$S_{q-1}$ 不能迫使单纯形，$S_q$ 可以。偶维 $d=2q\ge4$ 也有同样反例。等价地，对每个 $k\ge1$，非单纯形、$\delta$ 表且满足 $S_k$ 的载体最小维数恰为 $2k+1$。

**证明。** 奇维已由定理 77.7。偶维取 $A'=A_q\oplus\mathbb R$、$C'=C_q\oplus\mathbb R_+$、$u'(x,s)=u(x)+s$。其全基是原条带基与新经典顶点 $z=(0,1)$ 的凸包，纯态恰为这些点，维数 $2q$。整个 proper 效应区间恰是 $[0,u]\times[0,1]$：这由两个直和锥分量独立测试得到。

对条带参照，确认者为 $(f,t)$，$f\in F_p,0\le t\le1$；取 $t=0$ 最小化经典部分。若一份全基准备的条带总质量 $\mu>0$，比较就是 $\mu T_p(x/\mu)$；$\mu=0$ 时直接为零，不作除法。其条带系数仍给 (77.7) 的齐次式 $\alpha_i+\min\beta$ 或 $\beta_j+\min\alpha$。对 $z$ 的参照，取 $(0,1)$ 得比较恰为经典质量 $s$，其他确认者不能更低。因此全纯表仍为 $\delta$，$S_{q-1}$ 仍成立，而原中心的 $q$ 列准备仍使 $S_q$ 失败。

最后若 $d\le2k$，则 $m\le k$，定理 77.9 排除非单纯形 $S_k$ 模型；$q=k+1$ 的条带维数 $2k+1$ 给达到。所有直和零质量与边界均已包含。∎

### 77.6 共同极小者、标准 Helly 界及其范围

**引理 77.11（同一确认者的交集判据）。** 固定 $p$，令 $h_p=\dim\operatorname{aff}F_p\le d-1$，并对每个纯 $r$ 定义非空紧 exposed 面

$$
A_{pr}=\{f\in F_p:f(r)=T_p(r)\}.
\tag{77.9}
$$

在纯互反成立的范围内，对任一正权有限准备，(77.2) 成立，当且仅当其支持上的 $A_{pr}$ 有共同点。对每个固定有限支持，仅测试其均匀混合即足以判定共同点；共同点一旦存在，所有不等正权、补零权和重复标签都自动满足等式。

**证明。** $F_p$ 位于 $f(p)=1$ 的仿射超平面，故有维数界。最小值达到给各面非空，线性评价的最小层是紧 exposed 面，允许它等于整个 $F_p$。任何 $f\in F_p$ 都满足各非负超额 $f(r)-T_p(r)\ge0$。由互反，准备等式要求最小加权超额为零；其最小值由同一 $f$ 达到。各权严格正时，加权和为零恰要求全部超额为零。这就是交集条件，也证明均匀权测试的充分性。零权先去掉，重复先合并，不删原量词。∎

**命题 77.12（标准 Helly 充分界）。** 固定参照处的 $S_{h_p+1}(p)$ 蕴含该参照处全部有限等式，并给一个同时达到所有纯读数的最小确认效应。因此统一 $S_d$ 或 $S_{1+\max_ph_p}$ 足以推出完整 $S$。此处只把标准有限维 Helly 定理应用到 $\operatorname{aff}F_p$，不主张该界锐或定理新颖。

**证明。** 单项给该参照与每个纯态的互反。引理 77.11 使任意至多 $h_p+1$ 个面都有共同点。有限 Helly 定理于是使每个有限面族交非空；$h_p=0$ 时 $F_p$ 是一点，结论直接成立。$F_p$ 紧，闭面族的有限交性质使 $\bigcap_{r\in P}A_{pr}$ 非空，即使 $P$ 无限或含非 exposed 极点。取交中 $e_p$，则 $e_p(r)=T_p(r)\le f(r)$ 对每个纯 $r$ 及每个确认者 $f$ 成立。纯态生成锥，故 $e_p\le f$ 于整个 $C$。它本身是确认者，故为最小者并在所有 $x\in K$ 上等于 $T_p(x)$，得到所有有限等式。$h_p\le d-1$ 给统一界。Helly 的引用范围见 77.12 节文献说明。∎

### 77.7 全确认区间带来的更强局部界

**定理 77.13（固定参照的 $\max(1,h_p)$ 界）。** 定义 77.1 的全效应载体具有更强结论：$S_{\max(1,h_p)}(p)$ 已足以得到该参照处完整等式和最小确认者。仅要求所有至多该大小的不同纯支持之均匀混合等式也足够。因此 $S_{\max(1,d-1)}$ 在任一载体上都足以推出完整 $S$；这里没有断言一般最优阈值。

**证明。** 关键是：这些共同极小面若有一个有限极小空交族 $A_{pq_1},\ldots,A_{pq_n}$，则

$$
2\le n\le h_p.
\tag{77.10}
$$

每个单面非空，故 $n\ge2$。记 $t_i=T_p(q_i)$。若 $t_i=1$，因全部 proper 效应不超过一，该面为 $F_p$，不能出现在极小空交族中。所以 $t_i<1$。$u\in F_p$，在 $V=\operatorname{span}(F_p-u)$ 上定义线性函数

$$
g_i(v)=-\frac{v(q_i)}{1-t_i},\qquad
G_i(f)=g_i(f-u)=\frac{1-f(q_i)}{1-t_i}.
\tag{77.11}
$$

$\dim V=h_p$，$0\le G_i\le1$ 于 $F_p$，$G_i(u)=0$，且 $A_{pq_i}=\{G_i=1\}$。极小性允许为每个 $j$ 选 $f_j\in\bigcap_{i\ne j}A_{pq_i}$，但 $f_j\notin A_{pq_j}$。故 $\delta_j=1-G_j(f_j)\in(0,1]$。

若 $\sum_i c_ig_i=0$，记 $C_0=\sum_ic_i$。在 $f_j-u$ 上评价给

$$
C_0-c_j\delta_j=0,\qquad
C_0=\sum_jc_j=C_0\sum_j\delta_j^{-1}.
\tag{77.12}
$$

因 $\sum_j\delta_j^{-1}\ge n\ge2$，只能 $C_0=0$，进而所有 $c_j=0$。所以这 $n$ 个线性函数独立，$n\le\dim V=h_p$，证明 (77.10)。这一步使用 $u$ 属于同一全确认集、读数上界一，以及所有面都来自最小读数；任意凸集的任意面族不具有这个改进。

现在单项等式给互反。若某有限支持空交，取其中一个极小空交子族，它的大小至多 $h_p$，与引理 77.11 及假设的均匀混合测试矛盾。$h_p=0,1$ 时 (77.10) 本身排除有限空交；单项仍保留互反义务。最后用紧性有限交性质及命题 77.12 后半段，得到所有纯态共同的最小确认者和完整等式。补零、不等权及重复由引理 77.11 恢复。∎

### 77.8 关系的关系：回路平衡的完整刻画

**定义 77.14（纯态回路与平衡）。** 一个回路是不同纯态的有限最小线性依赖集 $Q=\{q_1,\ldots,q_n\}$。其非零关系 $\sum_ic_iq_i=0$ 唯一到非零实倍数，所有 $c_i\ne0$。回路平衡要求对每个纯参照 $p$ 和每个这样的关系

$$
\sum_i c_iT_{q_i}(p)=0.
\tag{77.13}
$$

这是对已有准备恒等式的比较值守恒，不把负系数当作负物理质量：施以 $u$ 后 $\sum_ic_i=0$，正负分开再归一，才是两套非负准备。

**引理 77.15（有限关系由支撑内回路生成）。** 不同纯态的任一有限线性关系均是其原支持内回路关系的实线性组合。每个回路有至多 $d+1$ 个标签；按正负分成凸准备后，每一侧至少两项，因而每一侧至多 $d-1$ 项。

**证明。** 对关系非零系数的支持大小归纳。若支持本身最小依赖，它已经是回路。否则在支持内选一个最小依赖子集及其关系 $v$；选其中某个 $j$，从原关系 $c$ 减去 $(c_j/v_j)v$。所得仍为关系，支持不增且至少去掉 $j$，归纳即可；这里不要求消元过程保持系数符号。最小依赖集删去任何一点即独立，所以大小不超过 $d+1$，其关系空间一维且无零系数。$u$ 给两侧相同正系数和；单项侧会把一个极点写成其他不同纯态的真凸组合，不可能。因此 $n\ge4$、两侧各至少两项，较长侧也至多 $d-1$。这些是实际线性恒等式的证明操作，不是新准备的生成程序。∎

**定理 77.16（完整 $S$ 当且仅当回路平衡）。** 在同一全态全效应载体上，以下条件逐模型等价：完整 $S$；对每个纯参照成立的回路平衡 (77.13)；纯互反加回路平衡；每个纯 $p$ 有一个最小 proper 确认效应 $e_p$ 且 $e_p(q)=e_q(p)$。回路平衡本身已蕴含纯互反；在这个接口中无需另加互反。其线性效应均作用于原 $A$，不引入另一份状态或另选准备表示。

**证明。** 完整 $S$ 含互反。把任意关系分成同一态的两份凸准备，对两份使用 $S$，即得到回路平衡，事实上得到所有有限关系的平衡。

反向只假设对每个纯参照的回路平衡。固定 $p$，引理 77.15 使赋值 $q\mapsto T_q(p)$ 保持每个有限线性关系。因此它从纯态自由线性组合下降为 $A$ 上唯一的线性泛函 $e_p$；唯一性由 $P$ 张成 $A$。全部纯值在 $[0,1]$，故 $0\le e_p\le u$ 于生成锥，且 $e_p(p)=1$。全 proper 效应可用性于是给 $e_p\in F_p$。按最小值定义，对每个纯 $q$ 有

$$
T_p(q)\le e_p(q)=T_q(p).
$$

在参考 $q$ 处同样构造 $e_q\in F_q$，交换两端便得 $T_q(p)\le e_q(p)=T_p(q)$。所以两不等式强制 $T_p(q)=T_q(p)$；这里没有输入任何对称性假设。于是对任意确认者

$$
e_p(q)=T_q(p)=T_p(q)\le f(q)\quad(q\in P,\ f\in F_p).
$$

所以 $e_p\le f$ 于整个 $C$。$e_p$ 自身属于 $F_p$，故它是最小确认者，$T_p(x)=e_p(x)$ 对全部归一态成立，线性性立刻给完整 $S$，且 $e_p(q)=e_q(p)$。最后若直接给最小确认者与这条互反，它们在每个 $x$ 达到最小值，线性性又给 $S$。这证明所有等价。∎

全 proper 效应可用性在将 $e_p$ 纳入原 $F_p$ 时承重；限制允许效应后，不能直接使用这一步。交换两端还用了每个纯参照处的平衡，不能只凭一个固定参照处的平衡作此交换。77.11—77.13 的固定参照共同极小者结论仍保留其指定的单参照互反或 $S_1(p)$ 条件。这里没有增加原准备，也没有把状态相等升级成历史相同。

**推论 77.17（一般有限界及仍未确定的最优元数）。** 任一 $d$ 维载体的 $S_{\max(1,d-1)}$ 蕴含完整 $S$。令 $b(d)$ 为保证所有该维载体之完整 $S$ 所需的最小正纯元数，则

$$
\left\lfloor\frac{d+1}{2}\right\rfloor\le b(d)\le d-1\quad(d\ge3),
\qquad b(3)=2,\qquad b(1)=b(2)=1.
\tag{77.14}
$$

$d\ge4$ 的一般最优值本章未定；$\delta$ 类的锐值不冒充一般答案。

**证明。** 当 $d\ge3$，每个回路的两份凸准备各至多 $d-1$ 项。分别用 $S_{d-1}$ 读同一个共享态，就得到对每个纯参照的 (77.13)；定理 77.16 由平衡本身给 $S$。$d\le2$ 时基为单纯形，直接成立。下界由定理 77.7 及推论 77.10 的奇偶维反例，上界由刚证结论；$d=3$ 两界相合。另一条充分性证明已经由定理 77.13 给出，它额外保留固定参照的 $h_p$ 信息。∎

### 77.9 任意混合余项的二元律恰好保留完整关系

**定义 77.18（混合余项二元律 $\mathrm B_{\rm mix}$）。** 对每个纯 $p,q\in P$、每个原基中的任意 $x\in K$ 和每个 $0\le t\le1$，要求

$$
\boxed{\quad
T_p(tq+(1-t)x)=tT_q(p)+(1-t)T_p(x).
\quad}
\tag{77.15}
$$

第一参照仍纯，余项 $x$ 不限于纯态，也不被改成一套特选制备。该式只约束已有数学态与其混合恒等式；将数学混合解释成某个原程序的实际彩票时，仍需原来源本已供应那项混合。

**定理 77.19（完整入口等价与三列诊断）。** 在同一全态全效应载体上，$\mathrm B_{\rm mix}\Longleftrightarrow S\Longleftrightarrow$ 对每个纯参照的回路平衡；也等价于纯互反加回路平衡，以及互反的最小确认者条件。后两项按定理 77.16 的完整量词理解。它不是纯二项测试 $S_2$，也没有减少独立公理或资源需求的结论。

**证明。** $t=1$ 给互反。对正权纯准备按支持大小归纳：取第一项权重 $t<1$，把其余项除以 $1-t$ 形成余项 $x\in K$，用 (77.15) 再对余项用归纳假设，得到完整 $S$；单项、$t=1$ 直接处理，零权删除、重复合并后恢复原量词。反向用命题 77.2 将任意混合余项 $x$ 有限纯分解，对组合准备及余项分别用 $S$，就得到 (77.15)，包括 $t=0,1$。与回路平衡及另外两项的等价由定理 77.16。

在 $q=3$ 条带中，取 $p=r_1,q=c_3,x=(c_1+c_2)/2,t=1/3$。右侧的 $T_{c_3}(r_1)=0$ 且 $T_{r_1}(x)=0$；但 $tq+(1-t)x=x_*$，左侧 $1/3$。所以混合余项二元律精确查出纯二项测试漏掉的那条关系。所漏的不是单个比较数的精度，而是“全列均匀准备等于全行均匀准备”这一原仿射恒等式。∎

### 77.10 保留全部原对象的完整候选

**定义 77.20（回路／混合余项完整候选）。** 对每个原系统 $X=A,D,E$，保留定义 73.15 的全部全态基、全效应区间和原始有序载体，只把其比较入口的完整 $S$ 换成对每个纯参照的全部回路平衡 (77.13)；这是该接口的最少关系版本，纯互反由它推出。另一等价入口是 (77.15) 的 $\mathrm B_{\rm mix}$，纯互反加全部回路平衡的版本亦然。先由定理 77.19 恢复每个系统的完整 $S$，然后直接复用本章开头的既有 Library 纸面桥，取得忠实的规范迹 EJA 坐标。它不假定已有 Born 或 CP 来证明这个入口，也不再加入一条独立 Jordan 或滤波纯性公理；这里的最少关系版本只省去这个接口的冗余互反合取，不声称独立逻辑或物理公理、资源成本减少。

其余承重对象与量词逐项保留。令 $n=\tau_A1_A,m=\tau_D1_D,\omega=1_D/m$；只供应同一个实际全锥正实双线性 $L:D\times A\to E$ 与同一个实际全锥正实线性 $p:E\to D$，所有内部映射仍为

$$
\begin{aligned}
K(a)&=pL(\omega,a),& M(a,b)&=pL(K(a),b),& J(a)&=M(a,1_A),\\
H(d)&=L(d,1_A),&B_1&=pH,&Q(a,b,c)&=L(M(a,b),c).
\end{aligned}
\tag{77.16}
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
\tag{77.17}
$$

特别地，$D_H$ 遍及整个实际双份正锥，$Z$ 遍及全部实方向。第 74 节已经付清的有限张成框架版本可以按定理 74.7 等价复用，但这里不借它删除任何全锥正性、实张成或原菜单量词。

方向入口仍是定义 71.8 的 NB：从第一接口 $F=C_D^{-1}M$ 及其内在中心块形成完整 $\mathfrak E(F)$，每个两端非标量活跃有序块的条件态联合纯而 $F$ 内在边缘混，块质量任意严格正；非活跃块任意正，包括零，无活跃块时取整个态基。要求存在一个这样的同一原态 $\rho$，经由 $T_{\rm raw}(a,c)=L(Ja,c)$、$I^{\rm raw}=\widetilde T_{\rm raw}\widetilde M^{-1}$ 定义的原插入后仍在 $E_+$。第一接口可逆性建立后才取逆，不先运输或更换 $\rho$，不按输出反选资格。其每个成员检测 C13、非空性和全部边界沿 71.4—71.8a；也可完整使用第 72 节原混态非支配 H13 的已证等价版本。

最后，实际 $M:A\times A\to D$ 的两位置和实际 $L:D\times A\to E$ 的两位置，各保留定义 73.2 的严格正份额重置补全，共四项。每位置固定合法输出块、任意秩密度 $\sigma$ 和 $0<c\le1$；成功为 $cR_\sigma$，$R_\sigma(z)=\tau(z)\sigma$，其余有限局部分支正。联合分支须在整个原联合锥上正、满足同一个实际接合的全部实乘积延拓律，两层总和各自 TP。它们不是四个独立任意联合映射，也不先假定所有局部分支 CP。保留原标量锚

$$
\mathrm A_0:\qquad \tau_E L(\omega,1_A/n)=1.
\tag{77.18}
$$

这份候选的“重置补全”是原空间、原迹上的数学映射存在性；指定装置、程序、同菜单、成功失败记录实际供应这些分支，是另一个更强的来源条件，不能由存在量词自动获得。

**定理 77.21（同一原模型类与完整静态消费者）。** 定义 77.20 的回路平衡单独入口及混合余项入口，与定义 73.15 具有完全相同的实际 $(A,D,E,C_X,u_X,L,p)$ 模型类；其结论恰复用定理 73.16 及 (73.33)—(73.34)。存在有限非空扇区集及 $n_i\ge1$，在保持原迹、全部原态、全部原效应的坐标中

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
\tag{77.19}
$$

全部有序标签、重复标签、经典标量扇区、不等和零中心质量、实际相关与纠缠输入均保留。上述二份、三份与偏迹属于这些指定的原接口，不自动识别独立另一括号或四份以上组合。

**证明。** 在同一 $A,D,E$ 上逐个使用定理 77.19，由回路平衡本身或 $\mathrm B_{\rm mix}$ 恢复且仅恢复原完整 $S$；互反无需另作前件，全部其余未改前件给定义 73.15。其既有 Library 桥在这个顺序后使用，不把矩阵概率预置到比较定义中。71.6 与 71.8a 先从 NB 得原 C13；73.8 从四个正补全得原 $M$ 的滤子为单位、原 $L$ 仅剩一个共同正标量；73.10—73.11 的原锚消去该标量。于是 73.16 给实际普通乘积与两个唯一全实读回。原 Born 配对则已经由完整比较桥和 66.3、66.8 获得，73.9 明确它不是重置的新后果。逆向，定义 73.15 的完整 $S$ 给两个替代入口及纯互反，其他对象原封不动；所以这是同模型类等价，而非另造一个兼容量子模型。∎

### 77.11 操作、张量与时间消费者逐项保留来源

定义 77.20 的静态结论不能把数学重置存在性升级为全实际菜单供应。操作消费者严格沿 73.9：对每个原事件、分支、结果和记录，先要其同一实际操作满足原乘积延拓律，并在足够大的实际参考的整个联合正锥上为正。对每个输入块 $H_{n_i}$，若实际供应一个至少 $n_i$ 维的参考块及该同一事件的整个正延拓，才以嵌入的 $n_i$ 维 Bell 投影消费 Choi 判据，逐输入输出块取得 CP 及矩形 Kraus 形式。数学 Bell 态或原有限张量坐标的存在，都不供应所需参考、事件或菜单；73.13 的小旁观者转置控制继续有效。

若再保留原局部分支 TNI、相应联合预算，以及同一完整实际菜单的总 TP，则写输入块 $i$ 到输出块 $j$ 的分支为

$$
\Phi_{s,ji}(\rho_i)=\sum_\ell K_{s,ji,\ell}\rho_iK_{s,ji,\ell}^\dagger,
\qquad
\sum_{s,j,\ell}K_{s,ji,\ell}^\dagger K_{s,ji,\ell}=I_i
\tag{77.20}
$$

得到完整仪器；部分菜单的聚合预算用 $\le I_i$。结果概率是原未归一输出总迹 $q_s=\tau\Phi_s(\rho)$，只在 $q_s>0$ 才用 $\Phi_s(\rho)/q_s$ 条件化，零支保留其标签、记录和后续权限。顺序复合与真实粗粒化沿 69.3—69.4、69.11 的同族合同消费，不以一个 effect 唯一决定更新。锐投影效应 $P$ 的 Lüders 更新还须该实际 CP 分支效应恰为 $P$，且对每个确定接受的归一态逐点不变，才复用 71.8 所引锐中性唯一性；重复性、CP 或完整性各自不能代替这一条件。

(77.19) 给指定原二份、三份的普通有序乘积和相应偏迹，不意味着不同历史具有相同允许未来，也不从两份分别可得推断真实相关联合已供应。其他原参考、副本、另一括号、更高份联合及其来源相容性均保留原合同；没有免费复制、控制、相干叠加或准备生成。

仅当另有以原物理时间为参数的连续、时间齐次、可逆动力学群，且在这些有限复代数上为 $*$ 自同构，才沿 73.9 取得各块内推导及

$$
\dot\rho_i=-\frac{i}{\hbar}[H_i,\rho_i].
\tag{77.21}
$$

连续性固定离散中心标签；$H_i$ 仍有加标量自由度。原时钟、时间及能量单位、$\hbar$ 的识别都要其实际动力学来源。本章比较关系不供应该群，也不把失败、停止、销毁、返回或一般不可逆过程改成可逆运动。

### 77.12 成熟来源、已有固定元数先例与增量范围

**文献归属。** 条带的 free-sum 几何不是本章发明。Baumeister–Haase–Nill–Paffenholz，[Polytopes associated to Dihedral Groups，arXiv:1212.4442v1，Definition 3.1 与 Theorem 3.3，PDF 第 3—4 页](https://arxiv.org/pdf/1212.4442v1)，对每个整数 $n$ 描述 $Q_n$ 为两个 $(n-1)$-单纯形的 free sum，并归功 Collins–Perkinson。其 $W$ 的上部是重复 $I$，下部是 $I,R,\ldots,R^{n-1}$：每个坐标恰入一条上行、一条下行，且每对恰出现一次。依这个关联重排坐标并缩放 $1/q$，即得定义 77.3 的精确条带模型；这是此处说明的坐标对应，不把本文比较公式归成该文已述定理，也不主张先前 Collins–Perkinson 原文已被独立阅读。$q=3$ 还可与全部六个 $S_3$ 排列矩阵的 Birkhoff 多面体作数学识别，但无量子 Hilbert 维数含义。

77.6 节的标准 Helly 引用是 Amenta–De Loera–Soberón，[Helly's Theorem: New Variations and Applications，arXiv:1508.07606v2，Theorem 1.1，PDF 第 1 页](https://arxiv.org/pdf/1508.07606v2)。所用仅是有限仿射维数中每个至多 $h+1$ 子族有交则全部有限族有交；无限纯态族额外使用本章已证的紧性有限交性质。该引用的直接阅读范围是 PDF 第 1—2 页，不声称通读该综述；改进到 $h_p$ 的 (77.10)—(77.12) 在本章给出完整证明，不归给普通 Helly 定理。

**命题 77.22（已发表共同测量结果给出的固定纯元数先例）。** 无维数上界时，固定纯元数不足的广义概率理论现象已有发表来源。具体地，Lami–Goldwater–Adesso，[A Post-Quantum Associative Memory，arXiv:2201.12305v3，Definitions 2、8、9、11，Theorem 17、§4.2 的 (14)—(15) 及证明](https://arxiv.org/pdf/2201.12305v3)，给固定 $N$ 的共同归一化 $N$ 元测量构造；限制其选定纯顶点到凸包，再配备该凸包的全 proper 效应，就能推出非单纯形 $\delta$ 表的 $S_k$ 载体，取 $N=k+1$。这一限制和到 $S_k$ 的推论由下面证明承担，不是该文定理原句。

**证明。** 所引 Theorem 17 在 product-simplex GPT 中选出 $2^m$ 个纯顶点，使每个至多 $N$ 元子集有共同归一化区分测量，维数上界为 $d(N,m)\le m^{1+o_N(1)}$，$N$ 固定。取这些选中顶点的整个凸包与其锥的实张成。原顶点仍极端，有限凸包也没有其他纯态；原效应限制后 proper，所以给出的共同测量仍在新模型的全效应区间。全效应区间还可能增大，不能据此假设所有最小值不变；以下逐项确定所需最小值。

两个不同顶点有一个确认前者、在后者零值的测量效应，正性下界为零，故新纯表确为 $\delta$。给至多 $k$ 纯项的准备和参照 $p$，参照加准备的不同标签数至多 $k+1=N$，有共同区分表。其 $p$ 结果效应读出准备中 $p$ 的总权重；若 $p$ 不在准备中则读零。每个确认 $p$ 的正效应都不能低于这份权重，故下界达到，$S_k$ 成立，涵盖零权、不等权和重复。充分大 $m$ 时 $2^m>d(N,m)$，限制后维数不增而全部选中点仍纯，所以不是单纯形；定理 77.9 因而排除完整 $S$。

这证明宽泛的无维数统一固定元数失败已有文献先例。该来源的可靠准备、no-restriction 模型及数学测量没有供应原 $\Omega$ 的准备、菜单或复合接头。上述维数只使用所引渐近定理，不运行其程序、不复算数值，也不把其上界当成条带锐阈值。∎

该文直接阅读范围是 PDF 第 3—8、11—15 页；这里不声称阅读全篇。Library 的完整 $S$ 桥、第四卷的原恢复及第 73—74 节的结果均按原范围复用。本章集中给出全效应条带的达到公式、极小确认者与精确缺陷、$\delta$ 类锐维数阈值、共同极小面的局部改进、回路平衡与混合余项的完整同数据接口。这些是纸面综合及其手工推导，不声明全球新颖、优先权、独立公理或资源严格减少，更不声明 Lean 认证或新物理理论已完成。

### 77.13 普通解释、实际原来源成果与剩余目标

把一张方格纸上的每整行、每整列各看作一种纯准备。所有行平均与所有列平均是同一张均匀纸。确认某一行的测试，必须在那一行完全接受；由于行和列共享同一总量关系，它在全部列上的接受值总和至少一。给少于 $q$ 条列时，总能把不得不接受的那一份挪到没出现的列上，因此少项测试全过；所有列都出现后，再无地方可藏，最小读数就等于最小列权。两两纯比较表完全没有记录这个集体恒等式。正交的两个单纯形画出了同一个障碍：缺失的是两套铺满中心的方法之间的关系。

回路就是不能再拆小的制备恒等式。让每个纯参照的比较值保持这些回路，消元便保证它保持所有有限恒等式，并给出一个线性确认者：纯读数都在零到一之间，所以它在原全 proper 效应中可用。既然它是确认者，最小读数就不超过它的读数，得到一个方向的不等式；在另一个参考处重复构造、交换两端，又得反方向的不等式。互反于是自动成立，不需另行假定，线性确认者也随之成为全锥上的最小确认者，恢复完整 $S$。这一步同时需要所有纯参考的平衡和全 proper 效应可用性；单一固定参考的共同极小者论证仍保留其互反条件。也可以每次只剥出一个纯项，但余下整块必须允许是任意混合态：这样二元式每次都带着前面累积的关系，归纳才没有丢信息。只让两端都是纯态，就没有携带这块余项。有限维界说明需要看的支持大小受载体维数约束；它不是跨无界维数的一张固定有限验收表，更不是从三个标签直接制造三维量子系统。这给同一完整比较律两个精确替代入口，不意味着独立公理或资源成本减少。

原来源方面，[原观察卷 §§23—24](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ORIGINAL_INTERFACE_EXPOSURE_AND_RECOVERY.md#23-an-acquired-pending-operand-fibre-at-the-original-plan-entry)已经在明示原 $G_V$ 进展域上完成实际获取的有序操作数与独立 guard、真实拒绝和绑定、既有 Plan/Send 消费、无新增外部 IN 的不同下一原源及真实下一 Entry、实际服务返回、历史批次、HandbackResume、原 Stop／验证／消费和共同 INITIAL 终端答案；逐分支账目仍按原定理成立。新 DEV 的[续卷 §9](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ORIGINAL_INTERFACE_EXPOSURE_AND_RECOVERY_II.md#9-attribution-and-the-remaining-recovery-problem)还明确取得其新安装中 finitely attained completed canonical GuardAcquired 边界的当前四份交付与收到后 Plan 续接，其自身的 Busy、非规范输入和未改安装运输边界仍保留。这里不将这些已构造来源结果统称缺失，也不把新安装扩大成全部原域。既有下降、参考、递归支撑、原 $D$ 恢复及各有限返回合同继续按各自证明域成立。

本章没有构造[固定来源卷 (23.7)](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md)的原具名 analyzer 当前接受接口证书，也没有构造[有限返回卷定义 164.1](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md)所区分的原 $B_r$ 到 active-ready 接头。它们不是原观察卷已经证明的定理 23.7。矩阵相等、可逆字、纯态校准、数学效应表、存在菜单、矩阵综合和数学重置补全均不能自动填入这些实际来源。数学有限纯分解也不把全原准备改成实际纯态彩票生成，不把同一密度或同一比较表认作同一历史、记录与全部合法未来。

完整原 $\Omega$ 的全部准备、事件、过程、参考、副本、实际相关联合、零与不等质量、时钟与单位、控制、ready 与 flags、完整记录、失败、停止、销毁、返回及未来，连同所有原全菜单、固定支撑和每个已量化中间切口义务，均在其原域不变。定义 77.20 只等价重写比较入口，其他实际 PRE、NB／H13、四位置补全、锚及各量子消费者前件都保留。条带是这个入口的实质关系障碍，不是整个原世界的反模型；完整候选也没有完成实际 analyzer/menu/source、一般过程、物理时钟或严格简化的原总目标。原总目标仍未完成，没有以本章已完成的元数问题取代。

## 追加锚（本行以下为增补区）

## 78. 一个非负缺陷的完整候选与定量生成边界

本章第 65—72 章仍指第四卷，第 73—77 章指本卷。以下把同标两层零比较写为一个原几何缺陷，给保持同一实际模型类的完整候选；随后证明在两层生成条件数和原权重谱界下的显式稳定性，并以固定完整原接口区分精确恢复和无条件近似恢复。平方范数展开、正映射平方不等式、Peirce 规则和有限字典是证明内部的成熟工具，归属与适用范围见章末。

### 78.1 原基底、正分解与单缺陷候选

**定义 78.1（完整原域）。** $\mathrm{PRE}_0$ 精确取定义 75.1、76.1：每个 $X=A,D,E$ 是非零有限维实有序系统，具有闭尖生成锥、严格正归一化泛函、整个紧态基 $K_X$、全部效应和纯态集。只在纯第一端点定义最小确认比较，并对每个纯 $\xi$、每个有限纯态族及每组概率权重要求
$$
T^X_\xi(x)=\inf\{f(x):0\le f\le u_X,\ f(\xi)=1\},\qquad
T^X_\xi\!\left(\sum_\ell v_\ell\eta_\ell\right)=\sum_\ell v_\ell T^X_{\eta_\ell}(\xi). \tag{78.1}
$$
完整保留 75.1 的 $S$ 到一般有限 EJA 条件纸面桥、忠实态效应对应、正对偶生成、共同框架、面投影、项目性及滤波纯性。以下在该原忠实坐标中使用规范迹、完整平方锥、Jordan 乘积及 $\langle x,y\rangle=\tau(x\circ y)$；允许直和、秩一因子和 Albert，不预设复型。
结合 77.18—77.19，也可在每个原系统把 (78.1) 的完整有限混合律等价换成混合余项二元律
$$
T^X_\xi(t\eta+(1-t)x)=tT^X_\eta(\xi)+(1-t)T^X_\xi(x)
\quad(\xi,\eta\in P_X,\ x\in K_X,\ 0\le t\le1).
$$
记仅作这一入口替换的基底为 $\mathrm{PRE}_0^{\rm mix}$。它先在同一全态全效应载体上恢复完整 $S$，再使用原一般 EJA 桥；故与 $\mathrm{PRE}_0$ 是同实际模型类，不增加独立互反前件，不把混合余项改成纯态，也不供应实际纯态彩票。77.16 的原制备回路平衡是又一个等价入口，均按其全部纯参照量词保留。
唯一供应的映射和参考仍为全锥正实双线性 $L:D\times A\to E$、全锥正实线性 $p:E\to D$ 及 $\omega=1_D/\tau_D1_D$。所有内部量取同一个实际 $p$：
$$
\begin{aligned}
K(a)&=pL(\omega,a),&M(a,b)&=pL(K(a),b),&J(a)&=M(a,1_A),\\
H_{\mathrm s}(d)&=L(d,1_A),&B_1&=pH_{\mathrm s},&U&=M(1_A,1_A),\quad G=H_{\mathrm s}1_D,\quad F=P_{U^{-1/2}}M.
\end{aligned} \tag{78.2}
$$
保留两条实张成 $\operatorname{span}_{\mathbb R}M(A,A)=D$、$\operatorname{span}_{\mathbb R}L(D,A)=E$，以及全实 $Z:B_1M(a,b)=\tau_A(a)Jb$。$L,p$ 的正性遍及整个原锥，包含纠缠方向；实张成不是正乘积锥生成。$U,G>0$ 在任何零表之前已由正性和两张成证明，故 $F$ 已全乘积正且 $F(1,1)=1_D$；此时尚不宣称其为迹等距或 Jordan 组合接口。
取同一原几何中的 $s$ 套完整本原框架 $\mathfrak B=(B_r)$，定义
$$
\delta_J(\mathfrak B)=s\|U\|_2^2-\sum_r\sum_{e\in B_r}\|Je\|_2^2,\qquad
\delta_H(\mathfrak B)=s\|G\|_2^2-\sum_r\sum_{e,f\in B_r}\|H_{\mathrm s}F(e,f)\|_2^2,\quad
\delta=\delta_J+\delta_H. \tag{78.3}
$$
$\mathsf{JG}_3$ 仍指同一个 $1\le s\le3$ 的族 Jordan 生成整个 $A$，允许重复框架，不要求所选原子线性张满。见证取自原比较几何，其数学存在性不供应自然选取或物理制备。
**定义 78.2（完整原态关系）。** 在 $\delta=0$ 恢复 PRE 后，完全按定义 76.2 读取原 H13：对每个两端秩至少二的活跃块 $x=\pi_{ik}\rho$，至少 $\alpha_{ik}\alpha_{ik}^*x-x$ 或 $\beta_{ik}\beta_{ik}^*x-x$ 有严格负方向；伴随为原规范迹伴随，边缘铺回用未经维数归一化的单位。非活跃块任意正元含零；活跃集空时资格为整个 $K_D$。$\rho$ 为同一个原总迹一态，不作纯性、固定 Schmidt 谱或逐块条件化要求。
以同一原 $\widetilde M$、$T_{\rm raw}(a,c)=L(Ja,c)$ 定义 $I^{\rm raw}=\widetilde T_{\rm raw}\widetilde M^{-1}$；H13 要求存在上述合格原 $\rho$，其整个原输出 $I^{\rm raw}\rho$ 正。C13 则要求 $I^{\rm raw}(D_+)\subseteq E_+$。该阶段顺序不允许把未恢复 PRE 的对象预先赋予其块结构。

### 78.2 有限字典的量化生成

**定义 78.3（字深度和系数界）。** 对有限 EJA $X$ 中若干正单位分解 $\sum_i g_{ri}=1_X$，以 $1_X$ 及全部 $g_{ri}$ 为叶子，用带括号 Jordan 乘积组成有限字典 $W=(w_j)_{j=1}^q$。叶子深度为零，乘积深度为 $1+\max$ 两子字深度。每个字的谱范数至多一。字典具有参数 $(\ell,K)$，指深度至多 $\ell$，且每个 $x\in X$ 可写
$$
x=\sum_j c_jw_j,\qquad \sum_j|c_j|\le K\|x\|_\infty. \tag{78.4}
$$
这既要求生成，也量化拼出单位方向所需的系数。若合成算子 $W:\mathbb R^q\to X$ 的最小行奇异值为 $\sigma>0$，可取 $K=\sqrt{q\operatorname{rank}X}/\sigma$。字典取自原 Jordan 几何，不供应新的独立相位或操作。
**证明中的有限性。** 从叶子实张成 $V_0$ 递归取 $V_{j+1}=V_j+\operatorname{span}(V_j\circ V_j)$。一旦不再增长即为含叶子的 Jordan 子代数。因此在 $d=\dim_{\mathbb R}X$ 维空间，生成族必有深度至多 $d-1$ 的有限张成字典；但这不提供统一的 $K$。奇异值界由最小二范数逆解、$\|c\|_1\le\sqrt q\|c\|_2$ 及 $\|x\|_2\le\sqrt{\operatorname{rank}X}\|x\|_\infty$ 得到。这些有限线性代数工具只用于下述定理的定量前件。

### 78.3 精确候选与两层显式残差定理

**定理 78.4。** 在整个 $\mathrm{PRE}_0$ 上 $\delta\ge0$。对任意固定的有限 Jordan 生成完整框架族，$\delta=0\Longleftrightarrow D_J+D_H$。特别地，遗忘见证后有同一实际模型类的等价
$$
\boxed{\mathrm{PRE}_0^{\rm mix}+\exists\mathfrak B\,[\mathsf{JG}_3(\mathfrak B),\ \delta(\mathfrak B)=0]+\mathrm H13}
\quad\Longleftrightarrow\quad\mathrm{PRE}+\mathrm{C13}. \tag{78.5}
$$
删去两边的 H13、C13 仍等价；左侧 $\mathrm{PRE}_0^{\rm mix}$ 可等价换回 $\mathrm{PRE}_0$。
另设同一个模型上的局部原子字典具有 $(\ell_A,K_A)$，同标正分解 $F(B_r\times B_r)$ 在整个 $D$ 上的字典具有 $(\ell_D,K_D)$，并有
$$
\mu1_D\le U\le\mu R1_D,\qquad \mu1_E\le G\le\mu R1_E,\qquad
0\le\delta\le\varepsilon\le\mu^2,\quad \mu>0, R\ge1. \tag{78.6}
$$
令 $r_Y=\operatorname{rank}Y$、$N_Y=r_Y(r_Y+1)/2$，置
$$
C_{\ell,r,R}=(1+600R\sqrt r)(2N\sqrt N)^\ell,\quad N=r(r+1)/2,\qquad \eta=\varepsilon/\mu^2.
$$
则全部正交正元满足
$$
\begin{aligned}
\langle Ja,Jb\rangle_D&\le\mu^2K_A^2C_{\ell_A,r_D,R}^2\eta^{2^{-\ell_A}}\|a\|_\infty\|b\|_\infty,\\
\langle H_{\mathrm s}d,H_{\mathrm s}d'\rangle_E&\le\mu^2K_D^2C_{\ell_D,r_E,R}^2\eta^{2^{-\ell_D}}\|d\|_\infty\|d'\|_\infty.
\end{aligned} \tag{78.7}
$$
两个左端均非负；分别量化 $a,b\in A_+,a\circ b=0$ 与 $d,d'\in D_+,d\circ d'=0$。定量前件仅属于受限稳定性结论，不增添到 (78.5) 的精确候选。

**证明。** 每套 $Je$ 都是 $U$ 的正分解，每套 $H_{\mathrm s}F(e,f)$ 都是 $G$ 的正分解。平方范数展开给
$$
\delta_J=2\sum_r\sum_{e<e'}\langle Je,Je'\rangle_D,\qquad
\delta_H=2\sum_r\sum_{(e,f)<(e',f')}\langle H_{\mathrm s}F(e,f),H_{\mathrm s}F(e',f')\rangle_E. \tag{78.8}
$$
自对偶正锥使每项非负，故一个总缺陷为零当且仅当两表逐项为零。77.19 先把混合余项二元入口恢复为同一完整 $S$，所以可在原基底中调用定理 76.3：先在一般 EJA 恢复 $D_J$，再由 65.3 得两边缘嵌入，同标行列和使产品族生成整个 $D$，最后恢复 $D_H$。逆向先用旧 PRE 的分类再取三框架，无复型循环；H13 仍由 72.7—72.8 在恢复 PRE 后逐成员检测同一原输出。至此证明 (78.5)。在辅助内积空间 $D\oplus E$，各 $r$ 的 $(Je,0)$ 与 $(0,H_{\mathrm s}F(e,f))$ 是同一 $(U,G)$ 的正分解；(78.8) 正是这些分解的 Pythagorean 饱和，没有增加物理载体。
为证明显式界，暂取一般正 $T:X\to Y$，其 $h=T1$ 满足 $\mu1\le h\le\mu R1$，测试分解为 $\sum_i g_{ri}=1$。除 $T$ 以 $\mu$ 后，以下 $1\le h\le R1$，总测试缺陷至多 $\eta\le1$。置 $\Phi=P_{h^{-1/2}}T$、$\Delta(x)=\Phi(x^2)-(\Phi x)^2$，一般 EJA 的平方不等式由 75.4（一）给出。定义
$$
v_T(x)=\langle h,T(x^2)\rangle-\|Tx\|_2^2,\qquad
c_h(z)^2=2\langle z,(\ell_{h^2}-\ell_h^2)z\rangle.
$$
$T=P_{\sqrt h}\Phi$、$P_{\sqrt h}h=h^2$、$P_{\sqrt h}^2=P_h$ 及迹结合性给出原缺陷的两项恒等分解：
$$
v_T(x)=\langle h^2,\Delta(x)\rangle+c_h(\Phi x)^2,\qquad
c_h(z)^2=\frac12\sum_{i<j}(\lambda_i-\lambda_j)^2\|z_{ij}\|_2^2,\quad h=\sum_i\lambda_i e_i. \tag{78.9}
$$
第二式来自完整本原谱框架的正交 Peirce 分解：$\ell_h$ 在 $ij$ 空间的特征值为 $(\lambda_i+\lambda_j)/2$。因此两项非负，$v_T$ 为非负二次型、$\sqrt{v_T}$ 为半范数。第一项量化归一化平方缺陷，第二项量化权重不交换，均没有免费删除。
每个正分解项满足 $0\le g\le1$、$g^2\le g$，所以
$$
0\le v_T(g)\le\langle Tg,h-Tg\rangle\le\eta,
\qquad \|\Delta(g)\|_\infty\le\tau_Y\Delta(g)\le v_T(g),\quad c_h(\Phi g)\le\sqrt\eta. \tag{78.10}
$$
第一个上界使用 $T$ 正性；第二个上界使用所有分解交叉配对非负；最后用 $h^2\ge1$。这里没有要求 $g$ 幂等。
令 $q(x)=\sqrt{\|\Delta(x)\|_\infty}$。对每个归一化正态作用于 $\Delta(x+ty)\ge0$，标量二次式的判别式给
$$
\|\Phi(x\circ y)-\Phi x\circ\Phi y\|_\infty\le q(x)q(y). \tag{78.11}
$$
$q$ 是各态的平方缺陷半范数的上确界，故为半范数；又 $0\le\Delta(x)\le\Phi(x^2)\le\|x\|_\infty^21$，所以 $q(x)\le\|x\|_\infty$。依次在 $x\circ x^3$、$x\circ x^2$ 处分离 (78.11) 的缺陷，再展开 $(\Phi x^2)^2=((\Phi x)^2+\Delta(x))^2$，令 $t=\|x\|_\infty$，得
$$
q(x^2)^2\le2t^3q(x)+3t^2q(x)^2+q(x)^4\le6t^3q(x),\qquad
q(x\circ y)\le\sqrt{12(q(x)+q(y))}\quad(\|x\|_\infty,\|y\|_\infty\le1). \tag{78.12}
$$
后一式由 $4x\circ y=(x+y)^2-(x-y)^2$、半范数三角不等式和 $\|x\pm y\|_\infty\le2$ 得到。这里仅使用实自伴 Jordan 乘积，不把正映射升级为完整非自伴 Schwarz 映射。
还须控制第二项的乘积传播。令 $r=\operatorname{rank}Y$、$N=r(r+1)/2$、$b_r=N\sqrt N$，则
$$
c_h(z\circ w)\le b_r[\|z\|_\infty c_h(w)+\|w\|_\infty c_h(z)],\qquad
c_h(z)\le R\sqrt r\|z\|_\infty. \tag{78.13}
$$
给出第一式的具体一般 EJA 证明：每个 Peirce 分量 $z_p$ 满足 $\|z_p\|_\infty\le\|z\|_\infty$。对角投影为 $P_{e_i}$；非对角 $ij$ 投影为 $(P_d-P_s)/2$，$d=e_i+e_j,s=e_i-e_j$。这两个二次表示均正且把单位送到 $d$，所以各为谱范数收缩；不依赖结合矩阵表示。
$\ell_z$ 的迹内积算子范数至多 $\|z\|_\infty$，因为其谱特征值为 $\lambda_i$ 和 $(\lambda_i+\lambda_j)/2$，故 $\|z_p\circ w_q\|_2\le\|z_p\|_\infty\|w_q\|_2$，也可交换两项。给对角分量权重 $\omega_p=0$，给 $ij$ 权重 $\omega_p=|\lambda_i-\lambda_j|$。Peirce 规则使非零乘积或者只落在对角部分，或者落在单一非对角空间；后一种的输出权重至多 $\omega_p+\omega_q$。因此
$$
\begin{aligned}
c_h(z\circ w)&\le\sum_{p,q}\frac{\omega_p+\omega_q}{\sqrt2}\|z_p\circ w_q\|_2\\
&\le N\!\left[\|w\|_\infty\sum_p\frac{\omega_p}{\sqrt2}\|z_p\|_2+
\|z\|_\infty\sum_q\frac{\omega_q}{\sqrt2}\|w_q\|_2\right]
\le b_r[\|w\|_\infty c_h(z)+\|z\|_\infty c_h(w)].
\end{aligned}
$$
最后一步用至多 $N$ 个正交分量的 Cauchy–Schwarz。第二式由谱差至多 $R$、$\|z\|_2\le\sqrt r\|z\|_\infty$ 得到。重谱只使部分权重为零，全程没有除以谱差；同边乘积落在对角部分，贡献为零，Albert 同样适用。
对深度至多 $j$ 的字归纳，可取
$$
q(w)\le A_j\eta^{1/2^{j+1}},\quad c_h(\Phi w)\le B_j\eta^{1/2^{j+1}},\qquad
A_0=B_0=1,\quad A_{j+1}=\sqrt{24A_j},\quad B_{j+1}=2b_rB_j+R\sqrt r A_j^2. \tag{78.14}
$$
$q$ 的递推用 (78.12)。另一递推把 $\Phi(x\circ y)$ 分为 $\Phi x\circ\Phi y$ 及 (78.11) 的缺陷，再用 (78.13)；$\eta\le1$ 允许以较小指数统一上界。故 $A_j\le24$，$2b_r\ge2$ 给
$$
B_j\le(1+576R\sqrt r)(2b_r)^j,\qquad
\sqrt{v_T(w)}\le[R\sqrt r A_j+B_j]\eta^{1/2^{j+1}}
\le C_{j,r,R}\eta^{1/2^{j+1}}. \tag{78.15}
$$
字典系数界和 $\sqrt{v_T}$ 的三角不等式把此界传到全部 $x$。$v_T$ 的极化为
$$
V_T(a,b)=\langle h,T(a\circ b)\rangle-\langle Ta,Tb\rangle.
$$
当 $a\circ b=0$ 时，非负二次型的 Cauchy–Schwarz 给 $\langle Ta,Tb\rangle\le\sqrt{v_T(a)v_T(b)}$。恢复 $\mu^2$ 后即得一般 $T$ 的 (78.7) 形式。
最后，第一层取 $T=J$、分解项为 $B_r$ 原子；第二层取 $T=H_{\mathrm s}$、分解项为 $F(B_r\times B_r)$。后者在尚未恢复 $D_J$ 时已为正单位分解，所以无须先调用精确第一接口或声称其成员幂等。两层总测试缺陷各不超过 $\delta$，分别使用明确支付的字典参数便得 (78.7)。证毕。

### 78.4 固定完整原接口仍不能免除生成条件数

**命题 78.5（真生成族上的非一致性）。** 即使固定维数、全部原态效应、$L,p,\omega$、$U,G$ 和完整 C13，仍不存在与生成框架见证无关的 $f(t)\to0$，使全部真生成三框架的全域保零残差均不超过 $f(\delta)$。

**证明。** 固定 $0<\lambda<1$，使用 76.5 的同一个完整实际模型：
$$
A=H_4(\mathbb C),\quad D=H_{16}(\mathbb C),\quad E=H_{64}(\mathbb C),\qquad
T_\lambda a=\frac{1+\lambda}{2}a+\frac{1-\lambda}{2}a^T,\quad
L(d,a)=d\otimes T_\lambda a,\quad p=\operatorname{Tr}_1,\quad\omega=I_{16}/16. \tag{78.16}
$$
原 $p$ 始终为同一个四维首腿偏迹。$T_\lambda$ 全锥正、保单位、保迹且实线性可逆；两次读回给 $K(a)=I_4/4\otimes T_\lambda a$、$M(a,b)=T_\lambda a\otimes T_\lambda b$、$J(a)=T_\lambda a\otimes I_4$、$H_{\mathrm s}d=d\otimes I_4$、$U=I_{16}$、$G=I_{64}$、$F=M$。故两条实张成、全部实输入的 $Z$、完整 $D_H$ 均固定成立。$\widetilde M=T_\lambda\otimes T_\lambda$ 可逆且在 $I^{\rm raw}$ 中消去两端 $T_\lambda$；原插入为普通中间插单位，即 $d\mapsto d\otimes I_4$ 的腿置换，保整个原锥，给完整 C13。它对纠缠 $d$ 同样成立，不借尚未恢复的第一接口分类；正缺陷时不把分阶段 H13 宣称为已经成立。
仍令 $X,Y,Z$ 为 Pauli 矩阵，省略张量符号。取 76.4 的 $E,F$ 两套框架，第三套改为
$$
N_\theta=\cos\theta X+\sin\theta Y,\qquad
Q_{ab}(\theta)=\frac{I_4+aN_\theta I+bIN_\theta+abN_\theta N_\theta}{4},\quad a,b\in\{\pm1\}. \tag{78.17}
$$
这是两个可交换自伴随对合的四个联合谱投影，各迹一，故完整本原。前两套生成 $H_4(\mathbb R)$；具体地，$E$ 含对角 $e_j$，$q=F_{++}=\mathbf1\mathbf1^*/4$ 给 $16e_j\circ(e_k\circ q)=E_{jk}+E_{kj}$。当 $0<|\theta|<\pi/2$，第三套的带符号和给 $N_\theta I$，减去 $\cos\theta XI$ 并除以 $\sin\theta$ 得 $YI$。由 76.4 的虚 Peirce 分量及实边传播，得到全部虚反对称 Hermitian 矩阵单位，故 $\mathfrak B_\theta=(E,F,Q(\theta))$ 真正生成整个 $A$。$\theta=0$ 时第三套重复 $F$，只生成 $H_4(\mathbb R)$。
写 $c=\cos\theta,t=\sin\theta$。在全转置下反号的部分恰为
$$
Q^-_{ab}=\frac{atYI+btIY+abct(XY+YX)}4,
\qquad \|Q^-_{ab}\|_2^2=\frac12t^2(1+c^2).
$$
这四个 Pauli 张量迹正交、各范数平方四；其余部分被全转置固定。$T_\lambda$ 在两部分分别乘一和 $\lambda$，而每个 $Q_{ab}$ 的范数平方一，因此
$$
S_\theta=\sum_{a,b}\operatorname{Tr}[(T_\lambda Q_{ab})^2]
=4-2(1-\lambda^2)t^2(1+c^2),\qquad d_\theta=4-S_\theta. \tag{78.18}
$$
另两套实框架各自的平方范数和为四。第一层每套像的平方范数和为 $4S_r$，第二层为 $4S_r^2$，故由 $\|U\|_2^2=16,\|G\|_2^2=64$ 直接得
$$
\delta_J=4d_\theta,\qquad
\delta_H=4d_\theta(8-d_\theta),\qquad
\boxed{\delta(\mathfrak B_\theta)=4d_\theta(9-d_\theta)\longrightarrow0.} \tag{78.19}
$$
但前两维角中的固定本原投影 $p_\pm=(I_2\pm Y)/2$（其余两维补零）正交，且
$$
\langle Jp_+,Jp_-\rangle_D=2(1-\lambda^2)>0. \tag{78.20}
$$
它们的谱范数均为一，故直接否定所述统一模量。全部接口与尺度不动，只有框架见证接近真子代数；每个非零角度的生成性均没有失效。证毕。

**条件数为何必须退化。** 对任何预先固定的有限 Jordan 字典位置集，$\theta=0$ 的所有求值都实。取一个固定纯虚 Hermitian 元 $x$，使 $\|x\|_2=1$，则每个 $\langle x,w_j(\theta)\rangle$ 为 $\sin\theta$ 的倍数且余因子在零附近有界：Jordan 字的矩阵元素是 $c,t$ 的有限多项式，其纯虚部分在 $t=0$ 为零。因此若 $x=\sum_jc_jw_j(\theta)$，便有 $1\le C_W|\sin\theta|\sum_j|c_j|$。任何满足 (78.4) 的统一系数界必须至少按 $1/|\sin\theta|$ 发散，不能以“每次都生成”替代定量下界。

### 78.5 只控制源生成时的完整接口定性桥

**定理 78.6（有界原接口类的统一收敛）。** 固定 EJA 三元组 $A,D,E$、框架数 $1\le s\le3$、一套固定有限源 Jordan 字典位置集，以及正数 $\kappa,\zeta,R_0,\alpha,\beta$，其中 $\alpha\le\beta$。令 $W_{\mathfrak B}:\mathbb R^q\to A$ 为该字典的求值合成算子。考虑满足整个 $\mathrm{PRE}_0$ 和以下条件的全部原 $(L,p,\mathfrak B)$：
$$
\begin{gathered}
W_{\mathfrak B}W_{\mathfrak B}^*\succeq\kappa I_A,\qquad
\|\widetilde L\|,\|p\|\le R_0,\\
\widetilde M\widetilde M^*\succeq\zeta^2 I_D,\qquad
\widetilde L\widetilde L^*\succeq\zeta^2 I_E,\\
\alpha1_D\le U\le\beta1_D,\qquad \alpha1_E\le G\le\beta1_E.
\end{gathered} \tag{78.21}
$$
波浪号为双线性映射的原实线性化，映射范数、伴随均用原迹 Hilbert 张量坐标；行算子下界保持两条原实张成，不是要求冗余字典的列 Gram 正定。以谱范数至多一的全部正交正元对分别最大化 (78.7) 两个左端，得到 $r_J,r_H$。该类存在只依赖上述固定参数的有限模量 $\Omega(t)$，使
$$
r_J+r_H\le\Omega(\delta),\qquad \Omega(0)=0,\qquad
\lim_{t\downarrow0}\Omega(t)=0. \tag{78.22}
$$

**证明。** 全部有标签完整本原框架的集合紧：幂等、迹一、正交及和为单位是闭条件，且原子迹范数为一。有限字求值连续，故第一条行下界闭且保证生成。映射受统一范数界约束，全锥正性及全实 $Z$ 闭；两条映射行下界使满射张成在极限保留，$U,G$ 的下界使可逆性及归一化连续。因此 (78.21) 的完整原模型类 $\mathscr K$ 是有限维紧集。其余原态、效应及 $S$ 几何均已固定，没有把严格的满秩条件擅自当成自动闭条件。
$\delta$ 连续；两个残差对固定紧测试集取最大值，也连续。定义
$$
\Omega(t)=\sup\bigl(\{r_J+r_H:(L,p,\mathfrak B)\in\mathscr K,\ \delta\le t\}\cup\{0\}\bigr).
$$
紧性保证有限，精确零点定理 78.4 保证 $\Omega(0)=0$。若有 $t_k\downarrow0$ 而模量不趋零，取近似达上确界的模型并抽收敛子列，将得到同属 $\mathscr K$、缺陷零而残差正的极限，矛盾。证毕。

本结论只支付源字典下界，却另支付整个原接口的有界右逆和谱界；它只给定性收敛。显式 (78.7) 则直接支付两层字典参数，给指定指数和常数。不能把精确 65.3 当成正缺陷模型中的同态，免费从 $K_A$ 推出统一 $K_D$；如何在只知源条件数及原接口界时得到可用的第二层显式估计仍为 open。源框架字典在命题 78.5 的极限落入 $H_4(\mathbb R)$，故其行下界也必趋零，与本定理不矛盾。

### 78.6 量子消费者、简洁几何与完整白话

**推论 78.7（精确消费者及近似边界）。** 完整候选 (78.5) 精确满足时，76.6 的量子消费者及其额外前件逐项保留：

| 既有量子结构 | 本候选与既有推导的关系 |
| --- | --- |
| 复 Hilbert 态表示、全密度态、全效应、Born 迹配对 | 完整 $S$ 与一般 EJA 条件桥，加两层精确保零和两次组合关系，沿 65—66、75.7 得有限复 Hermitian 直和；单份纯态几何为 $\bigsqcup_i\mathbb{CP}^{n_i-1}$。 |
| 普通二份、三份辅助张量及相对方向 | 在 PRE 恢复后，原 H13 沿 72.7—72.8 排除错误相对转置；仍检查同一个合格原混态的整个原输出。 |
| 原准备的标准归一化与偏迹 | 仍另需 73.2、73.10—73.16 的两个原接口双侧正重置补全及一次原总迹锚 $\mathrm A_0$；$\delta=0$ 不自动令滤波权重为单位。 |
| CP 事件、仪器与 Lüders 更新 | 仍需 69.1—69.11 的实际旁观者、同事件联合正性、足够大参考及局部和原联合两预算；共同重置补全需输入行权重一致。锐效应与确定接受态逐点不变另行支付。 |
| Hamiltonian 动力学 | 仍需原物理时间的连续齐次可逆 $*$-自同构群；静态零缺陷不供应该群。 |

**证明与范围。** (78.5) 恢复的正是同一原 PRE+C13，故可直接代入 76.6、75.7 的消费者，不重新证明旧结论。正滤波权重、唯一逆迹平衡和原参考按原式保留。$\delta>0$ 时 (78.7)、(78.22) 只控制两个全域保零残差，不证明 $L,p$ 距某个精确模型的距离、不证明近似复型分类或有噪 H13/C13。近似方向检测另需负方向裕量、活跃块质量和滤波控制，不能从趋零残差略去。四份以上组合、无限维一致性、自然选框架、物理制备与全部过程合同仍未由这些关系供应。∎

本章的简洁几何是正分解的 Pythagorean 饱和：同一个总向量由若干正部分相加，只有各部分两两垂直时，平方长度才恰好相加。借助 76.3 的同步生成，一条 $\delta=0$ 同时写完两层有限保零约束；这是等价的表达压缩，不是独立物理前提减少，也不是一次实验即可检验。它保留完整基底、生成性、共同接口和原方向条件。定量内容进一步把“生成”分成是否能拼出全部方向，以及拼出这些方向会放大多少误差。

**完整白话。** 先保留所有状态、所有测试、随机制备的完整比较规则，以及一个准备和同一个读回连续用两次的原系统。选至多三套能生成整个空间的互斥方向，把每套方向经过第一接口，再把左右同一套方向排成双份方格并经过第二接口。每张图里的各部分都是正的，相加总是同一个总量；把总量长度的平方减去各部分长度平方之和，就得到所有交叉重叠的两倍。把两层这些差相加成一个非负缺陷，它为零时，每一处重叠都只能为零；行和、列和以及方向之间的组合再把这条规则传遍整个空间，包括纠缠方向。随后仍由原混态的边缘盖不住联合块、而整个原插入输出为正，排除错误相对方向。近似零还要多看一件事：第三套方向可能越来越贴近实矩阵平面，每次仍伸出一点虚方向，却必须除以越来越小的数才能把它还原。于是眼前的重叠越来越小，没直接看见的方向仍可保留固定错误。已经给出的界明确支付两层还原系数和权重范围，才把局部小误差传到全域；更弱的完整接口有界条件则保证全域误差趋零，但尚未给显式速率。这样，精确候选是一条长度饱和关系，近似理论则解释这条关系何时稳定，而不是把一个小数字直接叫作完整量子力学。

**数学来源与归属。** [B] [本卷第 77 章，固定文本 dec49aff](https://github.com/the-omega-institute/trureturing/blob/dec49aff60d5ad95634ef463c1de05c3ce7b4ec6/docs/develop/theory/QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md)：77.16、77.18—77.19 的回路平衡及混合余项二元律与完整 $S$ 的同载体等价；此处直接复用该入口，不将旧结果算作本章新推导。
[V] [本卷第 73—76 章，固定文本 3ace5269](https://github.com/the-omega-institute/trureturing/blob/3ace5269ce69f0a5f162a19af3a643ddd6329da2/docs/develop/theory/QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md)：完整原基底、一般 EJA 平方与 Peirce 工具、生成闭包、同标提升、原完整转置平均反模型及消费者。本章在这些既有结果上给两层显式误差传播和真生成族退化的完整原接口反例；不将范数展开、有限字典逆解或紧性方法作为工具原创。
[R] [第四卷第 65—72 章，同固定文本](https://github.com/the-omega-institute/trureturing/blob/3ace5269ce69f0a5f162a19af3a643ddd6329da2/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_IV.md)：65.3 第一接口的精确范围、66 的分类、69 的过程合同、72.7—72.8 的原方向检测，均按其原前提使用。
[S] [Library 完整比较桥与无序可区分纯对传递性附录，同固定文本](https://github.com/the-omega-institute/trureturing/blob/3ace5269ce69f0a5f162a19af3a643ddd6329da2/Library/QuantumStates/mullerududec2012selfduality.md)：保留其一般 EJA 条件桥与最小确认效应的独立前件，不以自对偶性独自替代完整 $S$ 或组合。
[D] E. Størmer，[Multiplicative properties of positive maps，math/0607090v1，§1](https://arxiv.org/abs/math/0607090v1)：正映射平方缺陷、标量态 Cauchy–Schwarz 及 definite-domain 思路；其 C*/JC 范围不自动含 Albert，故 (78.9)—(78.15) 使用一般有限 EJA 的直接谱、二次表示和 Peirce 证明。[C] J. van de Wetering，[Commutativity in Jordan Operator Algebras，1912.01903v1，§§2—3](https://arxiv.org/abs/1912.01903v1)：二次表示、算子交换及 Jordan 结构工具；本章未从文献中的全域近似同态稳定性直接移植任何指数。所有新增结论为给定前提下的纸面数学，不宣称形式核验、全球原创、最少公理或物理可得性。

## 追加锚（本行以下为增补区）

## 79. 一个局部固定泛函与两条原质量关系的前方向校准

本章第 65—72 章指第四卷，第 73—78 章指本卷。只替换归一化入口：在完整 PRE 上、尚未施加 NB 或 H13 之前，一份局部正保归一化映射与两条原实际质量恒等式恰好消去全部非标量权重；同一个原读回用两次进一步固定双份尺度。三份绝对尺度仍由原标量锚固定，接合相对方向仍单独由内在 NB/H13 选择。正映射谱论与张量和是成熟工具，本章的内容是它们接到同一原实际数据的精确接口及其反模型，不主张一般谱论、优先权或全球新意。

### 79.1 完整原域与不预选坐标的质量关系

**定义 79.1（保留的 PRE）。** PRE 完全取第四卷定义 71.1：每个 $X=A,D,E$ 为非零有限维实空间，具有闭尖生成锥 $C_X$、非零正元上严格正的归一化泛函 $u_X$、整个紧态基 $K_X=\{x\in C_X:u_X(x)=1\}$、全部效应 $[0,u_X]$ 及其纯态集。比较只以纯态为第一端点，且完整保留
$$
T^X_\xi(x)=\inf\{f(x):0\le f\le u_X,\ f(\xi)=1\},\qquad
T^X_\xi\!\left(\sum_rv_r\eta_r\right)=\sum_rv_rT^X_{\eta_r}(\xi). \tag{79.1}
$$
量词遍及每个纯参照、每个有限纯态族及每组概率权重。一般 EJA 的忠实规范迹、正对偶生成、共同框架、面投影、项目性与滤波纯性沿 75.1 所引完整条件纸面桥保留；不将自对偶性或纯端点互反单独冒充这条桥。在忠实坐标中 $u_X=\tau_X$，整个原态基与效应区间均保留。
唯一供应的接合和读回仍是整个原锥上正的实双线性 $L:D\times A\to E$、实线性 $p:E\to D$，原参考为 $\omega=1_D/\tau_D1_D$。全部内部量仍由同一个实际 $p$ 定义：
$$
\begin{aligned}
K(a)&=pL(\omega,a),&M(a,b)&=pL(K(a),b),&Q(a,b,c)&=L(M(a,b),c),\\
J(a)&=M(a,1_A),&H(d)&=L(d,1_A),&B_1&=pH.
\end{aligned} \tag{79.2}
$$
保留 $\operatorname{span}_{\mathbb R}M(A,A)=D$、$\operatorname{span}_{\mathbb R}L(D,A)=E$，全部正交正元对上的 $D_J,D_H$ 及全实 $Z:B_1M(a,b)=u_A(a)Jb$。特别地，$D_H$ 与 $L,p$ 的正性覆盖整个实际联合锥，包括纠缠方向；实张成不表示正乘积生成整个正锥。没有预设 $p$ TP、$M$ 归一化、$C_{\rm joint}$、C13、NB、H13 或重置补全。

**定义 79.2（局部见证与两条质量关系）。** 给一份实线性映射 $\Phi:A\to A$，要求
$$
\Phi(C_A)\subseteq C_A,\qquad u_A\Phi=u_A,\qquad
\{f\in A^*:f\Phi=f\}=\mathbb R u_A. \tag{79.3}
$$
最后一式遍及全部实线性泛函，不是有限检测表、仅已执行效应或逐扇区分别固定的条件。在复矩阵忠实坐标中它才写成 $\operatorname{Fix}(\Phi^*)=\mathbb R1_A$。不要求 CP、混合、忠实稳态、重置份额或实际程序供应。
固定 $0<t<1$、$0<s<1$。对原实际质量
$$
m_2(a,b)=u_D M(a,b),\qquad m_3(a,b,c)=u_EQ(a,b,c) \tag{79.4}
$$
只要求
$$
\begin{aligned}
\mathsf M_2:\quad m_2(a,b)
 &=t\,m_2(\Phi a,b)+(1-t)m_2(a,\Phi b),\\
\mathsf M_3:\quad m_3(a,b,c)
 &=st\,m_3(\Phi a,b,c)+s(1-t)m_3(a,\Phi b,c)
 +(1-s)m_3(a,b,\Phi c).
\end{aligned} \tag{79.5}
$$
量词遍及所有原正 $a,b,c$，包括零与不等质量。以下记 $\mathsf{Mass}_{t,s}$ 为存在满足 (79.3)—(79.5) 的数学见证 $\Phi$。

**量词说明。** (79.5) 是双线性、三线性恒等式。每个非零正元是其原质量乘一个 $K_A$ 中的态，零元的每项均为零，故在全部归一态上要求它们与上述全正量词等价。正锥生成整个实空间，再逐槽作正负分解，等式即扩展到全部实输入。这是恒等式的线性延拓，不把数学纯分解当成实际准备彩票，也不只抽样测试若干归一态。
(79.5) 没有新联合映射的正性前提，不假定各加项是独立可调用的操作，更没有供应随机选择装置。$\Phi$ 可以只是一份数学映射。原 $L,p$ 的全锥正性与全部既有来源义务一项不删。

### 79.2 先于 Jordan 分类的有序谱工具

**引理 79.3（幂有界与正权张量和）。** 在有限维非零 proper-cone 系统 $(A,C_A,u_A)$ 上，设 $\Phi$ 满足 (79.3)。则 $\Phi$ 的复谱位于闭单位圆盘，每个外围特征值半单，特征值一的代数重数为一。对任意有限 $r\ge1$ 及 $\alpha_\ell>0$、$\sum_\ell\alpha_\ell=1$，在纯代数实张量空间上定义
$$
\mathcal K_r=\sum_{\ell=1}^r\alpha_\ell\Phi_\ell,\qquad
\Phi_\ell=\operatorname{id}^{\otimes(\ell-1)}\otimes\Phi\otimes
\operatorname{id}^{\otimes(r-\ell)}.
$$
则特征值一在 $\mathcal K_r$ 上仍代数单纯，且
$$
\operatorname{Fix}(\mathcal K_r^*)=\mathbb R u_A^{\otimes r}. \tag{79.6}
$$
不需要给这个张量空间选择正锥，亦不要求任何实际 $r$ 份系统存在。

**证明。** $u_A$ 是对偶锥的内点，因而是 $A^*$ 的序单位。令 $S=\Phi^*$，则 $S$ 正且 $Su_A=u_A$。若 $-cu_A\le f\le cu_A$，保序性对每个整数 $N\ge0$ 给
$$
-cu_A\le S^Nf\le cu_A,\qquad
\|S^Nf\|_{u_A}\le\|f\|_{u_A},\qquad
\|f\|_{u_A}=\inf\{c\ge0:-cu_A\le f\le cu_A\}. \tag{79.7}
$$
对复化的实部、虚部分别使用此界，有限维范数等价使复化幂也一致有界。因此任何特征值 $\lambda$ 满足 $|\lambda|\le1$；若 $|\lambda|=1$ 有非平凡 Jordan 块，其 $N$ 次幂含 $N\lambda^{N-1}$ 及更高多项式项，与幂有界矛盾。故外围半单。实固定空间为 $\mathbb Ru_A$，复固定空间为 $\mathbb Cu_A$，一的几何、代数重数都恰为一；转置不改变这些重数，结论对 $\Phi$ 亦成立。
在同一复基中将 $S$ 上三角化，对每个张量因子用这一基。按字典序排列张量基，$\mathcal K_r^*$ 上三角，其对角元按代数重数恰为
$$
\sum_\ell\alpha_\ell\lambda_{j_\ell}.
$$
若该和等于一，则
$$
1=\sum_\ell\alpha_\ell\operatorname{Re}\lambda_{j_\ell}\le\sum_\ell\alpha_\ell=1.
$$
严格正的每个系数迫使每个实部为一；单位圆盘中这只可能是 $\lambda_{j_\ell}=1$。一在 $S$ 的对角表中只出现一次，故该张量对角位置也只出现一次。$u_A^{\otimes r}$ 已是非零固定向量，遂给 (79.6)，再取实部。该论证没有假定 $\Phi$ 可对角化或正规，也没有假定稳态在锥内点。证毕。

这只是成熟有序收缩与 Kronecker 和谱论的有限维应用。Yoshida–Hayashi [Y] Lemma A.2 给相应 $(K,u)$ 范数收缩，Lemma A.3 给外围半单；Proposition 5.16 将其 dynamical map 的遍历性等价于固定空间一维。$\Phi-I$ 与其转置的零空间维数相同，所以 (79.3) 正是这里所用的一维固定条件。该文 Theorem 5.20 在 $K$-正且谱半径正的线性映射范围给“混合”等价于同步张量平方遍历；此处谱半径为一。它解释同步的额外要求，不把同步张量平方在某个实际纠缠锥上的正性作为本引理事实。

**推论 79.4（两张实际质量张量）。** 在定义 79.1—79.2 下，先于任何 Jordan 或复矩阵分类，有常数 $\lambda,\kappa>0$，使全部实输入满足
$$
m_2(a,b)=\lambda u_A(a)u_A(b),\qquad
m_3(a,b,c)=\kappa u_A(a)u_A(b)u_A(c). \tag{79.8}
$$
**证明。** 将两个实际多线性质量分别视为 $A^{\otimes2}$、$A^{\otimes3}$ 上的线性泛函。(79.5) 正是对 $\mathcal K_2$、$\mathcal K_3$ 不变，其中权重分别为 $(t,1-t)$、$(st,s(1-t),1-s)$。引理 79.3 给 (79.8)。正性给两常数非负。$M$ 的实张成排除 $m_2$ 恒零；由 $M$ 张满 $D$ 及 $L(D,A)$ 张满 $E$，$Q(A,A,A)$ 也张满 $E$，排除 $m_3$ 恒零。严格正归一化泛函非零，故两常数都严格正。证毕。

“没有新增固定质量张量”不等于迭代混合。若经典翻转 $\Phi$ 的零质量方向 $v$ 满足 $\Phi v=-v$，则 $v^{\otimes r}$ 在 $\mathcal K_r$ 上仍有特征值 $-1$。因此这里不声称异步迭代收敛、所有相关消失、衰减率或任何物理连续时间动力学。

### 79.3 同一个 p 两次直接固定第一尺度

**定理 79.5（原参考处的尺度刚性）。** 在完整 PRE 上，(79.3)—(79.5) 迫使 $\lambda=1$，并有全部实 $d,c,z$ 上的关系
$$
u_Dp=\kappa^{-1}u_E,\qquad
u_EL(d,c)=\kappa u_D(d)u_A(c),\qquad
u_DpL(d,c)=u_D(d)u_A(c). \tag{79.9}
$$
这里公式中的 $u_D,u_E$ 是原归一化泛函，没有改变参考、迹或实际映射。

**证明。** 复用第四卷 65.6、66.2、71.2 的前交叉全实恢复律，即 (73.23)；它不需要 NB/C13：
$$
pQ(a,b,c)=u_A(a)M(b,c). \tag{79.10}
$$
对它取原质量，并代入 (79.8)，得到
$$
u_DpQ(a,b,c)=\lambda u_A(a)u_A(b)u_A(c)
 =\frac\lambda\kappa u_EQ(a,b,c).
$$
$Q$ 张满整个 $E$，故 $u_Dp=(\lambda/\kappa)u_E$。另一方面，对于 $d=M(a,b)$，(79.8) 给
$$
u_EL(d,c)=\frac\kappa\lambda u_D(d)u_A(c).
$$
$M$ 张满整个 $D$，遂对全部 $d,c$ 成立。组合两式即得 $u_DpL(d,c)=u_D(d)u_A(c)$。现在回到原 $\omega$，而不是另选一个参考：
$$
\begin{aligned}
u_DM(a,b)
 &=u_DpL(pL(\omega,a),b)\\
 &=u_DpL(\omega,a)u_A(b)
 =u_D(\omega)u_A(a)u_A(b)=u_A(a)u_A(b).
\end{aligned} \tag{79.11}
$$
两次调用都为 (79.2) 的同一个实际 $p$，且原 $u_D(\omega)=1$。与 (79.8) 比较，取任意两个归一态便得 $\lambda=1$，继而得到 (79.9)。这里没有借逆迹平衡重标原模型，也没有使用密度相同就历史相同。证毕。

### 79.4 质量先校准全部权重，方向仍单独检测

**定理 79.6（PRE 上的精确质量分类）。** 固定任意 $t,s\in(0,1)$。在同一完整 PRE 元组上，$\mathsf{Mass}_{t,s}$ 恰好等价于第四卷前 C13 正规形中的
$$
u_{ij}=I_j,\qquad g_{ijk}=\kappa I_k\quad\text{对全部有序 }i,j,k,\quad\kappa>0. \tag{79.12}
$$
式中的 $u_{ij}$ 为矩阵滤子，与归一化泛函 $u_X$ 区分。所有允许的有序转置位及其原读回正性限制仍然保留。结论不预设共同普通方向。

**证明。** 在质量推导 (79.8)—(79.11) 完成后，才用既有第四卷 66.3—66.7 的前 C13 分类。保原迹、全态、全效应的坐标给
$$
\begin{aligned}
M(a,b)_{ij}&=a_i\otimes\sqrt{u_{ij}}b_j^{T^{\varepsilon_{ij}}}\sqrt{u_{ij}},\\
L(d,c)_{ijk}&=d_{ij}\otimes\sqrt{g_{ijk}}c_k^{T^{\delta_{ijk}}}\sqrt{g_{ijk}},
\end{aligned} \tag{79.13}
$$
$u_{ij},g_{ijk}>0$，位 $\varepsilon_{ij},\delta_{ijk}$ 完整满足 (66.20)，逆迹平衡仍为 (66.14)。选择只支撑在指定 $i,j$ 的正输入，(79.11) 给
$$
\operatorname{Tr}(u_{ij}b_j^{T^{\varepsilon_{ij}}})=\operatorname{Tr}b_j\quad(b_j\ge0).
$$
PSD 锥张满 Hermitian 空间，迹配对非退化，故 $u_{ij}^{T^{\varepsilon_{ij}}}=I_j$，即 $u_{ij}=I_j$。再选择只支撑在 $i,j,k$ 的输入，$m_3$ 的乘积式给 $g_{ijk}^{T^{\delta_{ijk}}}=\kappa I_k$，故 $g_{ijk}=\kappa I_k$。独立块支撑只是全量词证明中的数学取值，不供应物理选块或制备。
逆向，在 (79.12) 下，任意允许的转置保持迹，直接给 $m_2=u_A^{\otimes2}$、$m_3=\kappa u_A^{\otimes3}$。因而任何正保归一化 $\Phi$ 都满足两质量恒等式。为满足全部泛函的固定条件，选任一数学态 $\sigma\in K_A$，令
$$
\Phi(a)=u_A(a)\sigma. \tag{79.14}
$$
它正保归一化，且 $f\Phi=f$ 当且仅当 $f=f(\sigma)u_A$。$\sigma$ 可在边界、可秩亏、可只在一个扇区；不需忠实稳态。该构造只给数学存在见证，不推出原源已供应这个重置程序。证毕。

**推论 79.7（原锚、原校准与方向的分工）。** 保留定义 73.10 的原标量锚，令 $n=\tau_A1_A$：
$$
\mathrm A_0:\quad u_EL(\omega,1_A/n)=1. \tag{79.15}
$$
则在完整 PRE 上、无须 NB/C13，
$$
\mathsf{Mass}_{t,s}+\mathrm A_0\quad\Longleftrightarrow\quad C_{\rm joint}. \tag{79.16}
$$
在再加入内在 NB 或 H13 之后，才允许同一原数据的同时普通方向，并得到原 $M,L,p$ 全部标准归一化。

**证明。** (79.9) 使锚左边恰为 $\kappa$，故 $\kappa=1$。在前方向正规形中，转置保迹及唯一原 $p$ 公式 (66.17) 给
$$
\delta=u_EL(1_D,1_A)=\kappa n^3,\qquad
\gamma=u_D(p1_E)=n^3/\kappa.
$$
所以 (79.12) 中 $C_{\rm joint}:\delta+\gamma\le2n^3$ 当且仅当 $\kappa=1$。反向先用第四卷定理 67.7：完整 PRE 的 $\mathcal B+D_H$ 与 $C_{\rm joint}$ 给 $U=1_D,H1_D=1_E$、原 $p$ TP，故 (79.13) 中 $u=g=I$，再由定理 79.6 得数学见证。这个反向同样不使用 C13。
随后 NB 沿 71.6、71.8a，或 H13 沿 72.7—72.8，才给原 C13；66.10 消除允许的相对转置位。原 $p$ 再由全实恢复律和 $Q$ 张成唯一给出
$$
\begin{aligned}
M(a,b)_{ij}&=a_i\otimes b_j,&L(d,c)_{ijk}&=d_{ij}\otimes c_k,\\
(pz)_{jk}&=\sum_i\operatorname{Tr}_i z_{ijk},&
(p_{13}z)_{ik}&=\sum_j\operatorname{Tr}_jz_{ijk},\quad p_{13}=(I^{\rm raw})^*.
\end{aligned} \tag{79.17}
$$
$(79.17)$ 是指定原二份、三份的结论，不识别独立另一括号或四份以上载体。证毕。

余尺度与锚的必要性是 73.8—73.11 已有结果。变换 $L\mapsto cL,p\mapsto c^{-1}p$ 保持 $pL$、两次同 $p$ 的 $M$，并把 $m_3$ 整体乘 $c$；齐次质量关系不能读出这个尺度。这里复用该障碍，不将它作为新发现。
同样，方向不能由质量替代：73.14 的实际 $A=H_2,D=H_4,E=H_8$、$L(d,c)=d\otimes c$、$p(z)=(\operatorname{Tr}_1z)^T$ 给 $M(a,b)=a\otimes b^T$。全部 PRE、质量关系和 $\mathrm A_0$ 成立，但原插入是单腿部分转置后插中间单位，Bell 投影有反对称负值 $-1/2$，故 C13/NB 失败。标量迹看不见这个离散错误。

### 79.5 更强的正平均过程解释与指定映射的严格边界

**推论 79.8（更强过程接口）。** 若另外有原整个联合锥上的正保原质量实线性 $P_D,P_E$，满足全部实输入的
$$
\begin{aligned}
P_DM(a,b)&=tM(\Phi a,b)+(1-t)M(a,\Phi b),\\
P_EL(d,c)&=sL(P_Dd,c)+(1-s)L(d,\Phi c),
\end{aligned} \tag{79.18}
$$
则它们蕴含 (79.5)，故适用定理 79.5—79.7。正性没有参与这个校准方向；取原质量及将第一式代入第二式就给两恒等式。实张成与既有 $\widetilde M,\widetilde Q$ 的可逆性使这些线性延拓若存在即唯一，不能另配不相干的联合映射。
在 PRE+NB 的 (79.12) 残尺度类中，数学存在性反向也成立：在共同普通方向选 (79.14)，用通常一腿迹重置的正 TP 扩张，构造 $\mathcal K_2,\mathcal K_3$，第二层整体正尺度 $\kappa$ 在共轭中抵消，故取得 (79.18)。这些数学映射在整个原锥上正，包括纠缠输入；未生成新的物理菜单或随机控制。对一份已经指定的 $\Phi$，质量关系本身没有这个正性反向。

**命题 79.9（指定局部映射的质量不认证联合合法性）。** 在已归一化的普通 qubit 元组上，令 $\Theta(X)=X^T$、$R(X)=\operatorname{Tr}(X)I_2/2$，并取
$$
\Phi_\epsilon=(1-\epsilon)\Theta+\epsilon R,\qquad0<\epsilon<2/3. \tag{79.19}
$$
它正保迹且固定效应只有标量，满足全部质量关系，却对每个 $t\in(0,1)$ 都没有正的第一层延拓。

**证明。** 转置与 $R$ 均正保迹且迹自伴。$\Phi_\epsilon$ 在 $I,X,Y,Z$ 的特征值依次为 $1,1-\epsilon,-(1-\epsilon),1-\epsilon$，故固定 Hermitian 效应恰为 $\mathbb RI$。归一化元组的两质量已为乘积迹，所以 (79.5) 对这份 $\Phi_\epsilon$ 全部成立。
令 $\Omega_2=|\Omega_2\rangle\langle\Omega_2|$、$|\Omega_2\rangle=(|00\rangle+|11\rangle)/\sqrt2$。任一腿的部分转置都将它送到 $F_{\rm swap}/2$，任一腿的 $R$ 都送到 $I_4/4$。因而唯一由第一层实乘积律确定的 $\mathcal K_2$ 满足
$$
\mathcal K_2(\Omega_2)=(1-\epsilon)F_{\rm swap}/2+\epsilon I_4/4,
\qquad
\langle\psi_-|\mathcal K_2(\Omega_2)|\psi_-\rangle=(3\epsilon-2)/4<0. \tag{79.20}
$$
两腿结果相同，故与 $t$ 无关。$\Omega_2$ 是原完整数学联合正锥中的方向，负值直接排除全锥正延拓；这不宣称供应其物理制备。它是过程解释的反模型，不反驳质量校准定理，更没有把任意正 TP 升级为 CP。证毕。

### 79.6 同一个 p 的经典实际族与同步的精确余参量

**引理 79.10（用于控制的完整实际族）。** 取 $h\ge2$，$A=\mathbb R^h,D=\mathbb R^{h^2},E=\mathbb R^{h^3}$，各取完整逐坐标正锥、求和质量、全态全效应。给正数 $u_{ij},g_{ijk}$，仅要求 $\sum_{i,j}u_{ij}^{-1}=h^2$。只供应
$$
\omega_{ij}=h^{-2},\qquad L(d,c)_{ijk}=g_{ijk}d_{ij}c_k,\qquad
(pz)_{jk}=u_{jk}\sum_i\frac{z_{ijk}}{u_{ij}g_{ijk}}. \tag{79.21}
$$
则得到完整 PRE+C13 的同一实际元组，且
$$
\begin{aligned}
(pL(d,c))_{jk}&=u_{jk}\left(\sum_i d_{ij}/u_{ij}\right)c_k,\\
w_j&=h^{-2}\sum_i u_{ij}^{-1},&K(a)_{jk}&=u_{jk}w_ja_k,\\
M(a,b)_{jk}&=u_{jk}a_jb_k,&Q(a,b,c)_{ijk}&=u_{ij}g_{ijk}a_ib_jc_k,\\
\mathrm A_0\text{ 左边}&=h^{-3}\sum_{i,j,k}g_{ijk}.
\end{aligned} \tag{79.22}
$$
**证明。** (79.21) 在整个正锥上正。直接计算第一式，$\sum_jw_j=1$，所以 $\sum_jK(a)_{jk}/u_{jk}=a_k$；将同一个 $pL$ 再用一次便给所示 $M$，没有独立供应它。乘积基与严格正权重给两张成；$J(a)_{ij}=u_{ij}a_i$、$H(d)_{ijk}=g_{ijk}d_{ij}$ 保持各自全部正交正元对。令 $(sd)_j=\sum_id_{ij}/u_{ij}$，则 $sM(a,b)=u_A(a)b$，故 $B_1M=u_A(a)Jb$，恢复律 $pQ=u_A(a)M(b,c)$ 亦直接成立。经典纯参照比较是相应坐标，完整 $S$ 成立。原插入作用为
$$
(I^{\rm raw}x)_{ijk}=\frac{u_{ij}g_{ijk}}{u_{ik}}x_{ik},
$$
故覆盖整个 $D_+$ 正，给 C13；这里没有两端非标量活跃块，NB/H13 的资格为整个态基。这也是第四卷 66.7 取全标量扇区、零方向位的特例；原 $p$ 的两次使用及全部控制的原属据此明确，不把例子称作整个 $\Omega$ 的反模型。证毕。

**定理 79.11（同步 h 周期的完整权重族）。** 在引理 79.10 中令 $u_{ij}=1$、指标取模 $h$，令 $(\Phi a)_i=a_{i-1}$。以同时更新替换 (79.5)，即要求
$$
m_2(a,b)=m_2(\Phi a,\Phi b),\qquad
m_3(a,b,c)=m_3(\Phi a,\Phi b,\Phi c). \tag{79.23}
$$
全部正权重解恰为
$$
g_{ijk}=a_{j-i,k-i},\qquad (a_{rq})\in\mathbb R_{>0}^{h^2}. \tag{79.24}
$$
原锚留下 $h^2-1$ 维正参数族，而非迫使常权重。

**证明。** $\Phi$ 是正 TP 周期置换，其固定泛函恰为求和泛函的倍数。直接从 (79.21)，
$$
(pL(d,c))_{jk}=\left(\sum_i d_{ij}\right)c_k,\qquad
K(a)_{jk}=a_k/h,\qquad M(a,b)_{jk}=a_jb_k. \tag{79.25}
$$
这些公式对任意正 $g$ 都成立；同一个 $p$ 两次的抵消不可略去。双质量已标准。三质量的同步恒等式由乘积基系数比较恰等价于 $g_{i+1,j+1,k+1}=g_{ijk}$。同时平移的每个轨道恰由 $(j-i,k-i)$ 标记，故 (79.24) 给全部而不只是若干解。每轨道有 $h$ 点，锚为
$$
h^{-3}\sum_{i,j,k}g_{ijk}=h^{-2}\sum_{r,q}a_{rq}=1. \tag{79.26}
$$
这是正参数域中的一个非退化仿射约束，维数恰为 $h^2-1$。
若要求更强同步过程解释，可直接取 $S_D,S_E$ 为分别同时平移两个、三个指标的置换；(79.24) 使它们满足 $S_DM(a,b)=M(\Phi a,\Phi b)$、$S_EL(d,c)=L(S_Dd,\Phi c)$，在整个原联合正锥上正 TP。没有从同步质量自动推断一般量子联合正性。
$h=2$ 时取 $g_{ijk}=1+\varepsilon(-1)^{j-i}$、$0<\varepsilon<1$，锚成立且非恒定。对基输入，异步三质量右边的相关项为 $(1-2s)\varepsilon(-1)^{j-i}$，左边为 $\varepsilon(-1)^{j-i}$；故在 $s>0$ 时明确失败。同步却始终保留该相对位置。证毕。

此周期 $\Phi$ 的任何正整数次幂均无正重置下界：若 $\Phi^N-cR_\sigma$ 正、$c>0$，对每个基态 $e_i$ 的正性迫使 $\sigma$ 支撑在 $\Phi^Ne_i$ 的单点上。不同 $i$ 的这些单点不交，故不存在迹一 $\sigma$。因此质量候选允许不具任意幂重置份额的局部见证；这是对指定见证的范围说明，存在性模型类仍与 (79.12) 相同，不是独立公理或物理资源的最小性结论。

### 79.7 删除与端点控制均保留同一原元组

以下均用引理 79.10 的全态、全效应、原 $\omega,L,p$ 与同一 $p$ 两次定义，不是只指定一张质量表。取 $h=2$、$\alpha=(2,2/3)$、$\beta=(1/2,3/2)$，$R(a)=u_A(a)(1/2,1/2)$。$R$ 满足 (79.3)，且 $\alpha_0^{-1}+\alpha_1^{-1}=2$、$\beta_0+\beta_1=2$。

**命题 79.12（单项删除）。**

| 删除项 | 同一实际参数 | 保留与失败 |
| --- | --- | --- |
| 只删 $\mathsf M_2$ | $u_{ij}=\alpha_i,g_{ijk}=1/\alpha_i,\Phi=R$ | $m_3=u_A^{\otimes3}$，$\mathrm A_0=1$，故 $\mathsf M_3$ 成立；$m_2=(\alpha\cdot a)u_A(b)$ 不标准。 |
| 只删 $\mathsf M_3$ | $u=1,g_{ijk}=\beta_k,\Phi=R$ | $m_2=u_A^{\otimes2}$，$\mathrm A_0=1$；$m_3=u_A(a)u_A(b)(\beta\cdot c)$ 不标准。 |
| 只删全实固定泛函条件 | 第一行参数，$\Phi=\operatorname{id}$ | 正性、保归一化、两质量恒等式和锚全保留，但双质量不标准。 |
| 只删 $\mathrm A_0$ | $u=1,g=\kappa\ne1,\Phi=R$ | 两质量恒等式、固定条件全保留；三份绝对尺度仍为 $\kappa$。 |

**证明。** 第一行逆迹和为 $2(1/2+3/2)=4$，锚为 $(1/2+3/2)/2=1$；$u_{ij}g_{ijk}=1$。取 $a=e_0$、$u_A(b)=1$，$m_2=2$，更新第一槽的值为 $4/3$，所以 $t>0$ 时 $\mathsf M_2$ 确实失败。第二行逆迹和四，锚为 $(\beta_0+\beta_1)/2=1$；取三输入均归一且 $c=e_0$，左边 $1/2$，右边 $s/2+(1-s)$，故 $s<1$ 时 $\mathsf M_3$ 失败。第三行两式成为恒等式而固定泛函空间为二维。第四行直接为 73 的已获尺度族。各行未删除的全锥、张成、零关系、$Z$、C13/NB 均由引理保留。证毕。

**命题 79.13（严格内点系数的全类必要范围）。** 下列端点各允许非标准归一化，即使仍有 (79.3)、另一条质量律及 $\mathrm A_0$：

| 端点 | 参数 | 未更新而能留下的质量 |
| --- | --- | --- |
| $t=0$ | $u_{ij}=\alpha_i,g_{ijk}=1/\alpha_i$ | 第一槽权重：$m_2=(\alpha\cdot a)u_A(b)$；$m_3$ 已标准。 |
| $t=1$ | $u_{ij}=\alpha_j,g_{ijk}=1/\alpha_j$ | 第二槽权重：$m_2=u_A(a)(\alpha\cdot b)$；$m_3$ 已标准。 |
| $s=0$ | $u=1,g_{ijk}=\beta_i$ | 前两槽未被三质量律更新；$m_3=(\beta\cdot a)u_A(b)u_A(c)$。 |
| $s=1$ | $u=1,g_{ijk}=\beta_k$ | 最后槽未被三质量律更新；$m_3=u_A(a)u_A(b)(\beta\cdot c)$。 |

**证明。** 每行取 $\Phi=R$。前两行逆迹和四，$g$ 的均值一，$Q$ 无权重；$t=0$ 只更新第二槽，$t=1$ 只更新第一槽，故两式均成立。后两行逆迹和四且 $g$ 均值一；$s=0$ 只更新第三槽，$s=1$ 只更新前两槽，所以所示非恒定权重均不被关系触及。$m_2$ 标准，另一质量律保留。引理给完整实际实现。它们说明开区间在整个模型类中的作用，不宣称一维或其他退化子类的每个端点都必须失败。证毕。

### 79.8 完整候选、原量子消费者与来源条件

**定义 79.14（同一原模型上的完整候选）。** 逐项保留定义 79.1 的全原域。比较入口可取原完整 $S$，或第 77 章每个纯参照上的全部回路平衡，或允许任意混合余项的二元律；后两者先由 77.16、77.18—77.19 恢复同一全态全效应载体上的完整 $S$，再用既有一般 EJA 桥。不能用固定纯元数比较替代它。
两层零关系可直接取完整 $D_J,D_H$，也可精确使用 75.4、76.3 的同标生成框架等价：在一般 EJA 中取 $1\le q\le3$ 套完整本原框架 $\mathfrak B=(B_r)_{r=1}^q$，其全体成员 Jordan 生成整个 $A$（$\mathsf{JG}_3$）。令 $U=M(1,1)$、$F=P_{U^{-1/2}}M$，要求每个 $r$ 的不同 $e,e^\prime\in B_r$ 满足 $Je\perp Je^\prime$，每个不同 $(e,f),(e^\prime,f^\prime)\in B_r\times B_r$ 满足 $HF(e,f)\perp HF(e^\prime,f^\prime)$；或依 78.4 把两表写为同一个非负缺陷 $\delta(\mathfrak B)=0$。先恢复全部 $D_J$，再经原两边缘和实张成恢复整个 $D$ 的生成性及 $D_H$，不把有限产品表当成只需测试可分离锥。所有版本仍保留原 $L,p$ 的全锥正性、两实张成、原参考与全实 $Z$。
归一化入口取一个 (79.3) 的局部见证、两条 (79.5) 与原 $\mathrm A_0$。方向入口另取内在 NB 或 H13：令 $U=M(1,1)$、$F=P_{U^{-1/2}}M$，按 71.4—71.8a 的原 $F$ 内在中心块定义 NB，要求存在同一个合格原总迹一态，其原 $I^{\rm raw}=\widetilde T_{\rm raw}\widetilde M^{-1}$ 输出正，其中 $T_{\rm raw}(a,c)=L(Ja,c)$。每个两端秩至少二的活跃块须严格正质量、条件联合纯而内在边缘混；非活跃块任意正分量含零，无活跃块则为整个态基。
也可取 72.7—72.8、76.2 的 H13：对每个活跃块 $x=\pi_{ik}\rho$，至少一项 $\alpha_{ik}\alpha_{ik}^*x-x$ 或 $\beta_{ik}\beta_{ik}^*x-x$ 有严格负方向；$\alpha_{ik}=F(-,c_k)|_{A_i}$、$\beta_{ik}=F(c_i,-)|_{A_k}$，伴随取原规范迹，边缘铺回用未经维数归一化的单位。再要求该同一原混态的整个原插入输出正。非活跃及空活跃边界同前，不要求纯性、固定 Schmidt 谱或逐块条件化；不得运输到另一个态或以输出反选资格。

**定理 79.15（完整候选的同数据等价）。** 遗忘数学见证后，定义 79.14 与原 PRE+NB+$C_{\rm joint}$，以及定义 73.15、77.20 的归一化候选，具有完全相同的实际 $(A,D,E,C_X,u_X,L,p)$ 模型类。
**证明。** 77 的入口先恢复完整 $S$；75—76 或精确 78.4 先恢复全部 PRE。质量定理 79.5—79.7 在该同一元组上、先于方向给且仅给 $C_{\rm joint}$。NB/H13 再按其既有原态逐成员定理给 C13；共同普通方向及唯一 $p$ 由 66.10 和 (79.10) 得到。反向原校准直接给 (79.12) 的 $\kappa=1$，(79.14) 构造一个数学见证；既有同载体入口及框架等价给所选其余版本。原 $L,p,\omega$ 和全部态效应没有被替换。73.11、73.16、77.21 给与旧候选的最后等价。证毕。

有限 Born、完整密度与完整效应域已经由完整比较桥及 66.3、66.8 取得；本章只更换原归一化接口。准确结论仍为有限复 Hermitian 直和及指定的二份、三份有序块：
$$
\begin{gathered}
A=\bigoplus_iH_{n_i}(\mathbb C),\qquad D=\bigoplus_{i,j}H_{n_in_j}(\mathbb C),\qquad E=\bigoplus_{i,j,k}H_{n_in_jn_k}(\mathbb C),\quad n_i\ge1,\\
\rho_i\ge0,\quad\sum_i\operatorname{Tr}\rho_i=1,\quad0\le f_i\le I_i,\qquad\Pr(f\mid\rho)=\sum_i\operatorname{Tr}(f_i\rho_i).
\end{gathered} \tag{79.27}
$$
单份纯态几何为 $\bigsqcup_i\mathbb{CP}^{n_i-1}$，同块纯比较为模方 Born，异块为零。
以及 (79.17) 的原张量与偏迹。标量扇区、不等维、零及不等中心质量、全相关和纠缠输入都保留；辅助谱证明中的任意 $r$ 不供应更高份、另一括号或其共同来源相容性。

其他实际事件的消费者仍逐个遵守 69.1—69.11、73.9、77.11 的原条件。对每个输入块 $H_{n_i}$，须先有同一实际事件、分支和记录的原乘积延拓律，以及一个至少 $n_i$ 维的实际参考块上的整个联合锥正性，才能用 Choi 判据得到逐输入输出块 CP 与矩形 Kraus。数学 Bell 元或存在一个正平均都不供应这个事件／参考，也不使平均的各项分别合法。
对固定旁观者 CP 族的未校准模型，仍须完整保留原两预算
$$
\sum_{a,j}F^a_{ji}\le I_i,\qquad
\sum_{a,j}F^a_{ji}\otimes u_{jk}\le I_i\otimes u_{ik},\qquad
F^a_{ji}=\sum_\ell K_{a,ji,\ell}^\dagger K_{a,ji,\ell}, \tag{79.28}
$$
以及同一完整实际菜单两边总 TP；共同重置的输入行一致条件仍属 69.8 的准确范围。归一化后 $u=I$ 时，这两预算相合，完整仪器给 $\sum_{a,j,\ell}K_{a,ji,\ell}^\dagger K_{a,ji,\ell}=I_i$。结果概率为原未归一输出总迹，只有严格正质量才可除以它定义条件态；零分支的标签、记录与后续权限照旧保留。顺序复合与真实粗粒化仍须同族合同。锐投影 $P$ 的 Lüders 结论另需同一个实际 CP 分支效应恰为 $P$，并对每个确定接受的归一态逐点不变；效应、重复性或 CP 本身不唯一指定更新。
Hamiltonian 消费者另需以原物理时间为参数的连续、时间齐次、可逆 $*$ 自同构群。连续性固定离散中心，各有限复块才有 $\dot\rho_i=-i[H_i,\rho_i]/\hbar$，$H_i$ 有加标量自由度；原时钟、时间／能量单位与 $\hbar$ 的对应仍由实际动力学来源承担。静态质量关系没有供应这个群，也不覆盖一般不可逆过程。

### 79.9 完整普通解释、成熟来源与原目标边界

**普通中文图像。** 保留全部状态和全部测试，比较规则先固定状态与测试共用的几何；两层零关系再锁住单份、双份、三份之间的形状。但实际接合仍可能在不同标签和不同矩阵方向上偷偷加上不同倍率。现在只给一个局部变化：它可以周期转动，也可以把质量送到边界；要求的是，在全部实读数中，只有总质量能在它作用后完全不变。然后对同一原准备提出两条关系：双份总质量等于只改第一位置与只改第二位置后的正权平均；三份总质量也等于只改一个位置的三种结果的正权平均。这里是在约束三个原输入之间的读数，不是在宣称有一台能随机切换这些操作的装置。
为什么这样就能消掉倍率？每个局部变化的谱都在单位圆盘里，正权平均想恰好停在最右端的一，参与的每一项都只能自己是一。因此双份、三份不变的质量读数都只能是各输入总质量的乘积，再乘一个常数。原系统还有一个关键关系：第三份读回后恢复后两份，而且从原参考连续读回两次用的是同一个读回。把这条关系的质量与两条实张成接起来，两次计算同一个双份准备，第一常数被迫为一。三份常数仍可在接合时放大、读回时反向缩小，所以要靠原来的一次总迹锚读出它。到这一步只是所有倍率正确；有没有把某个位置的复方向翻错，还必须由原态的联合—边缘关系和整个原插入输出检查。
若三个位置一起转动，两个相对位置始终不变，倍率就能藏在“第二位置离第一位置多远、第三位置离第一位置多远”这两个差里。$h$ 周期恰留下 $h^2$ 个正倍率，固定平均也还有 $h^2-1$ 个自由度。逐次只改一个位置的质量关系排除了这些额外固定读数，却不保证周期消失或所有相关都被冲掉。另一边，质量全对也不等于过程合法：qubit 转置混一点均匀化虽然对全部总质量都合格，放到纠缠输入上仍会给负输出。故质量、方向、实际操作和来源必须各守其对应关系，不能把一张正确的标量表当成全部物理接口。

**成熟来源及增量范围。** [Y] Y. Yoshida、M. Hayashi，[*Asymptotic Properties for Markovian Dynamics in Quantum Theory and General Probabilistic Theories*，arXiv:1801.03988v3](https://arxiv.org/abs/1801.03988v3)，Lemma A.2（pp.30—31）的 proper-cone $(K,u)$ 范数收缩，Lemma A.3（pp.31—32）的 dynamical map 外围半单，Proposition 5.16（p.19，证明 p.20）的一维固定空间／遍历等价，Theorem 5.20（p.21）的 $K$-正映射混合／同步张量平方遍历等价。它们适用于这里的一般正归一化保持情形，不要求 CP 或内点稳态。正权和的三角化计算已在引理 79.3 给出，不将一个经典随机扫描或量子通道特例当作全部证明。
[B] D. Burgarth 等，[*Ergodic and Mixing Quantum Channels in Finite Dimensions*，arXiv:1210.5625v3](https://arxiv.org/abs/1210.5625v3)，属于 CPTP quantum-channel 范围；本章没有把该文结论归为任意正映射版本。
[R] [第四卷第 65—72 章](QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_IV.md)：前 C13 全态几何、66.14—66.18 的完整权重与有序方向、66.7 的同一 $p$ 两次逆向、全实恢复与张成、67.7 的原联合校准、71—72 的 NB/H13；[本卷第 73—78 章](QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md)的重置尺度障碍、完整比较入口、生成表与精确缺陷入口均按原范围复用。78 的显式稳定性及生成条件数障碍不是本章质量定理；本章没有从精确质量关系推出近似稳定性。一般 Kronecker 和工具不是原创；新增是两条原质量关系在方向之前的同数据校准、同 $p$ 直接固定第一尺度及其精确同步／删除／解释边界。

**已得原来源与尚未构造的接口。** [原观察卷 §§23—24](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ORIGINAL_INTERFACE_EXPOSURE_AND_RECOVERY.md)在其明示原 $G_V$ 进展域内保留实际获取的有序操作数、独立 guard、真实拒绝和完整绑定、原 Plan/Send 消费、真实下一 Entry、服务返回、历史批次、HandbackResume、Stop／验证／消费及共同 INITIAL 终端答案。[第二卷 §9](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ORIGINAL_INTERFACE_EXPOSURE_AND_RECOVERY_II.md#9-attribution-and-the-remaining-recovery-problem)另在新安装的两种模式中、每个有限已达的 completed canonical GuardAcquired 边界取得实际当前调用恢复，保留完整过去 capture/use 历史；不外推任意 Busy、部分 IN／loan／copy 切口、无新 boot 的既有 $G_V$、全终端任务核或无限重复的统一有限资源。已有下降、参考、递归支撑及原 $D$ 恢复同样各按其原域保留，不倒称缺失。
[固定来源卷 (23.7)](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md)所要求的原具名 analyzer 当前接受接口证书，及[有限返回卷定义 164.1](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md)的原 $B_r$ 到 active-ready 接头，仍未由本章构造。该卷 162 的七项消费者继续带全部递归原前件；数值表、静态密度、矩阵综合、操作逆字、数学见证或扩充源的候选返回均不能填入这两个实际原接头。
完整原 $\Omega$ 的全部准备、事件、过程、参考、副本、实际相关联合、零与不等质量、时钟、单位、控制、ready／flags、完整记录、失败、停止、销毁、返回与未来，以及全部旧全菜单、固定支撑和每个已量化中间切口义务，一项不缩减。没有免费准备生成、复制、相干控制或实际彩票。完整候选是给定全部原前件的同模型类纸面数学；不主张完整 $\Omega$ 起源已完成、最少独立公理、物理资源减少或形式内核认证。

## 追加锚（本行以下为增补区）

## 80. 全框架缺陷的内在上包络与共同原映射修复

本章第 65—72 章仍指第四卷，第 73—79 章指本卷。第 78 章证明，某个生成见证上的小缺陷不足以控制整个原接口：框架可接近真子代数，掩盖固定错误。本章把见证从外加数据中移除，以原几何所有完整框架上的最大缺陷定义一个标量；证明精确候选、第一接口的线性全域界，以及有界完整原接口类中对同一对原 $L,p$ 的条件修复。该包络保留全框架量词，不是一次实验或有限检测表。

### 80.1 原对象与一个内在最大值

**定义 80.1（完整原基底与全框架缺陷）。** $\mathrm{PRE}_0^{\rm mix}$ 完全取定义 78.1：每个 $X=A,D,E$ 非零有限维，使用整个紧态基、全部 proper 效应、纯态最小确认比较，及所有纯 $\xi,\eta$、所有原混态 $x$、$0\le t\le1$ 的混合余项二元律
$$
T^X_\xi(t\eta+(1-t)x)=tT^X_\eta(\xi)+(1-t)T^X_\xi(x).
$$
先按 77.19 恢复完整 $S$，再使用同一一般有限 EJA 条件桥，包括正对偶生成、忠实态效应对应、共同框架、面投影、项目性与滤波纯性。在其原规范迹坐标中，不预设复型、不可约性、结合性或三框架生成，允许直和、秩一和 Albert。
唯一供应的接合与读回仍为全锥正实双线性 $L:D\times A\to E$ 和同一个全锥正实线性 $p:E\to D$；原参考 $\omega=1_D/\tau_D1_D$。全部内部量按原式
$$
\begin{aligned}
K(a)&=pL(\omega,a),&M(a,b)&=pL(K(a),b),&J(a)&=M(a,1_A),\\
H_{\mathrm s}(d)&=L(d,1_A),&B_1&=pH_{\mathrm s},&U&=M(1_A,1_A),\quad G=H_{\mathrm s}1_D,\quad F=P_{U^{-1/2}}M.
\end{aligned} \tag{80.1}
$$
保留 $\operatorname{span}_{\mathbb R}M(A,A)=D$、$\operatorname{span}_{\mathbb R}L(D,A)=E$ 及全部实 $a,b$ 上的 $Z:B_1M(a,b)=\tau_A(a)Jb$。$L,p$ 的正性覆盖整个原锥和纠缠方向；同一个 $p$ 连续两次、原迹与原参考均不变。正性与两实张成先给 $U,G>0$，故零关系之前 $F$ 已正且 $F(1,1)=1_D$。
令 $\mathcal F(A)$ 为原 $A$ 的全部完整本原 Jordan 框架；每个框架有 $n=\operatorname{rank}A$ 个成员。框架标签只用于求和。对 $B\in\mathcal F(A)$ 定义
$$
\begin{aligned}
q_J(B)&=\|U\|_2^2-\sum_{e\in B}\|Je\|_2^2,\\
q_H(B)&=\|G\|_2^2-\sum_{e,f\in B}\|H_{\mathrm s}F(e,f)\|_2^2,\\
q(B)&=q_J(B)+q_H(B),\qquad
\boxed{\mathcal D(L,p)=\max_{B\in\mathcal F(A)}q(B).}
\end{aligned} \tag{80.2}
$$
这是 78.3 的单套同标方格缺陷在整个原框架几何上的上包络。既不指定外加框架，也不输入字典、生成系数或条件数；全框架量词本身没有被删除。

**定义 80.2（原方向条件）。** 只在 $\mathcal D=0$ 恢复 PRE 后，按定义 78.2／76.2 读取 H13：同一个原总迹一混态 $\rho$ 在每个两端秩至少二的活跃块上，至少一项原边缘铺回差有严格负方向；原规范迹伴随及未经维数归一化的单位不变。非活跃块任取正元含零，活跃集空时资格为整个原态基。以原 $\widetilde M$ 与 $T_{\rm raw}(a,c)=L(Ja,c)$ 定义 $I^{\rm raw}=\widetilde T_{\rm raw}\widetilde M^{-1}$，要求同一合格原 $\rho$ 的整个原输出 $I^{\rm raw}\rho$ 正。C13 仍为 $I^{\rm raw}(D_+)\subseteq E_+$；此分阶段定义不赋予正缺陷对象未经证明的块结构。

### 80.2 完整候选、内在性与第一接口的线性界

**定理 80.3。** (80.2) 的最大值达到且非负，在固定 EJA 三元组上对原 $L,p$ 连续。它在保持原迹的 Jordan 同构以及框架重标号下不变。在整个原基底中，
$$
\mathcal D=0\quad\Longleftrightarrow\quad D_J+D_H,
\qquad
\boxed{\mathrm{PRE}_0^{\rm mix}+\mathcal D=0+\mathrm H13}
\quad\Longleftrightarrow\quad\mathrm{PRE}+\mathrm{C13}. \tag{80.3}
$$
删去第二个等价两边的 H13、C13 仍为同一实际模型类的等价。没有三框架生成前件，也没有提前使用复型。
此外，在任何原 $\mathrm{PRE}_0^{\rm mix}$ 模型中，全部正交正元均有
$$
0\le\langle Ja,Jb\rangle_D\le\frac{\mathcal D}{2}\|a\|_\infty\|b\|_\infty
\qquad(a,b\in A_+,\ a\circ b=0). \tag{80.4}
$$

**证明。** 一般有限 EJA 的有标签完整本原框架集合非空紧：$e_i^2=e_i$、$\tau e_i=1$、互相正交与和为单位都是闭条件，每个 $e_i$ 的迹二范数一。$U,G>0$ 使 $F$ 连续，故 $q(B)$ 连续并取得最大值。每套 $Je$ 与 $H_{\mathrm s}F(e,f)$ 分别为 $U,G$ 的正分解，78.8 给
$$
q_J(B)=2\sum_{e<e'}\langle Je,Je'\rangle_D\ge0,\qquad
q_H(B)=2\sum_{(e,f)<(e',f')}\langle H_{\mathrm s}F(e,f),H_{\mathrm s}F(e',f')\rangle_E\ge0. \tag{80.5}
$$
此时不要求 $F(e,f)$ 幂等。固定载体时，局部原映射参数及紧框架集的联合连续性给 $\sup_B|q_z(B)-q_{z'}(B)|\to0$，故最大值连续；它不是随模型移动的开生成族上的下确界。Jordan 同构保持单位、规范迹、二次表示及所有完整框架；将 $L,p,\omega$ 同时按原同构运输，(80.1) 的全部派生映射及 (80.2) 的求和与最大值均对应，给不变性。不能只运输一张边缘表而保留不相容的联合映射。
正交正 $a,b$ 的支撑正交，可在支撑及其补面内谱分解，得到同一个完整框架 $B=(e_i)$ 及不交支持集 $I,J$，使 $a=\sum_{i\in I}\alpha_i e_i$、$b=\sum_{j\in J}\beta_j e_j$，系数非负。零元直接处理。于是
$$
\langle Ja,Jb\rangle=\sum_{i\in I,j\in J}\alpha_i\beta_j\langle Je_i,Je_j\rangle
\le\|a\|_\infty\|b\|_\infty\sum_{i\in I,j\in J}\langle Je_i,Je_j\rangle
\le\frac{q_J(B)}2\|a\|_\infty\|b\|_\infty,
$$
因为每个跨支持无序对只出现一次，其余交叉项非负。$q_J(B)\le q(B)\le\mathcal D$ 给 (80.4)，特别地 $\mathcal D=0$ 先恢复整个 $D_J$。
现在才用不依赖 $D_H$/C13 的 65.3，取得原归一化的两边缘保单位 Jordan 嵌入 $\alpha=F(-,1),\beta=F(1,-)$、交换乘法算子以及 $F(a,b)=\alpha(a)\circ\beta(b)$；其满规范迹等距使每个 $F(B\times B)$ 为完整本原框架。
取 $A$ 的任一实线性基，每个基元作谱分解。所得至多 $d=\dim_{\mathbb R}A$ 套完整框架的并集线性张满，因而 Jordan 生成 $A$；这只是证明中取有限子族，不是新的模型输入。$\mathcal D=0$ 使它们每套的 (80.5) 均逐项为零。同标方格的行和、列和分别包含 $\alpha(e),\beta(e)$，故其 Jordan 闭包包含 $\alpha(A),\beta(A)$，再由乘积及第一实张成覆盖整个 $D$。对 $H_{\mathrm s}$ 应用 75.4 的一般 EJA 闭包工具，或者直接用 76.3 的任意有限生成族版本，得到整个纠缠锥上的 $D_H$。
逆向由 $D_J$ 得每套第一表及这些完整产品框架，由 $D_H$ 得每套第二表，故所有 $q(B)=0$。这证明第一个等价。原 H13 此后按 72.7—72.8 逐原成员检测 C13，取得完整候选及逆向。整个前向闭包没有预设复数、三生成框架或 Albert 的结合矩阵表示。证毕。

第一层界 (80.4) 不需要字典或谱条件数；它使用整个原框架量词。三框架见证的有限压缩仍可按 78.5 等价取回，但从一个特选框架的小缺陷不能推导 (80.4)。$\mathcal D$ 是不变量，最大化框架集合可以有很多成员；标量与集值极值不提供自然有限选框架。标准量子模型的每个 $q(B)=0$，其最大化集就是全部框架，72.16 的自然选择障碍仍保留。

### 80.3 固定错误不能藏在极值中

**命题 80.4（完整转置平均模型的包络）。** 在 78.5 的固定完整原接口 (78.16) 中，$0<\lambda<1$ 时
$$
\boxed{\mathcal D_\lambda=8(1-\lambda^2)(7+2\lambda^2)>0.} \tag{80.6}
$$
同一个模型在全部单框架上的最小 $q$ 却为零；在真正生成整个 $A$ 的三框架族上，旧 $\delta$ 的下确界为零而没有零见证。因此最小单框架、生成族下确界与全框架最大值不能互换。

**证明。** 保留 (78.16) 的全部原 $A,D,E,L,p,\omega$，包括同一个四维首腿偏迹、两实张成、全实 $Z$、$U=I_{16},G=I_{64}$ 和整个原锥上的 C13；该模型的 $D_J$ 失败、$D_H$ 成立。这里只计算新包络，不另造边缘代替实际接口。对单位 $v\in\mathbb C^4$ 及 $e=vv^*$，令 $a=(1+\lambda)/2,b=(1-\lambda)/2$。$e^T=\bar v v^T$，故 $\operatorname{Tr}(ee^T)=|v^Tv|^2$，从而
$$
\operatorname{Tr}[(T_\lambda e)^2]=a^2+b^2+2ab|v^Tv|^2
=\frac{1+\lambda^2}{2}+\frac{1-\lambda^2}{2}|v^Tv|^2. \tag{80.7}
$$
对任意完整秩一框架 $B$，置 $S_B=\sum_{e\in B}\operatorname{Tr}[(T_\lambda e)^2]$、$d_B=4-S_B$。由 $0\le|v^Tv|^2\le1$，有 $0\le d_B\le2(1-\lambda^2)$。同一原接口的第一表平方范数和为 $4S_B$，第二表为 $4S_B^2$；因此
$$
q_J(B)=4d_B,\qquad q_H(B)=4d_B(8-d_B),\qquad q(B)=4d_B(9-d_B). \tag{80.8}
$$
最后的多项式在 $0\le d_B\le2$ 上严格递增。取两个不交 $2\times2$ 角中 $Y$ 的正负本原投影，即由 $(1,\pm i,0,0)/\sqrt2$、$(0,0,1,\pm i)/\sqrt2$ 给出的完整框架。四个向量均有 $v^Tv=0$，达到 $d_B=2(1-\lambda^2)$，代入即得 (80.6)。实正交基给 $d_B=q(B)=0$，证明最小单框架为零。78.5 的真生成族 $\mathfrak B_\theta$ 则满足 $\delta(\mathfrak B_\theta)\to0$，而固定的 $\langle Jp_+,Jp_-\rangle=2(1-\lambda^2)>0$ 排除任何生成族零见证。后者是非闭生成族上的下确界，不是已达到的生成族最小值。证毕。

### 80.4 修复的是同一对原准备与读回

**定理 80.5（没有源字典前件的共同原映射修复）。** 固定非零有限 EJA 三元组 $A,D,E$ 及其全部原态、效应、比较桥和迹坐标。给定 $R_0,\zeta,\alpha,\beta>0$、$\alpha\le\beta$，令 $\mathscr K$ 为满足整个 $\mathrm{PRE}_0^{\rm mix}$ 及以下原接口界的全部 $z=(L,p)$：
$$
\begin{gathered}
\|\widetilde L\|,\|p\|\le R_0,\qquad
\widetilde M\widetilde M^*\succeq\zeta^2 I_D,\qquad
\widetilde L\widetilde L^*\succeq\zeta^2 I_E,\\
\alpha1_D\le U\le\beta1_D,\qquad
\alpha1_E\le G\le\beta1_E.
\end{gathered} \tag{80.9}
$$
波浪号为原实线性化，算子范数与伴随使用原迹 Hilbert 张量坐标。没有框架输入、Jordan 字配方或源字典行下界。此类紧，其精确零集
$$
\mathscr Z=\{z\in\mathscr K:\mathcal D(z)=0\}
=\mathscr K\cap\{\text{原 PRE 模型}\} \tag{80.10}
$$
有如下穷尽情形。$\mathscr K$ 空则结论无对象；$\mathscr K$ 非空而 $\mathscr Z$ 空，则 $\min_{\mathscr K}\mathcal D>0$。若 $\mathscr Z$ 非空，则有有限模量 $\eta_{\mathscr K}$，满足 $\eta_{\mathscr K}(0)=0$、$\eta_{\mathscr K}(t)\to0$，使每个 $z\in\mathscr K$ 均有同类中的精确原模型 $z_0=(L_0,p_0)\in\mathscr Z$，且
$$
\left(\|\widetilde L-\widetilde L_0\|_{\rm HS}^2+\|p-p_0\|_{\rm HS}^2\right)^{1/2}
\le\eta_{\mathscr K}(\mathcal D(z)). \tag{80.11}
$$
$z_0$ 使用同一个 $p_0$ 连续两次、同一原 $\omega$、全部原锥和全部实 $Z$；并非分别修复两个派生映射后假定它们相容。令 $r_J,r_H$ 分别为谱范数至多一的全部正交正元对上的两层残差最大值。若 $n=\operatorname{rank}A,m=\operatorname{rank}D$，则
$$
r_J\le\mathcal D/2,\qquad
r_H\le2R_0nm\,\eta_{\mathscr K}(\mathcal D). \tag{80.12}
$$
这里不主张显式幂率或可计算的修复算法。

**证明。** 原映射空间有限维，范数界给有界性。全锥正性和全实 $Z$ 闭；两条行下界保持原实张成，谱下界保持 $U,G$ 内点和 $F$ 连续。其余比较几何已经固定，所以 $\mathscr K$ 闭且紧。由 80.3，$\mathcal D$ 连续，零点恰为同一原 PRE，而不是换载体或换边缘的模型。紧集上的正连续函数取得严格正最小值，给空零集时的间隙。
若零集非空，它是紧集。使用 (80.11) 左端定义原映射对的距离，最近零点存在。定义
$$
\eta_{\mathscr K}(t)=\sup\bigl(\{\operatorname{dist}(z,\mathscr Z):z\in\mathscr K,\ \mathcal D(z)\le t\}\cup\{0\}\bigr). \tag{80.13}
$$
它有限且零点处为零。若 $t_j\downarrow0$ 而距离上确界不趋零，取与零集保持固定正距离的近似极值点并抽紧子列；其极限同属 $\mathscr K$，连续性给 $\mathcal D=0$，却仍与零集保持正距离，矛盾。该紧性论证是成熟有限维工具；实质应用在于其零集已识别为保留同一原定义关系的完整 PRE 对。
第一界由 (80.4)。对最近的 $z_0$，$H_0=L_0(-,1_A)$ 精确保零。$\|1_A\|_2=\sqrt n$ 给
$$
\|H_{\mathrm s}\|,\|H_0\|\le R_0\sqrt n,\qquad
\|H_{\mathrm s}-H_0\|\le\sqrt n\|\widetilde L-\widetilde L_0\|_{\rm HS}.
$$
若 $d,d'\in D_+$ 正交、谱范数至多一，则二者迹二范数至多 $\sqrt m$。从 $\langle H_0d,H_0d'\rangle=0$ 展开差，按两个因子的范数估计，得
$$
0\le\langle H_{\mathrm s}d,H_{\mathrm s}d'\rangle
\le2R_0nm\|\widetilde L-\widetilde L_0\|_{\rm HS}.
$$
取全域最大值并用 (80.11)，得第二界。证毕。

**推论 80.6（全原插入正性下的修复范围）。** 若 $\dim_{\mathbb R}D=(\dim_{\mathbb R}A)^2$，则 (80.9) 使 $\widetilde M$ 可逆且逆一致有界。令 $\mathscr K_C$ 为 $\mathscr K$ 中还满足整个原 C13 的子集。它紧，80.5 的间隙／修复结论可在其中原样使用；零点恰为同一原 PRE+C13。维数不等时，$\mathscr K$ 中没有精确零点，故非空 $\mathscr K$ 有严格正缺陷间隙。

**证明。** 同维时行下界给 $\|\widetilde M^{-1}\|\le\zeta^{-1}$，故由同一 $L,p$ 构造的 $I^{\rm raw}=\widetilde T_{\rm raw}\widetilde M^{-1}$ 连续。固定整个原锥上的正性是闭条件，$\mathscr K_C$ 因而为紧集，且每个最近零点仍具有整个原 C13。对它用 80.3—80.5 即得结论。维数不等时，若存在零点，80.3 恢复 $D_J$，65.3 将给 $\widetilde F:A\otimes_{\mathbb R}A\to D$ 满迹等距同构，与维数矛盾。证毕。

全 C13 是此推论的显式额外前件，不是把正缺陷时尚无块定义的 H13 擅自解释为近似资格。原单混态方向条件的有噪版本仍需负方向裕量、活跃块质量与滤波控制；本章未给这条桥。不同 EJA 类型之间的近似分类、统一幂率与自然修复选择也不由固定载体紧性得到。

### 80.5 量子公理的回接与几何范围

**推论 80.7（完整精确理论的消费者）。** 完整候选 (80.3) 精确成立时，它恢复同一个原 PRE+C13，因而 78.7 的消费者和所有额外前件逐项保留：

| 既有量子结构 | 从本候选回接的条件链 |
| --- | --- |
| 复 Hilbert 表示、密度态、全效应与 Born 迹配对 | 完整混合比较入口先恢复 $S$；原一般 EJA 桥及两层全域保零，沿 65—66、75.7 给有限复 Hermitian 直和，纯态几何为 $\bigsqcup_i\mathbb{CP}^{n_i-1}$。 |
| 普通二份、三份辅助张量及相对方向 | 精确 PRE 后的原 H13 恢复 C13，沿 72.7—72.8 排除错误相对转置；仍检测同一合格原混态的整个原输出。 |
| 原准备的标准归一化与偏迹 | 可取最新第 79 章的一个局部固定泛函见证、两条原质量关系及原 $\mathrm A_0$；由 79.7 在方向条件之前等价恢复 $C_{\rm joint}$。73.2、73.10—73.16 的双侧正重置补全仍是等价入口。零包络自身不校准权重。 |
| CP 事件、仪器、Lüders 更新 | 仍需 69.1—69.11 的实际旁观者、同事件联合正性、足够大参考和局部／原联合两预算；共同重置的输入行权重一致、锐效应与确定接受态逐点不变仍按原合同另付。 |
| Hamiltonian 动力学 | 仍需原物理时间的连续齐次可逆 $*$-自同构群；静态关系不产生该群、时间尺度或 $\hbar$。 |

此外，固定 $t,s\in(0,1)$，令 $\mathsf{Mass}_{t,s}$ 完全取定义 79.2：存在同一个原 $A$ 上正保原质量的实线性 $\Phi$，全部实固定泛函恰为 $\mathbb R u_A$；原 $m_2=u_DM$、$m_3=u_EL(M(-,-),-)$ 满足 (79.5) 的两条全正输入质量关系，包括零和不等质量。原锚 $\mathrm A_0$ 仍为 (79.15)，不改变原 $L,p,\omega$。则在同一实际模型类中还有完整归一化版本
$$
\boxed{\mathrm{PRE}_0^{\rm mix}+\mathcal D=0+\mathsf{Mass}_{t,s}+\mathrm A_0+\mathrm H13}
\quad\Longleftrightarrow\quad\mathrm{PRE}+C_{\rm joint}+\mathrm{C13}. \tag{80.14}
$$

**证明与边界。** 用 80.3 将精确候选直接代入 78.7，而非重证已有消费者。对 (80.14)，先由零包络恢复同一 PRE；79.5—79.7 再用同一个原 $p$ 两次和原参考，在 H13 之前由两质量关系及锚恰好恢复 $C_{\rm joint}$。最后 H13 给 C13，原张量与偏迹按 79.7 同时归一化。反向在同一原 PRE+$C_{\rm joint}$ 中由 79.7 及式 (79.14) 的数学见证恢复质量入口，80.3 与原方向定理给其余条件。该局部 $\Phi$ 只是原态几何中的存在见证，未供应实际随机装置、重置程序或新的联合正延拓。80.5 的近似结论只在固定载体和 (80.9) 的原接口类内给到某个精确 PRE 对的距离；80.6 才在额外整个原 C13 下给 PRE+C13 修复。它们不产生原实际仪器、装置、全菜单、四份以上组合、无限维一致性或新物理时间。完整原 $\Omega$ 的所有准备、事件、参考、副本、实际相关联合、零与不等质量、单位与时钟、ready 与 flags、失败、停止、销毁、返回、未来以及每个原全菜单与中间切口义务，均不因包络定义而删去。证毕。

**几何解释。** 仍是正分解的 Pythagorean 饱和：总向量平方长度减去部分平方长度之和，恰为全部交叉重叠的两倍。第 78 章以一套生成见证传播零关系；这里直接在原完整框架几何上取上包络，把外给见证和字典从候选的输入中移去。$\mathcal D=0$ 要求每套原分解都饱和，正好与已有精确候选等价。内在性指缺陷及其量词由原结构定义；零约束仍筛选模型，80.4 证明它并非定义自动恒真。其简洁性是同一原模型类中自由输入和定义层级的减少；全称框架信息被保留，因此不据此推断独立物理假设更少、有限认证成本更低或存在自然最优有限实验。

**完整白话。** 保留所有状态和测试、随机制备的完整比较规则，以及一个准备和同一个读回连续用两次的原系统。现在不先挑几套方向来替整个空间作证，而是把原几何中每一套完整互斥方向都放进同一个公式：先看第一接口，再把左右相同方向排成双份方格看第二接口。每张图中各部分都是正的，总和固定；总量长度的平方减去部分长度平方之和，记录的就是交叉重叠。把所有图中最大的这项重叠叫作缺陷。最大值为零，每一张图就都没有漏出的重叠，原来的全域保零关系随之恢复；随后由最新第 79 章的一个局部变化、两条总质量关系和原总迹锚校准倍率，再用原混态的方向条件排除错误转置，并按各自额外条件接回量子态、Born 配对、张量和过程。取最大值也堵住了第 78 章的漏洞：哪怕特选方向越来越贴近平面、把错误藏起来，总有另一张完整图把它照出来。若整个原接口保持有界且不塌缩，小最大缺陷还保证同一对准备、读回接近某个精确原模型；若这样的精确模型根本不存在，缺陷便隔着一条正间隙。公式少了外加见证，却仍要看遍所有方向，不能把这种简洁直接说成一次实验或无条件推出全部物理。

**数学来源与归属。** [P] [本卷第 78 章，固定文本 0790b557](https://github.com/the-omega-institute/trureturing/blob/0790b557ba64921e02107cc9da87ddc443a83610/docs/develop/theory/QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md)：78.1—78.2 的完整原基底、78.4 的精确零集、78.5 的固定完整接口反例、78.6 的条件紧性及 78.7 的全部消费者边界。本章新增的是不带生成见证的全框架上包络、第一层无字典线性界、原反例的极值公式以及对共同原映射对的条件修复，而非平方展开或紧性工具本身。
[J] [本卷第 75—77 章，同固定文本](https://github.com/the-omega-institute/trureturing/blob/0790b557ba64921e02107cc9da87ddc443a83610/docs/develop/theory/QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md)：75.4 的一般有限 EJA 闭包、76.3 的任意有限生成族版本、77.19 的混合余项入口均按原完整前件复用。[R] [第四卷第 65—72 章，同固定文本](https://github.com/the-omega-institute/trureturing/blob/0790b557ba64921e02107cc9da87ddc443a83610/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_IV.md)：65.3 第一接口满等距、66 的分类、69 的过程合同、72.7—72.8 的原方向检测及 72.16 自然有限选择障碍。[M] 本卷第 79 章，定义 79.2、定理 79.5—79.7、79.15：两条原质量关系、同 $p$ 尺度刚性、原锚与前方向校准均直接按完整原前件复用，(80.14) 只把这条最新归一化入口接到零包络恢复的同一个 PRE，不将该质量定理重算为本章新内容。一般有限 EJA 的谱分解、固定紧参数集上极值的连续性、有限维紧性与距离零集收敛均为成熟工具，证明内部已给出其所需条件；未从误差界文献移植未核条件的幂指数。新增结论为这些原前提下的仓内纸面综合推导，不声称内核核验、全球原创、最少物理公理或物理可得性。

## 追加锚（本行以下为增补区）

## 81. 对角几何的单个内在投影与完整量子候选

本章第 65—72 章仍指第四卷，第 73—80 章指本卷。第 80 章以全框架最大缺陷移除了外给生成见证；这里进一步把极值搜索改为原对称几何的固定矩收缩。保留同一个原模型类，不先假复型、不可约性或物理可执行的随机平均；新增条件仍是定义间的非平凡约束。

### 81.1 完整原数据与对角投影轨道

**定义 81.1（原基底与内在矩）。** 完整原基底取定义 80.1 的 $\mathrm{PRE}_0^{\rm mix}$：非零有限维 $A,D,E$ 使用全部原态与 proper 效应、纯态最小确认比较及任意混态余项的全部二元律；先由 77.19 恢复完整 $S$，再按原正对偶生成、忠实态效应对应、共同框架、面投影、项目性及滤波纯性等完整条件进入一般有限 EJA。允许异型直和、秩一和 Albert。原接合 $L:D\times A\to E$、原读回 $p:E\to D$ 在整个原锥上正，包括纠缠方向；同一个 $p$ 连续两次，原 $\omega=1_D/\tau_D1_D$、两实张成和全部实 $Z$ 均不变。全部 $K,M,J,H_{\rm s},B_1,U,G,F$ 严格按 (80.1) 定义。两张成与正性先给 $U,G>0$，故在零关系之前 $F=P_{U^{-1/2}}M$ 已正且保单位。

以下 $d=\dim_{\mathbb R}A$、$n=\operatorname{rank}A$，$\operatorname{Tr}$ 为原迹 Hilbert 空间上线性算子的迹，区别于 Jordan 迹 $\tau_A$。对完整本原框架 $B$ 令
$$
\Pi_B=\sum_{e\in B}|e\rangle\langle e|,\qquad
\mathscr P_A=\{\Pi_B:B\text{ 是原完整本原框架}\}.
\tag{81.1}
$$
$\Pi_B$ 是到框架实张成的正交投影，$\Pi_B^2=\Pi_B$、$\operatorname{Tr}\Pi_B=n$、$\Pi_B1_A=1_A$。标签只重排求和，不是新输入。以全部数学 Jordan 自同构的紧群 $\mathscr G_A=\operatorname{Aut}_J(A)$ 共轭作用于 $\mathscr P_A$；不把该群自动认作原源供应的物理操作。

**引理 81.2（一般有限 EJA 的投影轨道）。** $\mathscr P_A$ 非空紧且为 $\mathscr G_A$ 的单一轨道。因此存在唯一不变全支撑概率 $\nu_A$，由任意轨道点的归一化 Haar 推前给出。

**证明。** 原完整框架集合在 $A^n$ 中由幂等、迹一、正交与和为单位的闭等式给出，每项范数一；谱定理给非空，故其连续投影像紧。Jordan 自同构保持原规范迹内积，是正交群中由保乘积等式定义的闭子群，故紧。将 $A$ 分解为简单理想；本原幂等元只能位于一个理想，每套完整框架在每个理想有该理想秩数的成员。简单因子的完整框架传递性用 [F] 的不可约情形，包含 Albert；各因子自同构直和便把任意一套无标签框架送到另一套。由此所有 $\Pi_B$ 共轭，不需一般直和的纯态传递性或有标签框架逐槽传递性。
若 $\Pi_1=h\Pi_0h^{-1}$，Haar 右不变性使以二者为起点的轨道平均相同。对任一不变概率，先沿群平均连续函数再沿该概率积分，内层由传递性为常数，故概率唯一。非空轨道开集的逆像为群中非空开集，Haar 质量为正，给全支撑。证毕。

定义两个只由原 $A$ 决定的有限维算子及原派生映射
$$
\mathsf C_A=\int\Pi\,d\nu_A(\Pi),\qquad
\mathsf W_A=\int(\Pi\otimes\Pi)\,d\nu_A(\Pi),\qquad
\mathcal T=H_{\rm s}\widetilde F:A\otimes_{\mathbb R}A\to E.
\tag{81.2}
$$
以原迹坐标定义平均缺陷
$$
\boxed{\mathcal Q(L,p)=\|U\|_2^2+\|G\|_2^2
-\operatorname{Tr}(J^*J\,\mathsf C_A)
-\operatorname{Tr}(\mathcal T^*\mathcal T\,\mathsf W_A).}
\tag{81.3}
$$
几何算子固定，$L,p$ 只通过原派生量进入收缩；没有模型依赖的最大化、外给字典或生成框架。

### 81.2 零平均、全域关系与有限维比较

**定理 81.3（同零集与最坏缺陷控制）。** 完整原基底中 $\mathcal Q\ge0$，在固定原 EJA 三元组上连续，并在全部原数据共同按保原迹 Jordan 同构运输时不变。令 $\mathcal D$ 为 (80.2)，则
$$
\mathcal Q=0\quad\Longleftrightarrow\quad\mathcal D=0
\quad\Longleftrightarrow\quad D_J+D_H.
\tag{81.4}
$$
令 $h=d(d+1)/2$，$V$ 为 $\mathscr P_A$ 上所有关于自伴算子坐标的二次齐次多项式限制，$N=\dim V$；则 $1\le N\le\binom{h+1}{2}$ 且
$$
\boxed{\mathcal Q\le\mathcal D\le N\mathcal Q.}
\tag{81.5}
$$
所有原正交正元均满足
$$
0\le\langle Ja,Jb\rangle_D
\le\frac{N\mathcal Q}{2}\|a\|_\infty\|b\|_\infty
\qquad(a,b\in A_+,\ a\circ b=0).
\tag{81.6}
$$

**证明。** 固定原映射，定义
$$
q_z(\Pi)=\|U\|_2^2+\|G\|_2^2
-\operatorname{Tr}(J^*J\Pi)
-\operatorname{Tr}(\mathcal T^*\mathcal T(\Pi\otimes\Pi)).
\tag{81.7}
$$
Hilbert–Schmidt 展开使 $q_z(\Pi_B)$ 恰为 (80.2) 的 $q_J(B)+q_H(B)$。每套 $Je$ 是 $U$ 的正分解，每套 $H_{\rm s}F(e,f)$ 是 $G$ 的正分解；平方展开为全部交叉内积的两倍，故逐点非负，无须先假 $F(e,f)$ 幂等。式 (81.3) 正是 $\int q_z\,d\nu_A$。若一点严格正，连续性在某开邻域给正下界，全支撑使积分严格正，证明零平均恰为处处零。随后按 80.3 的原顺序先恢复 $D_J$，才用 65.3 的第一接口满等距及 75.4／76.3 的一般 EJA 闭包恢复全 $D_H$；不新增 JG3 或复型前提。
固定几何上 $U>0$ 保持 $F$ 连续，紧轨道使局部映射参数变化给 $q_z$ 一致连续，故积分连续。同构共同运输 $L,p,\omega$ 及原迹、二次表示与投影轨道，唯一不变概率亦对应，给不变性。
因 $\operatorname{Tr}\Pi=n$，常数及一次函数可分别乘 $(\operatorname{Tr}\Pi/n)^2$ 及 $\operatorname{Tr}\Pi/n$ 写成二次齐次函数，故 $q_z\in V$；共轭作用线性，$V$ 不变。全支撑使 $L^2(\nu_A)$ 在有限维 $V$ 上正定。取实正交基 $\varphi_1,\ldots,\varphi_N$，核 $K(\Pi,\Pi')=\sum_j\varphi_j(\Pi)\varphi_j(\Pi')$ 的对角由不变性与传递性恒定，积分为 $N$，故恒等于 $N$。在最大点应用评价的 Cauchy–Schwarz，并用 $0\le q_z\le\mathcal D$，得
$$
\mathcal D^2\le N\|q_z\|_{L^2}^2\le N\mathcal D\mathcal Q.
$$
$\mathcal D=0$ 单独处理，其余相除；概率积分给另一侧。式 (81.6) 由 (80.4) 与 (81.5)。上界是符号维数界，不是已计算 $N$ 的读数。证毕。

非负性、全支撑和不变有限维空间各承担不同义务：二点均匀平均的有符号函数 $(1,-1)$ 可以积分零而非处处零；$[0,1]$ 上 $\delta_0$ 与 $q(x)=x^2$ 表明无全支撑会漏方向；圆周上不变测度与非不变空间 $V=\operatorname{span}\{1+\cos\theta\}$ 则有 $N=1$、平均一、最大二。上述环节不是把一般平均命名为“内在”便自动取得。

### 81.3 固定有限矩、直和与同框架相关

**命题 81.4（矩的有限表达与范围）。** 在原 Hilbert–Schmidt 空间上，令
$$
\begin{aligned}
\mathcal R_1(X)&=\int_{\mathscr G_A}gXg^{-1}\,dg,\\
\mathcal R_2(Y)&=\int_{\mathscr G_A}(g\otimes g)Y(g^{-1}\otimes g^{-1})\,dg.
\end{aligned}\tag{81.8}
$$
它们分别为共轭表示固定子空间的正交投影。对任意 $\Pi_0\in\mathscr P_A$，有 $\mathsf C_A=\mathcal R_1(\Pi_0)$、$\mathsf W_A=\mathcal R_2(\Pi_0\otimes\Pi_0)$，结果不依赖 $\Pi_0$。因此 (81.3) 可由固定有限不变空间的正交投影写成有限收缩；这不选择自然有限框架或供应实际精确读数。

若原简单理想分解为 $A=\bigoplus_\alpha A_\alpha$，$r_\alpha=\operatorname{rank}A_\alpha$、$d_\alpha=\dim A_\alpha$，则
$$
\mathsf C_A=\bigoplus_\alpha\mathsf C_\alpha,
\qquad
\mathsf C_\alpha=P_{\mathbb R1_\alpha}
+\frac{r_\alpha-1}{d_\alpha-1}P_{A_\alpha^0}\quad(r_\alpha>1),
\tag{81.9}
$$
其中 $A_\alpha^0=\ker\tau_\alpha$。标量因子 $\mathbb R$ 只有单位方向，取 $\mathsf C_\alpha=I$，不写 $0/0$。第二矩在 $A_\alpha\otimes A_\beta$ 上为 $\mathsf W_\alpha$（同因子）或 $\mathsf C_\alpha\otimes\mathsf C_\beta$（异因子）。尤其不能一般地用 $\mathsf C_A\otimes\mathsf C_A$ 代替 $\mathsf W_A$。

两个矩还能收进单个源投影。令 $P_0=|1_A\rangle\langle1_A|/n$、$\mathsf h_A=P_0\otimes P_0$，定义原 Hilbert–Schmidt 子空间与其正交投影
$$
\mathscr H_A=\operatorname{span}_{\mathbb R}\{\Pi\otimes\Pi:\Pi\in\mathscr P_A\},\qquad
\mathsf P_A:\operatorname{End}(A\otimes A)\to\mathscr H_A,\qquad v_A=\mathsf P_A\mathsf h_A.
\tag{81.8a}
$$
对同一个原映射对 $z=(L,p)$ 令 $S_J=J^*J$，并定义
$$
\Gamma_z=(\|U\|_2^2+\|G\|_2^2)\mathsf h_A
-\tfrac12(S_J\otimes P_0+P_0\otimes S_J)-\mathcal T^*\mathcal T.
\tag{81.8b}
$$
则 $v_A\ne0$，$\dim\mathscr H_A=N$，且
$$
\mathsf W_A=\frac{v_A}{\|v_A\|_{\rm HS}^2},\qquad
\boxed{\mathcal Q(z)=\frac{\langle\Gamma_z,v_A\rangle_{\rm HS}}{\|v_A\|_{\rm HS}^2}.}
\tag{81.8c}
$$
因此完整候选的零条件只需一个固定正交投影的收缩；平均张量 $\mathsf W_A$ 自身通常不是幂等投影，不能与 $\mathsf P_A$ 或 $\mathcal R_2$ 混同。

**证明。** Haar 平移及逆元不变性给 $\mathcal R_i^2=\mathcal R_i=\mathcal R_i^*$，像恰为固定子空间；轨道传递性给基点无关性。选该有限固定子空间任一正交基，正交投影就是有限内积和，换基不改变算子。
因 $\operatorname{Tr}(P_0\Pi)=1$，$\langle\mathsf h_A,\Pi\otimes\Pi\rangle=1$，故 $v_A\ne0$；又 $\mathsf h_A$ 不变，$\mathscr H_A$ 群不变，故 $v_A$ 不变。在 $\mathscr H_A$ 中任一不变向量 $w$ 与全部 $\Pi\otimes\Pi$ 的内积为同一个常数；若该常数零，则 $w$ 与其张成空间正交而为零。因此不变子空间至多一维，非零 $v_A$ 使之恰为 $\mathbb Rv_A$。$\mathcal R_2$ 在这个空间上正是到该直线的正交投影，而 $\langle\Pi\otimes\Pi,v_A\rangle=1$，所以其平均为 $v_A/\|v_A\|^2$。把 (81.7) 写成 $q_z(\Pi)=\langle\Gamma_z,\Pi\otimes\Pi\rangle$ 后积分，得 (81.8c)。$\mathscr H_A$ 的线性函数限制于这个轨道的像，恰为 81.3 的全部二次齐次限制空间；有限维对偶的秩等于原张成空间的维数，故二者维数同为 $N$。
简单因子中 $\mathsf C1=1$，且自伴，故保持迹零空间。该空间在自同构群下不可约：任一非零不变子空间内取非零迹零元，将其谱框架送到固定框架；有序框架置换使其系数排列张满迹零对角空间，再用完整谱框架传递性得到全部迹零元。于是自伴 $\mathsf C$ 在迹零空间只有一个特征值 $c$；$\operatorname{Tr}\mathsf C=r$ 给 $1+c(d-1)=r$，得 (81.9)。无标签框架为各因子框架的并，乘积 Haar 的推前是不变概率，唯一性给上述直和及异因子公式。重复同型因子的置换不改变该分布。Albert 的 $r=3,d=27$ 给 $c=1/13$；不借用八元数结合矩阵运算。
对简单 $A$ 且 $d>n>1$，取原迹正交基 $(a_k)$ 并令 $\Xi=\sum_ka_k\otimes a_k$，则
$$
\langle\Xi,\mathsf W_A\Xi\rangle=n,
\qquad
\langle\Xi,(\mathsf C_A\otimes\mathsf C_A)\Xi\rangle
=1+\frac{(n-1)^2}{d-1}<n.
\tag{81.10}
$$
前式用 $\Pi^2=\Pi$，后式用 (81.9)，证实同一框架的相关不能拆掉。一般直和也不能仅用总秩与总维数给统一迹零系数：$\mathbb R\oplus H_2(\mathbb C)$ 的两个中央单位均为特征值一方向。证毕。

**命题 81.5（同一个原反例的精确平均）。** 在 (78.16)／80.4 的固定完整转置平均模型中，$0<\lambda<1$ 时
$$
\mathcal Q_\lambda=\frac{216}{35}(1-\lambda^2)(6+\lambda^2)
\ge\frac{24}{5}(1-\lambda^2)(7+2\lambda^2)>0,
\qquad
\frac35\mathcal D_\lambda\le\mathcal Q_\lambda\le\mathcal D_\lambda.
\tag{81.11}
$$
实框架的 $q$ 仍为零；原全锥正 $L,p$、同 $p$ 两次、两实张成、全实 $Z$ 与整个原 C13 均保持。此处不将这个正缺陷对象预先赋予 H13 块资格。

**证明。** 原 $A=H_4(\mathbb C)$ 给 $\mathsf C_A=P_{\mathbb R1}+(1/5)P_{A^0}$。$T_\lambda$ 在实对称迹零九维上为恒等，在纯虚反对称六维上乘 $\lambda$；$J(a)=T_\lambda(a)\otimes I_4$，故平均 $q_J=24(1-\lambda^2)/5$。沿用 (80.8) 的 $d_B$ 并记 $s=1-\lambda^2$，有 $\mathbb E d_B=6s/5$、$0\le d_B\le2s$、$q=4d_B(9-d_B)$。
为算二阶矩，令 Haar $U(4)$ 的列为 $v_i$，$X_i=|v_i^Tv_i|^2$、$R=\sum_iX_i$，则 $d_B=s(4-R)/2$。复单位球面的对称张量恒等式 $\mathbb E(|v\rangle\langle v|)^{\otimes k}=P_{\rm sym}/\binom{4+k-1}{k}$ 由酉不变性、对称幂不可约性及迹一得到。取 $k=2,4$ 得 $\mathbb EX_i=2/5$、$\mathbb EX_i^2=8/35$。不能把不同列当成独立：条件于 $v_i=v$，$v_j$ 均匀位于三维正交补，令 $P=I-vv^*$，同一二阶球面矩给
$$
\mathbb E(X_j\mid v)=\frac{2\operatorname{Tr}(PP^T)}{3\cdot4}
=\frac{2+X_i}{6},\qquad
\mathbb EX_iX_j=\frac{2\mathbb EX_i+\mathbb EX_i^2}{6}=\frac6{35}.
$$
这里的条件平均是同一 Haar 框架的数学积分，不增加实际准备的独立性。于是 $\mathbb ER=8/5$、$\mathbb ER^2=104/35$、$\mathbb Ed_B^2=54s^2/35$，故 $\mathcal Q=36\mathbb Ed_B-4\mathbb Ed_B^2=(216/35)s(7-s)$。另逐点用 $9-d_B\ge7+2\lambda^2$ 得所列下界，(80.6) 给比例式，实框架取值仍按 80.4。这里只对同一完整原模型计算新指标，没有以独立边缘替代原接口。证毕。

有限维也给一个正面的数学存在结论：$\mathsf W_A$ 属于紧轨道 $\{\Pi\otimes\Pi\}$ 的凸包，而该轨道处于 $\mathscr H_A$ 的仿射超平面 $\langle\mathsf h_A,-\rangle=1$。Carathéodory 定理给至多 $N$ 个轨道点和正权，表示同一个 $\mathsf W_A$；与任意 $\Gamma_z$ 收缩便得到对全部原模型同时成立的固定有限正权求积。因此若这种精确求积和精确原读数另已供应，存在数学上的有限零证书。该结论不选取自然节点、不供应物理准备或噪声控制；一般生成框架也不自动满足求积关系。

### 81.4 共同原映射修复与完整量子入口

**推论 81.6（原修复类的运输）。** 固定原 EJA 三元组与 (80.9) 的有界不塌缩原映射类 $\mathscr K$，其精确零集仍为 $\mathscr Z=\mathscr K\cap\mathrm{PRE}$。若 $\mathscr K$ 空则无对象；非空而零集空，则 $\min_{\mathscr K}\mathcal Q\ge(\min_{\mathscr K}\mathcal D)/N>0$。零集非空时，每个原 $(L,p)$ 有同类精确原对 $(L_0,p_0)$，且
$$
\operatorname{dist}_{\rm pair}((L,p),\mathscr Z)
\le\eta_{\mathscr K}(N\mathcal Q),\qquad
r_J\le N\mathcal Q/2,\quad
r_H\le2R_0nm\,\eta_{\mathscr K}(N\mathcal Q),
\tag{81.12}
$$
其中 $\eta_{\mathscr K}$ 为 (80.13)、$m=\operatorname{rank}D$，距离为 (80.11) 的原映射对 Hilbert–Schmidt 距离。最近原对仍以同一个 $p_0$ 连续两次和同一原 $\omega$ 定义全部派生映射。整个原 C13 子类的修复、维数不等时的正间隙及其精确范围仍按 80.6；不由此产生有噪单混态 H13 桥、显式幂率或修复算法。

**证明。** (81.4) 保留同一零集，(81.5) 及 $\eta_{\mathscr K}$ 单调性使 80.5—80.6 直接适用；空零集情形按点态比较取最小值。它修复同一对原准备、读回，不是分别修补两个派生边缘。证毕。

**定义 81.7（由原单位固定的质量见证）。** 在原 EJA 坐标中令 $n=u_A(1_A)=\tau_A1_A$，定义数学映射 $R_A(a)=u_A(a)1_A/n$，以及原 $m_2(a,b)=u_DM(a,b)$、$m_3(a,b,c)=u_EL(M(a,b),c)$。要求全部原正输入含零及不等质量满足
$$
\begin{aligned}
\mathsf E_2:\quad m_2(a,b)&=\tfrac12[m_2(R_Aa,b)+m_2(a,R_Ab)],\\
\mathsf E_3:\quad m_3(a,b,c)&=\tfrac13[m_3(R_Aa,b,c)+m_3(a,R_Ab,c)+m_3(a,b,R_Ac)].
\end{aligned}\tag{81.13}
$$
它不供应实际重置过程或随机控制。保留同一原锚 $\mathrm A_0:u_EL(\omega,1_A/n)=1$。只在 $\mathcal Q=0$ 恢复 PRE 后，才按定义 80.2 读取完整原 H13：同一个总迹一原混态在每个活跃块至少有一个原边缘铺回差的严格负方向，非活跃块允许零，活跃集空时资格为全原态基；原规范迹伴随、未经维数归一化的单位及同一合格态的整个原插入输出正性不变。

**定理 81.8（完整同数据候选）。** 在同一实际原模型类中，
$$
\boxed{\mathrm{PRE}_0^{\rm mix}+\langle\Gamma_z,v_A\rangle_{\rm HS}=0+\mathsf E_2+\mathsf E_3+\mathrm A_0+\mathrm H13}
\quad\Longleftrightarrow\quad\mathrm{PRE}+C_{\rm joint}+\mathrm{C13}.
\tag{81.14}
$$
删去质量、锚及 $C_{\rm joint}$ 的精确未校准版本同样成立。它接回现有量子公理的全部条件如下。

| 量子结构 | 同数据回接与保留的前提 |
| --- | --- |
| 复 Hilbert 表示、密度态、全效应与 Born 配对 | 完整比较及一般 EJA 桥先成立；零平均给两层全域保零，65—66、75.7 才给有限复 Hermitian 直和及纯态 $\bigsqcup_i\mathbb{CP}^{n_i-1}$，配对为 $\sum_i\operatorname{Tr}(\rho_if_i)$。 |
| 二份、三份张量及相对方向 | 精确 PRE 后的同一原 H13 给整个原 C13，沿 72.7—72.8 取得共同普通方向；不自动给四份以上或另一括号的共同来源。 |
| 原尺度、标准准备与偏迹 | 两条 (81.13) 加原锚先于 H13 恢复 $C_{\rm joint}$；方向条件随后使同一个原 $M,L,p$ 同时标准归一化。 |
| CP 事件、仪器与 Lüders 更新 | 69.1—69.11 的实际事件、参考、同事件联合正性、局部及原联合两预算、共同重置输入行等条件仍另付；锐投影效应与全部确定接受态逐点不变才给原 Lüders 结论。 |
| Hamiltonian 动力学 | 仍需原物理时间上的连续齐次可逆 $*$-自同构群；静态零平均不供应时间群、单位或 $\hbar$。 |

**证明。** (81.8c) 的分母严格正，故零收缩与零平均等价；(81.4) 先恢复同一原 PRE。$R_A$ 正且保原质量，$fR_A=f$ 恰当且仅当 $f=f(1_A/n)u_A$，故全部实固定泛函为 $\mathbb Ru_A$；(81.13) 是 79.2 取固定 $t=1/2,s=2/3$ 的同一质量入口。因此 79.5—79.7 与原锚先给 $C_{\rm joint}$，原 H13 此后才给 C13。反向由原 PRE+$C_{\rm joint}$，79.6—79.7 给 $m_2=u_A^{\otimes2}$、$m_3=u_A^{\otimes3}$，故这个由单位固定的 $R_A$ 满足两条等权关系；(81.4) 和原方向定理给其余条件。固定数学态与权重只是 79.6 构造的直接应用，不计为新增质量定理。消费者按 80.7 逐项运输，不重证已有分类和过程结论。
完整原 $\Omega$ 的准备、事件、参考、副本、实际相关联合、零与不等质量、单位与时钟、ready 与 flags、失败、停止、销毁、返回、未来、每个原全菜单及中间切口义务不因平均而删去。固定载体上的数学平均、有限矩与距离零集收敛，均不构造这些实际来源接口。证毕。

**几何与白话。** 每套完整互斥方向张成一个对角子空间，原迹几何给它一张正交投影。现在不挑几套方向，也不搜索最坏方向，而让原几何的全部对角子空间各按其对称权重进入同一个平均。被平均的不是待测态，而是每张图已经非负的交叉重叠：平均为零，所有方向就都没有重叠；有限维比较还保证错误不能只藏在很小一撮方向里。公式最后只剩原几何固定的一个正交投影：把单位方向的张量投到所有对角投影张量张成的空间，再与同一准备、同一读回所派生的系数作一次内积；左右同一框架的相关仍完整保留。再把质量见证固定成“原质量乘原单位的归一化”，由双份、三份的两条等权质量关系和原锚校准倍率；随后用同一个原混态的方向条件排除错误转置，按各自完整前提接回量子态、Born、张量和过程。有界且不塌缩的原接口若平均缺陷小，就接近某个同来源的精确原模型；若该类没有精确模型，缺陷就有正间隙。简洁发生在外给选择、极值搜索和定义层级上，未减少已保留的独立物理前提，也未制造自然有限实验或物理时间。

**来源与归属。** [F] Faraut–Korányi, *Analysis on Symmetric Cones*, [Chapter IV](https://doi.org/10.1093/oso/9780198534778.003.0004), Corollary IV.2.7；出版方摘要明确是不可约情形的完整框架传递性。[B] Barnum–Hilgert, [arXiv:1904.03753v1 §4.1](https://arxiv.org/html/1904.03753v1#S4.SS1), Proposition 4.7 的证明转引同一结论并说明有序框架范围；其所在 §4 为简单 EJA，不能将未限定的命题措辞推广为任意异型直和的纯态或部分框架强对称性。本章给出所需的完整无标签框架之逐因子推广，不增加该强对称前提。[H] von Neumann, [*Zum Haarschen Maß in topologischen Gruppen*](https://www.numdam.org/item/CM_1935__1__106_0/), Compositio Mathematica 1, 106—114：紧可分群不变积分；本章群为有限维紧矩阵群。有限维核比较、Haar 正交投影及简单因子迹零论证已在文中给出；它们是成熟工具，不作全球新颖性主张。[P] 本卷 78—80 及第四卷 65—72 的完整原接口、闭包、分类、方向、修复和消费者按原前件复用；归一化固定见证仅应用本卷 79.2、79.6—79.7。新增综合内容是同一原模型类的无极值平均缺陷、单个内在投影表示、最坏缺陷比较、原反例的精确平均及共同原映射修复的运输；这是纸面理论，不声称 Lean 内核核验、最少物理公理或物理可得性。

## 追加锚（本行以下为增补区）

## 82. 同事件三腿固定探针的完整正性证书与有限二腿目录障碍

本章第 65—72 章指第四卷，第 73—80 章指本卷。完整归一化原候选直接复用 (80.14)，也保留定义 79.14 的全部等价入口；不重复质量校准。这里处理另一条关系：**对同一个已经指定的局部事件，作用于一个位置后的加权平均，何时足以认证该事件的完全正性？** 三份相同标签给出一个固定数学探针及精确 Choi 压缩；整个二份正锥也足够，但任何预先固定的有限严格加权二份 PSD 检测目录都不足。后一个结论在单个非经典矩阵块上证明，不能外推为全经典或任意直和的混合反模型。

### 82.1 约定、同映射加权提升与三腿压缩

**定义 82.1（矩阵、迹和量词）。** 令 $\mathcal A=\bigoplus_{i\in I}M_{n_i}(\mathbb C)$，$I$ 有限非空，$n_i\ge1$，$A=\mathcal A_{\rm sa}$，$n=\sum_i n_i$，$u_A=\sum_i\operatorname{Tr}$。二份、三份为全部有序块的普通矩阵张量直和，包含整个 PSD 锥；不只包含可分离元。$\Phi:\mathcal A\to\mathcal A$ 为复线性保 Hermitian 映射（HP），其输入 $i$、输出 $j$ 的块记 $\Phi_{ji}$。实 Hermitian 线性映射一律取唯一的这种复延拓。
在每个原块上任意固定一套共同矩阵标架，先于且独立于 $\Phi$；向量化及未归一 Choi 顺序取输出在前、输入在后：
$$
\operatorname{vec}X=\sum_{a,b}X_{ab}|a\rangle\otimes|b\rangle,\qquad
J(\Phi_{ji})=\sum_{a,b=1}^{n_i}\Phi_{ji}(E_{ab})\otimes E_{ab}. \tag{82.1}
$$
令 $\Phi_\ell$ 只作用第 $\ell$ 位置，按块转移并对输入标签求和。例如三份的第一位置满足
$$
(\Phi_1Z)_{jkl}=\sum_i(\Phi_{ji}\otimes\operatorname{id}_{n_k}\otimes\operatorname{id}_{n_l})Z_{ikl}.
$$
定义
$$
\mathcal K_{2,t}(\Phi)=t\Phi_1+(1-t)\Phi_2,\quad 0\le t\le1,\qquad
\mathcal K_{3,\alpha}(\Phi)=\sum_{\ell=1}^3\alpha_\ell\Phi_\ell,\quad
\alpha_\ell\ge0,\quad\sum_\ell\alpha_\ell=1. \tag{82.2}
$$
每个位置必须是**同一份** $\Phi$；不能以三个不相关事件的平均替代。本章 CP 判据本身不要求 $\Phi$ 正、TP、保单位、遍历或混合。三腿和整个二腿锥判据允许权重端点，与第 79 章质量定理所需的严格 $t,s\in(0,1)$ 分开。

**引理 82.2（单块的精确三腿 Choi 压缩）。** 对 $\Phi:M_d\to M_d$，置
$$
|G_d\rangle=d^{-1/2}\sum_{i=1}^d|iii\rangle,\qquad G_d=|G_d\rangle\langle G_d|,
$$
并定义复线性 $F_d:\mathbb C^d\otimes\mathbb C^d\to(\mathbb C^d)^{\otimes3}$：
$$
F_d(\operatorname{vec}B)=\sum_i B_{ii}|iii\rangle+
\sum_{j\ne i}B_{ji}(|jii\rangle+|iji\rangle+|iij\rangle).
\tag{82.3}
$$
则对定义 82.1 的全部三腿权重，
$$
\boxed{F_d^*\,\mathcal K_{3,\alpha}(\Phi)(G_d)\,F_d=J(\Phi)/d.} \tag{82.4}
$$
$F_d^*F_d$ 在对角矩阵单位坐标上为一，在非对角坐标上为三，故 $F_d$ 单射且 $F_d^*F_d\le3I$；它通常不是等距映射。

**证明。** 对角字符串 $iii$ 与每组具有两个 $i$、一个不同 $j$ 的三个字符串互不相交；多数标签唯一确定 $i$，少数标签唯一确定 $j$。因此 (82.3) 给出的范数平方恰为 $\sum_i|B_{ii}|^2+3\sum_{j\ne i}|B_{ji}|^2$。
HP 使 $J(\Phi)$ Hermitian。对它作有限谱分解，把每个特征向量反向量化为 $H_a$，由矩阵单位上的 Choi 对应得到带实符号的 Kraus 展开
$$
J(\Phi)=\sum_a c_a|\operatorname{vec}H_a\rangle\langle\operatorname{vec}H_a|,\qquad
\Phi(X)=\sum_a c_aH_aXH_a^*,\qquad c_a\in\mathbb R. \tag{82.5}
$$
这里允许负 $c_a$，没有预用 CP。对每个 $H_a$ 和任一腿 $\ell$，直接比较字符串系数：
$$
\langle F_d(\operatorname{vec}B)|H_a^{(\ell)}|G_d\rangle
=d^{-1/2}\sum_{j,i}\overline{B_{ji}}(H_a)_{ji}
=d^{-1/2}\operatorname{Tr}(B^*H_a).
$$
三种位置得到完全相同的振幅。因此把 (82.5) 代入三腿平均并用 $\sum_\ell\alpha_\ell=1$，所得每个二次型都是 $d^{-1}\sum_ac_a|\operatorname{Tr}(B^*H_a)|^2$，即 $J(\Phi)/d$ 的二次型。Hermitian 极化给算子恒等式 (82.4)。$d=1$ 也直接成立。证毕。

**定理 82.3（一个固定三份数学探针检测全部扇区）。** 在定义 82.1 的全部有序块上指定迹一正元
$$
\Xi_{iii}=\frac{n_i}{n}G_{n_i},\qquad \Xi_{ijk}=0\quad\text{若不全相等}. \tag{82.6}
$$
对任意固定的共同块标架、任意允许的 $\alpha$，
$$
\boxed{\mathcal K_{3,\alpha}(\Phi)(\Xi)\ge0
\quad\Longleftrightarrow\quad\Phi\text{ CP}
\quad\Longleftrightarrow\quad\mathcal K_{3,\alpha}(\Phi)\text{ 在整个三份锥上正}.} \tag{82.7}
$$
全部标量、不等维和重复标签扇区均在结论中。

**证明。** 在输出 $iii$，其他种子的标签不可能只改一处便变成 $iii$；故该块恰为 $(n_i/n)\mathcal K_{3,\alpha}(\Phi_{ii})(G_{n_i})$。用 $F_{n_i}$ 压缩，得到 $J(\Phi_{ii})/n$。
对 $j\ne i$，输出 $jii$ 只能来自种子 $iii$ 的第一腿。令 $V_i|a\rangle=|aa\rangle$，则 $V_i^*V_i=I$，且该块为
$$
[\mathcal K_{3,\alpha}(\Phi)(\Xi)]_{jii}
=\frac{\alpha_1}{n}(I_{n_j}\otimes V_i)J(\Phi_{ji})(I_{n_j}\otimes V_i)^*. \tag{82.8}
$$
若 $\alpha_1>0$，以这个等距嵌入压缩就检测所有矩形 $J(\Phi_{ji})$。若第一权重为零，选择某个正权重腿，对 $iji$ 或 $iij$ 作相同论证与因子置换即可。至少一腿权重正。因此左边蕴含每个 $J(\Phi_{ji})\ge0$。
成熟的矩形 Choi 定理给每个块 CP。有限直和映射 CP 当且仅当全部分量 CP：必要性由中心包含与投影，充分性由任意辅助矩阵放大后逐输出块求正和。于是得到 $\Phi$ CP。反向每个一腿放大 CP，非负权平均也 CP，故在整个三份锥正，特别在 $\Xi$ 正。证毕。

$\Xi$ 是选定共同标架后的一个固定数学正元，独立于待测映射；任何这样的标架选择都适用。它不是自然、唯一或无基底的原物理准备选择器，不抵触 71.7 的自然单点障碍。$V_i$ 重复的是证明中的基标签，**不是**对未知态的复制程序。三份正元和压缩的存在不供应原 GHZ 制备、参考、副本或相干控制。

### 82.2 归一坐标中的定量 CP 修正

**推论 82.4（带明确迹规范的误差界）。** 设 $\epsilon\ge0$，在定义 82.1 的普通总迹规范中有
$$
\mathcal K_{3,\alpha}(\Phi)(\Xi)\ge-\epsilon I_E.
$$
令 $\delta=3n\epsilon$、$\Delta_A(X)=u_A(X)1_A$。则 $\Phi+\delta\Delta_A$ CP。若另外 $\Phi$ TP，
$$
\widehat\Phi=\frac{\Phi+\delta\Delta_A}{1+n\delta}\text{ 为 CPTP},\qquad
\|\Phi-\widehat\Phi\|_\diamond\le2n\delta=6n^2\epsilon. \tag{82.9}
$$
$\|\cdot\|_\diamond$ 为各普通迹块直和上的完全有界迹范数；没有声称常数最优。

**证明。** 对角输出的压缩给
$$
J(\Phi_{ii})/n\ge-\epsilon F_{n_i}^*F_{n_i}\ge-3\epsilon I.
$$
选择 $\alpha_\ell\ge1/3$ 的一腿，对任意非对角转移用 (82.8) 的等距压缩，得 $J(\Phi_{ji})\ge-(n/\alpha_\ell)\epsilon I\ge-3n\epsilon I$。所有块因此同有下界 $-\delta I$。$\Delta_A$ 的每个矩形 Choi 块都是 $I_{n_j}\otimes I_{n_i}$，所以相加后全为 PSD，按 Choi 定理得到 CP。
$u_A\Delta_A=n u_A$，故 TP 时分母使 $\widehat\Phi$ 保迹。置 $\mathcal R=\Delta_A/n$，它 CPTP，并有
$$
\Phi=(1+n\delta)\widehat\Phi-n\delta\mathcal R,\qquad
\Phi-\widehat\Phi=n\delta(\widehat\Phi-\mathcal R).
$$
CPTP 映射在该范数中为一（等价地，其每个放大的伴随为保单位 CP 映射，算子范数为一）。三角不等式给 (82.9)。$\epsilon=0$ 包括在内；未要求 $\Phi$ 本来正或遍历。证毕。

这个修正是一份数学 CP 映射，不是原过程的已供应修复装置；不推断同菜单、记录或未来接头也被修复。原滤波坐标下的谱误差须另计滤波范数，不能原样使用 (82.9)。

### 82.3 整个二份锥足够：复用相似转置的方法

**定理 82.5（完整二份锥的精确判据）。** 对定义 82.1 的全部矩阵直和及每个 $0\le t\le1$，
$$
\boxed{\mathcal K_{2,t}(\Phi)\text{ 在整个二份 PSD 锥正}
\quad\Longleftrightarrow\quad\Phi\text{ CP}.} \tag{82.10}
$$
不要求半群、连续时间、TP、局部正性或严格内点权重。

**证明。** 先取单块 $M_d$，用 (82.5)。给任意复矩阵 $W$，存在可逆 $A$ 使 $A^{-1}WA=W^T$：每个复方阵与其转置有相同 Jordan 形，而每个 Jordan 块的转置经倒序基变换回原块。置 $B^*=A^{-1}W$，则
$$
AB^*=W,\qquad (B^*A)^T=W.
$$
向量化恒等式给每个 $H_a$ 的两个振幅
$$
\begin{aligned}
\langle\operatorname{vec}B,(H_a\otimes I)\operatorname{vec}A\rangle
 &=\operatorname{Tr}(AB^*H_a)=\operatorname{Tr}(WH_a),\\
\langle\operatorname{vec}B,(I\otimes H_a)\operatorname{vec}A\rangle
 &=\operatorname{Tr}((B^*A)^TH_a)=\operatorname{Tr}(WH_a).
\end{aligned}
$$
若整个二份提升正，测试输入 $|\operatorname{vec}A\rangle\langle\operatorname{vec}A|$ 与输出向量 $\operatorname{vec}B$，得到
$$
0\le\sum_ac_a|\operatorname{Tr}(WH_a)|^2
=\langle\operatorname{vec}(W^*),J(\Phi)\operatorname{vec}(W^*)\rangle. \tag{82.11}
$$
$W$ 任意，故 $J(\Phi)\ge0$，从而 CP。这里没有要求输入、测试向量正交，也未对 $W$ 加迹零条件。
对直和，在输入中心块 $ii$、输出 $ii$ 上先用此单块证明取得 $\Phi_{ii}$ CP。对 $j\ne i$，若 $t>0$，输入 $ii$ 的 Bell 正元在输出 $ji$ 恰给正倍数 $J(\Phi_{ji})$；另一个位置输出在不同块 $ij$，不能抵消。若 $t=0$，改用第二位置的 $ij$ 即可。矩形 Choi 判据给所有转移 CP；标量输入同样成立。逆向由一腿 CP 与非负和立即得到。证毕。

上述选择 $A,B$ 的步骤复用 Benatti–Floreanini–Romano [BFR] Lemma 3 的相似于转置方法。该文 Theorem 3 是 **HP、TP、连续半群** $\gamma_\tau$ 的 $\gamma_\tau\otimes\gamma_\tau$ 正性与 CP 的等价；它不是 (82.10) 这个瞬时加权和命题。其生成元证明使用正交、迹零条件，本章对完整 HP 映射的带符号 Choi 二次型无须这些限制。不能把一般张量平方正性改称 CP：转置的张量平方就是整块转置，虽正却非 CP。整个输入锥的量词也不能被有限固定输入表偷换。

### 82.4 有限严格加权二份目录的精确障碍

**引理 82.6（所用成熟负参数去极化族）。** 固定单块 $d\ge2$，$U$ 酉，$0<\eta<d-1$。令
$$
\Phi_{\eta,U}(X)=\frac{d\operatorname{Tr}(X)I_d-(1+\eta)UXU^*}{d^2-1-\eta},\quad
w=\operatorname{vec}U/\sqrt d,\quad c_\eta=d^2-1-\eta. \tag{82.12}
$$
它是严格改善正性的 TP、保单位、非 CP 正映射，且其幂收敛于 $\mathcal R(X)=\operatorname{Tr}(X)I_d/d$；映射及其伴随的固定 Hermitian 空间都只有标量。其 Choi 为
$$
J(\Phi_{\eta,U})=\frac d{c_\eta}\bigl[I-(1+\eta)ww^*\bigr], \tag{82.13}
$$
沿 $w$ 的特征值为 $-d\eta/c_\eta<0$。

**证明。** $c_\eta>0$。对非零 $X\ge0$，$UXU^*\le\operatorname{Tr}(X)I$，故分子至少为 $(d-1-\eta)\operatorname{Tr}(X)I>0$。取迹及代入 $I$ 分别给 TP 与保单位。$\mathcal R$ 的 Choi 为 $I/d$，酉共轭的 Choi 为 $dww^*$，故得 (82.13) 与非 CP。
令 $q=-(1+\eta)/c_\eta$，则
$$
\Phi_{\eta,U}=(1-q)\mathcal R+q\operatorname{Ad}_U,\qquad
\Phi_{\eta,U}^{\,N}=\mathcal R+q^N\operatorname{Ad}_{U^N}(\operatorname{id}-\mathcal R). \tag{82.14}
$$
由 $\eta<d-1$ 得 $2+2\eta<2d\le d^2$，故 $|q|<1$。$\operatorname{Ad}_U$ 及其伴随在迹二范数上等距，零迹空间的谱半径为 $|q|<1$；固定空间遂均只有标量，并得到幂收敛。这里“混合”只指这个有序空间正映射的幂收敛，**不是**把它称为量子通道或实际量子过程。该族是酉共轭下的标准负参数去极化映射；不把映射族或其阈值当作新数学。证毕。

**引理 82.7（有限坏子空间不能占尽酉矩阵）。** 给 $M_d(\mathbb C)$ 的有限个真复线性子空间，总有酉 $U$ 的 $\operatorname{vec}U$ 不属于它们的并。

**证明。** 酉群 $U(d)$ 是连通实解析流形：每个酉经谱分解写为 $V\operatorname{diag}(e^{i\theta_j})V^*$，把角度连续缩到零给路径；通常矩阵坐标给实解析结构。酉矩阵的复线性张成是整个 $M_d$。具体地，若 $D_j$ 是只在第 $j$ 个对角元为 $-1$ 的对角酉，则 $E_{jj}=(I-D_j)/2$；左乘一个将 $e_j$ 送到 $e_i$ 的置换酉，就把它变成 $E_{ij}$，仍为两个酉的线性组合。
对每个真子空间取一个非零复线性泛函 $\ell$，使该子空间包含于 $\ker\ell$。实解析函数 $U\mapsto|\ell(\operatorname{vec}U)|^2$ 不恒零，否则违背上述张成。连通实解析流形上的恒等原理使其零集无内部；它又闭，故为闭无处稠密集。有限个这样的集合不能覆盖非空流形：在任意非空开集依次删去一个闭无内部集，总还能选取非空开子集。因而可同时避开全部子空间。证毕。

**定理 82.8（任何固定有限严格加权 PSD 目录都不能认证 CP）。** 固定 $d\ge2$，任取有限个、事先独立于待测映射指定的 $\rho_l\ge0$ 于 $\mathbb C^d\otimes\mathbb C^d$，以及 $0<t_l<1$。允许 $\rho_l$ 纯、混合、秩亏、满秩、未归一或为零。存在引理 82.6 的正 TP、保单位、混合、标量固定效应而非 CP 映射，使
$$
\mathcal K_{2,t_l}(\Phi_{\eta,U})(\rho_l)\ge0\qquad\text{对每个 }l. \tag{82.15}
$$
严格的是平均权重，不是输入态的混合度。即使加入任意有限个纯探针，结论仍成立。

**证明。** 对每个非零 $\rho_l$ 作有限谱分解，把其正特征值吸收进非零矩阵 $X$，写成若干 $|\operatorname{vec}X\rangle\langle\operatorname{vec}X|$ 之和。这只是在证明中分解给定正元，不宣布这些谱项是原准备或可调用分支。只须找同一 $U,\eta$ 使这个有限列表的每个纯分量通过其所属权重测试。
令 $\mathsf S$ 为两因子交换酉，对列表中每个 $X$ 置
$$
A_X=I\otimes X^T,\qquad B_X=\mathsf S(I\otimes X),\qquad
S_X=\operatorname{Ran}A_X+\operatorname{Ran}B_X.
$$
对任意 HP 映射的 Choi 矩阵 $C$，向量化和交换恒等式给纯输入的准确输出
$$
\mathcal K_{2,t}(\Phi)(|\operatorname{vec}X\rangle\langle\operatorname{vec}X|)
=tA_XCA_X^*+(1-t)B_XCB_X^*. \tag{82.16}
$$
其中第一项来自 $\operatorname{vec}X=(I\otimes X^T)\operatorname{vec}I$；交换后的输入为 $\operatorname{vec}(X^T)$，再交换输出恰给第二项。没有转置错配或输入生成假设。
先在 $\eta=0$ 的 CP 边界取 $C$ 的正倍数 $P=I-ww^*$。记
$$
\begin{aligned}
Y_X&=tA_XPA_X^*+(1-t)B_XPB_X^*,\\
Z_X&=tA_Xww^*A_X^*+(1-t)B_Xww^*B_X^*.
\end{aligned} \tag{82.17}
$$
因为 $t,1-t>0$，
$$
v\in\ker Y_X\quad\Longleftrightarrow\quad
A_X^*v\in\mathbb Cw\ \text{且}\ B_X^*v\in\mathbb Cw. \tag{82.18}
$$
若 $X$ 奇异，$A_X^*=I\otimes\overline X$、$B_X^*=(I\otimes X^*)\mathsf S$。这两个像空间的向量反向量化后秩都不超过 $\operatorname{rank}X<d$，而酉 $U$ 满秩，所以 $w$ 不属于任何一个像。于是 (82.18) 迫使两项都为零，恰得 $\ker Y_X=S_X^\perp$。这对每个酉 $U$ 都成立，无须一般位置假设。
若 $X$ 可逆，则 $A_X,B_X$ 可逆。对非零 $v$，(82.18) 等价于 $w$ 是
$$
T_X=B_X^*(A_X^*)^{-1}
$$
的特征向量：先写 $v=c(A_X^*)^{-1}w$，其中 $c\ne0$，再代入第二条件。$T_X$ 不是标量；否则 $B_X$ 为 $A_X$ 的标量倍数，右乘 $I\otimes X^{-1}$ 将迫使 $\mathsf S=I\otimes R$。但 $\mathsf S(e_i\otimes e_j)=e_j\otimes e_i$，在 $i\ne j$ 时改变第一因子，而 $I\otimes R$ 不会，矛盾。
每个非标量复矩阵的特征向量集是有限个真特征子空间的并。列表有限，引理 82.7 因而允许选择同一酉 $U$，使 $w$ 避开所有可逆 $X$ 的这些坏子空间。于是它们的 $Y_X$ 核为零；其 $S_X$ 也为全空间。结合奇异情形，所有非零分量统一满足
$$
\ker Y_X=S_X^\perp. \tag{82.19}
$$
现已固定 $U$。$Y_X$ 在非零有限维 $S_X$ 上严格正，令其最小特征值为 $\lambda_X>0$。$Y_X,Z_X$ 均自伴，像包含于 $S_X$，且消去 $S_X^\perp$，所以没有离开结构支撑的交叉项。选同一
$$
0<\eta<d-1,\qquad \eta\|Z_X\|<\lambda_X
\quad\text{对所有 }Z_X\ne0\text{ 的分量}. \tag{82.20}
$$
有限性保证这种正 $\eta$ 存在；$Z_X=0$ 不加限制。每个 $Y_X-\eta Z_X$ 在 $S_X$ 正，在补空间为零。由 (82.13)、(82.16)—(82.17)，实际测试输出恰是 $(d/c_\eta)(Y_X-\eta Z_X)\ge0$。逐 $\rho_l$ 求这些正分量之和便得 (82.15)；零输入直接成立。若目录没有非零输入，任取酉及 $0<\eta<d-1$ 即可。引理 82.6 同时保证所需非 CP、正性、TP、保单位、混合及固定空间性质。证毕。

**信息与适用域边界。** 定理只否定“有限个 $\mathcal K_{2,t_l}(\Phi)(\rho_l)\ge0$ 的合取即可推出 CP”。它**不**否定有限信息完备过程层析：一组张成输入的完整矩阵输出可以确定映射，再以跨输出的线性关系重构 $J(\Phi)$ 并检验 PSD；这种额外关系不是逐输出 PSD 合取。例如在该单块上，若完整输出已确定 $T=\mathcal K_{2,t}(\Phi)$，令 $\beta=\operatorname{Tr}[T(I\otimes I)]/d=\operatorname{Tr}\Phi(I)$，则 $t>0$ 时
$$
\Phi(X)=\frac{\operatorname{Tr}_2[T(X\otimes I)]-(1-t)\beta X}{td}.
$$
这是利用输出间关系的线性重构，不是仅检查每个输出的 PSD，也不供应任何实际制备。
本障碍也不覆盖权重端点、按 $\Phi$ 反选见证、已带标签的实际单腿分支、额外实际控制、任意有类型过程或资源最优性。端点上一个 Bell 输入已是普通 Choi 测试，故严格权重不可删。$\eta$ 依赖给定目录及其支撑间隙，不给跨目录统一扰动半径。
本障碍只在一个 $M_d$、$d\ge2$ 上建立，足以反驳适用于全部允许原模型的普遍有限二腿替换规则。全经典直和上正性已经等于 CP；这里没有证明一般直和上的混合非 CP 反模型扩张。全扇区三腿证书 82.3 则没有这个单块限制。

### 82.5 一个 Bell 控制与原质量候选中的反模型范围

**命题 82.9（固定对称 Bell 测试的简单控制）。** 在 $d=2$ 上取 Pauli 矩阵 $\sigma_y$，$1/4<h<1/2$，令
$$
\Phi(X)=\operatorname{Tr}(X)I_2/2-ih[\sigma_y,X]. \tag{82.21}
$$
它为正 TP、保单位、混合、标量固定效应的非 CP 映射，但对 $\Omega=|\Omega\rangle\langle\Omega|$、$|\Omega\rangle=(|00\rangle+|11\rangle)/\sqrt2$，
$$
\mathcal K_{2,1/2}(\Phi)(\Omega)=I_4/4.
$$

**证明。** Bloch 向量被送到 $2h(e_y\times r)$，其范数至多 $2h\|r\|$，且 $2h<1$。故态球映入内部，映射正；迹与单位直接保持，零迹子空间上幂收敛于零，固定效应只有标量。Choi 的重置部分为 $I_4/2$。令 $f=(\sigma_y\otimes I)|\Omega\rangle$，则 $f\perp\Omega$、$\|f\|=1$；其余部分为 $-2ih(|f\rangle\langle\Omega|-|\Omega\rangle\langle f|)$。因此 Choi 特征值为 $1/2\pm2h,1/2,1/2$，有负值。另一方面 $(\sigma_y\otimes I+I\otimes\sigma_y)|\Omega\rangle=0$，平均对易子项消失，两腿重置均送 $\Omega$ 到 $I_4/4$。这只击破该固定 Bell 测试，不击破定理 82.5 的整个二份锥。证毕。

定理 82.8 的映射以及命题 82.9 可放在已付标准归一元组
$$
A=H_d,\quad D=H_{d^2},\quad E=H_{d^3},\quad
L(d,c)=d\otimes c,\quad p=\operatorname{Tr}_1,\quad\omega=I_{d^2}/d^2.
$$
它的 PRE、NB、$\mathrm A_0$ 及全态全效应域直接按第四卷 65.11、66.7 的零方向单位滤波逆向和第 79 章复用。同一个 $p$ 两次实际给 $K(a)=I_d/d\otimes a$、$M(a,b)=a\otimes b$、$Q(a,b,c)=a\otimes b\otimes c$，未独立供应 $M$。两个质量已为乘积迹，故任何上述 TP 映射均满足 79.5；其固定效应条件亦成立。这样得到的是该元组中 **CP 接口** 的反模型，不是整个 $\Omega$ 的反模型，也没有供应一个实际非 CP 程序。82.8 的有限输出全正不使其二份延拓全锥正；82.5 保证仍有未列入目录的负输出方向。标量质量、有限逐输出 PSD 与完整过程合法性因而是不同关系。

### 82.6 只替换同事件 CP 入口，不能供应单腿控制

**定义 82.10（原同事件平均提升）。** 先在 (80.14) 或定义 79.14 的完整归一化原数据上，由既有定理得到 (79.17) 的普通 $M,L,p$。取一族已指定的原同载体事件 $e:A\to A$，逐个固定其实际实线性映射 $\Phi_e$、分支标签、完整记录及原定义域，不把它识别为第 79 章存在量化的校准见证 $\Phi_{\rm cal}$。对于每个 $e$，另须供应同一事件的实线性三份提升 $P_{E,e}$，满足所有原实输入上的精确关系
$$
\begin{aligned}
P_{E,e}Q(a,b,c)={}&\alpha_{e,1}Q(\Phi_e a,b,c)
+\alpha_{e,2}Q(a,\Phi_e b,c)
+\alpha_{e,3}Q(a,b,\Phi_e c),\\
&\alpha_{e,\ell}\ge0,\qquad\sum_\ell\alpha_{e,\ell}=1.
\end{aligned} \tag{82.22}
$$
这是同事件、同原对象、同全实载体的 intertwining，不能由只在已准备样本、密度相同或矩阵综合上的相等替代。原 $Q$ 实张满整个 $E$，所以普通坐标中它唯一规定 $P_{E,e}=\mathcal K_{3,\alpha_e}(\Phi_e)$。线性唯一性不供应各平均加项作为分别可调用的实际分支，不供应随机开关、GHZ 输入或物理滤器。

**定理 82.11（同事件 CP 的等价证书与递归正性的冗余）。** 在定义 82.10 的同一增广数据上，逐事件有
$$
P_{E,e}(\Xi)\ge0\quad\Longleftrightarrow\quad\Phi_e\text{ CP}
\quad\Longleftrightarrow\quad P_{E,e}\text{ 全锥正}. \tag{82.23}
$$
若同一事件另给推论 79.8 形式的精确全实递归律
$$
\begin{aligned}
P_{D,e}M(a,b)&=t_eM(\Phi_ea,b)+(1-t_e)M(a,\Phi_eb),\\
P_{E,e}L(d,c)&=s_eL(P_{D,e}d,c)+(1-s_e)L(d,\Phi_ec),
\qquad 0\le t_e,s_e\le1,
\end{aligned} \tag{82.24}
$$
则 $P_{D,e}$ 全锥正已迫使 $\Phi_e$ CP，继而已唯一确定的 $P_{E,e}$ CP；因此在这些确切前件下，另列 $P_{E,e}$ 全锥正是冗余的。这里不从单独的质量关系推断 (82.24)。

**证明。** 实张成与普通张量律把 (82.22) 唯一变成 (82.2)，82.3 给第一组等价。(82.24) 的第一式同样使 $P_{D,e}=\mathcal K_{2,t_e}(\Phi_e)$；由 82.5，其全锥正给 $\Phi_e$ CP。第二式及 $Q$ 张成再唯一给三腿权重 $(s_et_e,s_e(1-t_e),1-s_e)$，CP 蕴含该非负和 CP。反之对既有全实提升，CP 同时使二份、三份提升全锥正。没有为局部映射增加 TP 或遍历前提，也未把不存在的实际平均操作从数学存在式中生成。证毕。

原过程的 TP、TNI、质量和完整菜单条件继续独立保留；正性冗余不删除它们。尤其第 79 章的 $\Phi_{\rm cal}$ 可以只是数学存在见证，不能因为它有某个正平均，就把每个任意原事件 $e$ 替换成它。

**推论 82.12（未经校准的正合同只给精确等价）。** 若先只用 PRE+NB 得同时普通方向，复用第四卷 (66.15)—(66.16)、(69.2)：
$$
\begin{gathered}
M=C_Dm,\quad Q=C_Eq,\qquad m(a,b)=a\otimes b,\quad q(a,b,c)=a\otimes b\otimes c,\\
(C_DX)_{ij}=S_{ij}X_{ij}S_{ij},\quad S_{ij}=I_i\otimes\sqrt{u_{ij}},\\
(C_EZ)_{ijk}=T_{ijk}Z_{ijk}T_{ijk},\quad
T_{ijk}=I_i\otimes\sqrt{u_{ij}}\otimes\sqrt{g_{ijk}},\quad u_{ij},g_{ijk}>0.
\end{gathered}
$$
满足同一全实平均律的提升唯一为 $C_D\mathcal K_2C_D^{-1}$、$C_E\mathcal K_3C_E^{-1}$。$C_D,C_E$ 是可逆 CP 合同，其逆也 CP 且全锥正；逆逐块分别夹乘 $S_{ij}^{-1}$、$T_{ijk}^{-1}$，由正定性确实存在。因此整个二份正性判据仍有效，三份则可测试
$$
\Xi_{\rm raw}=C_E\Xi/Z,\qquad Z=u_E(C_E\Xi)>0.
$$
其输出为 $Z^{-1}C_E\mathcal K_3(\Phi)(\Xi)$，故输出 PSD 仍等价于 CP。证明只需把全实平均律分别左乘 $C_D^{-1},C_E^{-1}$，用乘积实张成给唯一性；可逆正合同保持且反映 PSD，给全部等价。此处没有把 $\Xi_{\rm raw}$ 当成已供应物理准备或把滤波当成实际操作。
若原输出只满足 $P_E(\Xi_{\rm raw})\ge-\epsilon I$，退滤波只能先给 $\mathcal K_3(\Phi)(\Xi)\ge-Z\epsilon C_E^{-1}(I)$。不控制 $Z$ 与逆滤波范数就不能移植 (82.9) 的归一常数。本章的定量界限于其明确普通总迹规范。证毕。

### 82.7 完整候选及原量子消费者

**定义 82.13（保留完整原模型的候选）。** 静态部分直接取已有 (80.14)：$\mathrm{PRE}_0^{\rm mix}+\mathcal D=0+\mathsf{Mass}_{t,s}+\mathrm A_0+\mathrm H13$，$t,s\in(0,1)$；它已与原 PRE+$C_{\rm joint}$+C13 同数据等价，不外加新的生成框架输入。也可取定义 79.14 的完整版本：每个原 $A,D,E$ 的整个态基与全部效应、完整纯参照有限混合比较 $S$ 及一般 EJA 忠实桥，或精确 77.16、77.18—77.19 的全部回路／任意混合余项入口；两层完整 $D_J,D_H$，或精确 75.4、76.3、78.4 的生成同标框架入口；全锥正的原 $L,p$、两实张成、同一个 $p$ 连用两次、原 $\omega$、全实 $Z$；原 NB 或 H13 的完整活跃／非活跃及零质量量词；79.3 的局部校准见证、两条全正质量关系和原 $\mathrm A_0$。这些是既有候选的等价版本，不能缩为纯二元比较或固定有限目录。
在这同一原静态元组上，只对**已经另供定义 82.10 同事件平均提升**的同载体 $A\to A$ 事件族，把原逐事件 CP 认证谓词换成 (82.23) 的固定探针输出正。提升精确全实律、事件本身及其全部源合同仍是前件。82.11 证明的是这份共同增广数据上的等价 CP 证书；不声称旧 CP 谓词单独生成新的实际提升或探针。其他类型的原事件全部继续使用其原 CP／实际参考入口。原实际关联联合、参考、副本、全部控制与权限不因换证书而丢失。

**推论 82.14（候选的准确替换范围）。** 定义 82.13 在其同一供应数据和全量词上恢复原静态结论与被覆盖同载体事件的 CP；保留其余原操作前件时，恢复相应量子消费者。它只替换所指定 CP 入口，不推出更多份、另一括号、任意有类型过程来源或完整 $\Omega$。

**证明与消费者。** 80.14 或 79.15 首先给同一原 PRE、校准和 C13，故复用第四卷 66.3、66.8—66.10 及本卷 (79.17)、(79.27)：
$$
\begin{gathered}
A=\bigoplus_iH_{n_i},\quad D=\bigoplus_{i,j}H_{n_in_j},\quad
E=\bigoplus_{i,j,k}H_{n_in_jn_k},\\
\rho_i\ge0,\quad\sum_i\operatorname{Tr}\rho_i=1,\quad0\le f_i\le I_i,\qquad
\Pr(f\mid\rho)=\sum_i\operatorname{Tr}(f_i\rho_i),\\
M(a,b)_{ij}=a_i\otimes b_j,\quad L(d,c)_{ijk}=d_{ij}\otimes c_k,\quad
(pz)_{jk}=\sum_i\operatorname{Tr}_iz_{ijk},\quad
(p_{13}z)_{ik}=\sum_j\operatorname{Tr}_jz_{ijk}.
\end{gathered}
$$
单块纯态为复射影空间、模方 Born、不同中心块比较为零，均是已有结论。82.11 才在同事件全实提升上把固定三份 PSD 换成其 CP，没有借旧 Born／CP／QC 反推源。
逐输入输出块 CP 给矩形 Kraus，但接到实际仪器仍须原有类型分支、同事件参考或 intertwining、真实记录及预算。对第 69 章固定旁观者族，未校准时完整保留局部／原联合两预算
$$
\sum_{a,j}F^a_{ji}\le I_i,\qquad
\sum_{a,j}F^a_{ji}\otimes u_{jk}\le I_i\otimes u_{ik},\qquad
F^a_{ji}=\sum_\ell K_{a,ji,\ell}^*K_{a,ji,\ell};
$$
完整菜单两边总 TP 时取等号；本候选已校准 $u=I$ 时相合为每个输入 $i$ 的 $\sum_{a,j,\ell}K_{a,ji,\ell}^*K_{a,ji,\ell}=I_i$。实际顺序复合、真粗粒化、共同重置补全各按 69.1—69.11、73.9 原域，不能从某个平均全正供应单独加项的可调用性。
结果概率仍为原未归一输出质量；只有严格正质量才可除以它作条件态。零质量分支及记录、标签和未来权限照旧保留。Lüders 另需同一 CP 分支有锐投影效应且对每个确定接受态逐点不变；效应、CP、重复性或完备性本身不唯一指定更新。
Hamiltonian 另需原物理时钟参数上的连续、时间齐次、可逆 $*$ 自同构群。连续性固定离散中心后，有限矩阵块才得到 $\dot\rho_i=-i[H_i,\rho_i]/\hbar$，$H_i$ 仍有加标量自由度；时间／能量单位及 $\hbar$ 的物理对应由原动力学源承担。82.7 的三腿是给定三份系统的证书，不识别独立另一括号，不供应四份以上相容性或时间动力学。证毕。

### 82.8 白话、成熟来源和未构造的原接口

**完整普通解释。** 一个事件在单独系统上把所有正元送成正元，仍可能在与参考相关联时露出负值；完全正性就是要排除这种错误。若只能看到“同一个事件随机落在某一位置”的平均，两个位置产生的坏方向可以互相遮住。看遍所有二份输入依然能找出它：按照想检测的矩阵，选择一对相似转置所连接的输入和读出，让两项恰好暴露同一个坏读数。但这个输入一般随待找坏方向而变，不能直接改成预先固定的有限表。
三份提供了另一种几何。用三个相同标签叠加的一个指定数学态，再把每个非对角矩阵元放进“一个不同标签在三个位置轮换”的三个互不重叠坐标。无论事件落在哪一腿，这个读出都得到同一个振幅，所以三个加项没有机会用不同方向互相遮掩。准确压缩后就是整个 Choi 矩阵，不只是它的迹或某几个校准值；连标签转移到不等维、标量扇区的块也被保留下来。因此一个固定三份数学正元就够，任意固定共同标架都可用。
有限二份目录的障碍不是说它没有信息。把完整输出保存下来，一组有限张成输入可以重建整个映射，再计算 CP；这里限制的是只问每个输出“是否 PSD”。证明从一个成熟的 CP 边界映射出发，其 Choi 只有一个零方向。对任何有限输入表，可选择一个酉方向，使两位置输出的零方向不会额外重合；奇异输入不可避免的零空间也被原封不动保留。然后沿该方向推入一点负值，每个目录输出仍然正，但完整 Choi 已负。小量取决于整张目录，没有统一误差额度。这说明平均输出分别合格并不等于原事件对所有参考合法；也不说明三份准备、实际控制或资源更容易获得。
原归一化质量定理解决倍率，本章解决指定事件的 CP 证书，两者不是同一件事。数学上写出一个三份态和一个平均式，仍没有造出这份准备，也没有把其中每条单腿过程变成可调用分支；真实来源必须逐事件给同一个对象、同一个完整记录和同一条全实关系。

**成熟来源与增量范围。** [C] M.-D. Choi，*Completely positive linear maps on complex matrices*，Linear Algebra and its Applications **10** (1975), 285–290，[DOI](https://doi.org/10.1016/0024-3795(75)90075-0)；A. Jamiołkowski，*Linear transformations which preserve trace and positive semidefiniteness of operators*，Reports on Mathematical Physics **3** (1972), 275–278，[DOI](https://doi.org/10.1016/0034-4877(72)90011-0)。矩形 Choi／Kraus、谱分解和迹预算直接沿[Watrous 条目](../../../Library/Quantum/watrous2018theory.md#complete-channel-representations)的 Theorems 2.22、2.26 及第四卷 69.2—69.4 使用，不计为新增结果。
[BFR] F. Benatti、R. Floreanini、R. Romano，*Complete positivity and dissipative factorized dynamics*，[arXiv:quant-ph/0208023v1](https://arxiv.org/abs/quant-ph/0208023v1)，pp.4—6 的 Theorem 3、Lemmas 1—3、Remarks 4；Journal of Physics A **35**(39) (2002), **L551–L556**，[DOI](https://doi.org/10.1088/0305-4470/35/39/101)。相似于转置的输入／读出配对方法归于该文；其半群和生成元条件不得省略后再把本章瞬时和命题归为该文原定理。
[F] G. M. D’Ariano、P. Lo Presti，*Imprinting Complete Information about a Quantum Channel on its Output State*，Physical Review Letters **91** (2003), 047902，[DOI](https://doi.org/10.1103/PhysRevLett.91.047902)，为信息完备探针的背景；它不等于逐输出 PSD 合取。负参数去极化族、矩阵相似、酉群实解析结构与有限真子空间规避都是成熟工具。新增仓内纸面综合是 (82.4) 的精确三腿压缩、其全扇区与定量连接、以及借结构支撑和有限坏子空间规避得到的 82.8 与其原 CP 接口边界；不主张优先权、全球新颖性或文献穷尽。
[R] [第四卷 §§65—72](QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_IV.md)与本卷 §§73—80 的完整静态分类、原两次同 $p$ 恢复、下降、参考、递归支撑、原 $D$ 恢复、操作预算与质量／方向入口，均按各自已证纸面域复用。尤其 80.14 是已有更简洁完整归一化候选，本章没有重复其证明，也没有把固定标架探针称作自然原态。

**原来源的已得部分与未得部分。** [原观察卷 §§23—24](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ORIGINAL_INTERFACE_EXPOSURE_AND_RECOVERY.md)的原 $G_V$ 进展域已经取得实际有序操作数、独立 guard、真实下一 Entry、完整原绑定、原 Plan／Send、服务返回、历史批次、HandbackResume、Stop／验证／消费与共同 INITIAL 终端答案。[第二卷 §9](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ORIGINAL_INTERFACE_EXPOSURE_AND_RECOVERY_II.md#9-attribution-and-the-remaining-recovery-problem)在其两种新安装模式、有限已达 completed canonical GuardAcquired 边界上取得实际当前调用恢复；完整过去 capture/use 历史保留。已有下降、参考、递归支撑、原 $D$ 恢复及[有限返回卷 §165](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md)的条件完整图正常完成，各按原准确域保留，不把它们倒称全缺失，也不外推 Busy、部分切口、无新 boot 或无限重复统一资源。
[固定来源卷 (23.7)](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md)所需原具名 analyzer 当前接受接口证书，及[有限返回卷 164.1](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md)中原 $B_r$ 到 active-ready 的接头，仍未由本章构造。该卷 162 的七项消费者与其完整递归来源合同继续保留。矩阵相等、纯校准、操作逆字、存在菜单、数学谱分解、矩阵综合、静态密度或扩大源的候选返回均不能供应这两个原接头，更不能以密度相同识别历史。
完整原 $\Omega$ 的全部准备、事件、过程、参考、副本、实际相关联合、零及不等质量、原时钟与单位、控制、ready／flags、完整记录、失败、停止、销毁、返回、未来，以及旧全菜单、固定支撑和每个已量化中间切口义务一项不减。没有免费准备生成、复制、相干控制或实际彩票。本章不声称形式内核认证、物理资源减少、最少独立公理或完整量子起源目标完成。

## 追加锚（本行以下为增补区）

## 83. 显式二阶对角权的乘积平均与 Pythagorean 完整候选

本章第 65—72 章指第四卷，第 73—82 章指本卷。第 81 章的同框架平均保留其原定义；这里另用两个几何积分变量，独立证明一个不同标量具有同一完整原 PRE 零集。候选的定义只使用原源的显式二阶对角权与两个 Hilbert–Schmidt 范数，不再使用四阶框架相关矩、循环张成空间或极值。

### 83.1 完整原域与显式对角权

**定义 83.1（同一原基底的固定对半入口）。** 完整保留定义 80.1 的 $\mathrm{PRE}_0^{\rm mix}$ 的全部原对象与其他谓词，只将比较主入口取为下述 FH1，记所得同类基底为 $\mathrm{PRE}_0^{1/2}$。具体地，每个 $X=A,D,E$ 非零有限维，具有闭尖生成锥 $X_+$、在非零正元上严格正的 $u_X$、整个紧态基 $K_X=\{x\in X_+:u_X(x)=1\}$、全部 proper 效应 $[0,u_X]$ 及纯态集 $P_X=\operatorname{ext}K_X$。对全部纯 $\xi,\eta\in P_X$ 及全部原混态 $x\in K_X$，要求
$$
T^X_\xi(x)=\inf\{f(x):0\le f\le u_X,\ f(\xi)=1\},\qquad
T^X_\xi\!\left(\frac{\eta+x}{2}\right)=\frac{T^X_\eta(\xi)+T^X_\xi(x)}2.
\tag{83.1}
$$
先应用固定来源 [FH] 的同载体完整定理 $\mathrm B_{1/2}\Longleftrightarrow S\Longleftrightarrow\mathrm B_{\rm mix}$，在每个原 $X$ 上恢复全部实 $t\in[0,1]$ 的纯端加混态比较律与完整有限混合律 $S$，再复用同一一般有限 EJA 条件纸面桥；正对偶生成、忠实态效应对应、共同框架、面投影、项目性与滤波纯性等义务全部保留。这里仅应用已有固定对半证明，不将它计作本章新数学；混态余项遍及整个原态基，不能缩为纯二项 $S_2$。忠实坐标中 $u_X=\tau_X$，原态基、效应区间、单位和比较配对均被保留。允许异型直和、秩一及 Albert，不预设复型、不可约性或 $\mathsf{JG}_3$。
唯一供应的映射仍为全锥正实双线性 $L:D\times A\to E$ 和同一个全锥正实线性 $p:E\to D$，原参考 $\omega=1_D/\tau_D1_D$；正性覆盖全部原联合锥，包括纠缠方向。定义
$$
\begin{aligned}
K(a)&=pL(\omega,a),&M(a,b)&=pL(K(a),b),&J(a)&=M(a,1_A),\\
H_{\rm s}(d)&=L(d,1_A),&B_1&=pH_{\rm s},&U&=M(1_A,1_A),\quad G=H_{\rm s}1_D,\\
F&=P_{U^{-1/2}}M,&\mathcal T&=H_{\rm s}\widetilde F:A\otimes_{\mathbb R}A\to E.
\end{aligned}\tag{83.2}
$$
保留 $\operatorname{span}_{\mathbb R}M(A,A)=D$、$\operatorname{span}_{\mathbb R}L(D,A)=E$ 和全部实 $a,b$ 上的 $Z:B_1M(a,b)=\tau_A(a)Jb$。两次读回均为这一个 $p$，不能独立供应 $M$。正性及两实张成先给 $U,G>0$，故零关系之前 $F$ 已正且 $F(1_A,1_A)=1_D$；这里使用 75.2／80.1 的先行内点结论。

**定义 83.2（只由原源确定的权）。** 写原中心简单理想分解 $A=\bigoplus_iA_i$，单位为 $1_i$，规范迹为 $\tau_i$，秩、实维数为 $r_i,d_i$。令 $n=\tau_A1_A=\sum_i r_i$，并在原迹 Hilbert 空间中定义
$$
P_i a_i=\frac{\tau_i(a_i)}{r_i}1_i,\qquad P_i^0=I_{A_i}-P_i,\qquad
\mathsf C_i=\begin{cases}I_{A_i},&r_i=1,\\ P_i+\dfrac{r_i-1}{d_i-1}P_i^0,&r_i>1,\end{cases}
\qquad \mathsf C_A=\bigoplus_i\mathsf C_i,\quad \mathsf D_A=\mathsf C_A^{1/2}.
\tag{83.3}
$$
秩一简单因子为 $\mathbb R$，没有迹零项，不出现 $0/0$。在 $r_i>1$ 的因子上，$\mathsf D_i=P_i+\sqrt{(r_i-1)/(d_i-1)}P_i^0$。因此 $\mathsf C_A>0$；定义没有任意基框架、字典或未指定投影。因子重排不改变算子，且每个中央单位都是特征值一方向。

**定理 83.3（乘积平均的显式范数式）。** 对定义 83.1 的全部原模型，令
$$
\boxed{\mathcal Q_\times(z)=\|U\|_2^2+\|G\|_2^2
-\|J\mathsf D_A\|_{\rm HS}^2
-\|\mathcal T(\mathsf D_A\otimes\mathsf D_A)\|_{\rm HS}^2,\qquad z=(L,p).}
\tag{83.4}
$$
它非负，在固定原 EJA 三元组上连续，并在全部原数据共同按保原迹 Jordan 同构运输时不变。其证明中的积分表征如下：对完整无标签本原框架 $B,C$，置 $\Pi_B=\sum_{e\in B}|e\rangle\langle e|$，则
$$
\begin{aligned}
h_z(B,C)&=\|U\|_2^2-\sum_{e\in B}\|Je\|_2^2
+\|G\|_2^2-\sum_{e\in B,f\in C}\|H_{\rm s}F(e,f)\|_2^2,\\
\mathsf C_A&=\int\Pi_B\,d\nu_A(B),\qquad
\mathcal Q_\times(z)=\iint h_z(B,C)\,d\nu_A(B)d\nu_A(C).
\end{aligned}\tag{83.5}
$$
这里 $\nu_A$ 严格指投影轨道上的唯一不变全支撑概率；框架记号仅用于写其求和。乘积测度只作用于这两个数学变量，没有给原系统、制备、事件或 $L,p,\omega$ 增加物理独立性。

**证明。** 81.2 的完整无标签投影轨道非空紧，$\operatorname{Aut}_J(A)$ 为紧正交群且在该轨道上传递。其准确一般直和理由是：每个本原幂等元位于一个简单理想，每套完整框架在该理想内恰有 $r_i$ 项；逐因子用简单 EJA 的完整框架传递性即可，不需要跨异型因子的有序框架或纯态传递性。Haar 推前的唯一性及全支撑沿 81.2，乘积概率同样全支撑。
为核实 (83.3) 的范围，逐因子应用 81.4 的论证：平均投影固定 $1_i$、自伴且与自同构交换。简单因子的迹零表示不可约，因为非零不变子空间内的非零谱系数，经同一框架的所有排列，其差张满迹零对角空间；再运输谱框架便得到全部迹零元。这里所需的有序框架传递性只在简单因子使用。自伴平均算子的特征空间因而迫使迹零部分为标量；$\operatorname{Tr}\Pi_B=r_i$ 给 $1+c(d_i-1)=r_i$。每个 $\Pi_B$ 已按原理想块对角，故无跨理想项；同型因子置换也不改变结果。这是 (81.9) 的复用，不增加不可约性假设。Albert 的 $r=3,d=27$ 给迹零权 $1/13$，不使用八元数的结合矩阵表示。
对每个 $B,C$，$(Je)_{e\in B}$ 是 $U$ 的正分解，$(H_{\rm s}F(e,f))_{B\times C}$ 是 $G$ 的正分解，因为双重和为 $H_{\rm s}F(1,1)=G$。每个缺陷均为不同部分之全部交叉内积的两倍，由自对偶性非负；此时不要求 $F(e,f)$ 幂等。
框架原子在原迹内积下正交归一，故两平方和分别为 $\operatorname{Tr}(J^*J\Pi_B)$、$\operatorname{Tr}(\mathcal T^*\mathcal T(\Pi_B\otimes\Pi_C))$。有限维 Fubini 给 $\iint\Pi_B\otimes\Pi_C=\mathsf C_A\otimes\mathsf C_A$，再用 $\|XS\|_{\rm HS}^2=\operatorname{Tr}(X^*XS^2)$ 得 (83.4)。这里 $\operatorname{Tr}$ 为实 Hilbert 空间的算子迹，与 Jordan 迹 $\tau_X$ 区分。连续性来自 $U>0$ 上二次表示与逆平方根的连续性；共同同构保持全部原迹、派生映射和 (83.3)，给不变性。证毕。

### 83.2 独立的零集证明与几何边界

**定理 83.4（完整原零集）。** 在同一完整原基底中，
$$
\boxed{\mathcal Q_\times=0\quad\Longleftrightarrow\quad\mathcal D_{\rm old}=0
\quad\Longleftrightarrow\quad \bigl(D_J\ \&\ D_H\bigr).}\tag{83.6}
$$
$\mathcal D_{\rm old}$ 指 (80.2)，并写 $q_{\rm old}(B)=h_z(B,B)$；$D_J,D_H$ 保持原全部正交正元对的量词，特别是整个纠缠锥上的第二层量词。

**证明。** 先明确逐点分解与正表的行列关系。对任意完整原框架 $B,C$，令
$$
\begin{aligned}
q_J(B)&=\|U\|_2^2-\sum_{e\in B}\|Je\|_2^2,\\
x_{ef}&=H_{\rm s}F(e,f),\qquad
 g_z(B,C)=\|G\|_2^2-\sum_{e\in B,f\in C}\|x_{ef}\|_2^2,\\
a(B)&=\|G\|_2^2-\sum_{e\in B}\|H_{\rm s}F(e,1_A)\|_2^2,\\
b(C)&=\|G\|_2^2-\sum_{f\in C}\|H_{\rm s}F(1_A,f)\|_2^2,\qquad
h_z(B,C)=q_J(B)+g_z(B,C).
\end{aligned}
$$
所有 $x_{ef}$ 属于原 $E_+$；行和为 $\sum_f x_{ef}=H_{\rm s}F(e,1_A)$，列和为 $\sum_e x_{ef}=H_{\rm s}F(1_A,f)$，总和为 $G$，故 $a(B),b(C)$ 分别就是此表的行、列缺陷，且与另一槽的框架无关。另因 $(Je)_{e\in B}$ 是 $U$ 的正分解，有 $q_J(B)\ge0$。

以下只在这里完整展开一次所需的有限正表恒等式。对自对偶锥内任意有限表 $x_{ij}$，令
$$
v=\sum_{i,j}x_{ij},\qquad r_i=\sum_jx_{ij},\qquad c_j=\sum_ix_{ij},
$$
并置
$$
\delta=\|v\|^2-\sum_{i,j}\|x_{ij}\|^2,\quad
\delta_{\rm row}=\|v\|^2-\sum_i\|r_i\|^2,\quad
\delta_{\rm col}=\|v\|^2-\sum_j\|c_j\|^2.
$$
按有序指标逐项展开，得到
$$
\begin{aligned}
\delta&=\sum_{(i,j)\ne(k,\ell)}\langle x_{ij},x_{k\ell}\rangle,\\
\delta_{\rm row}&=\sum_{i\ne k}\sum_{j,\ell}\langle x_{ij},x_{k\ell}\rangle,\qquad
\delta_{\rm col}=\sum_{j\ne\ell}\sum_{i,k}\langle x_{ij},x_{k\ell}\rangle,\\
\delta-\delta_{\rm row}&=\sum_i\sum_{j\ne\ell}\langle x_{ij},x_{i\ell}\rangle,\qquad
\delta-\delta_{\rm col}=\sum_j\sum_{i\ne k}\langle x_{ij},x_{kj}\rangle,\\
\delta_{\rm row}+\delta_{\rm col}-\delta
&=\sum_{i\ne k,\ j\ne\ell}\langle x_{ij},x_{k\ell}\rangle.
\end{aligned}
$$
每项内积因自对偶性非负，故
$$
0\le\delta_{\rm row},\delta_{\rm col}\le\delta\le
\delta_{\rm row}+\delta_{\rm col},\qquad
0\le a(B),b(C)\le g_z(B,C)\le a(B)+b(C).
\tag{83.6a}
$$
后一组不等式是把同一展开用于上述 $x_{ef}$。再分别在两槽取同一框架，得到 $a(B)\le g_z(B,B)$、$b(C)\le g_z(C,C)$，从而
$$
\begin{aligned}
h_z(B,C)&\le q_J(B)+a(B)+b(C)\\
&\le q_J(B)+g_z(B,B)+g_z(C,C)\\
&\le h_z(B,B)+h_z(C,C).
\end{aligned}
\tag{83.6b}
$$
这保留同一原 $F$、同一个 $p$ 两次、原纠缠锥上的全部正输入及两槽先后，不需要产品框架分类。

现在 $h_z$ 是完整投影对上的连续非负函数。若其积分零而某点严格正，连续性在某非空乘积开邻域给正下界，全支撑使积分严格正，矛盾。所以 $\mathcal Q_\times=0$ 迫使所有 $B,C$ 上 $h_z(B,C)=0$。取 $C=B$ 即有 $q_{\rm old}(B)=0$，故 $\mathcal D_{\rm old}=0$；对角线即使测度为零也无妨，因为取对角线发生在已经得到处处零之后。
反向，若 $\mathcal D_{\rm old}=0$，即非负函数 $q_{\rm old}$ 的最大值为零，则所有 $h_z(B,B)=0$，(83.6b) 给 $0\le h_z(B,C)\le0$，积分即给 $\mathcal Q_\times=0$。最后按 80.3 的原顺序，先 $D_J$、再第一接口、最后整个原 $D_+$ 上的 $D_H$，恢复同一完整 PRE，得到
$$
\mathcal Q_\times=0\quad\Longleftrightarrow\quad\mathcal D_{\rm old}=0
\quad\Longleftrightarrow\quad\bigl(D_J\ \&\ D_H\bigr).
$$
这里 $D_J,D_H$ 始终是原全量词谓词，未将它们定义成数值缺陷。证毕。

**推论 83.5（Pythagorean 等式的准确意义）。** 令 $S_z=\|U\|_2^2+\|G\|_2^2>0$，定义实 Hilbert–Schmidt 算子
$$
X_z=\operatorname{diag}\bigl(J\mathsf D_A,\mathcal T(\mathsf D_A\otimes\mathsf D_A)\bigr):
A\oplus(A\otimes_{\mathbb R}A)\longrightarrow D\oplus E,\qquad \Phi_z=X_z/\sqrt{S_z}.
\tag{83.7}
$$
全部原模型都有 $\|\Phi_z\|_{\rm HS}\le1$；零缺陷恰为其可实现派生像中的球面点，即
$$
\|J\mathsf D_A\|_{\rm HS}^2+\|\mathcal T(\mathsf D_A\otimes\mathsf D_A)\|_{\rm HS}^2
=\|U\|_2^2+\|G\|_2^2.\tag{83.8}
$$
**证明与范围。** (83.4) 给 $\|X_z\|_{\rm HS}^2=S_z-\mathcal Q_\times$，再用 83.4。该直接重写不是独立的新结构定理：原 $L,p$、同 $p$ 两次、$Z$、正性及 $F$ 的约束仍为原约束，未证明 $z\mapsto\Phi_z$ 满射到整球。原态正锥与效应区间没有被换成球或椭球。
第 81 章的 $\mathsf W_A=\int\Pi_B\otimes\Pi_B$ 仍是同变量相关矩。对简单 $A$ 且 $d>n>1$，81.10 的同一 $\Xi$ 给 $\langle\Xi,\mathsf W_A\Xi\rangle=n$，而 $\langle\Xi,(\mathsf C_A\otimes\mathsf C_A)\Xi\rangle=1+(n-1)^2/(d-1)<n$。本章改变被平均的非负函数及积分域，绝没有证明 $\mathsf W_A=\mathsf C_A\otimes\mathsf C_A$，也不把 $\mathcal Q_\times$ 与原 $\mathcal Q$ 视为同一标量。

### 83.3 最坏缺陷比较、共同原映射修复及有限证书

**定理 83.6（乘积域比较）。** 只为证明和误差界，令下列函数均限制在 83.3 证明中的完整无标签投影轨道上：
$$
V=\{\Pi\mapsto\operatorname{Tr}(R\Pi):R=R^*\in\operatorname{End}_{\mathbb R}(A)\},\quad
k=\dim V,\quad \mathcal D_{\rm pair}=\max_{B,C}h_z(B,C).
\tag{83.9}
$$
则 $1\le k\le d(d+1)/2$，$d=\dim_{\mathbb R}A$，并有
$$
\boxed{\begin{gathered}
0\le\mathcal Q_\times\le\mathcal D_{\rm pair},\\
\mathcal D_{\rm old}\le\mathcal D_{\rm pair}
\le\min\{2\mathcal D_{\rm old},\kappa\mathcal Q_\times\},\qquad
\kappa:=\min\{k^2,2k\}.
\end{gathered}}\tag{83.10}
$$
以下比较无需假定 $\mathcal Q_\times\le\mathcal D_{\rm old}$；这里也未证明或反驳这条额外不等式。全部原正交正元满足
$$
0\le\langle Ja,Jb\rangle_D\le\frac{\kappa\mathcal Q_\times}{2}\|a\|_\infty\|b\|_\infty.
\tag{83.11}
$$

**证明。** 83.4 的同一正表步骤 (83.6a)—(83.6b) 已在完整原域上给出 $h_z\ge0$、$0\le a,b\le g_z\le a+b$ 及 $h_z(B,C)\le h_z(B,B)+h_z(C,C)$；此处仍用同一原 $F$、同一个 $p$ 两次及全部纠缠正输入，不另选映射或缩小第二层量词。取平均给 $\mathcal Q_\times\le\mathcal D_{\rm pair}$，取对角给 $\mathcal D_{\rm old}\le\mathcal D_{\rm pair}$，对最后一个逐点上界取最大值得 $\mathcal D_{\rm pair}\le2\mathcal D_{\rm old}$。

为完整给出当前评价核的依据，由 $\operatorname{Tr}\Pi=n>0$，取 $R=I_A/n$ 可知常数一属于 $V$，而自伴算子空间的维数给 $1\le k\le d(d+1)/2$。原 Jordan 自同构的正交共轭保持投影轨道及 $V$，不变概率使其在 $V$ 上的作用保持 $L^2(\nu_A)$ 内积。全支撑保证该内积正定：连续函数若有某个非零值，便在一个正质量开集上平方严格正，故可取 $L^2$ 正交归一基 $f_1,\ldots,f_k$。评价核 $K(B,C)=\sum_{j=1}^k f_j(B)f_j(C)$ 的对角由群作用的传递性恒定，而其对角积分为 $\sum_j\int f_j^2=k$，所以 $K(B,B)=k$。乘积空间 $V\otimes V$ 的评价核为两个单变量核的乘积，对角为 $k^2$；由 (83.5) 的迹表达及常数属于 $V$，有 $h_z\in V\otimes V$，Cauchy–Schwarz 遂给
$$
\mathcal D_{\rm pair}^2\le k^2\iint h_z(B,C)^2
\le k^2\mathcal D_{\rm pair}\mathcal Q_\times.
$$
$\mathcal D_{\rm pair}=0$ 时结论直接成立，否则约去一个 $\mathcal D_{\rm pair}$ 得到原 $k^2$ 界 $\mathcal D_{\rm pair}\le k^2\mathcal Q_\times$。

还可得到同一比较定理内的行列强化。83.4 定义的 $q_J,a,b$ 都属于 $V$ 且逐点非负：它们分别是常数减去 $J^*J$、$(a\mapsto H_{\rm s}F(a,1_A))^*(a\mapsto H_{\rm s}F(a,1_A))$、$(a\mapsto H_{\rm s}F(1_A,a))^*(a\mapsto H_{\rm s}F(1_A,a))$ 在相应 $\Pi$ 上的评价。对任意逐点非负 $f\in V$，上述单变量评价核给
$$
\|f\|_\infty^2\le k\int f^2\le k\|f\|_\infty\int f,
$$
所以 $\|f\|_\infty\le k\int f$（零函数情形显然）。由 (83.6a)，
$$
\begin{aligned}
\mathcal D_{\rm pair}
&\le\|q_J+a\|_\infty+\|b\|_\infty\\
&\le k\left(\int q_J+\int a+\int b\right)\\
&\le k\left(\int q_J+2\iint g_z\right)
\le2k\mathcal Q_\times.
\end{aligned}
$$
其中 $\int a,\int b\le\iint g_z$，且 $\mathcal Q_\times=\int q_J+\iint g_z$；所用积分均为 $\nu_A$ 或其乘积。两条上界合并即 $\kappa$ 界。由于
$$
\kappa\le\kappa_d:=
\min\left\{\left[\frac{d(d+1)}2\right]^2,d(d+1)\right\},
$$
也可统一用纯 $d$ 常数 $\kappa_d$ 代替 $\kappa$。这是同一完整模型类内的常数选择；本章的两个显式范数不保证误差常数也更优，不主张它与第 81 章常数有普遍严格比较。最后由 (80.4) 将 $\mathcal D_{\rm pair}$ 的界代入，得到 (83.11)。群的乘积只用于函数空间，不是给原实际联合增加独立性。证毕。

**推论 83.7（修复同一对原映射）。** 固定原 EJA 三元组及其全部原比较几何，取 (80.9) 的同一个有界不塌缩类 $\mathscr K$：
$$
\begin{gathered}
\|\widetilde L\|,\|p\|\le R_0,\quad
\widetilde M\widetilde M^*\succeq\zeta^2I_D,\quad\widetilde L\widetilde L^*\succeq\zeta^2I_E,\\
\alpha1_D\le U\le\beta1_D,\qquad\alpha1_E\le G\le\beta1_E,\qquad R_0,\zeta,\alpha>0,\qquad\alpha\le\beta.
\end{gathered}\tag{83.12}
$$
该类紧，精确零集仍为 $\mathscr Z=\mathscr K\cap\mathrm{PRE}$。空类无对象；非空而 $\mathscr Z=\varnothing$ 时，$\min_{\mathscr K}\mathcal Q_\times\ge \kappa^{-1}\min_{\mathscr K}\mathcal D_{\rm old}>0$。零集非空时，用 (80.13) 的单调模量，有
$$
\operatorname{dist}_{\rm pair}(z,\mathscr Z)\le\eta_{\mathscr K}(\kappa\mathcal Q_\times),\qquad
r_J\le \kappa\mathcal Q_\times/2,\qquad
r_H\le2R_0nm\,\eta_{\mathscr K}(\kappa\mathcal Q_\times),\quad m=\operatorname{rank}D.
\tag{83.13}
$$
距离为 (80.11) 的原 $(\widetilde L,p)$ 对的 Hilbert–Schmidt 距离；$r_J,r_H$ 分别在全部谱范数至多一的原正交正元对上取最大值。最近零点仍使用同一个 $p_0$ 两次、同一原 $\omega$、全原锥和全实 $Z$。
**证明与范围。** 83.4 保持同一零集，83.6 与 $\eta_{\mathscr K}$ 单调性直接运输 80.5；这里用同一比较定理的 $\kappa$ 界，原 $k^2$ 界仍是合法的较弱替代。若 $\dim_{\mathbb R}D=d^2$，行下界使全部 $\widetilde M$ 可逆且逆一致有界；整个原 C13 子类 $\mathscr K_C$ 紧。将 $\mathscr K,\mathscr Z,\eta_{\mathscr K}$ 一并替换为该子类及其零集、模量，便修复到同类 PRE+C13。若维数不等，65.3 排除精确零点，非空类有正间隙。这不提供有噪单混态 H13 桥、统一幂率、修复算法或自然最近点选择。

**推论 83.8（有限精确求积的存在边界）。** 对每个固定原 $A$，存在至多 $k$ 个投影轨道点 $\Pi_{B_j}$ 与严格正权 $w_j$、$\sum_jw_j=1$，使
$$
\mathsf C_A=\sum_jw_j\Pi_{B_j},\qquad
\mathcal Q_\times(z)=\sum_{j,\ell}w_jw_\ell h_z(B_j,B_\ell)
\quad\text{对全部原 }z\text{ 同时成立}.\tag{83.14}
$$
**证明。** $\dim\operatorname{span}\{\Pi_B\}=k$，其凸包包含概率平均，且全轨道处于 $\operatorname{Tr}\Pi=n$ 的仿射超平面内，仿射维数至多 $k-1$。有限维 Carathéodory 定理给至多 $k$ 点，删除零权即可；取乘积给至多 $k^2$ 对并用 (83.5)。该成熟凸包工具不计作新内容。如果精确节点与精确原读数另已供应，非负性给数学有限零证书；存在性不选自然节点、不供应物理制备或有限精度认证，也不声称任何有限精确证书不可能。

### 83.4 同一个完整转置平均模型的纸面值

**命题 83.9（保留完整原接口的非零检验）。** 对 (78.16) 的同一模型，$0<\lambda<1$ 时
$$
\boxed{\mathcal Q_{\times,\lambda}=\frac{72}{25}(1-\lambda^2)(13+2\lambda^2)>0.}\tag{83.15}
$$
**证明。** 保留全部原态效应及其比较入口，$A=H_4(\mathbb C),D=H_{16}(\mathbb C),E=H_{64}(\mathbb C)$，原全锥上
$$
T_\lambda a=\tfrac{1+\lambda}{2}a+\tfrac{1-\lambda}{2}a^T,\qquad
L(d,a)=d\otimes T_\lambda a,\qquad p=\operatorname{Tr}_1,\qquad\omega=I_{16}/16.
\tag{83.16}
$$
这里 $p$ 始终是同一个四维首腿偏迹。$T_\lambda$ 正、保单位、保迹且实线性可逆，$L$ 对全部纠缠 $d\ge0$ 仍正，$p$ 对整个 $E_+$ 正。两次实际调用给
$$
K(a)=I_4/4\otimes T_\lambda a,\quad M(a,b)=T_\lambda a\otimes T_\lambda b,\quad J(a)=T_\lambda a\otimes I_4,\quad
H_{\rm s}d=d\otimes I_4,\quad U=I_{16},\ G=I_{64},\ F=M.
\tag{83.17}
$$
可逆性及 Hermitian 简单张量的实张成给两条原实张成；$B_1(d)=(\operatorname{Tr}_1d)\otimes I_4$，故 $B_1M(a,b)=\tau_A(a)Jb$ 对全部实 $a,b$ 成立。$\widetilde M=T_\lambda\otimes T_\lambda$ 在 $I^{\rm raw}=\widetilde T_{\rm raw}\widetilde M^{-1}$ 中抵消两端 $T_\lambda$，原插入是普通中间插入 $I_4$，对整个纠缠锥正；所以整个原 C13 成立。$H_{\rm s}$ 保全部正交正元，而 78.20 的同一对正交 $p_\pm$ 有 $\langle Jp_+,Jp_-\rangle=2(1-\lambda^2)>0$。这个正缺陷对象不被预先赋予分阶段 H13 资格。
(83.3) 给 $\mathsf C_A=P_{\mathbb R I_4}+\frac15P_{A^0}$。$T_\lambda$ 在实对称十维为恒等，在纯虚反对称六维乘 $\lambda$，因此
$$
S=\operatorname{Tr}(T_\lambda^*T_\lambda\mathsf C_A)
=1+\tfrac95+\tfrac65\lambda^2=\tfrac{14+6\lambda^2}{5},\qquad
\|J\mathsf D_A\|_{\rm HS}^2=4S,\quad
\|\mathcal T(\mathsf D_A\otimes\mathsf D_A)\|_{\rm HS}^2=4S^2.
\tag{83.18}
$$
于是 $\mathcal Q_\times=80-4S-4S^2$，展开得 (83.15)，不需要同框架四阶积分。实框架仍有旧 $q(B)=0$，所以零平均约束并非定义恒真。与 (81.11) 的同框架值比较，$\mathcal Q_{\times,\lambda}-\mathcal Q_\lambda=\frac{72}{175}(1-\lambda^2)^2>0$，显式展示两个平均不同。$\lambda=0$ 的极限丢失实张成，不把它算作完整原模型。证毕。

### 83.5 固定质量关系、分阶段 H13 与完整同数据等价

**定义 83.10（固定质量入口与原方向关系）。** 由原单位固定数学映射 $R_A(a)=u_A(a)1_A/n$，令 $m_2(a,b)=u_DM(a,b)$、$m_3(a,b,c)=u_EL(M(a,b),c)$。对全部原正输入，包括零与不等质量，要求
$$
\begin{aligned}
\mathsf E_2:\quad m_2(a,b)&=\tfrac12[m_2(R_Aa,b)+m_2(a,R_Ab)],\\
\mathsf E_3:\quad m_3(a,b,c)&=\tfrac13[m_3(R_Aa,b,c)+m_3(a,R_Ab,c)+m_3(a,b,R_Ac)],\\
\mathrm A_0:\quad&u_EL(\omega,1_A/n)=1.
\end{aligned}\tag{83.19}
$$
这不供应实际重置或随机控制；$R_A$、等权与原锚不是额外可调输入。
只在 (83.8) 恢复精确 PRE 后，才定义原 H13。取 $D_{ik}=\operatorname{span}_{\mathbb R}F(A_i,A_k)$ 及其中心投影 $\pi_{ik}$，令 $\alpha_{ik}=F(-,1_k)|_{A_i}$、$\beta_{ik}=F(1_i,-)|_{A_k}$，活跃集 $\mathcal I=\{(i,k):r_i,r_k\ge2\}$。所有伴随使用原规范迹，并令
$$
\begin{aligned}
\mathcal H(F)=\{\rho\in K_D:\ \forall(i,k)\in\mathcal I,\ x=\pi_{ik}\rho,\quad
\alpha_{ik}\alpha_{ik}^*x-x\not\succeq0\ \text{或}\ \beta_{ik}\beta_{ik}^*x-x\not\succeq0\},\\
T_{\rm raw}(a,c)=L(Ja,c),\quad I^{\rm raw}=\widetilde T_{\rm raw}\widetilde M^{-1},\qquad
\mathrm H13:\exists\rho\in\mathcal H(F),\ I^{\rm raw}\rho\in E_+,\qquad
\mathrm{C13}:I^{\rm raw}(D_+)\subseteq E_+.
\end{aligned}\tag{83.20}
$$
每个活跃块至少一差有严格负方向，不要求两差都不正或负定；活跃块正质量随之成立。铺回使用未经维数归一化的单位。非活跃块任取正元含零；活跃集空时 $\mathcal H(F)=K_D$。始终检测同一个原总迹一混态的整个原输出，不换态、参考、固定效应或总迹读数。

**定理 83.11（显式二阶权的完整候选）。** 在同一实际原模型类中，
$$
\boxed{\mathrm{PRE}_0^{1/2}+(83.8)+\mathsf E_2+\mathsf E_3+\mathrm A_0+\mathrm H13
\quad\Longleftrightarrow\quad\mathrm{PRE}+C_{\rm joint}+\mathrm{C13}.}\tag{83.21}
$$
这里 $C_{\rm joint}$ 严格取原双迹条件 $\delta+\gamma\le2n^3$，$\delta=u_EL(1_D,1_A)$、$\gamma=u_D(p1_E)$。删去质量、锚及 $C_{\rm joint}$，得到同样成立的未校准版本。
**证明。** 在各原载体上，(83.1) 先由 [FH] 恢复全部实混合权重及完整 $S$，其余原对象与谓词不变，故与原 $\mathrm{PRE}_0^{\rm mix}$ 同类；(83.8) 与 83.4 再恢复同一 PRE。$R_A$ 正保原质量，且全部实泛函满足 $fR_A=f\Longleftrightarrow f=f(1_A/n)u_A$，故固定泛函恰为 $\mathbb Ru_A$。(83.19) 正是 79.2 的 $t=1/2,s=2/3$，因为三槽权重 $st,s(1-t),1-s$ 均为 $1/3$。79.5—79.7 与同一原锚先于 H13 给 $C_{\rm joint}$；72.7—72.8 再由非空 $\mathcal H(F)$ 及同一原输出给 C13。
反向，原 PRE 的完整比较律由 [FH] 给同一 (83.1)，且 PRE+$C_{\rm joint}$ 由 79.6—79.7 给 $m_2=u_A^{\otimes2}$、$m_3=u_A^{\otimes3}$ 及原锚，所以这个固定 $R_A$ 满足两条等权关系；83.4 给 (83.8)，原 C13 与 72.7 给 H13。所有关系在同一个原 $L,p,\omega$ 上成立。此处仅应用既有质量定理，不把固定数学见证重计为新质量定理。证毕。

### 83.6 量子消费者、简化尺度与完整白话

**推论 83.12（回接的全部附加条件）。** (83.21) 接回旧量子公理的范围，严格为 80.7／81.8 的同数据消费者，并按固定来源 [CP] 的 82.10—82.11 复用指定同载体事件的 CP 入口：

| 结构 | 必须保留的条件与结论范围 |
| --- | --- |
| 复 Hilbert 表示、密度态、全效应、Born 配对 | 全态全效应、全部混态余项的 (83.1) 先由 [FH] 恢复完整 $S$ 与全部实混合权重，再经完整一般 EJA 条件桥；零缺陷恢复两层全域保零，65—66、75.7 才给有限复 Hermitian 直和及配对 $\sum_i\operatorname{Tr}(\rho_if_i)$，不预选单一非经典扇区。 |
| 原二份、三份张量与普通相对方向 | PRE 后的同一原 H13 检测整个原输出，恢复整个原 C13；再用 72.7—72.8、66.10 的方向桥。不识别另给的另一括号或四份以上共同来源。 |
| 原尺度、标准准备与偏迹 | 两条固定质量关系及原 $\mathrm A_0$ 先恢复 $C_{\rm joint}$，方向条件随后使同一个原 $M,L,p$ 同时标准归一化；零范数差本身不校准倍率。 |
| CP 事件与仪器 | 在已归一化原数据上，对另供的同一实际同载体事件 $e:A\to A$、满足精确全实三份平均律的同事件提升 $P_{E,e}$ 及原完整记录／来源合同，[CP] 的 82.10—82.11 给 $P_{E,e}(\Xi)\ge0\Longleftrightarrow\Phi_e\text{ CP}\Longleftrightarrow P_{E,e}\text{ 全锥正}$。事件、提升与探针的实际来源均须另供；其他类型事件仍使用 69.1—69.11 的实际旁观者、同事件联合正性及每输入扇区有正权且参考足够大的实际联合参考入口，局部与原联合两概率预算、实际分支、完整菜单及共同重置的同族补全与输入行一致条件全部保留，不能由数学 $R_A$ 代替。 |
| Lüders 更新 | 除上述事件合同，仍需锐投影效应及全部确定接受态逐点不变等原中性前提；Born 效应或 CP 本身不唯一确定更新。 |
| Hamiltonian 动力学 | 仍需原物理时间上的连续齐次可逆 $*$-自同构群；静态候选不产生该群、时间尺度、单位或 $\hbar$。 |

**证明与边界。** 83.11 恢复同一个 PRE+$C_{\rm joint}$+C13，逐项调用上述原定理即可，不重证成熟分类、Choi/Kraus 或更新工具。第 82 章的数学 $\Xi$ 与共同标架不被称为自然或可准备，平均提升不供应每个单腿的实际控制，校准见证 $\Phi_{\rm cal}$ 也不等同任意事件。完整原 $\Omega$ 的准备、事件、参考、副本、实际相关联合、零与不等质量、单位与时钟、ready 与 flags、失败、停止、销毁、返回、未来、每个原全菜单及中间切口义务全部保留；也未完成无限维一致性、实际装置供应或经验对应。固定来源 RRO-II 的第 18.3 节定理与第 19.3 节命题对原单元接收切口给出原生续接与发生账；它仍把任意 busy 切口、内部 compiler/loan/copy、原 $Q$/终端 kernel、结构最小性和物理实现列为未决。因此该源域进展不自动完成量子实际准备、事件、参考及完整原 $\Omega$ 桥。
本章简化的尺度只比较同一完整模型类的自由输入、固定几何对象、优化和矩层级：显式 (83.3) 加两个范数替代同框架四阶相关矩及其循环空间；任意局部质量见证和权重已在 81.7 固定，不能再算一次新增简化。证明仍使用全部框架，修复运输使用 $\kappa$（或纯 $d$ 的 $\kappa_d$）；原 $k^2$ 界仍保留。这些结论不证明独立物理前提最少、自然有限实验、物理可得性或全球原创。

**完整白话。** 保留原来所有状态和所有测试，比较入口只要求“纯端加任意混态对半；共同最小确认效应可换任意权重”。已有固定对半定理保证同一个确认效应在全部有限纯态支撑上共同取到最小值，因而能换成任意实概率权重，恢复完整比较律；混态余项仍遍及整个原态基，不能只测两个纯态。也保留一个原准备与同一个原读回连续使用两次的整套关系。现在让左右两张完整互斥方向图分别走遍原几何；这两个变量只在数学积分里分开，不表示两个实际系统独立。每对图上的各部分都为正且总和固定，所以“总长度平方减去各部分长度平方之和”仍只记录非负交叉重叠。平均为零就逼每对图都没有重叠，特别包含左右相同的旧图，因而恢复整个原接口；反过来，精确原接口使任意左右图都正交。两个积分分开后，每边只需同一个显式几何权：每个中央单位权为一，每个简单因子的迹零方向按秩和维数给固定权。公式因此只剩两个算子长度的平方相加恰好等于两个总量长度的平方。它与先前让左右始终使用同一张图的平均数不同，但选择的精确模型相同。随后由两条固定质量关系及原锚校准倍率，再用同一个原混态的方向条件排除错误转置，按各自额外合同接回量子态、Born、张量和过程。有界且不塌缩时，小缺陷保证同一对原准备、读回接近某个精确原模型；没有精确模型的类则有正间隙。这个球面等式描述的是满足原约束的派生映射像，没有把状态变成球，也没有凭空制造实际制备、事件或时间。

**数学来源与归属。** [J] Jeong–Gowda, *Spectral sets and functions on Euclidean Jordan algebras*, LAA 518 (2017), 31–56, [作者原文](https://userpages.umbc.edu/~gowda/papers/trGOW16-06.pdf), [DOI](https://doi.org/10.1016/j.laa.2016.12.020)：pp. 36—37 的 Proposition 2、3 及 p. 55 的 Appendix Theorem 11；其框架按有序对象理解，简单因子的传递性与一般直和的限制均保持原条件。逐理想的无标签投影论证不声称一般直和有序框架或纯态全局传递。[H] von Neumann, [*Zum Haarschen Maß in topologischen Gruppen*](https://www.numdam.org/item/CM_1935__1__106_0/), Compositio Mathematica 1 (1935), 106—114：紧可分群的不变概率与非空开集正质量；此处群是有限维紧矩阵群。Carathéodory、有限维评价核及紧性均为成熟工具。[P] 本卷 75—81 及第四卷 65—72 的固定接口，取 [1b2e8ef358413a6230c43718fc0ce44c7797683b](https://github.com/the-omega-institute/trureturing/tree/1b2e8ef358413a6230c43718fc0ce44c7797683b) 所载原文，条件桥、质量、方向、共同修复与消费者仅按原范围复用。 [FH] [Library 固定对半入口](https://github.com/the-omega-institute/trureturing/blob/9fc08bdbd0c3f530279b76dd419b5c4ade8bd81d/Library/QuantumStates/mullerududec2012selfduality.md)，*Appendix: a fixed-half pure–mixed entrance to S*：在同一非零有限有序载体、整个原态基及全部 proper 效应上，FH1 与完整 $S$、$\mathrm B_{\rm mix}$ 等价，包含任意混态余项和全部实概率权重；其同类替换仅用于本章 (83.1)、83.11—83.12。[CP] [本卷第 82 章](https://github.com/the-omega-institute/trureturing/blob/9fc08bdbd0c3f530279b76dd419b5c4ade8bd81d/docs/develop/theory/QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md)，82.10—82.11：只在已归一化原数据及另供的同一实际同载体事件、精确全实三份提升、完整记录与来源合同上复用固定探针 CP 等价，不供应实际事件、探针准备、单腿控制或其他类型事件的来源。
 [RRO-II] `RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ORIGINAL_INTERFACE_EXPOSURE_AND_RECOVERY_II.md`，固定源版本 `e0d88f7785c79e7a863611cd332c2549adbea64e`，仅用于上述第 18.3 节与第 19.3 节的数学范围对应。新增承重推导是乘积平均在完整原模型上的双向零集、显式二阶范数入口、乘积最坏缺陷控制及同一完整反例的新标量；不将标准平均、(81.9) 或归一化应用当作新工具。

## 追加锚（本行以下为增补区）

## 84. 共同锚点的序反射、任意纯三腿探针与原事件相容商

本章第 65—72 章指第四卷，第 73—83 章指本卷。静态完整候选沿用 (81.14)，同事件全实提升沿用 (82.22)。要放宽的是第 82 章特定 GHZ 坐标探针的形状，不是实际源合同：给定一份纯三腿张量，各位置作用之间的全部线性关系何时允许读回同一个局部矩阵？共同单位锚点使这个问题具有必要且充分的答案。下文给出序反射与共同解码器的等价证明、各维显式探针、失败时的强正非 CP 反模型、全部有限中央扇区及噪声边界。所有证明均为有限维纸面推导，不是形式内核认证。

### 84.1 共同锚点把序反射变成相容商

**定义 84.1（带共同锚点的局部作用）。** 取有限复 Hilbert 空间 $\mathsf E,\mathsf F$、有限非空指标集 $S$、严格正权 $p_\ell$ 且 $\sum_{\ell\in S}p_\ell=1$。给复线性 $V_\ell:\mathsf E\to\mathsf F$，以及同一个非零 $e\in\mathsf E$，满足 $V_\ell e=v$ 与 $\ell$ 无关。定义

$$
\begin{aligned}
T(X)&=\sum_{\ell\in S}p_\ell V_\ell XV_\ell^*,\qquad X\in\operatorname{Herm}(\mathsf E),\\
\mathbb V:\bigoplus_{\ell\in S}\mathsf E&\longrightarrow\mathsf F,
&\mathbb V((x_\ell))&=\sum_\ell V_\ell x_\ell,\\
\Sigma:\bigoplus_{\ell\in S}\mathsf E&\longrightarrow\mathsf E,
&\Sigma((x_\ell))&=\sum_\ell x_\ell.
\end{aligned}\tag{84.1}
$$

序反射指对每个 Hermitian $X$，$T(X)\ge0$ 蕴含 $X\ge0$；$T$ 本来就保持 PSD。共同解码器是复线性 $C:\mathsf F\to\mathsf E$，满足每个 $CV_\ell=I_{\mathsf E}$。它是数学读出，不假定为实际可执行的滤器、通道或复制程序。

**定理 84.2（共同锚点序反射的充要条件）。** 在定义 84.1 下，以下四项等价：

1. $T$ 在整个 $\operatorname{Herm}(\mathsf E)$ 上反射 PSD。
2. 对每个单位 $x\in\mathsf E$ 及每个 $\eta>0$，$T(I-(1+\eta)|x\rangle\langle x|)$ 不是 PSD。
3. 存在共同解码器 $C$。
4. $\ker\mathbb V\subseteq\ker\Sigma$。

共同解码器还给出整个 Hermitian 空间上的精确恒等式

$$
\boxed{CT(X)C^*=X.}\tag{84.2}
$$

所以序反射是否成立只依赖活跃作用的相容关系，不依赖这些严格正权的具体大小。

**证明。** 第 1 项蕴含第 2 项，因为被测试的输入在 $x$ 方向特征值为 $-\eta$。证明第 2 项蕴含第 3 项是关键。若 $v=0$，置 $x=e/\|e\|$，则每个 $V_\ell x=0$，所以 $T(I-(1+\eta)|x\rangle\langle x|)=T(I)\ge0$，与第 2 项矛盾。故可设 $v\ne0$。

令 $R=\sum_\ell\operatorname{ran}V_\ell\subseteq\mathsf F$，并仅在 $R$ 上取 $S_0=T(I)|_R$。若 $z\in R$ 且 $\langle z,S_0z\rangle=0$，严格正权给每个 $V_\ell^*z=0$，于是 $z$ 既在 $R$ 又与 $R$ 正交，故 $z=0$。因此 $S_0>0$。对任一单位 $x$ 置

$$
P_x=|x\rangle\langle x|,\qquad
A_x=S_0^{-1/2}T(P_x)|_R S_0^{-1/2},\qquad 0\le A_x\le I_R.
\tag{84.3}
$$

若 $\lambda_{\max}(A_x)<1$，可取足够小 $\eta>0$ 使 $(1+\eta)\lambda_{\max}(A_x)\le1$。则 $T(I)-(1+\eta)T(P_x)$ 在 $R$ 上 PSD，在 $R^\perp$ 为零，违反第 2 项。因此每个 $A_x$ 都有单位特征向量 $y$，满足 $A_xy=y$。置 $z=S_0^{-1/2}y\in R$。此时

$$
0=\langle z,T(I-P_x)z\rangle
=\sum_\ell p_\ell\|(I-P_x)V_\ell^*z\|^2.
$$

每项为零，故 $V_\ell^*z=c_\ell x$。共同锚点给

$$
\langle e,V_\ell^*z\rangle=\langle v,z\rangle.
\tag{84.4}
$$

当 $\langle e,x\rangle\ne0$ 时，所有 $c_\ell$ 必相等；共同值 $c$ 非零，因为 $\sum p_\ell|c_\ell|^2=\langle z,T(P_x)z\rangle=\langle y,A_xy\rangle=1$。定义复线性子空间和映射

$$
D_0=\{z\in\mathsf F:V_\ell^*z\text{ 对所有 }\ell\text{ 相同}\},\qquad
L_0:D_0\to\mathsf E,\quad L_0z=V_{\ell_0}^*z
\tag{84.5}
$$

（任取一个 $\ell_0\in S$）。上式证明 $\operatorname{ran}L_0$ 包含每个与 $e$ 不正交的单位方向。这些方向在单位球面稠密，而有限维线性像是闭子空间，所以 $L_0$ 满射。选一个线性右逆 $R_0:\mathsf E\to D_0$，则每个 $V_\ell^*R_0=I$；取 $C=R_0^*$ 即得共同解码器。共同锚点正是在 (84.4) 中把各位置本可不同的倍数锁成同一个倍数。

若有共同解码器，将其逐项代入 $T$ 就得到 (84.2)，故第 3 项蕴含第 1 项。最后，第 3 项给 $C\mathbb V=\Sigma$，自然蕴含核包含。反向若核包含，则

$$
C_R(\mathbb V((x_\ell)))=\Sigma((x_\ell))
$$

在 $R=\operatorname{ran}\mathbb V$ 上良定义且线性；将其在 $R^\perp$ 上延为零，得到 $CV_\ell=I$。这不是只给某个输入一个数值重构，而是全部局部矩阵共用的线性商。证毕。

### 84.2 任意纯三腿探针：必要性与强反模型

**定义 84.3（活跃腿、Choi 约定与相容条件）。** 在单块 $M_d(\mathbb C)$ 上保留 (82.1) 的未归一 Choi、输出在前／输入在后的向量化。令 $\psi\in(\mathbb C^d)^{\otimes3}$ 为归一化纯向量，$\rho_\psi=|\psi\rangle\langle\psi|$。固定 $\alpha_\ell\ge0$、$\sum_{\ell=1}^3\alpha_\ell=1$，只取活跃集 $S_\alpha=\{\ell:\alpha_\ell>0\}$。在 Hilbert–Schmidt 空间 $\mathsf E=M_d$ 上令

$$
V_{\psi,\ell}(H)=H^{(\ell)}\psi,\qquad
\mathbb V_{\psi,S}((H_\ell))=\sum_{\ell\in S}H_\ell^{(\ell)}\psi,\qquad
\Sigma_S((H_\ell))=\sum_{\ell\in S}H_\ell.
\tag{84.6}
$$

称 $\psi$ 对这些活跃腿相容，当且仅当

$$
\boxed{\ker\mathbb V_{\psi,S_\alpha}\subseteq\ker\Sigma_{S_\alpha}.}\tag{84.7}
$$

共同锚点为 $e=I_d$，每个 $V_{\psi,\ell}(I_d)=\psi$。全部矩阵均为复矩阵；只检验 Hermitian 局部生成元、局部酉轨道或几个坐标不能替代这个复线性核条件。记 $\mathcal K_{3,\alpha}(\Phi)=\sum\alpha_\ell\Phi_\ell$，各腿为同一份复线性 HP 映射 $\Phi$。

**推论 84.4（任意纯探针的准确 CP 刻画）。** 对固定 $\psi,\alpha$，以下三项等价：对所有 HP $\Phi:M_d\to M_d$，$\mathcal K_{3,\alpha}(\Phi)(\rho_\psi)\ge0$ 当且仅当 $\Phi$ CP；条件 (84.7)；存在共同 $C_\psi$ 使每个活跃腿 $C_\psi V_{\psi,\ell}=I_{M_d}$。此时对每个 HP $\Phi$ 有

$$
\boxed{C_\psi\mathcal K_{3,\alpha}(\Phi)(\rho_\psi)C_\psi^*=J(\Phi).}\tag{84.8}
$$

**证明。** 任一 Hermitian $J$ 都唯一对应一份复线性 HP 映射。按 (82.5) 作带实符号 Kraus 分解，逐项得

$$
J(\Phi)=\sum_ac_a|\operatorname{vec}H_a\rangle\langle\operatorname{vec}H_a|,\qquad
\mathcal K_{3,\alpha}(\Phi)(\rho_\psi)
=\sum_{\ell\in S_\alpha}\alpha_\ell V_{\psi,\ell}J(\Phi)V_{\psi,\ell}^*.
\tag{84.9}
$$

右侧把 $M_d$ 与其向量化空间等同，没有预用 CP。Choi 定理给 CP 恰为 $J\ge0$，故所求对全部 HP 的性质正是定理 84.2 的整个 Hermitian 序反射，三个条件及恒等式同时成立。$d=1$ 亦成立。权重为零的位置不进入核条件；至少一个位置活跃。证毕。

**命题 84.5（相容失败时，正、TP、保单位及混合仍不能补救）。** 设 $d\ge2$ 且 (84.7) 失败。则存在酉 $U$ 和 $0<\eta<d-1$，使

$$
\Phi_{\eta,U}(X)=\frac{d\operatorname{Tr}(X)I_d-(1+\eta)UXU^*}{d^2-1-\eta}
\tag{84.10}
$$

严格正化每个非零 PSD 输入、TP、保单位、迭代混合且全部固定效应只有标量，却非 CP，并且 $\mathcal K_{3,\alpha}(\Phi_{\eta,U})(\rho_\psi)\ge0$。因此推论 84.4 的必要性即使只用这一强正非 CP 类反测也成立；这些映射不称为量子通道。

**证明。** 用本探针定义 (84.5) 的 $D_0,L_0$。若 $L_0$ 满射，其右逆仍会给共同解码器，所以相容失败时 $W_0=\operatorname{ran}L_0$ 是 $M_d$ 的真闭复子空间。酉矩阵复线性张满 $M_d$：每个 Hermitian 收缩 $A$ 是 $[U+U^*]/2$，其中 $U=A+i\sqrt{I-A^2}$ 酉；任意矩阵再分成两个 Hermitian 部分。故有酉 $U_0\notin W_0$。

还可保证 $\operatorname{Tr}U\ne0$。若 $\operatorname{Tr}U_0=0$，非退化迹配对及 Hermitian 矩阵的复张成给某个 Hermitian $H$ 满足 $\operatorname{Tr}(HU_0)\ne0$。曲线 $U(t)=e^{itH}U_0$ 对足够小 $t$ 仍在 $W_0$ 外，而 $\operatorname{Tr}U(t)$ 在零点的导数为 $i\operatorname{Tr}(HU_0)\ne0$，故任意小邻域内可选非零迹的 $U$。这不需要枚举酉矩阵。

令 $w=\operatorname{vec}U/\sqrt d$，则 $w\notin W_0$ 且 $\langle I_d,w\rangle\ne0$。如果 (84.3) 中 $A_w$ 的最大特征值为一，共同锚点的 (84.4)—(84.5) 就会使 $w\in W_0$，矛盾。因此 $\lambda_{\max}(A_w)<1$。选 $\eta>0$ 足够小，使

$$
0<\eta<d-1,\qquad(1+\eta)\lambda_{\max}(A_w)\le1.
$$

于是 $T(I-(1+\eta)|w\rangle\langle w|)\ge0$。直接按 Choi 约定计算

$$
J(\Phi_{\eta,U})=\frac d{d^2-1-\eta}
\bigl(I_{d^2}-(1+\eta)|w\rangle\langle w|\bigr).
\tag{84.11}
$$

其 $w$ 特征值严格负，但探针输出 PSD。

记 $c_\eta=d^2-1-\eta$。对 $X\ge0$，$UXU^*\le\operatorname{Tr}(X)I$，故非零输入的分子至少为 $(d-1-\eta)\operatorname{Tr}(X)I>0$。迹及单位计算都给分母 $c_\eta$，所以 TP 且保单位。在迹零空间上它等于 $-q\operatorname{Ad}_U$，$q=(1+\eta)/c_\eta<1$；最后的不等式由 $\eta<d-1$、$d\ge2$ 给出。因此迭代趋向 $X\mapsto\operatorname{Tr}(X)I/d$，伴随在迹零效应上亦严格收缩，固定效应只有标量。$U,\eta$ 依赖给定探针；不提供统一负隙、统一容差或实际非 CP 程序。证毕。


### 84.3 所有 d≥3 的显式张量与成熟泛型几何

**定理 84.6（显式最小 GL 无穷小稳定子）。** 对每个整数 $d\ge3$ 及

$$
0<\varepsilon<\frac1{2(d-2)},\qquad
\psi_{d,\varepsilon}=Z_{d,\varepsilon}^{-1/2}
\left(\sum_{i=1}^d|iii\rangle+
\varepsilon\sum_{i,j,k\text{ 两两不同}}|ijk\rangle\right),\qquad
Z_{d,\varepsilon}=d+d(d-1)(d-2)\varepsilon^2,
\tag{84.12}
$$

有精确复线性核

$$
\ker\mathbb V_{\psi_{d,\varepsilon},\{1,2,3\}}
=\mathfrak b_d:=\{(c_1I,c_2I,c_3I):c_1+c_2+c_3=0\}.
\tag{84.13}
$$

特别可固定 $\varepsilon=1/[4(d-2)]$。这些探针对所有允许的三腿权重（含端点）都给推论 84.4 的精确 CP 证书。

**证明。** 假设 $\sum_{\ell=1}^3H_\ell^{(\ell)}\psi=0$，先消去非对角矩阵元。对 $j\ne i$，在恰有两个相同标签的坐标上逐项读系数，归一常数消去后得到

$$
\begin{aligned}
(H_1)_{ji}+\varepsilon\sum_{k\ne i,j}[(H_2)_{ik}+(H_3)_{ik}]&=0&&(|jii\rangle),\\
(H_2)_{ji}+\varepsilon\sum_{k\ne i,j}[(H_1)_{ik}+(H_3)_{ik}]&=0&&(|iji\rangle),\\
(H_3)_{ji}+\varepsilon\sum_{k\ne i,j}[(H_1)_{ik}+(H_2)_{ik}]&=0&&(|iij\rangle).
\end{aligned}\tag{84.14}
$$

这里每个求和只含非对角元，没有隐藏的对角项。令 $h$ 是全部三个矩阵的非对角元列向量，(84.14) 是方形系统 $(I+\varepsilon A)h=0$；每行 $A$ 恰有 $2(d-2)$ 个系数一，其余零。若 $M=\max_{\ell,i\ne j}|(H_\ell)_{ji}|$，逐行三角不等式给

$$
M\le2(d-2)\varepsilon M<M\quad\text{若 }M>0.
\tag{84.15}
$$

故 $M=0$。这是严格最大项界，不是小维枚举或数值秩实验。

剩余对角元记作 $a_i,b_i,c_i$。坐标 $iii$ 和所有两两不同的 $ijk$ 分别给

$$
a_i+b_i+c_i=0,\qquad a_i+b_j+c_k=0\quad(i,j,k\text{ 两两不同}).
\tag{84.16}
$$

当 $d\ge4$，任取 $i\ne i'$，可在这两者之外固定不同 $j,k$；比较 $(i,j,k)$ 与 $(i',j,k)$ 即得 $a_i=a_{i'}$。另外两个位置同理，所以三组对角元各为常数，总和零。

当 $d=3$，对任意两个不同 $i,j$，取剩余 $k$，交换前两位置得 $a_i-b_i=a_j-b_j=t$。由同标签式 $c_i=-2b_i-t$；再将任一不同三元组代入第二式，得到 $b_i+b_j-2b_k=0$，即 $3b_k=b_1+b_2+b_3$。三个 $k$ 都适用，故所有 $b_k$ 相等，继而 $a,c$ 各恒定。这补全三维边界，而非借用 $d\ge4$ 的第四个标签。

反向任何 $\mathfrak b_d$ 中三元组都把任意张量乘以零，故确为整个核。$\mathfrak b_d\subseteq\ker\Sigma_{\{1,2,3\}}$；将一个活跃子集的关系在其余腿补零，仍属整个核，因而也满足 (84.7)。推论 84.4 给结论。证毕。

**推论 84.7（泛型范围、GL／SL 与完整求和核）。** 对 $d\ge3$，纯向量空间中满足 $\operatorname{rank}\mathbb V_\psi=3d^2-2$ 的集合为非空 Zariski 开集、稠密且补集为零测度；归一化纯态流形上的相应集合也稠密且满测度。其每个成员均有 (84.13)，故对每组非负三腿权重反射 CP。

**证明。** 两维的 $\mathfrak b_d$ 对任何 $\psi$ 都在核内，故秩至多 $3d^2-2$。定理 84.6 在每个 $d\ge3$ 给达到上界的显式点。作用矩阵的元素对 $\psi$ 坐标线性，故达到上界等价于至少一个该阶子式非零。这是非空 Zariski 开条件；非零复多项式的零集是实 Lebesgue 零测度且无开内点，归一化及径向分解给球面上的对应结论。到处包含的两维子空间此时已占满核。证毕。

$\ker\mathbb V_\psi$ 是 $\mathrm{GL}_d(\mathbb C)^3$ 对向量 $\psi$ 的无穷小稳定子，不只是局部酉稳定子。最小核与 $\mathfrak{sl}_d^3$ 的交为零，所以其 SL 向量稳定子是零维、因而有限；不排除非平凡离散稳定子。只知道局部酉 Lie 稳定子小，不能替代复 GL 计算；单独的有限 SL 向量稳定子也不能不核对轨道闭性／非零不变量等项目缩放条件，就当作 GL 最小核的证明。

这里的完整求和核始终是

$$
\ker\Sigma_{\{1,2,3\}}=\{(H_1,H_2,H_3):H_1+H_2+H_3=0\},
\qquad \mathfrak b_d\subseteq\ker\Sigma_{\{1,2,3\}}.
\tag{84.17}
$$

它绝不只含平衡标量；$d\ge2$ 时任取非标量 $H$，$(H,-H,0)$ 就在其中。相容性允许比 $\mathfrak b_d$ 更大的核，只要求其全部关系的矩阵和为零。$d=2$ 时输出维数八小于 $3d^2-2=10$，所以不可能有 (84.13) 的最小 GL 核，但第 82 章 $G_2$ 仍有共同解码器，不能把最小核误当 CP 认证的必要条件。

泛型 SL 稳定性已有成熟归属：Derksen–Makam–Walter [DMW] 的 **arXiv:2011.03849v1 Theorem 1.5(4)** 对 $(d,d,d;m=1)$、$d\ge3$ 适用，因为 $d\le d^2/2$ 且不落在该项的例外形状；结合 Definition 2.2、Corollary 2.11 读取其稳定子结论。本章不把泛型有限稳定子认作新一般结果，也不使用另一版本的定理编号。这里的显式 GL 系数证明独立承担 (84.13)，避免把 SL 与 GL／项目稳定子混为一谈。泛型数学向量既不表示每个纠缠态都合格，也不选择自然或实际可准备的原探针。

### 84.4 乘积、W 与独立标架变换的反测

**命题 84.8（强纠缠与局部酉等价均非充分条件）。** 对三腿全活跃的情形，以下边界成立。

乘积向量 $a\otimes b\otimes c$、$d\ge2$ 不满足 (84.7)：可取非零 $H$ 使 $Ha=0$，则 $(H,0,0)$ 的局部作用为零，而求和为 $H\ne0$。

三 qubit 的

$$
|W\rangle=(|001\rangle+|010\rangle+|100\rangle)/\sqrt3
$$

在每腿都具有满 Schmidt 秩且真正三方纠缠，却不满足 (84.7)。确实，三个位置都取 $H=\operatorname{diag}(-1/3,2/3)$，每个非零字符串上三个对角数之和均为零，因此 $(H,H,H)\in\ker\mathbb V_W$，但 $3H=\operatorname{diag}(-1,2)\ne0$。满单体 Schmidt 秩不够。

共同可逆 $S$ 在三个位置同时作用保持相容性：对归一化后的 $(S\otimes S\otimes S)\psi$，核关系经 $H_\ell\mapsto S^{-1}H_\ell S$ 对应，求和也经同一共轭对应。独立局部可逆变换则没有这个保证，连独立局部酉也没有。令 $Z=\operatorname{diag}(1,-1)$、$X=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$，$B=2^{-1/2}\left(\begin{smallmatrix}1&1\\1&-1\end{smallmatrix}\right)$。原 $G_2$ 有关系 $(Z,-Z,0)$；在

$$
\psi'=(I\otimes B\otimes I)|G_2\rangle
$$

上相应关系为 $(Z,-BZB^*,0)=(Z,-X,0)$，其矩阵和 $Z-X\ne0$，故 $\psi'$ 失败。

**证明与标架含义。** 各展示的核向量均直接违反 (84.7)，推论 84.4 和命题 84.5 分别给不能认证与强正非 CP 反模型。共同 $S$ 的结论由三个局部算子逐腿共轭直接得出。独立 Hadamard 例子并不违反物理的换标架协变性：若独立换三腿物理标架，也必须各自共轭相应局部事件；此时三腿坐标式不再是未经运输的同一份 $\Phi$。本章固定的是“同一个原事件在三个位置用同一份矩阵”这一有来源义务的关系。证毕。

### 84.5 非最优 CP 修正与纯态流形内的局部稳定性

**命题 84.9（共同解码器的定量后果）。** 若 $\psi$ 对活跃腿相容，固定一个共同 $C_\psi$，令 $\kappa=\|C_\psi\|$。在普通未归一 Choi 及总迹规范中，对任一 HP $\Phi$，

$$
\mathcal K_{3,\alpha}(\Phi)(\rho_\psi)\ge-\epsilon I
\quad\Longrightarrow\quad J(\Phi)\ge-\delta I,
\qquad\delta=\kappa^2\epsilon,\quad\epsilon\ge0.
\tag{84.18}
$$

因而 $\Phi+\delta\Delta$ CP，其中 $\Delta(X)=\operatorname{Tr}(X)I_d$。若另外 $\Phi$ TP，则

$$
\widehat\Phi=\frac{\Phi+\delta\Delta}{1+d\delta}\text{ CPTP},\qquad
\|\Phi-\widehat\Phi\|_\diamond\le2d\delta.
\tag{84.19}
$$

这些常数未声称最优。

**证明。** (84.8) 压缩下界给 $J(\Phi)\ge-\epsilon C_\psi C_\psi^*\ge-\kappa^2\epsilon I$。$J(\Delta)=I$，故相加后 CP。TP 时 $\operatorname{Tr}\Delta(X)=d\operatorname{Tr}X$，分母恢复 TP。取 CPTP 的 $\mathcal R=\Delta/d$，则 $\Phi-\widehat\Phi=d\delta(\widehat\Phi-\mathcal R)$；两份 CPTP 的 diamond 范数为一，三角不等式给结论，未假定 $\Phi$ 本来 CP。证毕。

在推论 84.7 的最大秩纯向量集合上，核恒为固定的 $\mathfrak b_d$。对全三腿作用限制到 $\mathfrak b_d^\perp$，记其最小奇异值为 $\sigma_\psi>0$，则 Moore–Penrose 逆给

$$
C_\psi=\Sigma\mathbb V_\psi^+,\qquad
\|C_\psi\|\le\frac{\sqrt3}{\sigma_\psi}.
\tag{84.20}
$$

这是因为 $\mathbb V_\psi^+\mathbb V_\psi$ 为到 $\mathfrak b_d^\perp$ 的正交投影，而 $\Sigma$ 消去 $\mathfrak b_d$，且 $\|\Sigma\|=\sqrt3$。在任一固定最大秩点附近，限制作用仍单射，其 Gram 逆与伪逆连续，$\sigma_\psi$ 保持正下界；故这些解码器连续且局部有界。它们同时适用于任意活跃子集。这里的邻域在同维归一化纯态流形内；较低秩但仍相容的 GHZ 点没有被该恒秩连续性论证自动覆盖，也没有得到全部合格纯探针上的统一常数。数学修正不修复实际程序、菜单、记录或未来来源。

### 84.6 任意有限满秩目录的噪声障碍

**定理 84.10（不同有限张量次数也不能挽救满秩 PSD 目录）。** 固定 $d\ge2$。给一个非空有限目录：第 $r$ 项是某个有限 $q_r\ge1$ 份空间上的正定输入 $\rho_r>0$，以及固定非负权 $\alpha_{r,\ell}$、$\sum_{\ell=1}^{q_r}\alpha_{r,\ell}=1$，测试

$$
\mathcal K_{q_r,\alpha_r}(\Phi)(\rho_r)
=\sum_{\ell=1}^{q_r}\alpha_{r,\ell}\Phi_\ell(\rho_r)\ge0.
\tag{84.21}
$$

则存在一份命题 84.5 形式的正严格化、TP、保单位、混合且固定效应标量的非 CP 映射，同时通过全部这些测试。包括三腿或其他腿数的权重端点。因而在这个单块及“只取有限个输出 PSD 合取”的问题上，没有固定满秩探针或这样的有限目录能精确认证 CP。

**证明。** 取 (84.10) 中 $U=I$，先置 $\eta=0$。其 Choi 为 $d(I-|w\rangle\langle w|)/(d^2-1)\ge0$，且 $\Phi_{0,I}$ 保单位。每个一腿扩张都是 CP 保单位，故它们的非负权和也 CP 保单位。若 $\rho_r\ge m_rI$、$m_r>0$，则

$$
\mathcal K_{q_r,\alpha_r}(\Phi_{0,I})(\rho_r)\ge m_rI.
$$

每个空间有限维，(84.10) 对 $\eta$ 连续，因此每项在足够小正 $\eta$ 仍严格正。目录有限，取这些正邻域的共同交，并限制 $0<\eta<d-1$，就得到同一份非 CP 反模型。其余性质已经由命题 84.5 对该显式族的直接计算给出。证毕。

特别地，任一合格纯探针混入任意严格正份额的满秩噪声后，就不再具有这类精确的“一个平均输出 PSD 即 CP”性质。它与 (84.20) 的纯流形局部稳定性不矛盾：两个结论的扰动域不同。这个障碍没有证明每个奇异混态都失败，没有证明纯态是所有可能证书的必要形式，也没有否定保存完整矩阵输出再利用跨输出关系的过程层析。各 $q_r$ 仅为已固定的有限数，未声称对无限目录、随映射选探针、实际单腿标签、资源最优性或物理可实现性的不可能结论。


### 84.7 全部有限中央扇区与矩形转移检测

**定义 84.11（全扇区探针）。** 取定义 82.1 的原有限代数

$$
\mathcal A=\bigoplus_{i\in I}M_{n_i},\qquad n_i\ge1,\qquad
n=\sum_i n_i,\qquad u_A=\sum_i\operatorname{Tr}.
$$

在每个块上先于待测 $\Phi$ 指定归一化纯向量 $\psi_i$，要求它对全三腿具有共同解码器 $C_i$。这份供给总有数学实例：$n_i=1$ 取唯一的一维单位向量；$n_i=2$ 取第 82 章的 $|G_2\rangle$，其 $C_i=\sqrt2F_2^*$；$n_i\ge3$ 可取定理 84.6 的显式族，或任一满足完整核条件的已指定纯向量。定义迹一数学正元

$$
(\Xi_\psi)_{iii}=\beta_i|\psi_i\rangle\langle\psi_i|,\qquad
\beta_i=\frac{n_i}{n}>0,\qquad
(\Xi_\psi)_{ijk}=0\ \text{若不全相同}.
\tag{84.22}
$$

这是跨中心的奇异混态，而不是要求整个三份载体上的纯态。$\beta_i$ 是该测试正元的数学质量，不重标任何原输入质量，也不强迫每个原态的中心质量非零。

**定理 84.12（不等维、标量及所有转移的精确证书）。** 对定义 84.11 的固定探针、每个非负三腿权重（和为一）及每个 HP $\Phi:\mathcal A\to\mathcal A$，

$$
\boxed{\mathcal K_{3,\alpha}(\Phi)(\Xi_\psi)\ge0
\quad\Longleftrightarrow\quad\Phi\text{ CP}
\quad\Longleftrightarrow\quad\mathcal K_{3,\alpha}(\Phi)\text{ 全锥正}.}
\tag{84.23}
$$

这里不要求不可约、相等块维数、各权重严格正或实际副本生成。

**证明。** 在输出 $iii$，只有种子 $iii$ 能贡献，因为别的全相同标签种子不可能只改一腿就变为 $iii$。该块恰为 $\beta_i\mathcal K_{3,\alpha}(\Phi_{ii})(\rho_{\psi_i})$，经 $C_i$ 压缩为 $\beta_iJ(\Phi_{ii})$，所以输出 PSD 给全部对角 Choi 块 PSD。

先核对非对角转移所需的秩。每个 $CV_{\psi_i,\ell}=I$ 使 $V_{\psi_i,\ell}$ 单射。若 $\psi_i$ 在第 $\ell$ 腿的约化密度 $\rho_{i,\ell}$ 不满秩，可取非零 $H$ 消去其支撑，于是 $H^{(\ell)}\psi_i=0$，矛盾。故三个 $\rho_{i,\ell}>0$。对任意输出块 $j$，定义矩形线性作用

$$
V_{ji,\ell}:M_{n_j\times n_i}\longrightarrow
\mathbb C^{n_i}\otimes\mathbb C^{n_i}\otimes\mathbb C^{n_i}
\text{ 中将第 }\ell\text{ 因子换成 }\mathbb C^{n_j},\qquad
V_{ji,\ell}(H)=H^{(\ell)}\psi_i.
\tag{84.24}
$$

目标空间按该因子次序理解，未把不等维因子认作同一空间。直接按部分迹定义有

$$
\|V_{ji,\ell}(H)\|^2=\operatorname{Tr}(H^*H\rho_{i,\ell})
\ge\lambda_{\min}(\rho_{i,\ell})\|H\|_{\rm HS}^2.
\tag{84.25}
$$

故 $V_{ji,\ell}$ 单射，其最小奇异值平方恰为 $\lambda_{\min}(\rho_{i,\ell})$：取一行沿该最小特征向量即可取得等号。

对 $j\ne i$，若第 $\ell$ 腿活跃，输出标签在该位置是 $j$、其余两处是 $i$ 的块只能来自种子 $iii$ 的这一腿。对矩形 Choi 作带符号分解，所得块准确是

$$
\beta_i\alpha_\ell V_{ji,\ell}J(\Phi_{ji})V_{ji,\ell}^*.
\tag{84.26}
$$

其余种子与其他两腿均不落在这个块。单射 $V_{ji,\ell}$ 有线性左逆，压缩即得 $J(\Phi_{ji})\ge0$。至少一腿活跃，因此全部非对角转移也被检测；目标 $n_j=1$、源 $n_i=1$ 及其他不等维均适用。有限直和 CP 恰为所有分量 CP，理由仍是中心包含／投影与任意放大后的逐输出正和，故 $\Phi$ CP。反向每个一腿扩张 CP，非负权和全锥正，特别在 $\Xi_\psi$ 正。证毕。

定义 84.11 的全三腿解码性质使同一个探针适用于任意权重。若只讨论预先固定的活跃集，则每个块对该活跃集满足 (84.7) 已足够：所需满 Schmidt 秩只在被选的活跃腿上使用，直接由该腿的左逆得到。零权腿无须额外认证。若把某个种子的 $\beta_i$ 置零，就会失去本证明对该输入块的检测，不能借“原模型允许零质量”删掉正权测试种子；反过来，也不能把测试种子的正权要求加到所有原态。全经典直和正性本就等于 CP；定理 84.10 的单个非经典块噪声障碍没有被外推到全经典系统。

**推论 84.13（全扇区的非最优近似修正）。** 在上述普通总迹坐标中若 $\mathcal K_{3,\alpha}(\Phi)(\Xi_\psi)\ge-\epsilon I_E$，选一腿 $\ell_*$ 满足 $\alpha_{\ell_*}\ge1/3$。令

$$
K_\psi=\max\left(
\left\{\frac{\|C_i\|^2}{\beta_i}:i\in I\right\}
\cup
\left\{\frac1{\beta_i\alpha_{\ell_*}\lambda_{\min}(\rho_{i,\ell_*})}:
 i\in I,\ \exists j\ne i\right\}\right),\qquad\delta=K_\psi\epsilon.
\tag{84.27}
$$

没有非对角转移块时省去第二集合。则 $\Phi+\delta\Delta_A$ CP，其中 $\Delta_A(X)=u_A(X)1_A$。若 $\Phi$ TP，

$$
\widehat\Phi=\frac{\Phi+\delta\Delta_A}{1+n\delta}\text{ CPTP},\qquad
\|\Phi-\widehat\Phi\|_\diamond\le2n\delta.
\tag{84.28}
$$

**证明。** 对角块由 $C_i$ 压缩给 $J(\Phi_{ii})\ge-(\|C_i\|^2/\beta_i)\epsilon I$。非对角块用 (84.25) 的最小范数左逆，其范数平方为 $1/\lambda_{\min}(\rho_{i,\ell_*})$；压缩 (84.26) 给第二集合的下界。故所有 $J(\Phi_{ji})\ge-\delta I$。$\Delta_A$ 的各矩形 Choi 块恰为对应单位矩阵，相加即 CP。$u_A\Delta_A=nu_A$，所以分母恢复 TP。$\mathcal R=\Delta_A/n$ CPTP，$\Phi-\widehat\Phi=n\delta(\widehat\Phi-\mathcal R)$，按 (82.9) 的直和完全有界迹范数给结论。常数依赖已指定探针的条件数，未声称最优或与滤波条件数无关。证毕。

### 84.8 完整静态候选仍是原定义之间的约束

**定义 84.14（保留 (81.14) 的全前件）。** 静态部分准确取 (81.14)，而不是由探针倒推 Born／CP。展开其承重域如下。每个非零有限实 $X=A,D,E$ 有闭尖生成锥、非零正元上严格正的原 $u_X$、整个紧态基及全部 proper 效应。纯参照比较是

$$
T^X_\xi(x)=\inf\{f(x):0\le f\le u_X,\ f(\xi)=1\}.
$$

比较入口用定义 80.1 所引 $\mathrm{PRE}_0^{\rm mix}$ 的全部纯 $\xi,\eta$、全部原混态 $x$、全部 $t\in[0,1]$ 上的混合余项二元律；先按 77.19 恢复每个有限纯族和任意概率权的完整 $S$，再进入原一般有限 EJA 忠实桥。正对偶生成、忠实态效应对应、共同框架、面投影、项目性与滤波纯性等完整条件均保留，不把纯端互反、自对偶或固定有限比较目录当作该桥。也可直接使用完整 $S$ 的原入口。允许异型直和、秩一和 Albert；复型是后果。

唯一供应的接合与读回仍为整个原锥上正的 $L:D\times A\to E$、$p:E\to D$，原 $\omega=1_D/\tau_D1_D$。$K=pL(\omega,-)$、$M=pL(K(-),-)$、$Q=L(M(-,-),-)$ 使用同一个 $p$ 两次；保留两实张成与全部实 $a,b$ 上的 $Z:B_1M(a,b)=u_A(a)Jb$，$J=M(-,1_A)$、$H_{\rm s}=L(-,1_A)$、$B_1=pH_{\rm s}$。正性覆盖纠缠输入，不把正乘积当作整个联合正锥的生成假设。

全部原完整本原框架、原规范迹和未经重标的单位进入 81.1—81.4 的投影轨道、$\mathsf P_A$、$v_A$、$\Gamma_z$；要求 (81.8c) 的 $\langle\Gamma_z,v_A\rangle_{\rm HS}=0$。此零收缩先恢复完整 $D_J,D_H$ 及同一 PRE。归一化用定义 81.7 的数学 $R_A(a)=u_A(a)1_A/n$、两条 $\mathsf E_2,\mathsf E_3$ 和原锚 $\mathrm A_0:u_EL(\omega,1_A/n)=1$；量词遍及全部原正输入、零输入及不等质量。$R_A$ 是固定数学见证，不供应实际重置程序。完整静态条件为

$$
\mathsf S_{\rm orig}:=
\mathrm{PRE}_0^{\rm mix}
+\langle\Gamma_z,v_A\rangle_{\rm HS}=0
+\mathsf E_2+\mathsf E_3+\mathrm A_0+\mathrm H13.
\tag{84.29}
$$

$\mathrm H13$ 只在 PRE 恢复后按原内在块读取：同一个总迹一原混态在每个两端秩至少二的活跃有序块有严格正质量，且至少一个原边缘铺回差有严格负方向；伴随使用原规范迹，铺回使用未经维数归一化的单位。非活跃块为任意 PSD 分量含零，无活跃块时资格为整个态基。要求这个同一合格态的整个原 $I^{\rm raw}$ 输出正，不能逐块另选态、条件化、运输到新态或由输出反选资格。等价方向入口 NB 则要求每个活跃块条件联合纯而内在边缘混，活跃质量严格正，其他量词同前；不把 NB 的纯性定义加到 H13，亦不把 H13 资格当作未恢复块结构时的定义。

由 81.8，(84.29) 与同一原 $\mathrm{PRE}+C_{\rm joint}+\mathrm{C13}$ 等价：完整比较及 EJA 桥、零关系先给形状，两条质量关系及同 $p$ 与原锚先给尺度，原 H13 或 NB 才排除错误相对转置。也可完整采用 (80.14) 的最大缺陷与 $\mathsf{Mass}_{t,s}$ 版本，包括其全实固定泛函条件及严格 $t,s\in(0,1)$；它只是既有同类替代表述。上述归一化权重条件与本章探针可用权重端点分属不同接口，不相互替换。


### 84.9 逐实际事件、分支与完整记录的同一全实提升

**定义 84.15（原事件上的探针入口）。** 先在定义 84.14 的同一原元组上取得 (79.17) 的普通且标准归一坐标。逐个固定已经供应的原同载体事件 $e:A\to A$、其全部实际分支、完整记录、输入输出类型及原合法域；每个分支也作为其自己的指定映射处理。令其原实线性映射的唯一复 HP 延拓为 $\Phi_e$。另须供应同一事件的原实线性 $P_{E,e}$，在**全部原实输入**上满足 (82.22)：

$$
\begin{aligned}
P_{E,e}Q(a,b,c)={}&\alpha_{e,1}Q(\Phi_e a,b,c)
+\alpha_{e,2}Q(a,\Phi_e b,c)
+\alpha_{e,3}Q(a,b,\Phi_e c),\\
&\alpha_{e,\ell}\ge0,\qquad\sum_{\ell=1}^3\alpha_{e,\ell}=1.
\end{aligned}\tag{84.30}
$$

该关系与其记录、ready、控制、参考、副本、钟及未来合同均是来源前件。探针另取定义 84.11 的 $\Xi_\psi$；对已固定事件权重，也可逐块仅要求相应活跃集的 (84.7)。不从静态比较、矩阵综合或存在菜单推断探针的实际制备。第 79 章用于质量校准的存在见证 $\Phi_{\rm cal}$ 不等同任意指定 $\Phi_e$；它也不供应 (84.30)。

**定理 84.16（在共同供应数据上准确替换 CP 入口）。** 对定义 84.15 的每个实际事件及每个实际分支，

$$
\boxed{P_{E,e}(\Xi_\psi)\ge0
\quad\Longleftrightarrow\quad\Phi_e\text{ CP}
\quad\Longleftrightarrow\quad P_{E,e}\text{ 全锥正}.}
\tag{84.31}
$$

单块中，若指定纯探针不满足相应活跃核条件，则命题 84.5 给同一代数式上的强正非 CP 反模型，因此 (84.7) 是准确边界，非仅一个充分探针配方。

**证明。** 原 $Q$ 的全部实乘积张满整个 $E$，所以 (84.30) 在普通坐标中唯一规定 $P_{E,e}=\mathcal K_{3,\alpha_e}(\Phi_e)$。定理 84.12 或其固定活跃集版本给全部等价。全实唯一性并未供应各加项作为分别可调用的实际单腿分支；正性测试也未增加 TP、TNI、预算或实际参考前件。单块反模型是同一数学提升律与探针条件的反例，不能因此宣布原源存在该非 CP 程序。证毕。

如果同一事件另已供应 (82.24) 的完整二层递归律并且原 $P_{D,e}$ 全锥正，则 82.5 已给 $\Phi_e$ CP，故这里的三腿正性自动成立；不重复把该已得 CP 当作新的来源支付。反过来，只有质量相等并不供应该递归律。

未校准但已用 PRE+NB 或 PRE+H13 取得共同普通方向的类，仍可精确复用 82.12：$M=\mathcal C_Dm$、$Q=\mathcal C_Eq$，$\mathcal C_D,\mathcal C_E$ 为逐块正定可逆合同，逆也 CP。在同一全实提升律下唯一有

$$
P_{E,e}=\mathcal C_E\mathcal K_{3,\alpha_e}(\Phi_e)\mathcal C_E^{-1},\qquad
\Xi_{\psi,\rm raw}=\frac{\mathcal C_E\Xi_\psi}{Z_\psi},\qquad
Z_\psi=u_E(\mathcal C_E\Xi_\psi)>0.
\tag{84.32}
$$

可逆合同反射 PSD，所以 $P_{E,e}(\Xi_{\psi,\rm raw})\ge0$ 仍等价于 CP。该归一化仅定义数学测试态，不重标实际原数据、不供应滤器或准备。若原输出只大于 $-\epsilon I$，退滤波先得到 $\mathcal K_{3,\alpha_e}(\Phi_e)(\Xi_\psi)\ge-Z_\psi\epsilon\mathcal C_E^{-1}(I)$；没有 $Z_\psi$ 和逆滤波范数的控制，不能套用 (84.27)—(84.28) 的普通坐标常数。

所以完整增广候选是 (84.29)、逐事件 (84.30)、所给探针的相容条件及逐事件输出正性，并完整合取其他原操作合同。与原逐事件 CP 谓词的等价只在这份**同一已供应增广数据**上成立；CP 谓词本身不构造实际提升或探针。其他输入输出类型的原事件继续使用其原同事件参考／递归参考 CP 入口，不能从同载体定理外推全部 typed 过程。

### 84.10 Born、张量、Kraus、更新与物理时间的完整回接

**推论 84.17（所有消费者各守其原前件）。** 定义 84.14—84.15 的原数据、探针及事件条件成立，并保留下述各消费者的全部原来源合同，便得到相应量子结论。本章扩展 CP 测试的纯探针几何，不减去这些合同。

**证明：静态与 Born。** 首先调用 81.8，不用探针重证一般 Jordan 或复分类。在保原单位、原规范迹和比较的忠实坐标中，第四卷 65—66、75.7 及 (79.17)、(79.27) 给

$$
\begin{gathered}
A=\bigoplus_i\operatorname{Herm}_{n_i}(\mathbb C),\qquad
D=\bigoplus_{i,j}\operatorname{Herm}_{n_in_j}(\mathbb C),\qquad
E=\bigoplus_{i,j,k}\operatorname{Herm}_{n_in_jn_k}(\mathbb C),\\
\rho_i\ge0,\quad\sum_i\operatorname{Tr}\rho_i=1,\quad0\le f_i\le I_i,\qquad
\Pr(f\mid\rho)=\sum_i\operatorname{Tr}(f_i\rho_i),\\
M(a,b)_{ij}=a_i\otimes b_j,\qquad L(d,c)_{ijk}=d_{ij}\otimes c_k,\\
(pz)_{jk}=\sum_i\operatorname{Tr}_iz_{ijk},\qquad
(p_{13}z)_{ik}=\sum_j\operatorname{Tr}_jz_{ijk}.
\end{gathered}\tag{84.33}
$$

同块纯态几何是复射影空间、纯比较是内积模方；不同中心块比较零。整个态基、效应区间、零及不等中心质量、相关和纠缠输入保留。这个 Born 结论以完整比较与忠实桥为前件，不从测试态的数学写法假设旧 Born。张量结论仅识别给定的二份、三份原载体及共同普通方向；不自动识别独立另一括号、四份以上、全部原有实际联合来源或无限维一致性。

**证明：CP、矩形 Kraus 与实际仪器。** 对已供应 (84.30) 的同载体事件，84.16 给每个 $J(\Phi_{e,ji})\ge0$；有限谱分解和成熟矩形 Choi 定理于是给

$$
\Phi_{e,ji}(X)=\sum_\nu K_{e,ji,\nu}XK_{e,ji,\nu}^*,\qquad
K_{e,ji,\nu}:\mathbb C^{n_i}\to\mathbb C^{n_j}.
\tag{84.34}
$$

其他类型的原过程仍按第四卷 69.1—69.11 或固定源 50—73 的完整 typed／实际递归参考合同取得自己的 CP，不能以一个三腿平均替代实际环境、输出与全未来。数学 Kraus 分解不给操作实现、独立调用或制备。

对一份已经供应同族、细分支、全部记录及真粗粒化接头的有限全矩阵实际仪器，令 $a$ 为全部结果标签，$F^a_{ji}=\sum_\nu K_{a,ji,\nu}^*K_{a,ji,\nu}$。第 69 章未校准旁观者族的两条预算仍须同时满足

$$
\sum_{a,j}F^a_{ji}\le I_i,\qquad
\sum_{a,j}F^a_{ji}\otimes u_{jk}\le I_i\otimes u_{ik}
\quad\text{对全部原输入 }i\text{ 和旁观者 }k.
\tag{84.35}
$$

次单位只给 TNI，原完整实际菜单两边总 TP 才取等号。采用 (84.29) 的标准归一化后 $u_{ik}=I_k$，完整仪器条件相合为 $\sum_{a,j,\nu}K_{a,ji,\nu}^*K_{a,ji,\nu}=I_i$。顺序复合须保原实际接线；真粗粒化才可求分支和；共同重置补全还须 69.8 的输入行权重一致及同族合同。全部原菜单、固定支撑与每个已量化中间切口仍各在原域成立，不能只留接受分支。无限维、非离散或无限记录的消费者仍须各自正常物理表示、前对偶、可数可加与收敛来源。

**证明：质量、条件化与 Lüders。** 对原未归一输入 $x=(x_i)\ge0$，结果 $a$ 的原输出为 $y_{a,j}=\sum_{i,\nu}K_{a,ji,\nu}x_iK_{a,ji,\nu}^*$，其质量是 $m_a=\sum_j\operatorname{Tr}y_{a,j}$；输入总质量为 $m=u_A(x)$。只有 $m>0$ 时才将 $m_a/m$ 读作该输入下的条件概率，且只有 $m_a>0$ 时才定义结果后条件态 $y_a/m_a$。零质量分支不作除法，其程序标签、记录、失败／停止／销毁及未来权限仍保留，不由零矩阵识别历史。

Lüders 还要求同一 CP 分支具有锐投影效应 $P$，并对每个确定接受归一态逐点不变，连同原完整输出校准。单矩阵块中，该效应先使每个 Kraus 消去 $P^\perp$；所有 $P$ 内纯态保持使每个 Kraus 在 $P$ 的每条射线上为标量，线性性再使其在 $P$ 上为同一个标量倍数，效应归一给这些模方和一。因此该原分支才是 $x\mapsto PxP$。按原块与类型合同复用 69.11 的版本；仅相同效应、概率、CP、重复性或菜单完备性均不唯一决定更新。

**证明：Hamiltonian。** 此消费者另需原物理时间参数上的连续、时间齐次、可逆 $*$-自同构群，并有实际逆、原时钟、单位及所需动态源。有限中心的连续群不作离散块置换，各有限矩阵块的连续生成元为内 $*$-导子，故可写

$$
U_i(t)=e^{-itH_i/\hbar},\qquad
\dot\rho_i=-\frac i\hbar[H_i,\rho_i],\qquad H_i=H_i^*.
\tag{84.36}
$$

$H_i$ 有加标量自由度。共同正 $\hbar$、时间／能量单位与其物理对应来自原动力学合同，不从静态核条件产生。无限维的强连续性、生成元域及所有原单位条件继续按有限返回卷 162.2 第七项的完整递归来源保留。原钟、控制、旗标与记录不因写下指数式而供应。证毕。


### 84.11 原来源的准确进展、未接头及几何白话

**原具名接受接口。** [固定来源卷 §23.3、式 (23.7)](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md)要求对每个原切口、准备、参考及允许记录副本、每条原合法 analyzer 字 $b$ 和坐标子集 $J_0$，在同一原输入与未归一标尺上，将字面旧程序的接受族接到实际全菜单事件 $k_b^\dagger P_{J_0}k_b$。允许的当前接受证书可由原重接、回连或共同细分提供，不要求整条历史双射；它仍须保原程序、输入输出类型、ready、参考、控制、钟、互补结果、完整记录和合法未来。本章没有构造该证书。

该卷 (23.3) 已显示为何矩阵相等不足：原负相位字两次有 $\phi(L_-^2)=I_3$，但原负载为 $\epsilon(L_-^2)=\operatorname{diag}(4,1,1)$。同一个可见矩阵不能确定输入形状相关负载、CountRead 失败或旧接受归属。$Q>0$ 的已付数值校准不能扩到独立正质量而 $Q=0$ 的平衡表。共同解码器压缩的是局部作用产生的矩阵，它也不会把这个源差别变成同一事件；纯向量校准、存在菜单、操作逆字及精确矩阵综合均不代付 (23.7)。

**原活动返回。** [有限返回卷定义 164.1](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md)准确区分增加只读控制、活动凭据及条件地址服务的候选 $R^{\mathsf P}_{r_\star}$ 与原 $B_{r_\star}$。候选与不能返回的发生标识反模型已分离档案保存和活动资源；它们没有构造原 $B_{r_\star}[h_\star]\to A_{\rm ready}[h_\star]$ 接头、全参考／控制／钟与全部旧未来对应。本章的纯探针、伪逆或 CP 数学修正也没有构造它。该卷 162.1—162.2 的七项消费者及其完整递归原前件在原准确域上继续适用，不能用本章的有限直和接口摘要替换。

**已取得的来源不倒称缺失。** 固定源 50—73 的实际全未来下降、参考、递归支持、typed CP 与 C128 的相应原 $D$ 恢复，各保其已证域；固定源 74—85 的近似参考／容量结果也保留其精度、深度、支持和来源条件。它们不是上述接受或 active-ready 接头的无条件构造，但也不是本章待从零重做的内容。有限返回卷 165 的同时正常完成仍以其已供应的全类型图和混合完整性为前件，本章没有从探针反推该图。

[原观察第二卷 §§10—19](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ORIGINAL_INTERFACE_EXPOSURE_AND_RECOVERY_II.md)的范围比只在 completed canonical GuardAcquired 边界恢复更广：在明示的新原始 boot $G_O$、单一原源及理想顺序 constructed-tape 基础中，原单元接收器的初始 pre-IN、两 bit 的 post-IN／EX／WR／RD、已达 testing-CTL、post-MR 切口均有四份真实来源体的付费构造、接收、独立解码及实际原生续接；含任意有限未完前缀、有限外轮重复和三个内部阶段，不要求未来补零。Theorem 18.3 与 Proposition 19.3 保留所有原始输入、完整记录、权限、响应、成本及 owed 原行一次执行；completed-entry、Plan／Send／服务完整返回、历史与终端消费者按原合同继续成立。

其基础物理符合性仍是来源定义 10.1 的 `ASSUMED-UNVERIFIED`；结论是该理想基础内的有限数学程序规范与构造性证明，不是印出的扩展安装字、已装执行工件或物理验证。它不改写已达旧 $G_C/G_V$，不覆盖任意 Busy、compiler／descriptor／loan／copy 内部切口、非规范准备／程序／先验或向未变旧安装运输。新增行的原 $Q$ 核、跨 entry 的原 $Q$ 等价、完整原终端任务核、结构最小性及物理实现仍在其明示边界之外；逐次有限完成不给无限未完 guard、未来外部结束、统一有限资源／截止或 halt 后重入。上述真实源进展没有被缩回 §9，也没有被本章扩大成量子全源证明。

**完整普通中文。** 想象有三个位置拿着同一份总规则，每次只让其中一个位置执行同一个局部变化，然后把三个结果按固定权重相加。要判断这份局部变化在任何相关参考面前都是否合法，不能只看总量是否正确，也不能只说三个位置各自都合法；平均可能把不同坏方向互相遮住。

本章先问更原始的关系问题：把三个局部矩阵分别作用在同一纯张量上，若三份作用相消成零，那么三个原矩阵的和是否也必为零？若答案是肯定的，同一观察结果的所有表达方式都对应同一个矩阵和，因此可以在作用的像空间上定义一个共同读回。这就是相容商。它使事件落在任何活跃位置时，读出的都恰好是同一个局部矩阵，而不是三个互不一致的替身；压缩整个输出便精确恢复 Choi 矩阵，负方向无处藏。

必要性也有内容。先把单位输入的输出当作尺，将一个纯方向的输出归一化。如果它在任何方向都没有完全碰到这把尺的上边界，就可以把该输入方向往负处推一点，而输出仍为正，说明测试漏报。若从不漏报，每个方向必须有碰边的读数。三个局部读数原本还可有不同倍率；但单位在所有位置都产生同一个原张量，这个共同锚点迫使与单位不正交的方向使用相同倍率。这样的方向已张满全部矩阵空间，于是共同读回被迫存在。不能只把一个充分构造命名为“必要”；必要性来自这条归一化与共同锚点论证。

GHZ 是把“同一个矩阵”藏在三个相同标签的特殊铺法。新的显式族在这些标签之外加上小量的三标签互异项：若还想用非对角局部动作抵消，每个最大矩阵元只能由严格更小的总量抵偿，矛盾，所以非对角动作全被排除；剩下的三组对角数又被完整互异标签关系锁成总和为零的三个常数。三维的最后一步有自己的证明，不靠第四个标签。这给每个 $d\ge3$ 一份具体数学探针，并解释为何一般纯张量也合格；qubit 虽无法拥有这种最小稳定子，仍可用 GHZ 的较大而相容的核。乘积态、W 态乃至独立改一腿标架后的 GHZ 则显示“纠缠足够强”或“局部酉等价”都不是准确判据；准确判据是相消关系与矩阵求和是否相容。

中心标签也不能省。每个输入块都放一份正权种子，原事件把标签转到另一个不等维块时，输出的特殊标签位置就单独暴露这次转移；满 Schmidt 秩保证矩形矩阵没有被压掉。原输入仍可有零或不等质量，测试种子的配重并未改写这些输入。若只知道输出接近正，解码器的条件数给一份明确但不声称最优的 CP 数学修正；这不修复原程序或其未来。

纯张量的精确相消结构也解释噪声边界。混入满秩噪声后，某个 CP 边界映射的每个固定输出都有正裕量；将映射向非 CP 侧推动一点，有限目录仍看不出。不同但有限的张量份数也不能消除这个有限正裕量。这与纯态流形内部的稳定性不冲突，也不是说过程层析或所有混态探针都不可能。

最后，把这份几何放回原问题时，状态、效应、比较、同一个读回两次、所有原菜单与实际事件先保持原身份。原静态定理负责 Born 与张量，逐实际事件的全实关系负责把三腿读数接到同一个事件，预算和中性条件才负责仪器与更新，真实连续时间群才负责 Hamiltonian。共同解码器没有替原源制造 analyzer、活动返回、准备、参考、副本、控制或时间。所得简化准确说是取消特定 GHZ 形状限制、改用一条必要且充分的局部作用关系；不是减少已独立承担的物理前提，也不是原世界里的一切已从定义自动产生。

**文献与结论归属。** [DMW] H. Derksen、V. Makam、M. Walter，*Maximum likelihood estimation for tensor normal models via castling transforms*，[arXiv:2011.03849v1](https://arxiv.org/abs/2011.03849v1)，[v1 原文 Theorem 1.5](https://arxiv.org/html/2011.03849v1) 的第 (4) 项、Definition 2.2、Corollary 2.11 及 §4；正式出版 Forum of Mathematics, Sigma **10**, E50，[DOI](https://doi.org/10.1017/fms.2022.37)。本章的定理编号明确属于 v1，其一般张量稳定性是成熟结果；不把出版版本中其他编号移植到 v1。这里实际需要的 GL 核由 84.6 直接计算，而不是从局部酉稳定子或未核对的项目缩放推断。

[C] Choi (1975)、Jamiołkowski (1972) 的准确原文与 [Watrous，Theorems 2.22、2.26](../../../Library/Quantum/watrous2018theory.md#complete-channel-representations) 按本卷 82.8 的条目使用。带符号 Choi 分解、有限谱论、Moore–Penrose 逆、最小奇异值连续性、非零多项式零集及有限维正定性开放都是成熟工具。第三方稳定子文献不承担原实际菜单、参考、控制或活动接头。

[R] 本卷 79.1—79.15、80.14、81.14、82.1—82.14 及[第四卷 §§65—72](QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_IV.md)给完整原静态桥、质量、方向、同事件关系、矩形 Kraus、两预算和消费者条件；固定来源卷 §23、有限返回卷 §§162、164—165 与原观察第二卷 §§10—19 的上述原域不变。本章的仓内纸面推导是共同锚点下的序反射充要定理、其任意纯探针精确应用、失败时的强反模型、各维显式 GL 核构造及相应扇区／稳定性／满秩目录边界。不主张穷尽文献、历史优先权或全球原创。

完整原 $\Omega$ 的所有准备、事件、过程、参考、副本、实际相关联合、零／不等／次归一质量、原时钟与单位、控制、ready／flags、完整记录、失败、拒绝、停止、销毁、返回、全部仍合法未来，以及旧固定 $S$、全菜单和每个已量化中间切口义务均保留；未定义请求不补零。没有免费准备生成、复制、相干控制或实际彩票。实际 (23.7) 与原 $B_r$ 的 active-ready 连接未由本章供应；自然原探针选择、额外括号与四份以上相容性、完整原来源及更少独立物理公理未由这些纸面定理推出。完整量子起源目标保持 active／incomplete。

## 追加锚（本行以下为增补区）
