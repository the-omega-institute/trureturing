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
