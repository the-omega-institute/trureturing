# QUANTUM ORIGIN: ENDOGENOUS CUT ATLAS AND DISCRETE RECONSTRUCTION BOUNDARIES IV

## 1. 全载体入口与未归一化的二元恢复

### 1.1 比较、规范迹与原始映射

**定义 64.1（有限比较入口与另行的 Jordan 桥）。** 对每个实际载体 $X=A,D,E$，取非零有限维实有序空间、闭尖生成锥 $X_+$、严格正归一化泛函 $u_X$、紧的全态基底 $K_X=\{x\in X_+:u_X(x)=1\}$ 和全部对偶效应 $[0,u_X]$。记纯态集合为 $P_X$。对每个 $\xi\in P_X$、$x\in K_X$ 定义

$$
T_\xi(x)=\inf\{f(x):0\le f\le u_X,\ f(\xi)=1\}.
$$

在三个实际载体上分别要求有限混合律 $S$：对任意整数 $\ell\ge1$、任意 $\xi,\eta_1,\ldots,\eta_\ell\in P_X$ 及任意 $w_j\ge0$、$\sum_jw_j=1$，

$$
\mathrm{(S)}\qquad
T_\xi\!\left(\sum_{j=1}^{\ell}w_j\eta_j\right)
 =\sum_{j=1}^{\ell}w_jT_{\eta_j}(\xi).
$$

另行保留三个实际载体各自到有限 Euclidean Jordan 代数的保归一化条件桥。桥后仍使用整个平方锥、所有正规范迹一态及全部效应 $[0,1_X]$；每个简单直和扇区的每个本原幂等元都有规范迹一。此桥是独立前提，不由这里的 $S$ 或其单点端点互反直接代替。记

$$
\langle x,y\rangle_X=\tau_X(x\circ y),\qquad
n=\tau_A(1_A)>0,\quad m=\tau_D(1_D)>0,\quad
R_E=\tau_E(1_E),\qquad e=1_A/n,\quad\omega=1_D/m.
\tag{64.1}
$$

这些迹等于各代数的秩，不允许扇区重标度。所有伴随均取这些固定的规范迹内积。张量积只指实向量空间张量积及其乘积内积，不预设张量正锥。

**定义 64.2（同一个读回的完整候选前置条件）。** 唯一原始映射为实双线性 $L:D\times A\to E$ 和实线性 $p:E\to D$，要求

$$
L(D_+,A_+)\subseteq E_+,\qquad p(E_+)\subseteq D_+.
$$

第一个量词覆盖所有实际 $d\in D_+$，包括纠缠正元；第二个覆盖整个 $E_+$。定义

$$
\begin{aligned}
B(d,c)&=pL(d,c),&K(a)&=B(\omega,a),&
M(a,b)&=B(K(a),b),\\
J(a)&=M(a,1_A),&r&=J^*,&U&=J1_A,\\
H(d)&=L(d,1_A),&h&=H^*,&B_1&=pH,\\
Q(a,b,c)&=L(M(a,b),c).
\end{aligned}
\tag{64.2}
$$

$M$ 中两次出现的 $p$ 是同一个实际映射。$J,H$ 插入的是未归一化单位；$e,\omega$ 才是迹一参考。要求两条实际实张成

$$
\operatorname{span}_{\mathbb R}M(A,A)=D,\qquad
\operatorname{span}_{\mathbb R}L(D,A)=E,
\tag{64.3}
$$

并保留如下四条输入：

$$
\begin{gathered}
\mathrm{(D_J)}\quad a,b\in A_+,\ \langle a,b\rangle_A=0
 \ \Longrightarrow\ \langle Ja,Jb\rangle_D=0,\\
\mathrm{(Z)}\quad B_1M(a,b)=\tau_A(a)Jb\quad(a,b\in A),\\
\mathrm{(W_H)}\quad H^*H=n\,\operatorname{id}_D,\\
\mathrm{(N)}\quad \gamma:=\tau_D\bigl(p1_E\bigr)\le n^3.
\end{gathered}
\tag{64.4}
$$

$Z$ 量化全部实方向，$W_H$ 是整个实 $D$ 上的范数恒等式。两条张成不是可分态假设。这里尚无 $W_J$、完整 I、II、III、全局 $p$ 保迹或任一单位律。完整候选在第 3 节追加且只追加那里精确定义的 $I_{13}(\sigma_*)\in E_+$；该条件在两个归一化二元接口建立以后才使用。

### 1.2 所用纸面接口与基本支撑事实

**定义 64.3（二元接口及其适用条件）。** 采用 [Library 的二元边缘接口 (15)–(18)](../../../Library/QuantumStates/barnumhilgert2019spectral.md#positive-marginals-recover-the-joint-effect-contract)。它的输入是在本卷全态、全效应、每扇区本原迹一的有限 EJA 上，一个全正双线性准备 $G:X\times Y\to Z$，其乘积实张成 $Z$，及两个在整个 $Z_+$ 上正、规范保迹的边缘 $R_X,R_Y$，满足所有实 $x,y$ 的

$$
R_XG(x,y)=\tau_Y(y)x,\qquad R_YG(x,y)=\tau_X(x)y.
$$

其条件性纸面结论是：$R_X^*,R_Y^*$ 为保单位单射 Jordan 同态，在整个 $Z$ 上算子交换；它们的 Jordan 乘积就是 $G$，给出正的全联合效应、精确因子化配对和分离。$G(1_X,1_Y)=1_Z$，本原乘积本原，$\widetilde G:X\otimes_{\mathbb R}Y\to Z$ 是满迹内积等距同构，且秩、维数分别相乘。纯边缘刚性也在此接口后使用：正迹一联合态若一个边缘本原，则它是该本原态与另一个正迹一态的 $G$-乘积。这是明确保留的纸面接口，不把其输入当作已由 $D_J$ 自动获得。

证明中使用的成熟 EJA 事实如下。令 $\ell_x(y)=x\circ y$，标准二次表示为 $P_x=2\ell_x^2-\ell_{x^2}$。它全锥正；正可逆 $x$ 时，$P_x$ 是自伴随锥自同构，逆为 $P_{x^{-1}}$。对幂等元 $q$，$P_q$ 是到支撑面代数 $X_1(q)$ 的正交投影。若 $z=x^2\ge0$，Peirce 分解给出

$$
\langle q,z\rangle=\|x_1\|^2+\tfrac12\|x_{1/2}\|^2.
$$

零配对因此把 $z$ 放进 $X_0(q)$；谱展开表明两个正元零配对时，其支撑正交。正元 $z$ 在自身支撑面内可逆；该面中的本原元也是环境代数的本原元，因为它下面的任何正分解仍在该面。因此支撑面继承环境的规范迹，不存在可自由选择的迹倍数。谱分解和纯态事实取自 [Barnum–Hilgert, Theorem 4.2、Definition 4.3、Proposition 4.4](https://arxiv.org/html/1904.03753v1#S4)，二次表示正性与幂等元的环境算子交换判据取自 [van de Wetering, Propositions 2.12、2.21、2.25](https://arxiv.org/html/1912.01903v1#S2)。这些事实包括例外 EJA。

### 1.3 从零比较保持到正左逆

**定理 64.4（单位律之前的归一化二元接口）。** 定义 64.1–64.3 下，仅用正性、$M$ 实张成、$D_J,Z$，便有 $U$ 内点及正映射 $j:D\to A$、$s=jB_1:D\to A$。令

$$
C=P_{\sqrt U},\qquad F=C^{-1}M,\qquad
\alpha(a)=F(a,1_A),\quad\beta(b)=F(1_A,b),\quad V=s^*1_A.
$$

则 $F$ 满足完整归一化二元接口，而且

$$
\begin{gathered}
jJ=\operatorname{id}_A,\quad sM(a,b)=\tau_A(a)b,\quad
B_1=Js,\quad sK=\operatorname{id}_A,\quad\tau_A(s\omega)=1,\\
m=n^2,\qquad sC=\beta^*,\qquad V=U^{-1},\qquad\tau_D(V)=m.
\end{gathered}
\tag{64.5}
$$

此时不宣称实际 $M$ 等距、$U=1_D$、$s$ 保迹或完整 III；也未使用 $W_H,N$、$L$ 张成或插入正性。

**证明。** 对正 $a\le\lambda1_A,b\le\mu1_A$，有 $0\le M(a,b)\le\lambda\mu U$。若正元与 $U$ 零配对，它消去所有正乘积；正锥生成及 $M$ 张成使它为零。故 $U$ 内点。若 $a\ge0$ 且 $Ja=0$，同样的第二因子支配给出 $M(a,b)=0$。$Z$ 遂给出 $\tau_A(a)Jb=0$。若 $a\ne0$，规范迹严格正，便有 $J=0$，与 $U$ 内点矛盾。因此 $J$ 无非零正核。

$C$ 与其逆 $P_{U^{-1/2}}$ 均全锥正、自伴随，且

$$
C1_D=U,\quad C^{-1}U=1_D,\quad C^{-1}1_D=U^{-1},\quad
F(1_A,1_A)=1_D.
\tag{64.6}
$$

取任意完整本原框架 $(q_i)$。$D_J$ 使 $Jq_i$ 的支撑 $c_i$ 两两正交，其和为 $1_D$。在 $D_1(c_i)$ 内，$U$ 等于 $Jq_i$；二次表示的谱公式给出 $C^{-1}Jq_i=c_i$。所以 $\alpha$ 把每个完整本原框架映到一个正交幂等分解，谱展开和极化使它保单位且保 Jordan 乘积。若 $\alpha(a)=0$，则 $\alpha(a^2)=0$，从而 $J(a^2)=0$；无正核给出 $a=0$。故 $\alpha$ 单射。

置 $T=\alpha^*\alpha$。形式 $\langle\alpha x,\alpha y\rangle_D$ 正定且结合，因 $\alpha$ 保乘积而满足
$\langle T(x\circ a),y\rangle_A=\langle Tx,a\circ y\rangle_A$。因此 $T$ 与每个 $\ell_a$ 交换。它保持每个简单理想；在一个简单理想内，$T$ 的每个特征空间也是理想，所以 $T$ 在该理想上是严格正标量。故 $T^{-1}$ 正。由自对偶性，$\alpha^*$ 正，于是

$$
j=T^{-1}\alpha^*C^{-1}\ge0,\qquad jJ=\operatorname{id}_A.
\tag{64.7}
$$

$Z$ 和 $M$ 实张成立即给出

$$
\begin{aligned}
s&=jB_1,&sM(a,b)&=\tau_A(a)b,&B_1&=Js,\\
B_1K&=J,&sK&=jB_1K=jJ=\operatorname{id}_A,&
sJx&=\tau_A(x)1_A.
\end{aligned}
\tag{64.8}
$$

这里 $B_1K=J$ 正是 $M$ 的原定义。又 $K1_A=B_1\omega=J(s\omega)$，故

$$
1_A=sK1_A=sJ(s\omega)=\tau_A(s\omega)1_A,\qquad
\tau_A(s\omega)=1,\qquad\tau_D(s^*1_A)=m.
\tag{64.9}
$$

这只用了已定型的实际映射复合，没有施加额外的 $K$ 固定点条件。

接着完成二元接口的全部前提。令 $R=sC$。对 $b\ge0$，$F(q_i,b)$ 被正倍数的 $c_i$ 支配，故位于 $D_1(c_i)$。将这些块求和得到 $\beta(b)$，因而

$$
F(a,b)=\alpha(a)\circ\beta(b),\qquad
[\ell_{\alpha(a)},\ell_{\beta(b)}]=0,\qquad
RF(a,b)=\tau_A(a)b.
\tag{64.10}
$$

算子交换发生在整个 $D$：$\beta(b)$ 对各 $c_i$ 无 Peirce 半空间分量，故与每个 $c_i$ 算子交换，再对 $\alpha(a)$ 的谱分解线性化。此时 $\beta$ 只已知正且保单位，尚不预设保平方。

对任意本原 $q\in A$，$R_q=R P_{\alpha(q)}$ 全锥正，并且

$$
P_{\alpha(q)}F(a,b)=F(P_qa,b),\qquad
P_qa=\langle q,a\rangle_Aq,\qquad
R_qF(a,b)=\langle q,a\rangle_A b.
\tag{64.11}
$$

第一式由 $\alpha$ 同态及 (64.10) 中环境算子交换得到。若 $\widetilde Fz=0$，则 $\langle q\otimes g,z\rangle=\langle R_q^*g,\widetilde Fz\rangle=0$ 对所有本原 $q$、实 $g$ 成立；本原元实张成，故 $z=0$。$F$ 张成使 $\widetilde F$ 满射。现在才定义对偶准备

$$
G(f,g)=(\widetilde F^*)^{-1}(f\otimes g),\qquad
\langle G(f,g),F(a,b)\rangle_D
 =\langle f,a\rangle_A\langle g,b\rangle_A.
\tag{64.12}
$$

由 (64.11)，$G(q,g)=R_q^*g$ 对本原 $q$ 和正 $g$ 为正；谱展开给出 $G$ 全正，且可逆线性化使其张成 $D$。$\alpha,\beta$ 正且保单位，故 $\alpha^*,\beta^*$ 在整个 $D_+$ 上正、规范保迹。(64.12) 给出全部实方向的

$$
\alpha^*G(f,g)=\tau_A(g)f,\qquad
\beta^*G(f,g)=\tau_A(f)g.
\tag{64.13}
$$

定义 64.3 的每一输入现已齐备，故可应用于 $(G,\alpha^*,\beta^*)$：$\widetilde G$ 为满等距同构。由于 $\widetilde G=(\widetilde F^*)^{-1}$，有 $\widetilde F=(\widetilde G^*)^{-1}=\widetilde G$。所以 $F=G$，$F$ 也是满等距，$m=n^2$，两嵌入现在都是 Jordan 同态，且 $F$ 具有纯乘积和精确全效应配对。由 $RF(a,b)=\tau_A(a)b$ 与张成，$R=\beta^*$，所以

$$
CV=R^*1_A=\beta1_A=1_D,\qquad
V=C^{-1}1_D=U^{-1},\qquad\tau_D(U^{-1})=m.
\tag{64.14}
$$

最后一个迹式来自 (64.9)，没有使用第一参考的范数条件。$\square$

## 2. 加权读回、支持面与共同参考校准

### 2.1 在两个单位律之前恢复完整 III

**定理 64.5（加权参考及全实三元读回）。** 在定理 64.4 的阶段，令 $w=s\omega$、$t=sp$。则 $w$ 内点、正迹一，并有

$$
\begin{gathered}
K(a)=M(w,a),\\
\mathrm{(III)}\quad B(M(x,a),b)=\tau_A(x)M(a,b)
 \quad(x,a,b\in A),\\
B(d,c)=M(sd,c)\quad(d\in D,c\in A),\qquad
tL(d,c)=\langle V,d\rangle_Dc.
\end{gathered}
\tag{64.15}
$$

这里尚未用 $w=e$ 或任一单位律。

**证明。** (64.14) 给出
$w=\beta^*(U^{-1})/m$。对每个非零正 $a$，$\beta(a)\ne0$ 且 $U^{-1}$ 内点，故 $\langle w,a\rangle>0$；(64.9) 已给出 $\tau_A(w)=1$。令 $\widehat K=C^{-1}K$。它全锥正，满足 $\beta^*\widehat K=sK=\operatorname{id}_A$，所以由 $\beta^*$ 保迹得到 $\widehat K$ 保迹；而
$\widehat K1_A=C^{-1}Jw=\alpha(w)=F(w,1_A)$。

对任意本原 $a$，纯第二边缘刚性给出 $\widehat K(a)=F(\rho_a,a)$，其中 $\rho_a\ge0$、$\tau_A(\rho_a)=1$。取含 $a$ 的任意完整本原框架 $(a_j)$。由 $\widehat K1_A=F(w,1_A)$，与 $F(x,a_k)$ 作等距配对，有
$\langle x,\rho_{a_k}\rangle=\langle x,w\rangle$ 对所有实 $x$ 成立。因此每个 $\rho_{a_k}=w$；每个本原可纳入这样的框架，谱展开给出 $K=M(w,-)$。同一个 $p$ 的两次定义遂给出
$B(M(w,a),b)=M(a,b)$。

取任意本原 $q,a,b$。$w$ 内点使某个 $\varepsilon>0$ 满足 $w\ge\varepsilon1_A\ge\varepsilon q$。正性给出
$0\le B(M(q,a),b)\le\varepsilon^{-1}M(a,b)$。
$F(a,b)$ 本原，$C$ 是锥自同构，故 $M(a,b)$ 位于极射线；存在非负 $\lambda_q(a,b)$ 使
$B(M(q,a),b)=\lambda_q(a,b)M(a,b)$。取含任意 $b$ 的完整本原框架 $(b_j)$，由 $B_1=Js$、$sM(q,a)=a$，

$$
\sum_j\lambda_q(a,b_j)M(a,b_j)=B_1M(q,a)=Ja
 =\sum_jM(a,b_j).
$$

$\widetilde M=C\widetilde F$ 单射，所以固定非零 $a$ 后这些向量线性独立，所有系数都等于一。三份本原元分别实张成 $A$，三线性延拓给出全实 III。再由 $M$ 张成，$B(d,c)=M(sd,c)$。施加 $s$ 得到 $tL(d,c)=\tau_A(sd)c=\langle V,d\rangle c$。此外

$$
\tau_DpL(d,c)=\tau_D M(sd,c)
\qquad(d\in D,c\in A)
\tag{64.16}
$$

仍只是复合迹式，尚非 $p$ 全局保迹。$\square$

### 2.2 只对第一二元接口选择类型和权重

**定理 64.6（早期有序扇区与未消去的权重）。** 在定理 64.4–64.5 的阶段，存在有限非空扇区集 $\Lambda$、整数 $n_i\ge1$、$n=\sum_i n_i$，及保迹 Jordan 序坐标，使
$A=\bigoplus_iH_{n_i}$、$D=\bigoplus_{i,j}H_{n_in_j}$，其中 $H_q=\operatorname{Herm}_q(\mathbb C)$。在此处的一种坐标选择中，保留每个有序对的独立转置位 $\varepsilon_{ij},\delta_{ij}$，并有严格正矩阵 $u_{ij}\in H_{n_j}$，使

$$
\begin{aligned}
F(a,b)_{ij}&=a_i^{T^{\varepsilon_{ij}}}\otimes b_j^{T^{\delta_{ij}}},\\
U_{ij}&=I_{n_i}\otimes u_{ij},\qquad
V_{ij}=I_{n_i}\otimes u_{ij}^{-1},\\
M(a,b)_{ij}&=a_i^{T^{\varepsilon_{ij}}}\otimes
 u_{ij}^{1/2}b_j^{T^{\delta_{ij}}}u_{ij}^{1/2},\\
(sd)_j&=\sum_i\left[u_{ij}^{-1/2}
 (\operatorname{Tr}_i d_{ij})u_{ij}^{-1/2}\right]^{T^{\delta_{ij}}}.
\end{aligned}
\tag{64.17}
$$

没有假设扇区交换对称，也未消去这些权重；特别是 $U$ 此时不必在 $D$ 的中心。

**证明。** 对已完成的 $F$ 接口，精确配对、单位、乘积本原性、张量等距和秩相乘均已成立。可复用 [Library 的扇区论证](../../../Library/QuantumStates/barnumhilgert2019spectral.md#sector-composites-without-a-connectedness-input)，其条件在此逐项齐备。具体地，两个嵌入满足
$\alpha(a)\circ F(c,d)=F(a\circ c,d)$，以及第二因子的对应式。简单扇区的中心单位 $z_i$ 在 $D$ 中的乘法算子是 $\ell_{z_i}\otimes\operatorname{id}$，只有零、一特征值，没有 Peirce 半空间，故 $\alpha(z_i)$ 中心；$\beta(z_j)$ 同理。其共同块
$D_{ij}=\operatorname{span}F(A_i,A_j)$ 为理想，具有乘积秩和乘积维数。

每个 $D_{ij}$ 简单：简单 EJA 的本原比较图连通；乘积比较因子化，故任意两乘积本原元可先沿第一因子、再沿第二因子连通。如果有另一个比较连通分支，其中本原元与所有乘积本原元正交；张成和非退化性迫使其为零。因此不存在第二分支。这解释了简单性及每个有序块的实际存在，不额外要求局部整体连通。

实际自块 $D_{ii}$ 的秩、维数分别是 $A_i$ 的平方。对秩大于一的简单 $A_i$，这恰为 [van de Wetering, arXiv:1803.11139v3 Proposition 40](https://arxiv.org/pdf/1803.11139v3) 的代数条件，选出复矩阵型；不借用该文 Theorem 3 的 sequential-product 额外条件。其分类核对包括：实矩阵维数平方低于秩平方后的最小简单维数，四元数矩阵维数平方高于最大值；秩二 spin factor 的维数 $d$ 要满足 $d^2\in\{10,16,28\}$，仅 $d=4$ 可行；Albert 情形要求秩九、维数 $729$，而可能维数为 $45,81,153$。秩一简单代数为 $\mathbb R$。随后 $D_{ij}$ 的秩 $n_in_j$、维数 $n_i^2n_j^2$ 由同一分类表选出 $H_{n_in_j}$，包括秩一、二边界。

对每个有序块，$\widetilde F$ 单射且保持秩一 Hermitian 乘积。按 [Xu–Zheng–Fošner Main Theorem, (1.1)–(1.2), p.409](https://doi.org/10.1017/S1446788714000603)，正规形为带各输入独立转置的可逆合同；相等维数去掉零填充，正性固定共同符号，迹因子化和秩一乘积张成迫使合同矩阵为酉。单活跃因子用同文 Proposition 2.1，全标量因子用正性与单位。将此处的输出酉吸收到 $D$ 坐标，得到 (64.17) 第一式；不要求各有序对的转置位相同。

对任意 $A$-框架，$U$ 是各 $Jq$ 支撑块中的正元之和，故与每个 $\alpha(q)$ 环境算子交换；谱展开给出与整个 $\alpha(A)$ 算子交换。在上述矩阵块中，$\alpha(a)=a_i^{T^{\varepsilon_{ij}}}\otimes I_{n_j}$，其交换子代数为 $I_{n_i}\otimes H_{n_j}$，所以 $U_{ij}=I\otimes u_{ij}$；$U$ 内点使每个 $u_{ij}>0$。$C=P_{\sqrt U}$ 在矩阵块上是 $x\mapsto\sqrt U x\sqrt U$，给出 $M,V$ 公式。由 $sC=\beta^*$ 求伴随，得到 $s$ 的整块公式。$\square$

### 2.3 每个本原方向的支持面，不预设保迹

**定理 64.7（$W_H$ 的全本原支持面）。** 加上 $W_H$ 和实际 $L$ 实张成。对任意本原 $q\in D$，令

$$
z_q=Hq,\qquad P_q^{\mathrm s}=\operatorname{supp}(z_q),\qquad
F_q=E_1(P_q^{\mathrm s}),\qquad K_q(c)=L(q,c),\qquad
v_q=\langle V,q\rangle_D>0.
$$

则 $K_q:A\to F_q$ 是序同构，正逆为 $t|_{F_q}/v_q$，并且

$$
\operatorname{rank}(F_q)=n,\qquad\|z_q\|^2=n,\qquad
R_E=mn=n^3.
\tag{64.18}
$$

这不使用 $N,p$ 保迹、$H1_D=1_E$ 或第二二元接口。

**证明。** $W_H$ 使 $z_q\ne0$，且与 $H(1_D-q)$ 正交。对 $y\in(F_q)_+$，正的 $h$ 满足
$\langle1_D-q,hy\rangle=\langle H(1_D-q),y\rangle=0$。支撑规则和 $q$ 本原给出 $hy=\langle z_q,y\rangle q$。对 $c\ge0$ 取 $c\le a1_A$，则作为整个 $D$ 上的正映射序，$0\le L_c\le aH$，故
$0\le L_c^*y\le ahy$。极射线 $\mathbb R_+q$ 迫使 $L_c^*y$ 为 $q$ 的倍数。又 $0\le K_q(c)\le az_q$，故 $K_q(c)\in F_q$。配对再实线性延拓给出

$$
\Pi_qL(d,c)=\langle q,d\rangle_DK_q(c)
\quad(d\in D,c\in A),\qquad \Pi_q=P_{P_q^{\mathrm s}}.
\tag{64.19}
$$

投影实际 $L$ 张成得到 $K_q(A)=F_q$。而 (64.15) 给出 $tK_q=v_q\operatorname{id}_A$，故 $K_q$ 单射且逆为所述正映射。这一步没有要求 $t$ 保迹。

在面 $F_q$ 内，$z_q$ 可逆且

$$
\Theta_q=P_{z_q^{-1/2}}K_q:A\to F_q,
\qquad K_q=P_{\sqrt{z_q}}\Theta_q
\tag{64.20}
$$

是保单位序同构。有限 EJA 区间 $[0,1]$ 的极点正好是幂等元：非零、一的谱值可作双向小扰动；反向用互补 Peirce 支撑规则。故 $\Theta_q$ 及其逆保持幂等元。一个完整框架映成幂等分解，其两两正交性由平方求和及正配对得出；谱展开和极化使 $\Theta_q$ 为 Jordan 同构。它保持本原元，而面本原元也是环境本原元，故保持继承的规范迹和谱。于是面秩为 $n$，$W_H$ 给出 $\|z_q\|^2=n$。

对任意完整 $D$ 本原框架 $\mathcal Q$，各 $z_q$ 支撑正交。$H1_D$ 内点：每个正 $L(d,c)$ 被 $H1_D$ 的正倍数支配，与它零配对的正元遂消去全部 $L$-乘积，再由张成消去 $E$。所以 $\sum_{q\in\mathcal Q}P_q^{\mathrm s}=1_E$。细化每个面到本原框架，得到完整环境框架，秩恰为 $mn=n^3$。面之间允许存在非零 Peirce 半空间；这里没有把这些面当成 $E$ 的向量空间直和。$\square$

### 2.4 循环行列式的每个重数

**定理 64.8（未归一化权重的精确平衡）。** 在定理 64.7 的阶段，令 $Y=p^*1_D\ge0$、$Y_q=\Pi_qY$、$\ell_q=K_q^*Y\in A$。可选择一个完整实际 $D$ 本原框架 $\mathcal Q$，使

$$
\prod_{q\in\mathcal Q}\det_A(\ell_q)=1,\qquad
\det_{F_q}(Y_q)=\frac{\det_A(\ell_q)}{\det_{F_q}(z_q)}.
\tag{64.21}
$$

所有行列式均为元素的 Jordan 行列式，即每个本原谱值的乘积，不是线性算子的行列式；分母幂次为一。

**证明。** 对任意本原 $q\in D_{ij}$，(64.15) 和 (64.17) 在所有实 $c$ 上给出

$$
\begin{aligned}
\langle\ell_q,c\rangle_A
 &=\tau_DpL(q,c)=\tau_DM(sq,c),\\
(\ell_q)_k&=v_q u_{jk}^{T^{\delta_{jk}}}\quad(k\in\Lambda),\\
v_q&=\operatorname{Tr}\!\left(u_{ij}^{-1}\operatorname{Tr}_i q\right)>0,\\
Y_q&=P_{z_q^{-1/2}}\Theta_q(\ell_q).
\end{aligned}
\tag{64.22}
$$

最后一式来自 $K_q=P_{\sqrt{z_q}}\Theta_q$ 的伴随及 $\Theta_q$ 的规范迹等距性，不假定 $Y=1_E$。每个 $\ell_q$ 内点，故 $Y_q$ 也为面内点。以 $\Theta_q$ 识别 $F_q$ 和 $A$，在每个已分类复矩阵块上，
$\det(z^{-1/2}\ell z^{-1/2})=\det(\ell)/\det(z)$。
对所有简单块相乘得到 (64.21) 第二式。这里的本原规范迹不产生维数或 Peirce 重数幂次。

令 $u_{ij}$ 的实际本征值为 $\lambda_{ij,s}>0$，$s=1,\ldots,n_j$。在 $D_{ij}$ 取第一因子的任意正交基及第二因子的 $u_{ij}$ 本征基，令
$q_{ijrs}=|r\rangle\langle r|\otimes|s\rangle\langle s|$，$r=1,\ldots,n_i$。所有有序 $i,j$ 的这些元组成 $\mathcal Q$。有 $v_{q_{ijrs}}=\lambda_{ij,s}^{-1}$，从而

$$
\begin{aligned}
\det_A(\ell_{q_{ijrs}})
 &=\lambda_{ij,s}^{-n}\prod_k\det(u_{jk}),\\
\prod_{i,j,r,s}\det_A(\ell_{q_{ijrs}})
 &=\left[\prod_{i,j}\det(u_{ij})^{-n n_i}\right]
   \left[\prod_{j,k}\det(u_{jk})^{n n_j}\right]=1.
\end{aligned}
\tag{64.23}
$$

第一括号中每个谱值重复 $n_i$ 次；第二括号中固定 $j$ 有 $\sum_i n_in_j=n n_j$ 个框架元。重命名第二括号的行、列指标后，每个有序 $\det(u_{ij})$ 的指数分别是 $-n n_i$ 与 $+n n_i$。转置不改行列式；没有交换 $i,j$，也没有假定 $u_{ij}=u_{ji}$。$\square$

### 2.5 一个上界同时强制两个单位律

**定理 64.9（共同校准、全局保迹及完整第二接口）。** 定义 64.1–64.3 的全部前置条件推出

$$
\begin{gathered}
U=1_D,\qquad H1_D=1_E,\qquad \gamma=R_E=n^3,\\
\mathrm{(W_J)}\quad J^*J=n\operatorname{id}_A,\qquad
\mathrm{(I)}\quad rM(a,b)=\tau_A(b)a,\\
\tau_A r=\tau_D=\tau_A s,\qquad r\omega=s\omega=e,\qquad
\tau_Dp=\tau_E,\\
\mathrm{(II)}\quad hL(d,c)=\tau_A(c)d,\qquad
 tL(d,c)=\tau_D(d)c,\qquad
\tau_Dh=\tau_E=\tau_At.
\end{gathered}
$$

$\widetilde M,\widetilde L,\widetilde Q$ 均为满迹内积等距同构。所有等式量化其类型内全部实向量。

**证明。** 将定理 64.8 的实际框架 $\mathcal Q$ 的各 $z_q$ 细化为完整环境谱表，恰有 $R_E=mn=n^3$ 个正谱值 $\zeta_\alpha$。$W_H$ 给出 $\sum_\alpha\zeta_\alpha^2=\sum_q\|Hq\|^2=mn=R_E$。第一次 AM–GM 因此给出
$\prod_q\det(z_q)\le1$，等号当且仅当每个 $\zeta_\alpha=1$。由 (64.21)–(64.23)，$\prod_q\det(Y_q)\ge1$。

另一方面，各面支撑和为 $1_E$，所以即使 $Y$ 有面外 Peirce 分量，仍有 $\sum_q\tau_E(Y_q)=\tau_E(Y)=\gamma$。各 $Y_q$ 的正谱表也恰有 $R_E$ 项。第二次 AM–GM 及 $N$ 给出

$$
\gamma\ \ge\ R_E\left(\prod_q\det(Y_q)\right)^{1/R_E}
 \ \ge\ R_E=n^3\ \ge\ \gamma.
\tag{64.24}
$$

所以每步都是等号：每个 $Y_q$ 谱值为一，$\prod_q\det(Y_q)=1$，继而 $\prod_q\det(z_q)=1$，第一次等号使每个 $z_q$ 谱值也为一。因此对所选框架 $Y_q=P_q^{\mathrm s}=z_q$，求和得到 $H1_D=1_E$。这里并未从压缩相等推出 $Y=1_E$。

由 $\ell_q=K_q^*Y$ 和 (64.22)，此时 $\ell_q=1_A$。故对每个 $i,j\in\Lambda$、每个 $s=1,\ldots,n_j$ 和每个 $k\in\Lambda$，都保留原式

$$
u_{jk}^{T^{\delta_{jk}}}=\lambda_{ij,s}I_{n_k}
\qquad\text{对全部 }i,j,s,k.
\tag{64.25}
$$

固定 $j$ 并任选一个输入 $i,s$，原式表明出行 $j$ 的每个矩阵均是同一严格正标量 $c_j$ 乘单位。故 $u_{jk}=c_jI_{n_k}$ 对所有 $j,k$，特别是 $u_{ij}=c_iI_{n_j}$；后者的实际谱值是 $\lambda_{ij,s}=c_i$。把这两个事实代回 (64.25)，得到 $c_j=c_i$ 对所有 $i,j$。于是 $U=c1_D$，$c>0$。已推得的 $\tau_D(U^{-1})=m$ 给出 $m/c=m$，故 $c=1$。论证包含一个扇区、标量扇区和 $n=1$。

现在 $C=\operatorname{id}$、$M=F$、$J=\alpha$、$r=\alpha^*$、$s=\beta^*$。第一二元接口给出完整 I、$r,s$ 全锥正保迹及 $\widetilde M$ 等距，特别是 $W_J$。又 $s\beta(x)=n x$，所以
$\langle s\omega,x\rangle=\tau_D(\beta x)/m=n\tau_A(x)/n^2=\langle e,x\rangle$；同理 $r\omega=e$。因此 $K=M(e,-)$ 是此时的推论。

必须再对每个本原 $q$ 证明 $Hq$ 为幂等元，而不限于所选框架：$Hq$ 与 $H(1_D-q)$ 正交且和为 $1_E$，支撑分解遂使 $Hq$ 等于其支撑投影。定理 64.7 的 $K_q$ 因而自身就是保单位 Jordan 同构到 $F_q$，保持继承的规范迹，故 $\tau_EL(q,c)=\tau_A(c)$ 对每个本原 $q$ 及全部实 $c$ 成立。谱展开给出

$$
\tau_EL(d,c)=\tau_D(d)\tau_A(c)
 =\tau_DpL(d,c)\qquad(d\in D,c\in A).
$$

右等式来自 (64.15)、$s$ 保迹及第一二元接口的迹因子化。实际 $L$ 实张成使 $\tau_Dp=\tau_E$ 在全部 $E$ 上成立，至此才有 $Y=1_E$。所以 $t=sp$ 全锥正保迹，$H1_D=1_E$ 也使 $h$ 全锥正保迹。

最后，由任意本原 $q$ 的 (64.19)，

$$
\begin{aligned}
\langle q,hL(d,c)\rangle_D
 &=\langle Hq,L(d,c)\rangle_E\\
 &=\langle q,d\rangle_D\tau_A(c).
\end{aligned}
$$

本原元实张成给出完整 II。此时 $(L,h,t)$ 具有整个实际锥上的正性、两个全局正保迹边缘、两条全部实方向的丢弃律和实际实张成，才可第二次使用定义 64.3，得到 $\widetilde L$ 满等距；与 $\widetilde M$ 复合得到 $\widetilde Q$ 满等距。原先未给定的辅助映射也恢复为

$$
s=r\,pL(\mathord\cdot,e),\qquad
B(d,c)=M(sd,c),\qquad
\widetilde Q=\widetilde L(\widetilde M\otimes\operatorname{id}_A).
\tag{64.26}
$$

第一式因为 $rB(d,e)=rM(sd,e)=sd$。没有在两个单位律之前使用第二接口。$\square$

## 3. 一次预选纠缠探针恢复整锥插入正性

### 3.1 正规形只在归一化之后取得

由定理 64.9，$p$ 已全局保迹，$h,t$ 已规范保迹，$M,L$ 的两个二元接口和 $Q$ 的等距性已经成立；这一步仍未使用 $I_{13}$ 正性。现在才使用已有的有限扇区证明。它先从实际自复合的秩平方条件得到复杂矩阵扇区：对每个非标量 $A_i$，实际 $D_{ii}$ 是秩大于一的简单 EJA，并具有平方秩、平方维数；使用 [van de Wetering arXiv:1803.11139v3 Proposition 40](https://arxiv.org/pdf/1803.11139v3) 的这一充要条件，得到

$$
A=\bigoplus_i H_{n_i},\quad
D=\bigoplus_{i,k}H_{n_in_k},\quad
E=\bigoplus_{i,j,k}H_{n_in_jn_k},
\qquad H_q=\operatorname{Herm}_q(\mathbb C).
\tag{64.27}
$$

秩一简单扇区是 $\mathbb R$；没有使用该文 Theorem 3 的额外 sequential-product 条件。对每个标号扇区固定初始矩阵坐标，记所得坐标同构为 $\theta_A^0,\theta_D^0,\theta_E^0$。在两个活跃因子时，矩阵乘积秩一保持定理（[Xu–Zheng–Fošner, Main Theorem, journal p.409, (1.1)–(1.2)](https://doi.org/10.1017/S1446788714000603)）及其单活跃因子的 Proposition 2.1 给出所需正规形；其输入是二元等距性给出的实线性单射、对纯矩阵乘积保持秩一、输出维数等于因子维数乘积，且正性和迹归一化固定共同符号与酉共轭。于是

$$
M_{ik}(a,c)=U_{ik}\bigl(a^{T^{\varepsilon_{ik}}}\otimes c^{T^{\delta_{ik}}}\bigr)U_{ik}^*.
\tag{64.28}
$$

$U_{ik}$ 是酉矩阵；$\varepsilon_{ik},\delta_{ik}\in\{0,1\}$。标量槽位的转置位没有相对意义，只作无害记号。对 $L$ 同样取正规形，复合得到

$$
Q_{ijk}(a,b,c)=W_{ijk}
 \bigl(a^{T^{t_1}}\otimes b^{T^{t_2}}\otimes c^{T^{t_3}}\bigr)W_{ijk}^*.
\tag{64.29}
$$

具体写 $L_{ijk}(d,c)=V_{ijk}(d^{T^{\lambda_{ijk}}}\otimes c^{T^{\mu_{ijk}}})V_{ijk}^*$。这里 $V_{ijk}$ 为酉，$\lambda_{ijk},\mu_{ijk}\in\{0,1\}$，并且

$$
\begin{gathered}
t_1=\varepsilon_{ij}\oplus\lambda_{ijk},\qquad
t_2=\delta_{ij}\oplus\lambda_{ijk},\qquad t_3=\mu_{ijk},\\
W_{ijk}=\begin{cases}
 V_{ijk}(U_{ij}\otimes I_{n_k}),&\lambda_{ijk}=0,\\
 V_{ijk}(\overline{U_{ij}}\otimes I_{n_k}),&\lambda_{ijk}=1.
\end{cases}
\end{gathered}
$$

若 $L$ 的第一个输入先转置，则使用
$(U\,x\,U^*)^{\mathsf T}=\overline U\,x^{\mathsf T}U^{\mathsf T}$，没有把纠缠 $U$ 与部分转置错误地交换。到此只得到初始正规形，尚未作同时 untwist，也未使用跨扇区约束或插入正性。

### 3.2 交叉插入的精确块公式

在 $\mathcal M$ 已可逆后定义

$$
\mathcal T(a\otimes c)=Q(a,1_A,c),\qquad
I_{13}=\mathcal T\mathcal M^{-1}:D\to E.
\tag{64.30}
$$

对 $x\in H_{n_in_k}$，令 $\iota_j(x)$ 把未归一化的中间单位插入两个端点之间：若 $S_j$ 把 $|a,c,b\rangle$ 送到 $|a,b,c\rangle$，则

$$
\iota_j(x)=S_j(x\otimes I_{n_j})S_j^*.
$$

令 $\Gamma_{u,v}=T^u\otimes T^v$，其中 $T$ 是整个矩阵转置。对

$$
 u_{ijk}=\varepsilon_{ik}\oplus t_1,\qquad
 v_{ijk}=\delta_{ik}\oplus t_3,
\tag{64.31}
$$

得到每个初始坐标块的精确公式

$$
\bigl(I_{13}d\bigr)_{ijk}
=\operatorname{Ad}(W_{ijk})\,
 \iota_j\!\left[
 \Gamma_{u_{ijk},v_{ijk}}
 \left(\operatorname{Ad}(U_{ik}^*)d_{ik}\right)
 \right].
\tag{64.32}
$$

证明必须先把 $U_{ik}$ 解开：对 $d=M_{ik}(a,c)$，先得到
$\operatorname{Ad}(U_{ik}^*)d=a^{T^{\varepsilon_{ik}}}\otimes c^{T^{\delta_{ik}}}$，再施加 $\Gamma$，最后插入 $I_{n_j}$ 并共轭 $W_{ijk}$。因为 $M_{ik}(A_i,A_k)$ 实张成整块，(64.32) 对每个纠缠 $d_{ik}$ 也成立。不同端点块落在互不相交的中心块中，不会相互抵消；被插入的 $1_j$ 只消去中间转置，不产生迹或除数。

### 3.3 预选 Bell 状态及等价性

令

$$
\mathcal P=\{(i,k):n_i\ge2,\ n_k\ge2\}
$$

是带顺序的端点对，重复标签按有序出现，$N=|\mathcal P|$（此计数与归一化假设 $\mathrm{(N)}$ 区分）。对每个 $(i,k)\in\mathcal P$，在固定的初始基中取

$$
 v_{ik}=(|0_i0_k\rangle+|1_i1_k\rangle)/\sqrt2,\qquad
 b_{ik}=v_{ik}v_{ik}^*.
$$

定义实际 $D$ 中的正迹一元

$$
 \beta_{ik}=(\theta_D^0|_{D_{ik}})^{-1}
 \bigl(U_{ik}b_{ik}U_{ik}^*\bigr),
$$

并把它嵌入其他 $D$ 中心块为零。若 $N>0$，令

$$
\sigma_*={1\over N}\sum_{(i,k)\in\mathcal P}\beta_{ik};
\tag{64.33}
$$

若 $N=0$，令 $\sigma_*=1_D/m$。这是实际载体中的正迹一态；没有对 $b_{ik}$ 使用 $\mathcal M^{-1}$ 来宣称物理性。初始坐标和正规形在测试前固定，且选择规则只依赖 $M$ 的系数、标号中心块和固定基：允许任意一个满足 (64.28) 的选择；若需要单值规则，可先在 $(00,01,10,11)$ 中取有非空酉解集的首个位对，再按固定矩阵元顺序逐项最小化实部、虚部；约束只需在有限基乘积上检查，解集是酉群中的闭紧集，故这些连续函数的逐项最小值存在并确定一个酉解。该规则不读取 $Q,W,I_{13}$ 或测试结果。

**定理 64.10（一次预选态等价于整锥插入正性）。** 对上述任意预先固定的初始正规形选择，

$$
 I_{13}(D_+)\subseteq E_+
 \quad\Longleftrightarrow\quad
 I_{13}(\sigma_*)\in E_+.
\tag{64.34}
$$

输出不要求归一化；由 $I_{13}(1_D)=1_E$ 和等距性，
$\tau_EI_{13}(\sigma_*)=n$。若 $N=0$，两边自动成立。

**证明。** 若 $n_i=1$ 或 $n_k=1$，$\Gamma_{u,v}$ 至多作用于一个非标量矩阵，因此是恒等或整个转置，保持正性。若两端点都活跃，$u=v$ 时 $\Gamma_{u,v}$ 是恒等或全局转置，也保持整个矩阵锥；$u\ne v$ 时，取两维子空间上的 Bell 投影 $b$，单因子转置把它压到交换算子 $F_2/2$，在

$$
(|0_i1_k\rangle-|1_i0_k\rangle)/\sqrt2
$$

上有本征值 $-1/2$。

对实际探针，必须使用正确的方向：

$$
\operatorname{Ad}(U_{ik}^*)
 \bigl(U_{ik}b_{ik}U_{ik}^*\bigr)=b_{ik}.
\tag{64.35}
$$

因此 (64.32) 中的算子是 $\Gamma_{u,v}(b_{ik})$，不是把 $\Gamma$ 错误地直接作用在 $\beta_{ik}$ 上；任意纠缠的 $U_{ik}$ 都已在 (64.35) 中消去。若 $N>0$，每个活跃端点对和每个中间 $j$ 的输出块是

$$
{1\over N}\operatorname{Ad}(W_{ijk})
 \iota_j\bigl(\Gamma_{u_{ijk},v_{ijk}}(b_{ik})\bigr).
\tag{64.36}
$$

若某个有序对的两个位不同，该块有本征值 $-1/(2N)$，并按 $n_j$ 重复；直和正性不允许由其他块抵消。所以单一测试迫使

$$
 u_{ijk}=v_{ijk}
 \quad\text{对每个有序活跃 }(i,k)\text{ 和每个 }j,
\tag{64.37}
$$

其中包括 $n_j=1$ 的标量中间旁观者。反之，(64.37) 使所有活跃块的 $\Gamma$ 正；非活跃端点块已由第一段正。故 (64.34) 成立。

若全部扇区均为标量，继承的二元正规形给出
$D=\mathbb R^{|\Lambda|^2}$、$E=\mathbb R^{|\Lambda|^3}$，且
$M(a,c)_{ik}=a_ic_k$、$(I_{13}d)_{ijk}=d_{ik}$；$\sigma_*=1_D/m$ 直接通过测试。这也包含 $A=\mathbb R$ 的普通标量乘法。

### 3.4 方向控制与非对角标量旁观者

**定理 64.11（全锥正的转置控制与有序跨扇区控制）。** 下述两个实例满足定理 64.9 的全部前置条件及结论，却违反预选探针条件。

**证明。** 在 $A=H_q,D=H_{q^2},E=H_{q^3}$ 中取

$$
L(d,c)=d\otimes c^{\mathsf T},\qquad
p(z)=\bigl(\operatorname{Tr}_1z\bigr)^{\mathsf T},
$$

其中 $p$ 的转置是迹掉第一份后剩余两份上的**整个**转置。两映射在全锥上正，$p$ 保迹；直接计算给出

$$
M(a,b)=a^{\mathsf T}\otimes b,\quad
Q(a,b,c)=a^{\mathsf T}\otimes b\otimes c^{\mathsf T},\quad
H(d)=d\otimes I_q,
$$

以及 $W_J,W_H,\mathrm{I},\mathrm{III}$ 和两条张成。这里 $(\varepsilon,\delta)=(1,0)$、$(t_1,t_2,t_3)=(1,0,1)$，故插入位为 $(0,1)$。当 $q=2$ 时，预选 Bell 态的输出在第 1、3 份上是 $F_{13}/2$，对
$|0,k,1\rangle-|1,k,0\rangle$ 的归一化向量本征值为 $-1/2$。这证明整锥插入条件仍有实质作用，不能由两个单位切片或 $N$ 删除。

还可检验有序跨扇区和标量中间不能被对角测试代替。令
$A=H_2\oplus H_3\oplus\mathbb R$，标签为 $u,v,s$，取标准分块 $D,E$。令
$\chi_{ijk}=1$ 当且仅当 $(i,j,k)=(u,s,v)$，其余为零，并定义

$$
L(d,c)_{ijk}=d_{ij}\otimes c_k^{T^{\chi_{ijk}}},\qquad
(pz)_{jk}=\sum_i\bigl(\operatorname{Tr}_1z_{ijk}\bigr)^{T^{\chi_{ijk}}}.
\tag{64.38}
$$

每个 $p$ 分块都在全锥上正并保迹，$L$ 在全部实际 $D_+\times A_+$ 上正；$M,L$ 的两条实张成成立，内部 $M$ 是普通张量，$H(d)_{ijk}=d_{ij}\otimes I_{n_k}$ 且 $H^*H=6\operatorname{id}_D$。所有对角端点测试都通过，反向交叉也没有缺陷；但从 $D_{uv}$ 到 $E_{usv}$ 的插入在标量中间 $s$ 的旁观下对 $v$ 作部分转置。四个有序非标量端点对等权时，(64.36) 给出负本征值 $-1/8$。所以探针必须覆盖所有有序端点对和标量中间，而不是只选一个自复合块。$\square$

**一次探针的中文结论。** 在定理 64.9 已恢复两个单位、$p$ 保迹、完整 II 和两个二元接口之后，先在尚未同时 untwist 的标号矩阵坐标中按 $M$ 预选每个有序非标量端点对的 Bell 态，再等权组成一个实际正迹一态。解开 $U^*\beta U$ 后，任何单因子转置的错误都会在相应的输出直和块留下负本征值；中间扇区即使是标量也不消除它。因此一个整态测试等价于整锥 $I_{13}$ 正性，且结论覆盖任意允许的初始正规形选择。

## 追加锚（本行以下为增补区）
