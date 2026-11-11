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

上述纯边缘结论也可直接由该接口的全效应配对得到。若 $R_Y\rho=q$ 本原，对任意效应 $0\le f\le1_X$，用 $\langle g,y_f\rangle_Y=\langle G(f,g),\rho\rangle_Z$ 定义条件向量。联合效应正性给出 $0\le y_f\le q$，所以 $y_f=\lambda_fq$；取 $g=1_Y$ 得 $\lambda_f=\langle f,R_X\rho\rangle_X$。于是 $\rho$ 与 $G(R_X\rho,q)$ 对全部乘积效应配对相同，分离性给出相等。$R_X$ 正保迹保证 $R_X\rho$ 是正迹一态。故这里没有另加可分离性或纯边缘分解假设。

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

以下统一记 $\mathcal M=\widetilde M:A\otimes_{\mathbb R}A\to D$、$\mathcal L=\widetilde L:D\otimes_{\mathbb R}A\to E$、$\mathcal Q=\widetilde Q:A\otimes_{\mathbb R}A\otimes_{\mathbb R}A\to E$，分别将简单张量送到 $M,L,Q$。这三个映射均为满迹内积等距同构。所有等式量化其类型内全部实向量。

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

由定理 64.9，$p$ 已全局保迹，$h,t$ 已规范保迹，$M,L$ 的两个二元接口和 $Q$ 的等距性已经成立；这一步仍未使用 $I_{13}$ 正性。定理 64.6 已经选定 $A,D$ 的类型。现在将同一中心块和连通比较论证用于第二接口，得到实际简单块 $E_{ijk}=\operatorname{span}L(D_{ij},A_k)$，秩为 $n_in_jn_k$，维数为其平方。同一有限 EJA 分类表遂选定 $E$ 的复矩阵类型，包括秩一和秩二边界。因此

$$
A=\bigoplus_i H_{n_i},\quad
D=\bigoplus_{i,k}H_{n_in_k},\quad
E=\bigoplus_{i,j,k}H_{n_in_jn_k},
\qquad H_q=\operatorname{Herm}_q(\mathbb C).
\tag{64.27}
$$

这里另取任意允许的初始坐标，不要求沿用 (64.17) 吸收输出酉的坐标。对每个标号扇区固定初始矩阵坐标，记所得坐标同构为 $\theta_A^0,\theta_D^0,\theta_E^0$。在两个活跃因子时，矩阵乘积秩一保持定理（[Xu–Zheng–Fošner, Main Theorem, journal p.409, (1.1)–(1.2)](https://doi.org/10.1017/S1446788714000603)）及其单活跃因子的 Proposition 2.1 给出所需正规形；其输入是二元等距性给出的实线性单射、对纯矩阵乘积保持秩一、输出维数等于因子维数乘积，且正性和迹归一化固定共同符号与酉共轭。于是

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

若 $N=0$，令 $\sigma_*=1_D/m$。这是实际载体中的正迹一态；没有对 $b_{ik}$ 使用 $\mathcal M^{-1}$ 来宣称物理性。初始坐标和正规形在测试前固定，且选择规则只依赖 $M$ 的系数、标号中心块和固定基：允许任意一个满足 (64.28) 的选择；若需要单值规则，可先在 $(00,01,10,11)$ 中取有非空酉解集的首个位对，再按固定矩阵元顺序逐项最小化实部、虚部；约束只需在有限基乘积上检查，解集是酉群中的闭紧集，故这些连续函数的逐项最小值存在并确定一个酉解。该规则不读取 $Q,W,I_{13}$ 或测试结果。探针本身只使用 $A,D,M$ 及其预选坐标；$E$ 坐标和 $Q,W$ 正规形只用于证明测试的充分性。

**定理 64.10（一次预选态等价于整锥插入正性）。** 对上述任意预先固定的初始正规形选择，

$$
 I_{13}(D_+)\subseteq E_+
 \quad\Longleftrightarrow\quad
 I_{13}(\sigma_*)\in E_+.
\tag{64.34}
$$

输出不要求归一化。由 $Q$ 等距及 (64.30)，$I_{13}^*I_{13}=n\operatorname{id}_D$，而 $I_{13}1_D=1_E$，所以 $I_{13}^*1_E=n1_D$，即 $\tau_EI_{13}(d)=n\tau_D(d)$ 对全部实 $d$ 成立；特别是 $\tau_EI_{13}(\sigma_*)=n$。若 $N=0$，两边自动成立。

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

**证明。** 对任意整数 $q\ge2$，在 $A=H_q,D=H_{q^2},E=H_{q^3}$ 中取

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

以及 $W_J,W_H,\mathrm{I},\mathrm{III}$ 和两条张成。$D_J$ 随 $W_J$ 成立，$Z$ 随 III 成立；$p$ 保迹给出 $\gamma=q^3=n^3$，故满足 $N$。全矩阵态和效应满足定义 64.1 的比较及 Jordan 条件。这里 $(\varepsilon,\delta)=(1,0)$、$(t_1,t_2,t_3)=(1,0,1)$，故插入位为 $(0,1)$。当 $q=2$ 时，预选 Bell 态的输出在第 1、3 份上是 $F_{13}/2$，对
$|0,k,1\rangle-|1,k,0\rangle$ 的归一化向量本征值为 $-1/2$。这证明整锥插入条件仍有实质作用，不能由两个单位切片或 $N$ 删除。

还可检验有序跨扇区和标量中间不能被对角测试代替。令
$A=H_2\oplus H_3\oplus\mathbb R$，标签为 $u,v,s$，取标准分块 $D,E$。令
$\chi_{ijk}=1$ 当且仅当 $(i,j,k)=(u,s,v)$，其余为零，并定义

$$
L(d,c)_{ijk}=d_{ij}\otimes c_k^{T^{\chi_{ijk}}},\qquad
(pz)_{jk}=\sum_i\bigl(\operatorname{Tr}_1z_{ijk}\bigr)^{T^{\chi_{ijk}}}.
\tag{64.38}
$$

每个 $p$ 分块都在全锥上正并保迹，$L$ 在全部实际 $D_+\times A_+$ 上正。唯一异常块的中间因子 $j=s$ 为标量，故 $\operatorname{Tr}_1d_{us}$ 的整转置不改变它；其他块两次转置位为零。因此对所有实 $d,c$，

$$
B(d,c)_{jk}=\left(\sum_i\operatorname{Tr}_1d_{ij}\right)\otimes c_k,
\qquad M(a,b)_{ij}=a_i\otimes b_j.
$$

于是 $M,L$ 两条实张成、$W_J,D_J$、完整 I、III 和 $Z$ 全部成立；$H(d)_{ijk}=d_{ij}\otimes I_{n_k}$，$H^*H=6\operatorname{id}_D$，而 $\gamma=6^3=n^3$，故 $W_H,N$ 成立。全矩阵直和也满足定义 64.1 的入口。所有对角端点测试都通过，反向交叉也没有缺陷；但从 $D_{uv}$ 到 $E_{usv}$ 的插入在标量中间 $s$ 的旁观下对 $v$ 作部分转置。四个有序非标量端点对等权时，(64.36) 给出负本征值 $-1/8$。所以探针必须覆盖所有有序端点对和标量中间，而不是只选一个自复合块。$\square$

**一次探针的中文结论。** 在定理 64.9 已恢复两个单位、$p$ 保迹、完整 II 和两个二元接口之后，先在尚未同时 untwist 的标号矩阵坐标中按 $M$ 预选每个有序非标量端点对的 Bell 态，再等权组成一个实际正迹一态。解开 $U^*\beta U$ 后，任何单因子转置的错误都会在相应的输出直和块留下负本征值；中间扇区即使是标量也不消除它。因此一个整态测试等价于整锥 $I_{13}$ 正性，且结论覆盖任意允许的初始正规形选择。

## 4. 完整候选、严格逆向与复量子对应

### 4.1 保持实际载体和原始映射的严格恢复

**定理 64.12（完整候选及唯一补回）。** 定义 64.1–64.3 的有限全态全效应入口、另行规范迹 Jordan 桥、全域正 $L,p$、同一个 $p$ 的两次内部定义、两个实张成及 $D_J,Z,W_H,N$，再加按第 3 节任意允许的预选坐标规则定义的唯一条件
$I_{13}(\sigma_*)\in E_+$，推出定理 64.4–64.10 的全部结论。特别是原来的实际 $p$ 全局保迹，完整 I、II、III、$W_J$ 和两个单位律均成立，且唯一缺失读回为

$$
p_{13}=I_{13}^*:E\to D,
$$

它在整个 $E_+$ 上正并规范保迹。对全部实 $a,b,c$，

$$
p_{13}Q(a,b,c)=\tau_A(b)M(a,c).
\tag{64.39}
$$

该完整候选与 [Part III 定理 62.5](QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_III.md#62-两个原始映射内部插入与严格恢复) 所述旧三映射条件严格唯一扩张等价：忘掉 $p_{13}$ 与补回上述唯一 $p_{13}$ 互逆，保持同一实际 $A,D,E,L,p$ 和内部准备 $M$，而非仅保持坐标同构类。

**证明。** 定理 64.4–64.9 不使用探针；它们依次给出正左逆、完整归一化 $F$ 接口、单位律之前的加权 III、第一扇区权重、全部本原支持面、循环行列式、两个单位律、原 $p$ 全局保迹以及完整第二接口。至此 $\mathcal M=\widetilde M$ 可逆，故 (64.30) 良好，而且
$I_{13}1_D=Q(1_A,1_A,1_A)=H1_D=1_E$。定理 64.10 才将一次预选探针转成整个实际 $D_+$ 上的插入正性。自对偶性使 $p_{13}$ 全锥正；$I_{13}$ 保单位使其伴随规范保迹。

对任意实 $x,y,a,b,c$，$Q$ 等距给出

$$
\begin{aligned}
\langle M(x,y),p_{13}Q(a,b,c)\rangle_D
 &=\langle Q(x,1_A,y),Q(a,b,c)\rangle_E\\
 &=\tau_A(b)\langle x,a\rangle_A\langle y,c\rangle_A.
\end{aligned}
$$

$M$ 张成及非退化配对给出 (64.39)；$Q$ 张成使任何满足此律的实线性读回在全部 $E$ 上相等，故唯一性不只限于正保迹竞争者。由 $M$ 张成，还得到全实 $d,c$ 的
$p_{13}L(d,c)=M(rd,c)$。于是

$$
\begin{aligned}
pL\bigl(p_{13}L(\omega,a),b\bigr)
 &=B(M(r\omega,a),b)\\
 &=B(M(e,a),b)=\tau_A(e)M(a,b)=M(a,b).
\end{aligned}
\tag{64.40}
$$

旧的混合 $p_{13},p$ 定义因而与两次同一个 $p$ 的定义逐点相同。Part III 定理 62.5 的所有实际前提现在都满足，允许补回旧条件。

逆向也保持实际数据。由旧三映射条件的二元边缘和全实三元读回，先得规范二元单位、迹等距、$r\omega=s\omega=e$，以及 $B(d,c)=M(sd,c)$。因此其旧 $M$ 满足
$B(\omega,a)=M(e,a)$、$B(B(\omega,a),b)=M(a,b)$，确实恢复本卷的同一个内部 $M$。完整 I 的单位切片给出 $W_J$，故给出 $D_J$；完整 III 的末槽单位切片给出 $Z$。旧第二接口给出 $W_H$、$\operatorname{rank}(E)=n^3$，旧 $p$ 保迹给出 $\gamma=n^3$，所以 $N$ 成立。旧 $p_{13}$ 的正保迹和 (64.39) 使其伴随等于 (64.30) 的 $I_{13}$，全锥插入正性遂通过同一预选规则的探针。唯一性使补回的是原来的 $p_{13}$；因此两个操作严格互逆。$\square$

### 4.2 全块几何、相对转置位及 Born 配对

**定理 64.13（同载体的复直和张量几何）。** 定理 64.12 的完整条件及所列纸面接口下，存在固定的保迹 Jordan 序坐标，使

$$
A\simeq\bigoplus_iH_{n_i},\qquad
D\simeq\bigoplus_{i,j}H_{n_in_j},\qquad
E\simeq\bigoplus_{i,j,k}H_{n_in_jn_k},\qquad n_i\ge1,
\tag{64.41}
$$

同一实际映射为

$$
\begin{aligned}
M(a,b)_{ij}&=a_i\otimes b_j,&L(d,c)_{ijk}&=d_{ij}\otimes c_k,\\
(rd)_i&=\sum_j\operatorname{Tr}_2d_{ij},&
(sd)_j&=\sum_i\operatorname{Tr}_1d_{ij},\\
(hz)_{ij}&=\sum_k\operatorname{Tr}_3z_{ijk},&
(pz)_{jk}&=\sum_i\operatorname{Tr}_1z_{ijk},\\
(p_{13}z)_{ik}&=\sum_j\operatorname{Tr}_2z_{ijk}.
\end{aligned}
\tag{64.42}
$$

$L$ 的公式覆盖任意实际 $d$，包括纠缠正元。全态、全效应及概率为

$$
\rho_i\ge0,\qquad \sum_i\operatorname{Tr}\rho_i=1,\qquad
0\le F_i\le I_{n_i},\qquad
\Pr(F\mid\rho)=\sum_i\operatorname{Tr}(F_i\rho_i).
\tag{64.43}
$$

纯态空间是 $\coprod_i\mathbb{CP}^{n_i-1}$，同扇区的最小确认比较为平方重叠，异扇区为零。单一 $n_i=2$ 扇区的全态空间是 Bloch 球。

**证明。** 第一、第二二元接口给出 (64.27) 的简单中心块和独立初始正规形；这一阶段只给类型，尚未固定相对转置位。记 $\kappa_{ij}=\varepsilon_{ij}\oplus\delta_{ij}$，在两个非标量因子时有内对关系 $t_1\oplus t_2=\kappa_{ij}$。由全实读回及 $Q$ 张成，每个初始块上的原 $p$ 与唯一 $p_{13}$ 必须分别为

$$
\begin{aligned}
p|_{E_{ijk}}
 &=\operatorname{Ad}(U_{jk})\,
 \Gamma_{\varepsilon_{jk}\oplus t_2,\,\delta_{jk}\oplus t_3}
 \operatorname{Tr}_1\operatorname{Ad}(W_{ijk}^*),\\
p_{13}|_{E_{ijk}}
 &=\operatorname{Ad}(U_{ik})\,
 \Gamma_{\varepsilon_{ik}\oplus t_1,\,\delta_{ik}\oplus t_3}
 \operatorname{Tr}_2\operatorname{Ad}(W_{ijk}^*),
\end{aligned}
$$

各式仅进入标出的输出扇区。部分迹满射到整个保留因子 PSD 锥：把任意保留正元与一个被丢弃的正规范迹一本原元张量即可。全域 $p,p_{13}$ 正性于是迫使保留掩码正；两活跃因子时，Bell 的负本征值排除恰一个转置，给出
$t_2\oplus t_3=\kappa_{jk}$、$t_1\oplus t_3=\kappa_{ik}$。

对三个活跃位置，三条边关系给出
$\kappa_{ik}=\kappa_{ij}\oplus\kappa_{jk}$。重复标签给出 $\kappa_{ii}=0$ 和 $\kappa_{ij}=\kappa_{ji}$；这两式是结论，不是扇区交换假设。任选活跃扇区 $h$，令 $s_i=\kappa_{hi}$，便有 $\kappa_{ij}=s_i\oplus s_j$。恰有两个活跃位置时，所需边分别来自内对、$p$ 或 $p_{13}$，最后一种明确包括标量中间旁观者。至多一个活跃位置时，有效转置本就是整个矩阵转置。故每个三元掩码在其活跃位置上只与 $(s_i,s_j,s_k)$ 相差一个共同位。

在 $A_i$ 坐标施加 $T^{s_i}$；在 $D,E$ 的每个中心块解开其固定输出酉，再消去相应共同整块转置。这些都是全锥正、保迹 Jordan 序同构，给出同时固定的 (64.41)–(64.42)。该构造正是 [Part III 定理 62.7](QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_III.md#62-两个原始映射内部插入与严格恢复) 的表示；此处使用它时三个边关系已具备。$M$ 张成把 $L$ 在乘积上的公式延拓到全部实 $d$，读回公式由对应张成唯一确定。全标量情形就是普通经典直和张量，$A=\mathbb R$ 时由张成得 $D=E=\mathbb R$。

全态全效应和保迹序坐标直接给出 (64.43)。若 $\xi=|\psi\rangle\langle\psi|$ 本原，接受它概率一的效应在其射线上必须等于一，其余正部分只会增加对正态的配对；最小者是 $\xi$ 本身。故 $T_\xi(\rho)=\operatorname{Tr}(\xi\rho)$，对同扇区纯态给出 $|\langle\psi,\phi\rangle|^2$，异扇区可取零效应分量，比较为零。该式也逐项满足全部有限混合 $S$。反向地，任意有限非空 $\Lambda$、$n_i\ge1$ 的标准分块矩阵载体与 (64.42) 都满足完整候选：原两次 $p$ 的准备确为张量，$Z,W_H,D_J$ 由迹配对直接给出，$\gamma=n^3$，插入是未归一化中间单位而全锥正，所以原探针通过。

在同一个 $E$ 上还可选右准备
$R(a,d)_{ijk}=a_i\otimes d_{jk}$，两种括号均为同一 $a_i\otimes b_j\otimes c_k$，重括号识别为恒等；标准因子置换连同扇区标签置换给出正保迹的 $S_3$ 自同构。它构造一个所选右结构，不识别独立给定的右载体或其映射。$\square$

### 4.3 $W_J$、完整 III 与标量 $C$ 的特化

**定理 64.14（旧条件的有效范围与同数据等价）。** 在其余保留条件和同一个预选探针规则不变时，用 $W_J$ 替换 $D_J$ 得到完全相同的实际 $(A,D,E,L,p)$ 集合。用完整 III 替换 $Z$、用标量 $C:\tau_D(p1_E)=\tau_E(1_E)$ 替换 $N$ 的旧完整条件也保留本卷的全部结论。这些是同载体等价，不声称完整模型类严格扩大，也不声称条件独立或最少。

**证明。** 对正 $a,b$，$W_J$ 给出 $\langle Ja,Jb\rangle=n\langle a,b\rangle$，故蕴含 $D_J$；反向由定理 64.9 得到 $W_J$。完整 III 在末槽取 $1_A$ 就是 $Z$；反向已由定理 64.5 从 $D_J,Z$ 推出。定理 64.7 在不使用 $N$ 时已经给出 $R_E=n^3$；定理 64.8 及两次 AM–GM 在不使用上界时给出 $\gamma\ge n^3$。因此在此前置域内，$N$、$C$、$\gamma=n^3$ 与全局 $p$ 保迹等价：前两项任一给出等号及定理 64.9，保迹反向在单位上给出 $C$。

还可单独保留旧第一范数特化。若在定理 64.4 后直接另给 $W_J$，则 $\tau_D(U^2)=n^2=m$，而已得 $\tau_D(U^{-1})=m$。对完整正谱表，

$$
0=\sum_{\lambda\in\operatorname{spec}_{\rm prim}(U)}
 \left(\lambda^2+2/\lambda-3\right),\qquad
\lambda^2+2/\lambda-3
 =\frac{(\lambda-1)^2(\lambda+2)}{\lambda}\ge0.
$$

故 $U=1_D$，第一接口和完整 I 已可在不使用 $W_H,N,L$ 张成或探针时恢复；定理 64.5 随后恢复 III。这保留了第一单位切片的有效结论。再有 $W_H$、完整 III 和 $C$ 时，面逆为 $t|_{F_q}$，其逆迹公式为
$\tau_A(tP_q^{\mathrm s})=\tau_{F_q}(z_q^{-1})$。完整面谱于是满足
$\sum\lambda^2=R_E$、$\gamma=\sum\lambda^{-1}$；$C$ 或 $N$ 使同一非负谱恒等式饱和，恢复 $H1_D=1_E$。这些都是本卷结论的特化，无需另设整套证明。$\square$

**定理 64.15（删去归一化上界的经典控制）。** 即使保留 $W_J$、完整 I、III、$W_H$、全域正性、两条实张成和全锥插入正性，删除 $N$ 仍可使全局 $p$ 保迹、第二单位和完整 II 失败。

**证明。** 取 $A=\mathbb R^2,D=\mathbb R^4,E=\mathbb R^8$ 的整个坐标正锥、坐标和规范迹、全部态和效应。指标 $i,j,k\in\{0,1\}$，令 $w=(7/5,1/5)$，$\sum_kw_k^2=2$，定义

$$
L(d,c)_{ijk}=d_{ij}w_kc_k,\qquad
p(z)_{jk}=\sum_i z_{ijk}/w_k.
$$

两映射在全锥上正，非零权给出 $L$ 张成。使用两次同一个 $p$ 得到

$$
B(d,c)_{jk}=\left(\sum_i d_{ij}\right)c_k,\qquad
M(a,b)_{ij}=a_ib_j.
$$

所以 $M$ 张成，$W_J,D_J$、完整 I、III 及其切片 $Z$ 成立；$H^*H=2\operatorname{id}_D$，故 $W_H$ 也成立。所有载体是全经典 EJA，满足 $S$ 和所列 Jordan 入口。插入为 $(I_{13}d)_{ijk}=w_kd_{ik}$，整锥正，全标量的参考 $\sigma_*=1_D/4$ 也通过。可是

$$
\tau_Dp(e_{000})=5/7\ne1,\qquad
\gamma=160/7>8=n^3=R_E,
$$

并且 $H1_D\ne1_E$、$hL(d,c)=(\sum_kw_k^2c_k)d$ 在 $c=e_0$ 时违反 II。该实例不满足 $N$ 或 $C$，所以没有与定理 64.9–64.10 的归一化前置条件混用。$\square$

### 4.4 静态比较、共同态与物理边界

**定理 64.16（两两读数和端点互反的边界）。** 完整候选允许不同三份态具有相同全部两两约化态，也允许端点比较互反而非零几何相位及不交换投影同时存在。

**证明。** 标准三量子比特实例满足完整候选，而

$$
|G_\pm\rangle=(|000\rangle\pm|111\rangle)/\sqrt2
$$

给出不同正迹一态。迹掉任一份都消去符号交叉项，三对约化态均为对应基下
$(|00\rangle\langle00|+|11\rangle\langle11|)/2$。所以张成、唯一读回和所选右准备不意味着任意三份态的两两层析。

在同一标准实例取 $A=H_2$，三个向量
$|0\rangle$、$|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$、$|+i\rangle=(|0\rangle+i|1\rangle)/\sqrt2$。三对平方重叠都为 $1/2$ 且互反，但

$$
\langle0|+\rangle\langle+|+i\rangle\langle+i|0\rangle
 =(1+i)/4
$$

相位为 $\pi/4$，对应秩一投影也不全交换。因此端点互反、标签置换和括号识别既不强制零几何相位，也不等同于不相容测量在时间中的交换，更不提供共同的经典联合结果律。$\square$

**定义 64.17（完整候选的条件性含义与范围）。** 在三个实际非零有限的全态、全效应系统上，分别保留全部有限混合比较律 $S$；另给保归一化、每扇区本原迹一的规范迹 Jordan 桥；只给在整个实际 $D_+\times A_+$ 上正的准备 $L$ 和在整个 $E_+$ 上正的同一个读回 $p$，用两次此 $p$ 内部定义 $M$，保留 $M,L$ 的两条实张成。比较输入 $D_J$ 只要求零比较在未归一化单位参考插入后仍为零；另外保留全部实方向的第三单位切片 $Z$、完整范数律 $H^*H=n\operatorname{id}_D$ 和一次标量上界 $\tau_D(p1_E)\le n^3$。在明确保留的二元纸面接口、有限 Jordan 分类和矩阵乘积秩一保持工具下，先恢复加权完整 III，再用全部本原支持面和循环行列式共同消去两种参考权重，得到两个单位律、原 $p$ 全局保迹、完整 I、II 和两个归一化二元接口。之后才按原有序扇区公式选定一个实际正迹一 Bell 合成态；其整个输出算子的正性恢复整锥交叉插入正性，严格补回同载体唯一 $p_{13}$，给出含经典扇区的复量子静态几何、普通张量和 Born 配对。

上述条件逐项含有独立给定的系统信息：有限全态全效应与规范 Jordan 桥不只是端点数值对称；全域正性包括纠缠方向，两个实张成要求实际共同载体，$Z$ 是全实双线性等式，$W_H$ 保留整个范数尺度，$N$ 是共同参考校准。一次探针要求一个完整输出算子为正，编码所有有序非标量端点和每个中间扇区的约束，不是一次标量概率或维数无关的实验方案。这里的“只要求零比较”仅针对第一比较律；没有删除其余系统条件，也不由压缩的条件名称数目得到独立性、最小性或严格扩大完整模型类。

该条件定理保留标量和经典直和扇区；选择单一非经典扇区还需额外选择条件。数学上的单位、$\omega$、二次表示、初始坐标和 Bell 态不承诺物理参考、滤波器或纠缠态的可获得性、精度、程序或成本。这些有限静态条件没有给出任意独立操作的完全正性或参考扩张契约，也没有给出仪器、态更新、动力学、时钟、Hamiltonian、$\hbar$；也没有识别一个独立给定的右载体。四份一致性、无界份数的相干组合及无限维延拓均在结论之外。这里的推导是所列条件和纸面接口下的数学候选，不承担物理起源、文献新颖性或形式核验证明的主张。

## 追加锚（本行以下为增补区）


## 65. 全有限比较入口下的未校准正滤波分类

### 65.1 原载体、比较与规范迹的忠实对应

**定义 65.1（全有限混合比较系统）。** 对每个 $X=A,D,E$，取非零有限维实向量空间、闭尖生成锥 $C_X$、在 $C_X\setminus\{0\}$ 上严格正的线性泛函 $u_X$，以及完整紧态基
$K_X=\{x\in C_X:u_X(x)=1\}$。保留全部线性效应 $[0,u_X]$，记 $P_X=\operatorname{ext}K_X$。对于纯参照 $\xi\in P_X$ 及任意 $x\in K_X$，定义

$$
T^X_\xi(x)=\inf\{f(x):0\le f\le u_X,\ f(\xi)=1\}.
\tag{65.1}
$$

要求每个 $X$ 满足完整有限混合律：对任意有限纯态族 $\eta_1,\ldots,\eta_\ell$、任意概率权重 $w_j$ 及纯 $\xi$，

$$
T^X_\xi\left(\sum_jw_j\eta_j\right)
 =\sum_jw_jT^X_{\eta_j}(\xi).
\tag{65.2}
$$

单点族给出纯端点互反；再代入一般族便得到混合仿射性。它要求同一状态的不同有限制备关系给出一致比较，不只是纯端点的一张对称数表。第一端点仍限于纯态；不把同一 infimum 定义延伸到混合第一端点。

本节复用 [Library 的完整 $S$ 到 EJA 纸面定理及其逆向](../../../Library/QuantumStates/mullerududec2012selfduality.md#complete-conditional-candidate-and-its-scope)，包括其中的正对偶生成、共同框架、面投影及滤波纯性推导。该结果供应唯一对称正定配对 $B_X$、最小确认效应 $e_\xi=B_X(\xi,-)$、自对偶性及有限 EJA 锥几何。定义原比较单位 $U_X$ 为

$$
B_X(U_X,x)=u_X(x).
$$

每个完整正交纯框架之和是 $U_X$，其长度为正整数 $n_X=u_X(U_X)$。这些是所引纸面结果的推论，未另行供应内积、谱兼容、齐次性、强对称性或 Jordan 桥。

为明确原归一化的对应，即使只取该分类的锥同构 $\Psi:X\to J_X$，原泛函也唯一表示为

$$
u_X\Psi^{-1}(z)=\tau_{J_X}(h_X\circ z),\qquad h_X>0.
$$

这里及下文 $h_X>0$ 表示内点正可逆，$\tau_{J_X}$ 是每个简单理想中每个本原幂等元迹一的规范谱迹。严格正性排除 $h_X$ 的零谱值。令 $\ell_a(b)=a\circ b$、$P_a=2\ell_a^2-\ell_{a^2}$，置

$$
\Phi_X=P_{\sqrt{h_X}}\Psi.
\tag{65.3}
$$

二次表示自伴随、全锥正且有正逆，$P_{\sqrt{h_X}}1=h_X$，所以 $\tau_{J_X}\Phi_X=u_X$。因此 $\Phi_X$ 双射整个原态基到底层规范迹一基，且将纯态送到迹一本原幂等元；对偶拉回 $f\mapsto f\Phi_X^{-1}$ 双射整个原效应区间到 $[0,1]$，不是只对应一组选定效应。

这里可直接应用所引 EJA 逆向的最小效应结论。具体地，若 $q$ 本原、$0\le b\le1$、$\langle b,q\rangle=1$，则 $r=1-b$ 在互补面 $J_1(1-q)$ 内，且

$$
r=P_{1-q}r\le P_{1-q}1=1-q.
$$

所以 $b\ge q$，而 $q$ 自身是确认效应。全效应区间的对应遂给出

$$
T^X_\xi(x)=\tau_{J_X}(\Phi_X\xi\circ\Phi_Xx),\qquad
B_X(x,y)=\tau_{J_X}(\Phi_Xx\circ\Phi_Xy),\qquad
\Phi_XU_X=1_{J_X}.
\tag{65.4}
$$

第二式由纯态实张成延拓，第三式由原 $U_X$ 的 Riesz 定义及满射性得出。因此没有额外的谱兼容输入，也没有可任意选择的扇区迹倍数。此后在这些忠实坐标中书写，仍记实际载体为 $X$，原 $u_X$、$B_X$、$U_X$ 分别写作 $\tau_X$、$\langle-,-\rangle_X$、$1_X$。原态与效应没有被替换。

上述单系统桥是仓内纸面综合推导，不能归给 Müller–Ududec 的 bit symmetry 定理本身；其分类接口是 [Barnum–Müller–Ududec, Theorem 16](https://arxiv.org/html/1403.4147v4)，其有限项目性、互反及纯性前提由所引 Library 推导供应。它不是 Barnum–Hilgert 强对称性分类在较弱前提下的直接应用。

### 65.2 只保留实际正映射与三条关系

**定义 65.2（未校准的完整候选）。** 在定义 65.1 已导出的几何上，令

$$
n=\tau_A1_A,\qquad m=\tau_D1_D,\qquad \omega=1_D/m.
$$

唯一原始映射为实双线性 $L:D\times A\to E$ 和实线性 $p:E\to D$，满足

$$
L(D_+,A_+)\subseteq E_+,\qquad p(E_+)\subseteq D_+.
\tag{65.5}
$$

第一个条件覆盖整个实际 $D_+$ 中的正元，第二个覆盖整个实际 $E_+$。在矩阵坐标中，它们包括全部纠缠正元。为与配对 $B_X$ 区分，将复合双线性映射记为 $\mathcal B$：

$$
\begin{aligned}
\mathcal B(d,c)&=pL(d,c),& K(a)&=\mathcal B(\omega,a),\\
M(a,b)&=\mathcal B(K(a),b),&J(a)&=M(a,1_A),\\
H(d)&=L(d,1_A),&B_1&=pH,\\
Q(a,b,c)&=L(M(a,b),c),&U&=M(1_A,1_A).
\end{aligned}
\tag{65.6}
$$

特别地 $M(a,b)=pL(pL(\omega,a),b)$，两次均为同一个实际 $p$，参考始终是原比较单位给出的 $\omega$。$U$ 是原准备的单位输出，不是载体比较单位 $1_D$ 的另一记号。要求

$$
\operatorname{span}_{\mathbb R}M(A,A)=D,\qquad
\operatorname{span}_{\mathbb R}L(D,A)=E,
\tag{65.7}
$$

以及

$$
\begin{aligned}
D_J:\quad &a,b\in A_+,\ \langle a,b\rangle_A=0
 \Longrightarrow\langle Ja,Jb\rangle_D=0,\\
D_H:\quad &d,d'\in D_+,\ \langle d,d'\rangle_D=0
 \Longrightarrow\langle Hd,Hd'\rangle_E=0,\\
Z:\quad &B_1M(a,b)=\tau_A(a)Jb\qquad(a,b\in A).
\end{aligned}
\tag{65.8}
$$

$D_H$ 量化整个实际锥，$Z$ 量化全部实方向。先由下面的第一接口证明 $\widetilde M:A\otimes_{\mathbb R}A\to D$ 可逆，此后才定义

$$
T(a,c)=L(Ja,c),\qquad
I_{13}^{\rm raw}=\widetilde T\widetilde M^{-1}:D\longrightarrow E.
$$

完整候选再保留同一个整锥条件

$$
\mathrm{C13}:\qquad I_{13}^{\rm raw}(D_+)\subseteq E_+.
\tag{65.9}
$$

此处没有供应 $W_J,W_H$、范数或总标定上界、原 $M,H$ 保单位、原 $p$ 保迹或独立读回。它与定义 64.1–64.3 的系统前提及校准目标分别陈述：第 64 节的独立 Jordan 桥、$W_H,N$ 及其探针完整条件仍按原文适用；本节使用完整 $S$ 的既有纸面推论，以 $D_H$ 和明确的整锥 C13 处理另一个原始映射类，不改判那些较强前提下的结论。

### 65.3 第一接口及加权的完整 III

**定理 65.3（实际第一接口的未校准复用）。** 定义 65.1–65.2 下，不使用 $D_H$ 或 C13，令

$$
C_D=P_{\sqrt U},\qquad F=C_D^{-1}M,\qquad
\alpha=F(-,1_A),\quad\beta=F(1_A,-).
$$

则 $U>0$，$\widetilde F$ 是满规范迹内积等距同构；$\alpha,\beta$ 是保单位单射 Jordan 同态，其乘法算子在整个 $D$ 上交换，$U$ 与 $\alpha(A)$ 算子交换，且

$$
F(a,b)=\alpha(a)\circ\beta(b),\qquad m=n^2.
\tag{65.10}
$$

存在全锥正 $s:D\to A$，置 $V=s^*1_A$、$w=s\omega$，则

$$
\begin{gathered}
s=\beta^*C_D^{-1},\quad V=U^{-1},\quad\tau_D(U^{-1})=m,
\quad w>0,\quad\tau_Aw=1,\\
sM(a,b)=\tau_A(a)b,\quad B_1=Js,\quad sK=\operatorname{id}_A,
\quad K(a)=M(w,a),\\
pQ(a,b,c)=\tau_A(a)M(b,c),\qquad
\mathcal B(d,c)=M(sd,c),\\
spL(d,c)=\langle V,d\rangle_Dc
\qquad(a,b,c\in A,\ d\in D).
\end{gathered}
\tag{65.11}
$$

**证明。** (65.3)–(65.4) 已建立定理 64.4–64.5 证明所需的全部规范迹 EJA 前提；(65.5)–(65.8) 逐点就是那两条证明实际使用的正性、同一个 $p$ 的内部定义、$M$ 张成、$D_J,Z$。其中 $\mathcal B$ 对应原文双线性 $B$，$C_D$ 对应其 $C$。那两条证明明确不使用 $W_H,N$、$L$ 张成或晚期插入，故可直接复用，不把旧完整候选的额外条件一并带入。

精确的依赖链是：支撑支配给出 $U$ 内点及 $J$ 无正核；$D_J$ 归一化出 $\alpha$，正中心权重 $\alpha^*\alpha$ 的逆构造正左逆 $j$；$s=jB_1$ 由 $Z$ 得到 $sM=\tau_A(-)\operatorname{id}$、$B_1=Js$ 及 $sK=\operatorname{id}$。由实际恒等式 $K1_A=B_1\omega=J(s\omega)$ 得 $\tau_A(s\omega)=1$。支撑分解和正对偶准备随后建立 [Library 二元接口 (15)–(18)](../../../Library/QuantumStates/barnumhilgert2019spectral.md#positive-marginals-recover-the-joint-effect-contract) 的全部正保迹边缘前提，才得到 $F$ 等距、$m=n^2$、$sC_D=\beta^*$ 及 $V=U^{-1}$。于是 $\tau_DV=m$ 来自同一 $p$ 与原 $\omega$，不是校准。

其中 $U$ 与 $\alpha(A)$ 的算子交换也直接来自同一支撑构造：对于任意完整框架 $(q_r)$，$Jq_r$ 的支撑 $e_r=\alpha(q_r)$ 两两正交，$U=\sum_rJq_r$ 对每个 $e_r$ 无 Peirce 半空间分量，所以 $[\ell_U,\ell_{e_r}]=0$。对任意 $a$ 选其谱框架并线性延拓，便有 $[\ell_U,\ell_{\alpha(a)}]=0$，不要求 $U$ 中心。

定理 64.5 再由纯第二边缘刚性得 $K=M(w,-)$。对本原 $q,a,b$，$w\ge\varepsilon q$ 给
$0\le\mathcal B(M(q,a),b)\le\varepsilon^{-1}M(a,b)$；$F(a,b)$ 本原且 $C_D$ 为锥自同构，所以此输出在 $M(a,b)$ 的极射线上。对含 $b$ 的完整框架求和，$Z$ 与 $\widetilde M$ 单射使每个系数为一。本原元张成及三线性延拓给出全实 III，$M$ 张成给出 $\mathcal B(d,c)=M(sd,c)$，施加 $s$ 得最后一式。这正是所引既有证明的全实结论，而非面压缩读数。$\square$

### 65.4 第二切片的支撑归一化与全空间交织

**定理 65.4（由 $D_H$ 得到的 Jordan 切片）。** 在定理 65.3 的阶段，令

$$
G=H1_D=L(1_D,1_A),\quad C_G=P_{\sqrt G},\quad
\eta=C_G^{-1}H,\quad N=C_G^{-1}L,\quad\zeta=N(1_D,-).
\tag{65.12}
$$

则 $G>0$，$\eta:D\to E$ 是保单位单射 Jordan 同态，$G$ 与 $\eta(D)$ 算子交换。$N$ 在全正域为正、实张成 $E$，且对全部实 $a,d\in D,c\in A$，

$$
\begin{aligned}
N(d,c)&=\eta(d)\circ\zeta(c),&N(d,1_A)&=\eta(d),\\
[\ell_{\eta(d)},\ell_{\zeta(c)}]&=0,&
P_{\eta(a)}N(d,c)&=N(P_ad,c).
\end{aligned}
\tag{65.13}
$$

算子交换及二次交织均在整个 $E$ 上成立，此时还没有假设 $N$ 等距或 $\zeta$ 保平方。

**证明。** 正 $d\le r1_D,c\le t1_A$ 给 $0\le L(d,c)\le rtG$。若正元与 $G$ 正交，它消去全部正乘积，并由正锥生成及 $L$ 张成消去整个 $E$；故该元为零，$G$ 是内点。由 (65.11)，

$$
spH(d)=\langle V,d\rangle_D1_A.
\tag{65.14}
$$

$V>0$，所以 $H$ 没有非零正核。取任意完整本原框架 $(q_r)$，$D_H$ 使非零 $Hq_r$ 的支撑 $e_r$ 两两正交，和 $\sum_rHq_r=G>0$ 使 $\sum_re_r=1_E$。在 $E_1(e_r)$ 内 $G$ 与 $Hq_r$ 相同，谱公式给 $C_G^{-1}Hq_r=e_r$。谱展开和极化遂使 $\eta$ 保平方及 Jordan 乘积，且保单位。若 $\eta(d)=0$，则 $H(d^2)=C_G\eta(d^2)=0$，无正核推出 $d^2=0$，故单射。

$G$ 对每个 $(e_r)$ 均无 Peirce 半空间分量，故与每个 $e_r$ 算子交换，进而与所有 $\eta(d)$ 算子交换。正平方根及逆平方根继承这一性质。

对于 $c\ge0$，取 $c\le t1_A$，则
$0\le N(q_r,c)\le t\eta(q_r)=te_r$，故 $N(q_r,c)\in E_1(e_r)$。其和 $\zeta(c)$ 对各 $e_r$ 分块对角，且 $e_r\circ\zeta(c)=N(q_r,c)$。对 $d$ 的谱展开及 $c$ 的实线性延拓得到乘积公式和整个 $E$ 上的算子交换。特别地，$\ell_{\zeta(c)}$ 同时与 $\ell_{\eta(a)}$、$\ell_{\eta(a^2)}$ 交换，所以

$$
\begin{aligned}
P_{\eta(a)}N(d,c)
 &=P_{\eta(a)}\ell_{\zeta(c)}\eta(d)\\
 &=\ell_{\zeta(c)}P_{\eta(a)}\eta(d)
 =\ell_{\zeta(c)}\eta(P_ad)=N(P_ad,c).
\end{aligned}
$$

这是二次表示的多项式计算，不把三个任意 Jordan 元素当作可结合乘积。所用谱、Peirce 与二次表示事实为定义 64.3 引用的 [Barnum–Hilgert §4](https://arxiv.org/html/1904.03753v1#S4) 及 [van de Wetering, Propositions 2.12、2.21、2.25、Theorem 3.13](https://arxiv.org/html/1912.01903v1)。$\square$

### 65.5 正读出强制本原角同构与第二迹等距

**定理 65.5（无需单位或保迹输入的第二接口）。** 定理 65.4 下，存在定义在整个 $E_+$ 上的正映射 $R:E\to A$，满足

$$
RN(d,c)=\tau_D(d)c\qquad(d\in D,c\in A).
\tag{65.15}
$$

由此 $\widetilde N:D\otimes_{\mathbb R}A\to E$ 是满规范迹等距同构，$\eta,\zeta$ 是保单位 Jordan 嵌入，且

$$
\begin{gathered}
\eta^*N(d,c)=\tau_A(c)d,\qquad
\zeta^*N(d,c)=\tau_D(d)c,\\
\eta^*,\zeta^*\text{ 在全锥上正且全局保迹},\qquad
\operatorname{rank}E=mn=n^3,\qquad\eta^*\eta=n\operatorname{id}_D.
\end{gathered}
\tag{65.16}
$$

两个本原输入的 $N$-乘积本原。

**证明。** 取 $t'=spC_G$、$v=V^{-1/2}$，定义

$$
R=t'P_{\eta(v)}.
$$

每个因子在整个源锥上正。由 (65.11)、(65.13) 及二次表示自伴随性，

$$
\begin{aligned}
RN(d,c)&=t'N(P_vd,c)
 =\langle V,P_vd\rangle_Dc\\
 &=\langle P_vV,d\rangle_Dc=\tau_D(d)c,
\end{aligned}
$$

因为 $P_{V^{-1/2}}V=1_D$。没有以原 $p$ 保迹或原 $G=1_E$ 代入。

下面给出直接本原角证明，并写出它使用的全部一般前提。设规范迹 EJA $X,Y,Z$ 上的正双线性 $T:X\times Y\to Z$ 满足：乘积实张成 $Z$，$T(1,1)=1$，$\theta=T(-,1)$ 是保单位 Jordan 嵌入，以及某个全锥正 $R_T:Z\to Y$ 满足 $R_TT(x,y)=\tau_X(x)y$。本节的代入是

$$
(X,Y,Z,T,\theta,R_T)=(D,A,E,N,\eta,R);
$$

正性、张成、单位与 Jordan 性来自定理 65.4，最后一条刚刚证明，故全部前提已建立。

对 $X$ 的幂等元 $e$，支配 $0\le T(e,y)\le t\theta(e)$ 及互补幂等元的同一支配说明
$T(x,y)=\theta(x)\circ\chi(y)$、$\chi=T(1,-)$，并且两像在整个 $Z$ 上算子交换。与 (65.13) 相同的多项式推导给
$P_{\theta(a)}T(x,y)=T(P_ax,y)$。

固定本原 $e$，置 $q=\theta(e)$、$T_e(y)=T(e,y)$。由于 $P_ex=\langle e,x\rangle_Xe$，张成及交织给

$$
\begin{aligned}
Z_1(q)&=P_qZ
 =\operatorname{span}\{T(P_ex,y):x\in X,y\in Y\}\\
 &=T_e(Y),\qquad R_TT_e=\operatorname{id}_Y.
\end{aligned}
\tag{65.17}
$$

因此 $T_e:Y\to Z_1(q)$ 是保单位序同构，其正逆是 $R_T$ 在整个角上的限制。只有正左逆不足以得到此结论；这里的满角等式是必要步骤。

保单位序同构保持效应区间极点，故保持幂等元；同一框架的像之和为单位，故它们正交，谱展开及极化使它成为 Jordan 同构。角内本原元也是环境本原元，所以角的规范迹就是环境迹的限制，不带重数。于是 $T_e$ 保规范迹内积。对实 $x,y,y'$，

$$
\begin{aligned}
\langle T(e,y),T(x,y')\rangle_Z
 &=\langle T(e,y),P_qT(x,y')\rangle_Z\\
 &=\langle e,x\rangle_X\langle T_e(y),T_e(y')\rangle_Z\\
 &=\langle e,x\rangle_X\langle y,y'\rangle_Y.
\end{aligned}
$$

本原元实张成 $X$，得到全部输入的乘积迹内积；张成使 $\widetilde T$ 成为满等距同构。对完整框架 $(e_r)$，各 $T_{e_r}(Y)$ 属于正交角，故
$\chi(y)^2=\sum_rT_{e_r}(y)^2=\chi(y^2)$；$\chi$ 保单位、单射且保 Jordan 乘积。各 $T_{e_r}$ 把 $Y$ 框架送到本原框架，合起来是 $Z$ 的完整框架，证明秩乘法和乘积本原性。

回到 $N$，与 $N(x,1_A)$、$N(1_D,y)$ 配对便得 (65.16) 的边缘公式。正性和保单位的对偶性给出全锥正保迹；与 $N(d,1_A)$ 配对给 $\eta^*\eta=n\operatorname{id}_D$。所以第二接口是在本原角满射和规范迹上得到的结论，没有借用原始范数律。$\square$

### 65.6 内在滤波与实际映射的精确等式

**定理 65.6（原始映射与辅助三元组）。** 令

$$
C_E=C_GP_{\sqrt{\eta(U)}},\qquad
Q_0(a,b,c)=N(F(a,b),c),\qquad p_0=C_D^{-1}pC_E.
\tag{65.18}
$$

$C_D,C_E$ 均由实际 $U,G$ 及比较导出的 Jordan 运算决定，是自伴随锥自同构，其逆全锥正。并有全部实输入的

$$
\begin{aligned}
M(a,b)&=C_DF(a,b),\\
L(d,c)&=C_EN(C_D^{-1}d,c),\\
Q(a,b,c)&=C_EQ_0(a,b,c),\\
p&=C_Dp_0C_E^{-1},\qquad
p_0Q_0(a,b,c)=\tau_A(a)F(b,c).
\end{aligned}
\tag{65.19}
$$

$p_0$ 在整个 $E_+$ 上正，在整个 $E$ 上保原规范迹。

**证明。** $G$ 与 $\eta(D)$ 算子交换，故与 $\eta(U)$ 有共同谱框架。其谱函数的二次表示相互交换，所以 $C_G$ 与 $P_{\sqrt{\eta(U)}}$ 交换；两者自伴随、正且有正逆，乘积也如此。由 Jordan 同态及 (65.13)，

$$
P_{\sqrt{\eta(U)}}N(d,c)
 =P_{\eta(\sqrt U)}N(d,c)=N(C_Dd,c).
$$

这给出前三条恢复式；第四条是定义的逆式，最后一条由原全实 III 得到。

$\widetilde Q_0=\widetilde N(\widetilde F\otimes\operatorname{id}_A)$ 是满迹内积等距，且 $Q_0(1_A,1_A,1_A)=1_E$。故

$$
\tau_EQ_0(a,b,c)=\tau_A(a)\tau_A(b)\tau_A(c)
 =\tau_Dp_0Q_0(a,b,c).
$$

$Q_0$ 实张成整个 $E$，所以 $\tau_Dp_0=\tau_E$ 全局成立。这不是从产品正性或选定面上的等式冒推全锥性质。$\square$

**推论 65.7（原参考下同一个 $p_0$ 的两次使用）。** 在相同实际载体、原迹与原 $\omega$ 上，定义

$$
\mathcal B_0=p_0N,\quad K_0(a)=\mathcal B_0(\omega,a),\quad
M_0(a,b)=\mathcal B_0(K_0(a),b).
$$

则对全部实输入，

$$
\begin{aligned}
\mathcal B_0(d,c)&=F(\beta^*d,c),\\
K_0(a)&=F(1_A/n,a),\qquad M_0(a,b)=F(a,b).
\end{aligned}
\tag{65.20}
$$

辅助 $\mathcal B_0,K_0,M_0$ 一般不同于实际 $\mathcal B,K,M$。

**证明。** (65.19) 在 $d=F(a,b)$ 上给出第一式，因为 $\beta^*F(a,b)=\tau_A(a)b$；$F$ 张成把它延拓到全部 $d$。等距性给 $\beta^*1_D=n1_A$，而 $m=n^2$，所以第二式成立。再算
$\beta^*K_0(a)=a$，将它代入第一式，得到用同一个 $p_0$ 两次重算的第三式。未更换参考。原 $\mathcal B(d,c)=M(sd,c)$ 则使用 $s=\beta^*C_D^{-1}$ 和 $M=C_DF$，没有一般理由等同于 (65.20)。$\square$

### 65.7 同一个整锥插入的双向转移

**定理 65.8（插入与读回的正确类型）。** 定义

$$
T_0(a,c)=N(F(a,1_A),c),\quad
I_{13}^0=\widetilde T_0\widetilde F^{-1}:D\to E.
$$

则

$$
I_{13}^{\rm raw}=C_EI_{13}^0C_D^{-1}:D\to E,
\qquad
(I_{13}^{\rm raw})^*=C_D^{-1}p_{13}^0C_E:E\to D,
\quad p_{13}^0=(I_{13}^0)^*.
\tag{65.21}
$$

原 C13 当且仅当 $I_{13}^0$ 在同一个整个 $D_+$ 上正。此时 $p_{13}^0$ 全锥正保迹，且唯一满足

$$
p_{13}^0Q_0(a,b,c)=\tau_A(b)F(a,c)
\qquad(a,b,c\in A).
\tag{65.22}
$$

**证明。** $\widetilde M=C_D\widetilde F$ 已可逆，故原插入良定义。由 (65.19)，$T=C_ET_0$，立即给出第一式。自伴随滤波给第二式，方向不能互换。因为滤波及其逆全锥正，原插入正性与辅助插入正性相互推出，量词仍为整个原锥。

$\widetilde F(1_A\otimes1_A)=1_D$ 及 $N(1_D,1_A)=1_E$ 给 $I_{13}^01_D=1_E$，所以其正伴随保迹。对所有实 $x,y$，

$$
\begin{aligned}
\langle F(x,y),p_{13}^0Q_0(a,b,c)\rangle_D
 &=\langle N(F(x,1_A),y),N(F(a,b),c)\rangle_E\\
 &=\tau_A(b)\langle x,a\rangle_A\langle y,c\rangle_A.
\end{aligned}
$$

$F$ 张成给出 (65.22)，$Q_0$ 张成给出读回唯一性。原伴随一般不保迹，不能由 $p_{13}^0$ 的性质直接赋予。$\square$

### 65.8 归一化表示的全部前提与有序方向

**定理 65.9（原载体的有限复 Born 几何）。** 定义 65.1–65.2 的完整条件及所引纸面接口下，存在有限非空扇区集 $\Lambda$、整数 $n_i\ge1$ 及同时固定的保迹 Jordan 序坐标，使

$$
A=\bigoplus_i H_{n_i},\quad
D=\bigoplus_{i,j}H_{n_in_j},\quad
E=\bigoplus_{i,j,k}H_{n_in_jn_k},\qquad
H_r=\operatorname{Herm}_r(\mathbb C),\quad n=\sum_i n_i,
\tag{65.23}
$$

其中辅助映射为

$$
F(a,b)_{ij}=a_i\otimes b_j,\qquad
N(d,c)_{ijk}=d_{ij}\otimes c_k,\qquad
(p_0z)_{jk}=\sum_i\operatorname{Tr}_1z_{ijk}.
\tag{65.24}
$$

这些坐标保持原归一化、原比较配对、原单位、全态基及全效应区间。

**证明。** 将 [Library 的同一个三份载体与三个全正成对视图表示 (24)、(29)–(35)](../../../Library/QuantumStates/barnumhilgert2019spectral.md#one-actual-triple-and-three-positive-pair-views) 的映射代入为

$$
(M,L,r,p_{12},p_{23},p_{13})
 =(F,N,\alpha^*,\eta^*,p_0,p_{13}^0).
\tag{65.25}
$$

逐项的全实接口为

$$
\begin{aligned}
\alpha^*F(a,b)&=\tau_A(b)a,&\beta^*F(a,b)&=\tau_A(a)b,\\
\eta^*N(d,c)&=\tau_A(c)d,&\zeta^*N(d,c)&=\tau_D(d)c,\\
p_0Q_0(a,b,c)&=\tau_A(a)F(b,c),&
p_{13}^0Q_0(a,b,c)&=\tau_A(b)F(a,c).
\end{aligned}
\tag{65.26}
$$

第一行来自定理 65.3 的完整接口，第二行来自定理 65.5，第三行来自定理 65.6、65.8。全部六个读回均全锥正保迹，$F,N$ 全正且各自实张成，两次相同 $p_0$ 的内部定义由推论 65.7 成立。另有
$\alpha^*\alpha=n\operatorname{id}_A$、$\eta^*\eta=n\operatorname{id}_D$，分别由两次等距配对得到。因此 Part III §§62–63 表示中需要的辅助 Gram 或单位性质也是已建立的结论，不是原始 $J,H$ 的假设。所有输出都落入同一个 $D,F$，不是三个独立成对模型。

现可直接复用所引表示证明。其二元接口先将中心扇区分解为全部有序 $D_{ij}$、$E_{ijk}$，并由乘积本原性及张成得到每块简单和秩、维数乘法。实际简单自对 $D_{ii}$ 排除非复类型；秩一块保留为 $\mathbb R=H_1$，秩二、三及例外边界按所引 EJA 分类表处理。这一步在引入转置掩码之前完成。

为明确方向范围，在独立初始坐标中先保留

$$
F_{ij}(a,b)=V_{ij}(a_i^{T^{\varepsilon_{ij}}}
 \otimes b_j^{T^{\delta_{ij}}})V_{ij}^*,\qquad
\kappa_{ij}=\varepsilon_{ij}\oplus\delta_{ij},
$$

以及三元块的固定酉 $W_{ijk}$ 和三个位 $t_1,t_2,t_3$。这些初始正规形复用 [Library 所引 Xu–Zheng–Fošner 的秩一乘积保持定理及标量边界](../../../Library/QuantumStates/barnumhilgert2019spectral.md#conditional-normal-form-theorem-and-proof)，不是一开始假设共同转置。内对给 $t_1\oplus t_2=\kappa_{ij}$。全实读回与 $Q_0$ 张成使 $p_0,p_{13}^0$ 在每个整个块上分别成为偏迹后加保留因子掩码。偏迹满射到保留 PSD 锥；若两保留因子都非标量，单腿转置使二级 Bell 投影出现 $-1/2$ 特征值，故全锥正性分别强制

$$
t_2\oplus t_3=\kappa_{jk},\qquad
 t_1\oplus t_3=\kappa_{ik}.
\tag{65.27}
$$

三个活跃位置给 $\kappa_{ik}=\kappa_{ij}\oplus\kappa_{jk}$；重复标签给 $\kappa_{ii}=0$、$\kappa_{ij}=\kappa_{ji}$。选活跃基点 $h$、令 $s_i=\kappa_{hi}$，得到 $\kappa_{ij}=s_i\oplus s_j$。恰有两个活跃位置时，相关边分别由内对、$p_0$、$p_{13}^0$ 提供，最后一种明确覆盖标量中间旁观者。至多一个活跃位置时，转置只是整块 Jordan 转置。全标量情形直接给经典直和。

对每个 $A_i$ 施加固定 $T^{s_i}$，对 $D,E$ 各块解开固定输出酉及共同整块转置，得到同一组保迹 Jordan 序坐标 (65.23)–(65.24)。重复的维数不合并其原中心标签。张成把 $N$ 的公式延拓到所有实际 $d$，包括纠缠正元；读回在全 $E$ 上的公式由 $Q_0$ 张成唯一确定。这是所引归一化表示在全部前提已实例化后的应用，而非新的分类定理。$\square$

### 65.9 全部原始正滤波的正常形

**定理 65.10（唯一逆迹约束下的完整原始映射族）。** 在定理 65.9 的同时坐标中，对每个有序 $i,j$ 存在正定 $u_{ij}\in H_{n_j}$，对每个有序 $i,j,k$ 存在正定 $g_{ijk}\in H_{n_k}$，唯一参数约束为

$$
\boxed{\ \sum_{i,j}n_i\operatorname{Tr}(u_{ij}^{-1})=n^2.\ }
\tag{65.28}
$$

所有有序块都出现，包括重复标签与标量块；不同 $u,g$ 之间没有隐藏的块对称或共同对角化要求。实际单位输出及滤波为

$$
\begin{aligned}
U_{ij}&=I_i\otimes u_{ij},&
G_{ijk}&=I_i\otimes I_j\otimes g_{ijk},\\
(C_Dd)_{ij}&=(I_i\otimes\sqrt{u_{ij}})d_{ij}(I_i\otimes\sqrt{u_{ij}}),\\
(C_Ez)_{ijk}&=C_{ijk}z_{ijk}C_{ijk},&
C_{ijk}&=I_i\otimes\sqrt{u_{ij}}\otimes\sqrt{g_{ijk}}.
\end{aligned}
\tag{65.29}
$$

全部实际准备是

$$
\begin{aligned}
M(a,b)_{ij}&=a_i\otimes(\sqrt{u_{ij}}b_j\sqrt{u_{ij}}),\\
L(d,c)_{ijk}&=d_{ij}\otimes(\sqrt{g_{ijk}}c_k\sqrt{g_{ijk}}),\\
Q(a,b,c)_{ijk}&=a_i\otimes(\sqrt{u_{ij}}b_j\sqrt{u_{ij}})
 \otimes(\sqrt{g_{ijk}}c_k\sqrt{g_{ijk}}).
\end{aligned}
\tag{65.30}
$$

置 $A_{jk}=I_j\otimes\sqrt{u_{jk}}$、$W_{ijk}=I_i\otimes u_{ij}^{-1/2}\otimes g_{ijk}^{-1/2}$，则原始读回在整个 $E$ 上唯一为

$$
(pz)_{jk}=A_{jk}\left[\sum_i\operatorname{Tr}_1
 (W_{ijk}z_{ijk}W_{ijk})\right]A_{jk}.
\tag{65.31}
$$

其中 $\operatorname{Tr}_1$ 是未归一化普通首因子偏迹。其余全部内部映射恢复为

$$
\begin{aligned}
(sd)_j&=\sum_i u_{ij}^{-1/2}(\operatorname{Tr}_1d_{ij})u_{ij}^{-1/2},\\
V_{ij}&=I_i\otimes u_{ij}^{-1},&
\omega_{ij}&=(I_i\otimes I_j)/n^2,\\
w_j&=\frac1{n^2}\sum_i n_i u_{ij}^{-1},&\tau_Aw&=1,\\
\mathcal B(d,c)&=M(sd,c),&
K(a)_{ij}&=w_i\otimes(\sqrt{u_{ij}}a_j\sqrt{u_{ij}}),\\
J(a)_{ij}&=a_i\otimes u_{ij},&H(d)_{ijk}&=d_{ij}\otimes g_{ijk},\\
B_1&=Js.&
\end{aligned}
\tag{65.32}
$$

这些等式量化全部实输入，不限于已准备态。若 $\operatorname{ins}_{13,j}(x_{ik})$ 表示在首、末因子插入 $x_{ik}$ 并在中间插入 $I_j$，即 $x_{ik}\otimes I_j$ 的固定因子置换，则同一个原 C13 映射为

$$
(I_{13}^{\rm raw}z)_{ijk}
 =C_{ijk}\operatorname{ins}_{13,j}
 (A_{ik}^{-1}z_{ik}A_{ik}^{-1})C_{ijk}.
\tag{65.33}
$$

**证明。** 定理 65.3 已给 $U$ 与 $\alpha(A)$ 算子交换；定理 65.4 已给 $G$ 与整个 $\eta(D)$ 算子交换。在复 Hermitian 块中
$[\ell_x,\ell_y]z=[[x,y],z]/4$。若该算子对所有 Hermitian $z$ 为零，则矩阵 $[x,y]$ 中心，且其矩阵迹为零，故 $[x,y]=0$。因此这些环境算子交换条件正是普通矩阵交换条件。

(65.24) 给 $\alpha(a)_{ij}=a_i\otimes I_j$、$\eta(d)_{ijk}=d_{ij}\otimes I_k$，其交换子分别是 $I_i\otimes H_{n_j}$ 与 $I_i\otimes I_j\otimes H_{n_k}$，得到 (65.29) 的 $U,G$；标量因子同样成立。$\tau_D(U^{-1})=m=n^2$ 恰为 (65.28)，不限制任何 $g$。矩阵二次表示是合同变换；代入 (65.19)、(65.24) 得 (65.29)–(65.31)，代入 $s=\beta^*C_D^{-1}$、$w=s\omega$ 得 (65.32)。插入恢复式 (65.21) 得 (65.33)。

$\widetilde Q=C_E\widetilde Q_0$ 满射，所以原全实 III 在 $Q$ 上规定的 $p$ 唯一确定整个 $E$ 上的线性映射；不能额外添加在乘积外自由作用的读回项。固定同时坐标后，参数 $u_{ij},g_{ijk}$ 分别由实际 $U,G$ 唯一读出。坐标本身仍可作同时的保迹 Jordan 改变，不宣称扇区命名或基底规范唯一。$\square$

### 65.10 完整反向构造与条件分类

**定理 65.11（全有限 $S$、同一读回及整锥条件的逆定理）。** 任取有限非空 $\Lambda$、$n_i\ge1$ 及满足 (65.28) 的正定 $u_{ij}$、任意正定 $g_{ijk}$，在 (65.23) 的全 PSD 锥、全部总迹一态及全部效应上，仅按 (65.30) 的 $L$ 与 (65.31) 的 $p$ 定义原始映射。则完整满足定义 65.1–65.2 的每个条件；用原 $\omega$、同一个 $p$ 两次实际算出的全部内部映射，正是 (65.30)–(65.32)。因此定理 65.10 给出恰好全部原始模型，没有遗漏额外滤波自由度或附加参数约束。

**证明。** 在每个载体的规范 EJA 上，本原迹一投影是纯态，定义 65.1 内的互补面计算已证明它就是最小确认效应。因此 $T_\xi(x)=\tau(\xi x)$，其仿射性与纯端点互反逐项给出全部有限混合 $S$。这是 Library 已有 EJA 逆向的应用，包含任意混合直和，不要求跨扇区强对称性。

$L$ 在任意正 $d,c$ 上正：每块是实际正矩阵 $d_{ij}$ 与正合同像的张量积，$d_{ij}$ 内可纠缠。$p$ 是全正合同、全锥正偏迹、求和、再次全正合同的复合，故在整个 $E_+$ 上正，包括任意纠缠输入。

为避免先假定 $M$，暂把 (65.30) 的第一个公式叫作 $\widehat M$，把 (65.32) 的 $s$ 公式作为计算用映射。直接取消 $pL$ 内 $g$ 的正逆合同，得到全部实 $d,c$ 的

$$
pL(d,c)=\widehat M(sd,c),\qquad
s\widehat M(a,b)=\tau_A(a)b.
\tag{65.34}
$$

原 $\omega=1_D/n^2$ 给实际 $K(a)=\widehat M(w,a)$，其中 $w$ 如 (65.32)，且 (65.28) 恰给 $\tau_Aw=1$。故 $sK=\operatorname{id}_A$，用同一个 $p$ 的第二次调用计算

$$
M(a,b)=pL(K(a),b)=\widehat M(sK(a),b)=\widehat M(a,b).
\tag{65.35}
$$

因此所列 $M$ 确为实际内部构造；$J,H,Q,\mathcal B,B_1$ 随即逐点恢复，$B_1=Js$ 和 (65.34) 给全实 $Z$ 及全实 III。

Hermitian 实简单张量张成每个完整 Hermitian 块，可逆合同保持张成。按原中心标签选取输入就能分别支撑各有序块，所以两条实际实张成都成立。这不把全正锥缩为正乘积生成锥。

对正 $a,b$ 若 $\langle a,b\rangle_A=0$，各非负 $\operatorname{Tr}(a_ib_i)$ 皆零，故

$$
\langle Ja,Jb\rangle_D
 =\sum_{i,j}\operatorname{Tr}(a_ib_i)\operatorname{Tr}(u_{ij}^2)=0.
$$

对整个 $D_+$ 内任意正 $d,d'$ 若配对为零，各 $\operatorname{Tr}(d_{ij}d'_{ij})$ 皆零，于是

$$
\langle Hd,Hd'\rangle_E
 =\sum_{i,j,k}\operatorname{Tr}(d_{ij}d'_{ij})
 \operatorname{Tr}(g_{ijk}^2)=0.
$$

所以 $D_J,D_H$ 在所要求的整个锥上成立，包括纠缠 $d$。最后 $\widetilde M=C_D\widetilde F$ 可逆，按实际 $T=L(J-,-)$ 重算就得到 (65.33)。正合同、在中间插入单位及因子置换在整个 $D_+$ 上正，所以同一个 C13 成立。以上没有比较不同块的参数，也没有要求同一末因子上的 $u_{jk}$ 与 $g_{ijk}$ 交换。前向定理已从每个实际模型提取这些数据，反向又完整重算其原始定义，故参数约束仅为 (65.28)。$\square$

### 65.11 原 Born 几何与原始归一化的反例控制

**推论 65.12（原态几何、原映射单位及保迹的区别）。** 每个原载体 $X$ 的全态、全效应及实际效应概率，在上述忠实坐标中是

$$
\rho_\lambda\ge0,\quad\sum_\lambda\operatorname{Tr}\rho_\lambda=1,
\qquad 0\le E_\lambda\le I_\lambda,
\qquad \Pr(E\mid\rho)=\sum_\lambda\operatorname{Tr}(E_\lambda\rho_\lambda).
\tag{65.36}
$$

$A$ 的纯态空间为 $\coprod_i\mathbb{CP}^{n_i-1}$，同区比较为 $|\langle\psi,\phi\rangle|^2$，异区为零。$D,E$ 分别使用有序对、三元块，保留其全部纠缠正态。另一方面，原始映射的归一化条件分别是

$$
\begin{aligned}
M(1_A,1_A)=1_D&\iff u_{ij}=I_j\quad(\forall i,j),\\
H1_D=1_E&\iff g_{ijk}=I_k\quad(\forall i,j,k),\\
\tau_Dp=\tau_E&\iff
I_i\otimes u_{ij}^{-1}\otimes
 (g_{ijk}^{-1/2}u_{jk}g_{ijk}^{-1/2})=I_{ijk}
 \quad(\forall i,j,k).
\end{aligned}
\tag{65.37}
$$

它们均不是本节候选的普遍推论。

**证明。** (65.4) 的全态与全效应对应及后续保迹 Jordan 坐标给出 (65.36)，本原投影的迹配对给纯态比较。前两个等价直接由实际 $U,G$ 读出。最后一个由 $p=C_Dp_0C_E^{-1}$ 求伴随得到

$$
(p^*1_D)_{ijk}
 =I_i\otimes u_{ij}^{-1}\otimes
 (g_{ijk}^{-1/2}u_{jk}g_{ijk}^{-1/2}),
\tag{65.38}
$$

再用规范迹的 Riesz 唯一性。

三个控制族说明这些条件不能省略为结论。第一，$A=\mathbb R$ 时约束强制 $u=1$ 而 $g>0$ 任意：$D=E=\mathbb R$，$M(a,b)=ab$、$L(d,c)=gdc$、$p(z)=z/g$，原插入为 $g\operatorname{id}:D\to E$，其伴随为 $g\operatorname{id}:E\to D$。$g\ne1$ 时原 $H$ 不保单位、原 $p$ 不保迹。

第二，经典 $A=\mathbb R^2$、所有 $n_i=1$，取

$$
u_{1j}=2,\qquad u_{2j}=2/3\quad(j=1,2),\qquad g_{ijk}=1.
$$

则 $\sum_{i,j}u_{ij}^{-1}=4=n^2$、$w=(1/2,1/2)$，原 $M(a,b)_{ij}=u_{ij}a_ib_j$ 非保单位。原 $p$ 对支撑在 $(i,j,k)=(1,2,1)$ 的质量一输入输出总质量 $u_{21}/u_{12}=1/3$，所以不保迹。辅助 $M_0=F$ 是普通分块乘法，与原 $M$ 不同。

第三，单复矩阵扇区 $n_1=2$，取

$$
u=\operatorname{diag}(2,2/3),\qquad g=\operatorname{diag}(3,1).
$$

$2\operatorname{Tr}(u^{-1})=4$，所以逆定理适用，包括整个纠缠锥及 C13。原 $U=I_2\otimes u$、$G=I_4\otimes g$ 均非单位，并有
$p^*1_D=I_2\otimes\operatorname{diag}(1/2,3/2)\otimes(2I_2/3)\ne1_E$。$C_E$ 不是共同标量，且 $w=\operatorname{diag}(1/4,3/4)$，故原 $K,M$ 与辅助者不同。还可将 $g$ 换成任意非对角正定矩阵，如 $\left(\begin{smallmatrix}2&1\\1&2\end{smallmatrix}\right)$，它与 $u$ 不交换，逆定理仍适用。

任意标量及非标量扇区混合都由同一公式覆盖；全经典、重复标签、标量旁观者和非均匀矩阵滤波均未排除。这些是对较强原始单位、保迹主张的反例，同时是本节分类的实际模型。$\square$

### 65.12 完整候选的白话表述与数学范围

**推论 65.13（比较几何与正滤波自由度）。** 完整候选可表述为：在非零有限单份、双份、三份的实际全态全效应系统中，用“确定接受一个纯参照时，对另一态最少会误接受多少”定义比较。任意有限随机纯制备之后的比较，等于逐对交换端点后再平均。采用已引单系统纸面定理，这确定原比较配对、原单位与规范迹 Jordan 入口。只再给整个双份锥上的正准备和整个三份锥上的同一个正读回，以原规范参考两次调用这个读回，要求两条实张成、单份与双份两个指定单位切片的零比较保持、全部实方向的 $Z$，以及由实际准备之逆定义的同一个整锥交叉插入为正。则原系统具有有限复直和的 Born 态与效应几何，全部原始准备和读回恰由 (65.28)–(65.33) 的正滤波族描述，每个这样的族也反向满足完整候选。

**证明。** 定义 65.1–65.2 给出上述各量词，定理 65.3–65.9 给出原几何，定理 65.10–65.11 给出实际映射的双向分类，推论 65.12 给出归一化边界。白话说，比较规则固定了状态与测试共用的几何，但实际参考操作仍能对不同分支给出不同的正权重。第一输出 $U$ 与第二输出 $G$ 从原始映射中读出，这些权重不能仅靠给它们换一个“归一化”名称就删除。$C_D,C_E$ 是用于构造辅助映射的内在正滤波，一般不保持原迹一截面；它们与保持全态基的同时 Jordan 坐标选择是不同操作。

共同尺度族 $u_{ij}=I_j$、$g_{ijk}=\kappa I_k$ 只是本分类的一个子族，此时 $M=F$、$L=\kappa N$、$p=p_0/\kappa$，原 $\mathcal B,K,M$ 恰与辅助者相同；一般参数不具有这种不变性。第 64 节保留其校准前提及原始归一化结论，本节较大的未校准映射类不撤回那些条件定理。

本节使用的二次表示、谱迹、本原角与 EJA 分类事实属于所引文献（literature-attested）；完整 $S$ 桥、二元接口、三读回扇区及方向拼接属于明确引用的仓内纸面推导（repo-derived），不将它们计作本节新分类。新增综合内容是 $D_H$ 的未校准第二接口、全域正读出的权重消除、内在两滤波的精确恢复与完整原始参数逆向（repo-derived）。全部结论限于所述条件纸面模型，不作新颖性、优先性、独立或最少公理及内核验证声明。

有限静态几何不指定单一非经典扇区，也不证明规范参考或这些滤波物理可用、可免费实施或物理无关；全锥正性的结论不供应任意参考扩张的 CP 原则、仪器、测量更新、动力学、时间、Hamiltonian 或 $\hbar$。它不识别独立给定的右括号载体，不推出四份或任意多份一致性、无限维推广，亦不从实张成及读回唯一性推出任意三体态的两两边缘层析。纯端点互反不等于时间上的测量交换，不排除几何相位。因此这里恢复的是原始有限 Born 几何及全部允许的正滤波映射，不是完整物理起源。$\square$

## 追加锚（本行以下为增补区）

## 66. 第二插入的零比较、双迹可行域与共同尺度刚性

### 66.1 同一实际数据上的保留条件

**定义 66.1（不含第二范数律和归一化上界的基底）。** 记 $\mathcal B$ 为以下全部条件。三个实际载体 $X=A,D,E$ 非零、有限维，分别具有闭尖生成正锥、严格正归一化泛函 $u_X$、紧全态基底 $K_X=\{x\in X_+:u_X(x)=1\}$ 和全部对偶效应 $[0,u_X]$。纯态是 $K_X$ 的极点；对全部纯态 $\xi$ 及全部态 $x$，比较仍定义为

$$
T_\xi(x)=\inf\{f(x):0\le f\le u_X,\ f(\xi)=1\}.
$$

每个载体均要求定义 64.1 的完整有限混合律：对每个 $\ell\ge1$、纯态 $\xi,\eta_1,\ldots,\eta_\ell$ 及 $w_j\ge0$、$\sum_jw_j=1$，

$$
T_\xi\!\left(\sum_jw_j\eta_j\right)=\sum_jw_jT_{\eta_j}(\xi).
$$

完整比较入口正是定义 65.1；直接复用该节引用的完整 $S$ 到规范迹 EJA 的条件纸面定理及 (65.3)–(65.4)，得到保原归一化的坐标、整个平方锥、所有规范迹一态和全部效应 $[0,1_X]$。原比较配对、原单位、原态及原效应分别对应规范迹内积、$1_X$、全态基及全效应区间；每个简单扇区的每个本原幂等元迹一，不允许调节扇区迹权。这里的 Jordan 入口由所引既有纸面结果供应，不另列独立 Jordan 假设，也不将这条桥计为本节新成果。内积、参考和秩仍为

$$
\langle x,y\rangle_X=\tau_X(x\circ y),\quad
n=\tau_A1_A,\quad m=\tau_D1_D,\quad
R_E=\tau_E1_E,\quad e=1_A/n,\quad\omega=1_D/m.
$$

只给实际实双线性 $L:D\times A\to E$ 和实际实线性 $p:E\to D$，要求 $L(D_+,A_+)\subseteq E_+$、$p(E_+)\subseteq D_+$；前者量化整个实际 $D_+$，包含所有纠缠方向。内部定义原样保留：

$$
\begin{aligned}
B(d,a)&=pL(d,a),&K(a)&=B(\omega,a),&M(a,b)&=B(K(a),b),\\
J(a)&=M(a,1_A),&r&=J^*,&U&=J1_A,\\
H(d)&=L(d,1_A),&h&=H^*,&B_1&=pH,\\
Q(a,b,c)&=L(M(a,b),c).
\end{aligned}
\tag{66.1}
$$

$M$ 内两次使用同一个实际 $p$。要求 $\operatorname{span}_{\mathbb R}M(A,A)=D$、$\operatorname{span}_{\mathbb R}L(D,A)=E$，并保留

$$
\begin{gathered}
\mathrm{(D_J)}\quad a,b\ge0,\ \langle a,b\rangle_A=0
\ \Longrightarrow\ \langle Ja,Jb\rangle_D=0,\\
\mathrm{(Z)}\quad B_1M(a,b)=\tau_A(a)Jb\qquad(a,b\in A).
\end{gathered}
\tag{66.2}
$$

定义 64.3 的全正、实张成、正保迹二元边缘接口及其精确适用条件继续保留；有限 EJA 分类、定理 64.6 所用乘积秩一保持接口也继续保留。它们只在各自输入已经得到以后使用。$\mathcal B$ 不含 $W_H$、$N$、$p$ 保迹、第二单位律或交叉插入正性。

本节增加的是第二个二元零关系

$$
\mathrm{(D_H)}\quad d,d'\in D_+,\quad\langle d,d'\rangle_D=0
\ \Longrightarrow\ \langle Hd,Hd'\rangle_E=0.
\tag{66.3}
$$

设 $R=n^3$，并记

$$
Z=H1_D,\qquad Y=p^*1_D,\qquad
\delta=\tau_E(Z),\qquad\gamma=\tau_D(p1_E)=\tau_E(Y).
\tag{66.4}
$$

这里正元 $Z$ 与关系 $\mathrm{(Z)}$ 以字体和类型区分。$\delta$、$\gamma$ 都是原实际映射在原单位参考上的读数。

**引理 66.2（本原零关系的等价测试）。** $D_H$ 等价于只对正交本原幂等元 $q,q'\in D$ 要求 $\langle Hq,Hq'\rangle_E=0$。

**证明。** 必要性直接。反向，把任意 $d,d'\ge0$ 谱分解为 $d=\sum_s a_sq_s$、$d'=\sum_t b_tq'_t$，只保留正系数。自对偶性给出 $\langle q_s,q'_t\rangle\ge0$。若 $\langle d,d'\rangle=0$，则每个 $a_sb_t\langle q_s,q'_t\rangle=0$，故每个出现的本原对正交；假设使其像也零配对，双线性求和即得 $D_H$。此测试遍及实际 $D$ 的所有本原元，并不限于第一接口的乘积本原元；在复矩阵表示中，纠缠秩一方向仍全部包括。$\square$

### 66.2 无范数输入的完整支持面

**定理 66.3（零比较足以恢复全部本原支持面）。** 在 $\mathcal B+D_H$ 下，定理 64.4–64.6 的结论保持成立，特别是存在全锥正 $s:D\to A$、$t=sp:E\to A$，使

$$
\begin{gathered}
m=n^2,\quad V=U^{-1}>0,\quad\tau_D(V)=m,\\
tL(d,a)=\langle V,d\rangle_Da.
\end{gathered}
\tag{66.5}
$$

$Z$ 是 $E_+$ 内点，$H$ 没有非零正核。对任意本原 $q\in D$，令

$$
z_q=Hq,\quad P_q=\operatorname{supp}(z_q),\quad
F_q=E_1(P_q),\quad\Pi_q=P_{P_q},\quad
K_q(a)=L(q,a),\quad v_q=\langle V,q\rangle_D>0.
$$

则对全部实 $d,a$，

$$
\Pi_qL(d,a)=\langle q,d\rangle_DK_q(a),\qquad
K_q(A)=F_q,\qquad K_q^{-1}=t|_{F_q}/v_q.
\tag{66.6}
$$

$K_q$ 是序同构，$\Theta_q=P_{z_q^{-1/2}}K_q$ 是到面 $F_q$ 的保单位 Jordan 同构。因此每个 $F_q$ 秩为 $n$；任意完整 $D$ 本原框架的 $P_q$ 两两正交且和为 $1_E$，从而 $R_E=mn=R$。这里没有 $\|z_q\|^2=n$ 的结论。

**证明。** 这是定理 65.3–65.5 的证明级子结果的直接应用。先列出实际使用的全部输入：由定义 65.1 的既有纸面桥取得的全有限规范迹 EJA；整个 $D_+\times A_+$ 上的正 $L$、整个 $E_+$ 上的正 $p$；同一个 $p$ 两次定义的实际 $M$；$M,L$ 两条实张成；$D_J,D_H$ 及全部实方向的 $\mathrm{(Z)}$。定理 65.3 在这些输入中只用 $D_J,Z$ 和第一接口所需正性、张成，明确不使用 C13，给出 $s$、$V=U^{-1}>0$、$\tau_DV=m$ 和 (66.5)。定理 64.6 的早期有序扇区结论也只依赖这一阶段，不依赖 C13。定义 65.2 的完整包虽另含 C13，定理 65.4–65.5 的证明使用的正是此处列出的输入及已得 $V=U^{-1}$，没有使用 C13、$W_H,N$、总迹上界或原映射保单位、保迹。

精确代入为：第 65 节的 $G,C_G,\eta,N,R$ 在这里分别取

$$
Z,\quad C_Z=P_{\sqrt Z},\quad
\eta=C_Z^{-1}H,\quad N_Z=C_Z^{-1}L,\quad
R_Z=(tC_Z)P_{\eta(V^{-1/2})}.
$$

定理 65.4–65.5 已证明 $Z>0$、$H$ 无非零正核、$\eta$ 为保单位 Jordan 嵌入、$Z$ 与 $\eta(D)$ 算子交换，并有 $R_ZN_Z(d,a)=\tau_D(d)a$。对本原 $q$，$Hq=C_Z\eta(q)$ 的支撑是 $P_q=\eta(q)$。正映射支配 $0\le L_a\le bH$（$0\le a\le b1_A$）保证 $K_q(a)$ 落在这个完整支撑面。定理 65.5 的 (65.17) 以 $(X,Y,Z,T,\theta,R_T)=(D,A,E,N_Z,\eta,R_Z)$ 应用，给出实际的满角等式

$$
E_1(P_q)=N_Z(q,A),\qquad
N_Z(q,-):A\longrightarrow E_1(P_q)
\text{ 是保单位 Jordan 同构}.
$$

这一步使用全空间张成及 (65.13) 的二次交织，不把正左逆单独当成满射。由于 $C_Z$ 在此面上的限制正是 $P_{\sqrt{z_q}}$，故 $K_q=P_{\sqrt{z_q}}N_Z(q,-)$，给出 $K_q(A)=F_q$、$\Theta_q=N_Z(q,-)$。同一交织以 $D$ 上的本原二次表示 $P_q^{D}(d)=\langle q,d\rangle_Dq$ 代入，且 $C_Z$ 与该面投影交换，得到 (66.6) 的压缩式；(66.5) 给出 $tK_q=v_q\operatorname{id}_A$，因此所示正逆也成立。面同构保持继承的规范迹、秩及元素行列式。完整框架的支持单位和为 $1_E$、$R_E=mn$ 是 (65.16) 的直接结论。不同支持面之间仍允许非零 Peirce 半空间，不把这些面误作整个 $E$ 的向量空间直和。$\square$

### 66.3 没有范数的循环行列式与双谱

**定理 66.4（两份正谱的总乘积一）。** 在定理 66.3 下，存在完整实际 $D$ 本原框架 $\mathcal Q$，使 $Y_q=\Pi_qY$ 是 $F_q$ 内点，$\ell_q=K_q^*Y$ 是 $A$ 内点，并有

$$
\det_{F_q}(Y_q)=\frac{\det_A(\ell_q)}{\det_{F_q}(z_q)},\qquad
\prod_{q\in\mathcal Q}\det_A(\ell_q)=1.
\tag{66.7}
$$

令 $\zeta_1,\ldots,\zeta_R$ 为各 $z_q$ 的合并本原正谱表，$\eta_1,\ldots,\eta_R$ 为各 $Y_q$ 的合并面内正谱表，则

$$
\prod_{\alpha=1}^R\zeta_\alpha\prod_{\alpha=1}^R\eta_\alpha=1,
\qquad\sum_\alpha\zeta_\alpha=\delta,\qquad
\sum_\alpha\eta_\alpha=\gamma.
\tag{66.8}
$$

**证明。** 复用定理 64.6 的全部有序坐标，不作扇区交换假设。写 $A=\bigoplus_iH_{n_i}$、$D=\bigoplus_{i,j}H_{n_in_j}$、$n=\sum_i n_i$，权重为 $u_{ij}>0$。由实际 $pL(d,a)=M(sd,a)$ 及其规范迹，任意本原 $q\in D_{ij}$ 满足

$$
(\ell_q)_k=v_q u_{jk}^{T^{\delta_{jk}}},\qquad
v_q=\operatorname{Tr}\!\left(u_{ij}^{-1}\operatorname{Tr}_iq\right)>0.
\tag{66.9}
$$

这来自 (64.22) 的前两行，不使用 $H$ 的范数或第二单位律。由 $K_q=P_{\sqrt{z_q}}\Theta_q$、$\Theta_q$ 的迹等距性和 $K_q(A)=F_q$，有

$$
Y_q=P_{z_q^{-1/2}}\Theta_q(\ell_q)>0\quad\hbox{于 }F_q.
$$

因此 $\ell_q$、$Y_q$ 均可逆。通过 $\Theta_q$，每个面已识别为 $A$ 的复矩阵直和；逐块使用 $\det(z^{-1/2}\ell z^{-1/2})=\det(\ell)/\det(z)$，即得 (66.7) 第一式。这是元素的 Jordan 行列式，分母幂次是一，不是二次表示算子的行列式或其维数幂次。

令 $u_{ij}$ 的本征值为 $\lambda_{ij,s}>0$，$s=1,\ldots,n_j$。在每个有序 $D_{ij}$ 选第一因子的任意正交基及第二因子的 $u_{ij}$ 本征基，形成
$q_{ijrs}=|r\rangle\langle r|\otimes|s\rangle\langle s|$，$r=1,\ldots,n_i$。这些元组成完整实际框架，且

$$
\begin{aligned}
v_{q_{ijrs}}&=\lambda_{ij,s}^{-1},\\
\det_A(\ell_{q_{ijrs}})&=\lambda_{ij,s}^{-n}\prod_k\det(u_{jk}),\\
\prod_{i,j,r,s}\det_A(\ell_{q_{ijrs}})
&=\left[\prod_{i,j}\det(u_{ij})^{-nn_i}\right]
  \left[\prod_{j,k}\det(u_{jk})^{nn_j}\right]=1.
\end{aligned}
\tag{66.10}
$$

第一括号中，每个本征值重复 $n_i$ 次。第二括号中，固定 $j$ 的框架元数为 $\sum_i n_in_j=nn_j$；因此每个有序 $\det(u_{ab})$ 在两括号中的指数恰为 $-nn_a$、$+nn_a$。这里只改名求积的哑指标，没有交换数据 $u_{ij},u_{ji}$。转置不改行列式。定理 64.8 的循环消去由此完整保留，未用任何范数值。

定理 66.3 使两份谱各有 $R$ 项；$Z=\sum_qz_q$ 的谱是第一份合并谱。第二份的迹满足

$$
\sum_q\tau_E(Y_q)=\sum_q\langle P_q,Y\rangle_E
=\langle1_E,Y\rangle_E=\gamma.
$$

结合 (66.7) 即得 (66.8)。两份谱不要求逐项互为倒数，且此时不要求 $Y$ 没有面间 Peirce 分量。$\square$

### 66.4 锐利迹权衡及非负校准余量

**定理 66.5（双迹下界和精确余量）。** 在 $\mathcal B+D_H$ 下，$\delta,\gamma>0$，并有

$$
\delta\gamma\ge R^2,\qquad\delta+\gamma\ge2R,
\qquad\frac\delta c+c\gamma\ge2R\quad(c>0).
\tag{66.11}
$$

置 $\varphi(x)=x-1-\log x$。对定理 66.4 所选谱和任意 $c>0$，有精确非负恒等式

$$
\frac\delta c+c\gamma-2R
=\sum_{\alpha=1}^R\varphi(\zeta_\alpha/c)
 +\sum_{\alpha=1}^R\varphi(c\eta_\alpha).
\tag{66.12}
$$

特别取 $c=1$，这就是 $\delta+\gamma-2R$ 的精确非负谱余量。还成立

$$
\left\|\sqrt{Z/c}-1_E\right\|_2^2
+\sum_{q\in\mathcal Q}
 \left\|\sqrt{cY_q}-P_q\right\|_2^2
\le\frac\delta c+c\gamma-2R.
\tag{66.13}
$$

第二项在相应面内开平方，范数来自固定规范迹。

**证明。** 令 $G=(\prod_\alpha\zeta_\alpha)^{1/R}$。两次普通 AM–GM 与 (66.8) 给出 $\delta\ge RG$、$\gamma\ge R/G$，故乘积至少 $R^2$；再对 $\delta/c,c\gamma$ 用两数 AM–GM 即得其余下界。两份缩放谱的总乘积仍为一，故它们的对数和为零，展开 $\varphi$ 就得到 (66.12)。$\log x\le x-1$ 使每项非负。最后

$$
\varphi(x)-(\sqrt x-1)^2
=2(\sqrt x-1-\log\sqrt x)\ge0.
$$

对两份谱求和即为 (66.13)。取 $c=\sqrt{\delta/\gamma}$ 时右端是 $2(\sqrt{\delta\gamma}-R)$。该估计只控制 $Z$ 及所选 $Y_q$ 的平方根谱偏差；它不控制完整 $Y$ 的面间分量、完整映射的算子范数误差或任何物理资源成本。$\square$

### 66.5 乘积等号的全局共同尺度

**定理 66.6（精确尺度刚性）。** 在 $\mathcal B+D_H$ 下，以下条件等价：

$$
\begin{aligned}
&\delta\gamma=R^2;\\
&\text{存在 }c>0:\ U=1_D,\quad H1_D=c1_E.
\end{aligned}
\tag{66.14}
$$

此时 $c$ 唯一，$c=\delta/R=R/\gamma=\sqrt{\delta/\gamma}$，并强制

$$
\begin{gathered}
p^*1_D=c^{-1}1_E,\qquad\tau_Dp=c^{-1}\tau_E,
\qquad H^*H=c^2n\operatorname{id}_D,\\
hL(d,a)=c^2\tau_A(a)d,\qquad tL(d,a)=\tau_D(d)a,\\
\tau_Dh=c\tau_E,\qquad\tau_At=c^{-1}\tau_E.
\end{gathered}
\tag{66.15}
$$

第一接口完全归一化：$M=F$、完整 I、$W_J$、$r,s$ 全锥正保迹、$r\omega=s\omega=e$ 及完整 III 都成立。派生尺度坐标

$$
L_0=L/c,\quad p_0=cp,\quad H_0=H/c,\quad h_0=h/c,\quad t_0=ct
\tag{66.16}
$$

满足第 64 节全部归一化的探针之前结论；其内部 $B,K,M,J,U$ 与原实际数据逐点相同。反之，任意满足第 64 节归一化探针之前条件的数据，取实际 $L=cL_0,p=c^{-1}p_0$，便得到此等号类。对指定 $c>0$，$\delta/c+c\gamma=2R$ 当且仅当 (66.14) 以此 $c$ 成立。

**证明。** 乘积等号迫使定理 66.5 证明中的两次 AM–GM 分别等号，故每个 $\zeta_\alpha=c$、每个 $\eta_\alpha=c^{-1}$。对所选框架，这给出

$$
z_q=cP_q,\qquad Y_q=c^{-1}P_q,\qquad Z=c1_E.
$$

因而 $K_q=c\Theta_q$，$\ell_q=K_q^*Y_q=1_A$。将此代入 (66.9)，保留 (64.25) 的全部有序指标，得到

$$
u_{jk}^{T^{\delta_{jk}}}=\lambda_{ij,s}I_{n_k}
\qquad\text{对每个 }i,j,s,k.
\tag{66.17}
$$

固定 $j$ 并任选 $i,s$，出行 $j$ 的全部矩阵均为同一正标量 $a_j$ 乘单位。于是 $u_{ij}=a_iI_{n_j}$，其每个本征值为 $a_i$；代回 (66.17) 得 $a_j=a_i$ 对全部有序 $i,j$ 成立。故 $U=a1_D$。已付的 $\tau_D(U^{-1})=m$ 强制 $a=1$。这一步消去的是内部权重，不消去外部尺度 $c$；它不止证明中心性，且包括单扇区、标量扇区和 $n=1$。

接着只假定 $U=1_D,Z=c1_E$，给出剩余全局结论，也同时证明反向。现在 $C=\operatorname{id}$，第一接口为实际 $M=F$，$r=\alpha^*$、$s=\beta^*$；其完整 I、$W_J$、保迹及 $r\omega=s\omega=e$ 由定理 64.4 和相同迹配对得到，完整 III 来自定理 64.5。

必须对任意本原 $q\in D$ 重新使用 $D_H$，而不局限于所选框架。两个正元 $Hq,H(1_D-q)$ 支撑正交且和为 $c1_E$，故 $Hq=cP_q$。定理 66.3 的 $K_q/c$ 现在自身就是保单位 Jordan 同构，保持继承的规范迹。因此

$$
\tau_EL(q,a)=c\tau_A(a),\qquad
\tau_EL(d,a)=c\tau_D(d)\tau_A(a)
\tag{66.18}
$$

对全部本原 $q$ 和全部实 $d,a$ 成立，第二式由本原元实张成而来。另一方面，$pL(d,a)=M(sd,a)$ 及第一接口保迹给出

$$
\tau_DpL(d,a)=\tau_D(d)\tau_A(a).
$$

比较并用实际 $L(D,A)$ 张成整个 $E$，才得到 $\tau_Dp=c^{-1}\tau_E$ 和 $Y=c^{-1}1_E$。仅由所选 $Y_q=c^{-1}P_q$ 不能推出这个全局结论。

再对任意本原 $q$ 使用 (66.6)，有

$$
\begin{aligned}
\langle q,hL(d,a)\rangle_D
&=\langle Hq,L(d,a)\rangle_E\\
&=c\langle P_q,\Pi_qL(d,a)\rangle_E\\
&=c^2\langle q,d\rangle_D\tau_A(a).
\end{aligned}
$$

本原元张成给出 (66.15) 的第二插入公式；取 $a=1_A$ 得 $H^*H=c^2n\operatorname{id}$。$tL$ 由 $V=1_D$ 得到；两个全局迹式分别由 $H1_D=c1_E$ 和 $t=sp$、$s$ 保迹得到。

因此 $(L_0,h_0,t_0)$ 在整个锥上正、两个边缘全局规范保迹，满足全部实方向的两条丢弃律及实际实张成。现在才应用定义 64.3 的第二接口，得到 $\widetilde L_0$ 满等距、单位律和全效应配对。第一接口的 $\widetilde M$ 满等距使 $\widetilde Q_0$ 也满等距；原实际线性化则满足

$$
\widetilde M^*\widetilde M=\operatorname{id},\qquad
\widetilde L^*\widetilde L=c^2\operatorname{id},\qquad
\widetilde Q^*\widetilde Q=c^2\operatorname{id}.
$$

它们均满射。又 $p_0L_0=pL$，所以两次同一个读回产生的内部 $M$ 没有改变。特别是 $H_0^*H_0=n\operatorname{id}$、$p_0$ 保迹及 $\gamma_0=R$，故第 64 节所有探针之前结论均适用。若从 $U=1_D,Z=c1_E$ 出发，(66.18) 和全局读回迹式给出 $\delta=cR,\gamma=R/c$，完成反向。反向缩放构造的正性、张成、内部定义、$D_J,Z,D_H$ 同样逐项保留。最后指定尺度的和等号由 (66.12) 每项为零刻画。式 (66.16) 是尺度分类；原来的实际映射仍明确是 $L=cL_0,p=c^{-1}p_0$，$c\ne1$ 时没有把它们称为已归一化。$\square$

### 66.6 一条共同参考读数与原条件的同数据等价

**定理 66.7（第二范数律和单独上界的精确替换）。** 在同一 $\mathcal B$ 的实际数据上，

$$
\bigl(W_H\ \&\ N\bigr)
\quad\Longleftrightarrow\quad
\bigl(D_H\ \&\ C_{\rm joint}\bigr),\qquad
C_{\rm joint}:\ \delta+\gamma\le2R.
\tag{66.19}
$$

右侧强制 $\delta=\gamma=R$、$c=1$，故 $U=1_D$、$H1_D=1_E$、$p^*1_D=1_E$ 及定理 64.9 全部结论成立。

**证明。** 新方向由

$$
2R\ge\delta+\gamma\ge2\sqrt{\delta\gamma}\ge2R
$$

迫使全部等号，再用定理 66.6，得到 $c=1$、$W_H$ 及 $N$。反向，$W_H$ 对全部实方向的配对恒等式立即给出 $D_H$。此时可用定理 66.3–66.4，但尚不使用定理 64.9：对所选完整框架，$W_H$ 给出

$$
\sum_\alpha\zeta_\alpha^2=\sum_{q\in\mathcal Q}\|Hq\|^2=mn=R.
$$

$R$ 项 Cauchy–Schwarz 使 $\delta\le R$，而原 $N$ 给出 $\gamma\le R$，故 $C_{\rm joint}$ 成立。两方向保持同一 $A,D,E,L,p$，不存在换模型或暗中重标度。此等价只在全部保留前提下成立，不是条件独立性、最少公理或完整模型类严格扩大的定理。$\square$

### 66.7 固定简单矩阵载体上的完整双迹可行域

**定理 66.8（锐利双曲可行域的显式实现）。** 固定 $n\ge2$ 和数学载体 $A=H_n$、$D=H_{n^2}$、$E=H_{n^3}$，均取全部矩阵正锥、标准迹、全态和全效应。满足 $\mathcal B+D_H$ 的数据的双迹像恰好是

$$
\{(\delta,\gamma)\in(0,\infty)^2:\delta\gamma\ge n^6\}.
\tag{66.20}
$$

对任意正定 $w\in H_n$，一个实现族为

$$
\begin{aligned}
L_w(d,a)&=d\otimes w^{1/2}aw^{1/2},\\
p_w(X)&=(I_n\otimes w^{-1/2})\operatorname{Tr}_1(X)
             (I_n\otimes w^{-1/2}),
\end{aligned}
\tag{66.21}
$$

其中 $\operatorname{Tr}_1$ 丢弃三份中的第一份。此族满足

$$
\delta=n^2\operatorname{Tr}w,\qquad
\gamma=n^2\operatorname{Tr}w^{-1}.
\tag{66.22}
$$

**证明。** 这个族直接取定理 65.10–65.11 的单扇区参数 $n_1=n$、$u_{11}=I_n$、$g_{111}=w$；约束 (65.28) 为 $n\operatorname{Tr}I_n=n^2$。其 $L,p$ 恰为 (66.21)，所以整个实际锥上的正性、两条实张成、同一个 $p_w$ 两次的内部定义、$D_J,D_H,Z$、完整比较入口以及同一个整锥插入正性，都直接由该既有逆定理供应，包含纠缠方向。该族的分类与存在性不是本节新成果，也不把这个带 C13 的充分实现族用于普遍无 C13 迹下界的证明。为计算新迹读数，将 (65.32) 的对应内部映射列为

$$
\begin{aligned}
B_w(d,a)&=(\operatorname{Tr}_1d)\otimes a,\\
K_w(a)&=(I_n/n)\otimes a=e\otimes a,\\
M_w(a,b)&=a\otimes b,\qquad J_w(a)=a\otimes I_n,\\
H_w(d)&=d\otimes w.
\end{aligned}
\tag{66.23}
$$

单位上 $H_w1_D=I_{n^2}\otimes w$、$p_w1_E=nI_n\otimes w^{-1}$，取原规范迹即得新的 (66.22)。正定谱的 Cauchy–Schwarz 给出 $\operatorname{Tr}w\operatorname{Tr}w^{-1}\ge n^2$，等号恰为 $w$ 标量，符合定理 66.6。

为实现任意 $d_0,g_0>0$ 且 $d_0g_0\ge n^6$，令

$$
c=\sqrt{d_0/g_0},\qquad S=\frac{\sqrt{d_0g_0}}{n^2}\ge n,
\qquad t=S-n+2\ge2.
$$

取 $x=(t+\sqrt{t^2-4})/2\ge1$，则 $x+x^{-1}=t$。置

$$
w=c\operatorname{diag}(x,x^{-1},1,\ldots,1).
$$

两迹分别为 $cS,c^{-1}S$，所以 (66.22) 恰为 $\delta=d_0,\gamma=g_0$。这是显式手算恒等式，不依赖搜索或数值枚举。定理 66.5 给出所有允许数据的必要区域，此固定载体族实现整个区域，故 (66.20) 为精确像。$n=1$ 时，第一二元接口及支持面秩使 $A=D=E=\mathbb R$；$U=1$ 和内部定义使实际数据为 $L(d,a)=cda,p(x)=c^{-1}x$，只有 $\delta\gamma=1$ 的边界。经典和一般直和情形仍由前述普遍定理覆盖；这里的满区域实现专指 $n\ge2$ 的固定简单矩阵载体。该族构造数学映射，不构造原始 $\Omega$ 的实际准备或设备。$\square$

### 66.8 必须保留的零关系、尺度和 Bell 控制

**命题 66.9（遗漏控制的精确读数）。** 单独的联合迹校准不能替代 $D_H$；单独的最小迹乘积不能固定实际插入尺度；二者归一化后仍不能删除定理 64.10 的独立整输出 Bell 条件。

**证明。** 第一项复用 (62.44)–(62.46) 的经典例。取 $A=\mathbb R^2,D=\mathbb R^4,E=\mathbb R^8$，$P=\left(\begin{smallmatrix}3/4&1/4\\1/4&3/4\end{smallmatrix}\right)$，$L(d,a)=((P\otimes\operatorname{id})d)\otimes a$、$p=\operatorname{Tr}_1$。原例已经给出全锥正性、两条张成、同一个 $p$ 的内部普通张量 $M$、$D_J,Z$ 及全锥交叉插入正性。$P1=1$ 且 $p$ 保迹，故 $Z=1_E$、$\delta=\gamma=8$，正好满足联合校准。可是对任意坐标本原 $e_j\in\mathbb R^2$，两个正交本原元 $q=e_0\otimes e_j$、$q'=e_1\otimes e_j$ 的像满足

$$
\langle Hq,Hq'\rangle
=\left(\frac34\frac14+\frac14\frac34\right)\langle e_j,e_j\rangle
 \langle1_2,1_2\rangle=\frac34>0.
\tag{66.24}
$$

所以 $D_H$ 失败。原 $P^{\mathsf T}P$ 的非零交叉项也使 $W_H$ 和完整 II 失败。这是已有控制的新零关系读数，不重复计作新的模型构造。

第二项可取 (66.21) 的 $w=\lambda I_n$，或任意标准直和张量数据的全局尺度族 $L=\lambda L_{\rm tens}$、$p=\lambda^{-1}p_{\rm tr}$，$\lambda>0$。两次内部读回仍产生相同 $M$，$D_H$ 保持，而

$$
\delta=\lambda R,\quad\gamma=R/\lambda,\quad
\delta\gamma=R^2,\quad
\delta+\gamma=R(\lambda+\lambda^{-1}),\quad
H^*H=\lambda^2n\operatorname{id}.
\tag{66.25}
$$

因此 $W_H$ 当且仅当 $\lambda=1$；$\lambda>1$ 时甚至仍满足旧 $N$，却未固定实际尺度。迹和的最小值恰好排除这一个自由度。

第三项由定理 64.11 的全锥正转置控制给出：它满足旧 $W_H,N$，故由定理 66.7 满足新 $D_H,C_{\rm joint}$，但预选 Bell 输出仍有负本征值。其有序跨扇区和标量中间旁观者控制同样保留。零关系及迹校准只恢复探针之前的接口，没有免除交叉插入的独立条件。$\square$

### 66.9 完整静态候选与同数据复量子对应

**定义 66.10（双零关系与联合参考校准的完整候选）。** 完整输入是定义 66.1 的每一项：三个实际有限全态全效应比较入口及完整有限混合 $S$，其原比较单位、全态全效应及规范迹 Jordan 几何由既有 §65.1 条件纸面定理供应，不重复增加独立 Jordan 输入；全锥正的实际 $L,p$；同一个 $p$ 两次内部定义的 $M$；$M,L$ 两条实际实张成；全部量词下的 $D_J,\mathrm{(Z)}$。增加 $D_H,C_{\rm joint}$，保留定义 64.3 的二元纸面接口、有限 Jordan 分类和乘积秩一保持工具。先由定理 66.7 恢复两个归一化接口，再按第 64 节 3.3 的规则预选实际正迹一 $\sigma_*$，最后只增加一个条件

$$
I_{13}(\sigma_*)\in E_+,\qquad
I_{13}=\mathcal T\widetilde M^{-1},\qquad
\mathcal T(a\otimes c)=Q(a,1_A,c).
\tag{66.26}
$$

该预选规则使用 $M$ 的允许初始正规形及每个有序非标量端点对的两维 Bell 投影，等权直和；没有活跃端点对时用 $1_D/m$。选取不读取 $Q,I_{13}$ 或测试输出。要求的是整个 $E$ 输出为正，覆盖每个中间扇区，包括标量旁观者；它不是一次标量概率条件，也不附赠实际制备该探针的能力。

**定理 66.11（同数据等价、唯一读回及静态量子几何）。** 定义 66.10 的完整候选与定理 64.12 的完整候选在完全相同的实际 $A,D,E,L,p$ 上等价。它推出全部定理 64.9–64.13 的结论，特别是完整 I、II、III、全局 $p$ 保迹、整锥 $I_{13}$ 正性和唯一正保迹读回

$$
p_{13}=I_{13}^*,\qquad
p_{13}Q(a,b,c)=\tau_A(b)M(a,c)\quad(a,b,c\in A).
\tag{66.27}
$$

在固定保迹 Jordan 序坐标中，存在有限非空 $\Lambda$ 和 $n_i\ge1$，使

$$
A=\bigoplus_iH_{n_i},\quad D=\bigoplus_{i,j}H_{n_in_j},\quad
E=\bigoplus_{i,j,k}H_{n_in_jn_k},
$$

并且同一实际映射为

$$
\begin{aligned}
M(a,b)_{ij}&=a_i\otimes b_j,&L(d,c)_{ijk}&=d_{ij}\otimes c_k,\\
(rd)_i&=\sum_j\operatorname{Tr}_2d_{ij},&(sd)_j&=\sum_i\operatorname{Tr}_1d_{ij},\\
(hz)_{ij}&=\sum_k\operatorname{Tr}_3z_{ijk},&(pz)_{jk}&=\sum_i\operatorname{Tr}_1z_{ijk},\\
(p_{13}z)_{ik}&=\sum_j\operatorname{Tr}_2z_{ijk}.&&
\end{aligned}
\tag{66.28}
$$

全态、全效应与配对为 $\rho_i\ge0$、$\sum_i\operatorname{Tr}\rho_i=1$、$0\le f_i\le I_{n_i}$ 和 $\Pr(f\mid\rho)=\sum_i\operatorname{Tr}(f_i\rho_i)$。纯态空间为 $\coprod_i\mathbb{CP}^{n_i-1}$，同扇区最小确认比较是平方重叠、异扇区为零；单一 $n_i=2$ 扇区的全态为 Bloch 球。这里 $\mathbb{CP}^{n_i-1}$ 表示复射影空间，不是操作的完全正性假设。

**证明。** §65.1 的既有纸面结果在完全相同的完整比较入口上供应旧候选所列的保归一化 Jordan 桥，故这里删除重复输入不改变其条件适用域。定理 66.7 首先给出旧 $W_H,N$ 和定理 64.9，完全不使用 (66.26)。故 $\widetilde M$ 可逆、两个二元接口和 $Q$ 满等距已经成立，定理 64.10 的完整前提此时才齐备。其精确块公式 (64.32)、方向 $U_{ik}^*\beta_{ik}U_{ik}=b_{ik}$ 及每个有序输出块的 Bell 负本征值，证明 (66.26) 等价于整个 $D_+$ 上的插入正性；没有把一次输出的某个迹代替全算子正性。

由于 $I_{13}1_D=1_E$，自对偶性给出其伴随正保迹。$Q$ 等距给出

$$
\langle M(x,y),I_{13}^*Q(a,b,c)\rangle_D
=\tau_A(b)\langle x,a\rangle_A\langle y,c\rangle_A.
$$

$M$ 张成得到 (66.27)，$Q$ 张成使满足该读回律的实线性映射唯一。其余即在这些已经满足的输入下应用定理 64.12–64.13：全域 $p,p_{13}$ 正性消去相对转置缺陷，含重复标签和标量位置的三边关系允许同时 untwist，得到 (66.28)；全态全效应和规范迹给出 Born 配对、复射影纯态与 Bloch 几何。逆向，旧完整候选的 $W_H,N$ 给出新 $D_H,C_{\rm joint}$，其 $M$ 及预选探针规则逐点不变。标准直和矩阵数据满足两个完整候选，包括全标量经典扇区和 $A=\mathbb R$。故这是同实际数据的双向等价。$\square$

**推论 66.12（乘积边界上的带尺度对应）。** 若只用 $\delta\gamma=R^2$ 代替 $C_{\rm joint}$，再要求同一预选 Bell 输出正，则定理 66.6 的 $L_0,p_0$ 满足完整归一化候选。在相同固定矩阵坐标中，原实际 $M$ 仍为普通张量，而原实际 $L=cL_{\rm tens}$、$p=c^{-1}p_{\rm tr}$。此时 $I_{13}=cI_{13,0}$，正尺度使 Bell 条件与归一化条件等价。若要求实际缩放 $Q=cQ_0$ 的读回仍满足 (66.27) 的右端，唯一读回为

$$
p_{13}^{(c)}=c^{-1}I_{13,0}^*=c^{-2}I_{13}^*;
$$

它的迹尺度是 $c^{-1}$，只有 $c=1$ 时才是规范保迹读回。

**证明。** $p_0L_0=pL$ 保持内部 $M$，因此探针的预选不变，$Q=cQ_0$ 使交叉插入乘以 $c$。应用定理 66.11 于归一化数据，再缩放读回律，得到所示公式；唯一性仍来自实际 $Q$ 张成。此处没有把未校准的实际 $I_{13}^*$ 错当成原读回。$\square$

### 66.10 几何解释、来源与原始来源边界

**几何解释。** 零比较只问原来互不重叠的两个正方向，插入后是否仍互不重叠，并不规定它们的长度。第 65 节已有支持接口说明：正读回保证任何非零正方向不会被插入抹掉，实际张成保证每个本原方向承载一个完整的 $A$ 支持面，所有支持单位铺满环境单位。面之间仍可有量子相干的 Peirce 半空间，不能把这幅图理解为整个系统被拆成互不相干的经典格子。一般正滤波并不只是共同尺度；本节的乘积等号才强制 $U=1_D$、$H1_D=c1_E$。

循环内部定义使插入谱和读回压缩谱的总乘积为一。一边缩小，另一边必须补偿；方向之间不均匀还会增加迹的代价。双迹的可行域因而在一条双曲线之上，且显式矩阵权重实现它的每个点。双曲线边界上，所有方向只能共享一个尺度；联合迹和的最小值才把这个尺度固定为一。固定之后，一个预选 Bell 合成态的整个输出正性继续负责排除相对转置错误，普通复量子静态几何才完整接回。

**来源与归属。** 有限 EJA 的谱分解、自对偶、支撑及二次表示，保单位序同构的 Jordan 性、规范迹和元素行列式，复矩阵分类、乘积秩一保持以及 AM–GM、Cauchy–Schwarz、$\log x\le x-1$ 都是成熟工具。所用 EJA 与分类文献和精确接口见定义 64.3、定理 64.6、64.13 的原始出处链接。正左逆、加权 III、全部有序权重坐标、循环行列式、Bell 块公式及同时 untwist 复用第 64 节；经典模糊控制来自 (62.44)–(62.46)。完整 $S$ 到规范迹 EJA 的原单位、态、效应对应复用 §65.1 的既有条件纸面定理及其 Library 来源；无范数第二支持接口复用定理 65.3–65.5 的明确无 C13 证明级子结果；完整原始滤波分类、逆向及单扇区 $w$ 族复用定理 65.10–65.11。它们均不计作本节新成果。本节新增仓内综合内容是锐利双迹权衡及精确谱余量、全局共同尺度等号分类、同数据联合校准替换与固定矩阵载体的完整双迹像；不作全球新颖性、优先权、Lean 或完整量子起源声明。

**范围。** 本节是纸面条件定理，不含 Lean 形式核验。没有从原始 $\Omega$ 定义推出 $D_H$、$C_{\rm joint}$ 或探针的实际可获得性，也没有以条件名称变短证明原始来源上的实现更容易。所有原始对象、准备、事件、过程、参考、副本及相关联合，零质量和不等质量，时钟、单位、控制、ready 与 flags，全部记录、失败、停止、破坏、返回及未来，以及既有全菜单、固定支持和每个已量化中间切割义务，均按原有域保留；本节不结算其中尚未结清的义务。实际 acceptance 23.7 与 active Return 164 的原始连接仍未在此构造；不能从矩阵实现推断它们已成立。

数学上的单位、规范迹、二次表示、$w$、坐标、Bell 态和读回尺度，不附赠实际准备、相干控制、复制、参考或设备；没有用 Born 或完全正性循环定义原始输入。静态 Born 配对不推出任意独立操作的完全正性、参考扩张、仪器、Kraus 实现或态更新，也不推出过程误差、动力学、Hamiltonian、时钟或 $\hbar$。未构造新的原始 analyzer/menu/source incidence，未识别独立给定的右载体，未增加高份数、无限维或完整量子起源结论。此前来源及过程成果保持其各自已述适用域，不能由这里的归一化和可行域扩大其范围。

## 追加锚（本行以下为增补区）
