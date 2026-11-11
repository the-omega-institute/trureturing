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

## 66. 去掉交叉正性后的原态几何与有序方向分类

### 66.1 完整有限比较与唯一删除的条件

**定义 66.1（不要求 C13 的实际系统）。** 对每个 $X=A,D,E$，保留定义 65.1 的非零有限实载体、闭尖生成锥 $C_X$、严格正归一化 $u_X$、完整紧态基 $K_X=\{x\in C_X:u_X(x)=1\}$ 和全部效应 $[0,u_X]$。记纯态集 $P_X=\operatorname{ext}K_X$，仍只对纯第一端点定义

$$
T^X_\xi(x)=\inf\{f(x):0\le f\le u_X, f(\xi)=1\},
\qquad \xi\in P_X, x\in K_X.
\tag{66.1}
$$

对每个 $X$、每个纯 $\xi$、每个有限纯态族 $(\eta_\ell)$ 及每组概率权重 $(v_\ell)$，要求

$$
T^X_\xi\left(\sum_\ell v_\ell\eta_\ell\right)
 =\sum_\ell v_\ell T^X_{\eta_\ell}(\xi).
\tag{66.2}
$$

复用定义 65.1 所引 [完整 $S$ 到一般有限 EJA 的条件纸面桥](../../../Library/QuantumStates/mullerududec2012selfduality.md#complete-conditional-candidate-and-its-scope)，而不另加独立 Jordan 公理。该桥的项目性、共同框架和滤波纯性义务保持原范围；纯端点互反本身不代替这些推导。若其锥坐标 $\Psi_X$ 中原归一化表示为 $\tau_X(h_X\circ-)$、$h_X>0$，使用 $\Phi_X=P_{\sqrt{h_X}}\Psi_X$。由 (65.3)–(65.4)，此坐标保持原全态基、全效应区间及原比较配对：

$$
\tau_X\Phi_X=u_X,\qquad
B_X(x,y)=\tau_X(\Phi_Xx\circ\Phi_Xy),\qquad
\Phi_XU_X=1_X.
\tag{66.3}
$$

以下在该忠实坐标中写 $A,D,E$，每个理想的每个本原幂等元迹一。令 $n=\tau_A1_A$、$m=\tau_D1_D$、$\omega=1_D/m$。原始数据仅为实双线性 $L:D\times A\to E$ 和实线性 $p:E\to D$，要求

$$
L(D_+,A_+)\subseteq E_+,\qquad p(E_+)\subseteq D_+.
\tag{66.4}
$$

定义全部实际内部映射为

$$
\begin{aligned}
\mathcal B(d,c)&=pL(d,c),&K(a)&=\mathcal B(\omega,a),\\
M(a,b)&=\mathcal B(K(a),b),&J(a)&=M(a,1_A),\\
H(d)&=L(d,1_A),&B_1&=pH,\\
Q(a,b,c)&=L(M(a,b),c),&U&=M(1_A,1_A).
\end{aligned}
\tag{66.5}
$$

这里两次调用的是同一个实际 $p$，参考是同一个原 $\omega$。保留两条实张成以及全部原量词：

$$
\begin{gathered}
\operatorname{span}_{\mathbb R}M(A,A)=D,\qquad
\operatorname{span}_{\mathbb R}L(D,A)=E,\\
a,b\in A_+, \langle a,b\rangle_A=0
 \Longrightarrow \langle Ja,Jb\rangle_D=0\quad(D_J),\\
d,d'\in D_+, \langle d,d'\rangle_D=0
 \Longrightarrow \langle Hd,Hd'\rangle_E=0\quad(D_H),\\
B_1M(a,b)=\tau_A(a)Jb\qquad(a,b\in A)\quad(Z).
\end{gathered}
\tag{66.6}
$$

相对于定义 65.1–65.2，仅删除 C13。$D_H$ 仍覆盖整个实际 $D_+$，包括矩阵表示中的纠缠正元；$Z$ 覆盖全部实输入。不添加 $W_J,W_H$、原始保单位、原始保迹、校准或独立准备 $M$。第 65 节保留 C13 的条件结论保持其原范围。

### 66.2 前交叉接口的精确复用范围

**命题 66.2（只取 $F,N$ 及原始恢复接口）。** 定义 66.1 下，定理 65.3–65.6、推论 65.7 的前交叉证明给出以下接口。置

$$
\begin{aligned}
&C_D=P_{\sqrt U},\quad F=C_D^{-1}M,\quad
\alpha=F(-,1_A),\quad\beta=F(1_A,-),\\
&G=H1_D,\quad C_G=P_{\sqrt G},\quad
N=C_G^{-1}L,\quad\eta=N(-,1_A),\quad\zeta=N(1_D,-),\\
&C_E=C_GP_{\sqrt{\eta(U)}},\quad
Q_0(a,b,c)=N(F(a,b),c),\quad p_0=C_D^{-1}pC_E.
\end{aligned}
\tag{66.7}
$$

$U,G$ 正可逆，$\widetilde F:A\otimes_{\mathbb R}A\to D$、$\widetilde N:D\otimes_{\mathbb R}A\to E$ 均是满规范迹内积等距同构；$F,N$ 在各自全正乘积域为正、保乘积单位、将本原对送到本原元。$\alpha,\beta$ 以及 $\eta,\zeta$ 分别为环境中算子交换的保单位 Jordan 嵌入，且

$$
F(a,b)=\alpha(a)\circ\beta(b),\qquad
N(d,c)=\eta(d)\circ\zeta(c).
$$

$U$ 与 $\alpha(A)$、$G$ 与 $\eta(D)$ 算子交换。$C_D,C_E$ 是自伴随全锥序自同构，$C_E$ 的两个因子交换。全部实输入上有

$$
\begin{gathered}
m=n^2,\quad\operatorname{rank}E=n^3,\quad
s=\beta^*C_D^{-1}\ge0,\quad V=U^{-1},\quad\tau_DV=n^2,\\
w=s\omega>0,\quad\tau_Aw=1,\quad
sM(a,b)=\tau_A(a)b,\quad K(a)=M(w,a),\\
\mathcal B(d,c)=M(sd,c),\quad B_1=Js,\quad
pQ(a,b,c)=\tau_A(a)M(b,c),\\
M=C_DF,\quad L(d,c)=C_EN(C_D^{-1}d,c),\quad Q=C_EQ_0,\\
p=C_Dp_0C_E^{-1},\qquad
p_0Q_0(a,b,c)=\tau_A(a)F(b,c).
\end{gathered}
\tag{66.8}
$$

$p_0$ 全锥正且保规范迹。此处没有使用 13 插入、13 读回或三读回的同时定向表示。

证明。定理 65.3 的证明明确不使用 $D_H$ 或 C13；定理 65.4 只再使用 $D_H$ 和实际 $L$ 的全域正性、张成。第二接口的关键是定理 65.5 的满本原角，而非预设复矩阵类型：全锥正
$R=(spC_G)P_{\eta(V^{-1/2})}$ 满足 $RN(d,c)=\tau_D(d)c$。对本原 $e\in D$，支撑交织和张成给

$$
E_1(\eta e)=N(e,A),\qquad RN(e,-)=\operatorname{id}_A.
$$

故 $N(e,-)$ 是整个角上的保单位序同构，正逆是 $R$ 的限制。它保持效应区间极点、幂等元及谱分解，成为保规范迹的 Jordan 同构；角本原元也是环境本原元，不产生额外迹倍数。各本原角的配对给 $\widetilde N$ 等距及乘积本原性。定理 65.6 的交换二次表示计算给恢复等式，$Q_0$ 张成把其迹恒等式推广到全 $E$；推论 65.7 使用同一原 $\omega$ 重算辅助映射。以上均在定理 65.8 的 C13 步骤之前闭合，因而可原样复用。$\square$

### 66.3 先由第一接口、再由第二接口确定载体

**定理 66.3（无 C13 的全部原始复 Born 载体）。** 在上述条件纸面接口下，存在有限非空扇区集 $I$ 和整数 $n_i\ge1$，使原载体在保迹 Jordan 序坐标中恰为

$$
A=\bigoplus_i H_{n_i}(\mathbb C),\qquad
D=\bigoplus_{i,j}H_{n_in_j}(\mathbb C),\qquad
E=\bigoplus_{i,j,k}H_{n_in_jn_k}(\mathbb C),\qquad
n=\sum_i n_i.
\tag{66.9}
$$

全部有序块均出现，包括重复标签、标量块及混合块。该结论先于任何共同方向选择。

证明。先将 [Library 的中心扇区与简单自复合论证](../../../Library/QuantumStates/barnumhilgert2019spectral.md#sector-composites-without-a-connectedness-input) 精确施用于命题 66.2 的二元接口。一般地，设 $T:X\times Y\to Z$ 具有该处的正性、乘积单位、本原性、满迹等距及交换 Jordan 嵌入 $\alpha_T,\beta_T$。由交换及同态性质，

$$
\alpha_T(x)\circ T(x',y)=T(x\circ x',y).
\tag{66.10}
$$

若 $c_i,d_j$ 是局部简单理想的中心单位，则在 $T$ 的张成坐标上，$\ell_{\alpha_T(c_i)}=\ell_{c_i}\otimes\operatorname{id}$ 是投影。因此幂等元 $\alpha_T(c_i)$ 没有 Peirce 半空间，零、一空间是互补理想，即该幂等元在 $Z$ 中心；$\beta_T(d_j)$ 同理。它们的乘积 $z_{ij}=T(c_i,d_j)$ 非零、中心、两两正交且和为 $1_Z$，其理想恰为

$$
Z_{ij}=\operatorname{span}_{\mathbb R}T(X_i,Y_j),\qquad
\dim Z_{ij}=\dim X_i\dim Y_j.
\tag{66.11}
$$

这里的维数等式来自实线性化单射，不是只数产品态。

每个简单 EJA 的本原比较图连通：不同连通分支的本原元两两正交，其实张成空间也正交；正元的谱分解及正交正元乘积为零，使交叉 Jordan 乘积为零。结合迹内积的结合性，各分支张成空间成为互补理想，故简单性排除多个分支。迹等距给

$$
\langle T(q,r),T(q',r')\rangle
 =\langle q,q'\rangle\langle r,r'\rangle.
$$

固定一腿、沿另一腿的本原比较图移动，便连接 $Z_{ij}$ 的全部乘积本原像。一个本原元只属一个简单理想，非零比较不能跨理想，因此这些像同属一个简单理想；它们又张满 $Z_{ij}$，故 $Z_{ij}$ 简单。两个完整本原框架的像是两两正交本原元，和为 $z_{ij}$，于是

$$
\operatorname{rank}Z_{ij}
 =\operatorname{rank}X_i\operatorname{rank}Y_j.
\tag{66.12}
$$

先取 $T=F$。若 $A_i$ 的秩、实维数为 $r,d$，实际简单块 $D_{ii}$ 的秩、维数必须是 $r^2,d^2$。使用 [Library 的简单自复合维数筛选](../../../Library/QuantumStates/barnumhilgert2019spectral.md#complex-sectors-from-a-single-self-composite)，即 van de Wetering, [arXiv:1803.11139v3, Proposition 40](https://arxiv.org/abs/1803.11139v3) 的秩维数结论，而不使用其额外的 sequential-product 兼容条件。具体边界为：秩一简单块是 $\mathbb R=H_1(\mathbb C)$；秩二的任意简单 spin 因子需要一个秩四简单块，其可能维数仅为 $10,16,28$，其中只有 $16$ 是整数平方，故局部维数为 $4$，即复 qubit。对 $r\ge3$，实矩阵型的平方维数低于秩 $r^2$ 简单块的最小维数，差为

$$
\frac{r^2(r^2+1)}2-\left(\frac{r(r+1)}2\right)^2
 =\frac{r^2(r-1)^2}{4}>0.
$$

四元数型的平方维数高于该秩的最大维数，差为

$$
\bigl(r(2r-1)\bigr)^2-r^2(2r^2-1)
 =2r^2(r-1)^2>0.
$$

Albert 块 $(r,d)=(3,27)$ 则需要秩九、维数 $729$，而该秩简单块维数只有 $45,81,153$。因此 $A_i=H_{n_i}(\mathbb C)$。

每个混合 $D_{ij}$ 简单，秩 $q=n_in_j$、维数 $q^2$。$q=1$ 是标量，$q=2$ 是四维 spin 因子；$q\ge3$ 的实、复、四元数维数表仅允许复型，$q=3$ 时亦排除维数 $27$ 的 Albert 块。再且仅再将同一个扇区论证用于 $N:D\times A\to E$，得每个 $E_{ijk}$ 简单、秩 $q=n_in_jn_k$、维数 $q^2$，同一分类表给复型。没有用三读回表示反推 $A,D,E$，也没有要求整个 $A$ 的本原比较图连通。$\square$

### 66.4 两个有序接口的方向正规形

**命题 66.4（先固定 $D$、再固定 $E$）。** 在 (66.9) 的逐块保迹 Jordan 坐标中，可以取有序位 $\varepsilon_{ij},\delta_{ijk}\in\{0,1\}$，使

$$
F(a,b)_{ij}=a_i\otimes b_j^{T^{\varepsilon_{ij}}},\qquad
N(d,c)_{ijk}=d_{ij}\otimes c_k^{T^{\delta_{ijk}}}.
\tag{66.13}
$$

$T$ 是固定基底的普通转置，$T^0=\operatorname{id}$、$T^1=T$；同一个标签在不同位置仍按有序块处理。

证明。采用 [Library 的 Xu–Zheng–Fošner 精确秩保持接口](../../../Library/QuantumStates/barnumhilgert2019spectral.md#conditional-normal-form-theorem-and-proof)，文献为 *Linear maps preserving tensor products of rank-one Hermitian matrices*, J. Aust. Math. Soc. 98 (2015), 407–428，[DOI 10.1017/S1446788714000603](https://doi.org/10.1017/S1446788714000603)，p.409 Main Theorem (1.1)–(1.2)。其前件是实线性单射、各输入尺寸至少二、目标尺寸不小于输入尺寸之积，并将每个秩一 Hermitian 产品送到秩一 Hermitian 矩阵；不要求输出可分离。

$F_{ij}$ 的线性化因满迹等距而单射，两个本原输入的像秩一；非零秩一 Hermitian 元是本原投影的实倍数，故满足完整秩一前件。目标与输入乘积尺寸相等，没有零填充。定理给符号 $\lambda\in\{-1,1\}$、可逆 $S$ 及两个输入转置。正本原像迫使 $\lambda=1$，其迹一及产品本原投影的实张成使 $S^*S=I$。吸收输出酉共轭，再用整块输出转置同时翻转两输入位，令第一位为零，得到 $F$ 的公式。

保留这组已经固定的 $D$ 坐标，对 $N_{ijk}:H_{n_in_j}\times H_{n_k}\to H_{n_in_jn_k}$ 重复同一精确应用，只改变 $E$ 坐标，得第二式。若恰有一个因子非标量，则该单因子映射为保单位序同构：正性、迹等距和自对偶性使其逆亦正。文献 pp.410–411 Proposition 2.1 给可选整块转置与酉共轭；两因子都为标量时直接为乘法。因而所有标量边界也成立。作用于标量腿的位不可见；作用于唯一非标量腿的位仍可能表示整块转置。允许位冗余，不主张参数最小性或先验共同定向。$\square$

### 66.5 原始权重与整个读回的唯一公式

**定理 66.5（全部原始映射及唯一逆迹平衡）。** 在 (66.13) 的坐标中，存在任意正定 $u_{ij}\in H_{n_j}$、$g_{ijk}\in H_{n_k}$，其权重限制恰为

$$
\boxed{\sum_{i,j}n_i\operatorname{Tr}(u_{ij}^{-1})=n^2.}
\tag{66.14}
$$

定义

$$
\begin{aligned}
&U_{ij}=I_i\otimes u_{ij},\quad
G_{ijk}=I_i\otimes I_j\otimes g_{ijk},\quad V=U^{-1},\\
&A_{ij}=I_i\otimes\sqrt{u_{ij}},\quad
C_{ijk}=I_i\otimes\sqrt{u_{ij}}\otimes\sqrt{g_{ijk}},\quad
W_{ijk}=C_{ijk}^{-1},\\
&(C_Dd)_{ij}=A_{ij}d_{ij}A_{ij},\qquad
(C_Ez)_{ijk}=C_{ijk}z_{ijk}C_{ijk}.
\end{aligned}
\tag{66.15}
$$

则实际准备及三元映射为

$$
\begin{aligned}
M(a,b)_{ij}&=a_i\otimes
 (\sqrt{u_{ij}}b_j^{T^{\varepsilon_{ij}}}\sqrt{u_{ij}}),\\
L(d,c)_{ijk}&=d_{ij}\otimes
 (\sqrt{g_{ijk}}c_k^{T^{\delta_{ijk}}}\sqrt{g_{ijk}}),\\
Q(a,b,c)_{ijk}&=a_i\otimes
 (\sqrt{u_{ij}}b_j^{T^{\varepsilon_{ij}}}\sqrt{u_{ij}})
 \otimes(\sqrt{g_{ijk}}c_k^{T^{\delta_{ijk}}}\sqrt{g_{ijk}}).
\end{aligned}
\tag{66.16}
$$

以 $\operatorname{Tr}_i$ 表示所示块首 Hilbert 因子的普通未归一化偏迹。在整个实 $E$ 上，唯一读回为

$$
\begin{aligned}
(p_0z)_{jk}
 &=\sum_i\left(T_j^{\varepsilon_{ij}}\otimes
 T_k^{\delta_{ijk}\oplus\varepsilon_{jk}}\right)
 (\operatorname{Tr}_i z_{ijk}),\\
(pz)_{jk}
 &=A_{jk}\left[\sum_i\left(T_j^{\varepsilon_{ij}}\otimes
 T_k^{\delta_{ijk}\oplus\varepsilon_{jk}}\right)
 \left(\operatorname{Tr}_i(W_{ijk}z_{ijk}W_{ijk})\right)\right]A_{jk}.
\end{aligned}
\tag{66.17}
$$

全部内部映射，包括原参考的非均匀权重，恰为

$$
\begin{aligned}
(sd)_j&=\sum_i\left[u_{ij}^{-1/2}
 (\operatorname{Tr}_i d_{ij})u_{ij}^{-1/2}\right]^{T^{\varepsilon_{ij}}},\\
\omega_{ij}&=I_{ij}/n^2,&
w_j&=\frac1{n^2}\sum_i n_i(u_{ij}^{-1})^{T^{\varepsilon_{ij}}},\\
\mathcal B(d,c)&=M(sd,c),&K(a)&=M(w,a),\\
J(a)_{ij}&=a_i\otimes u_{ij},&H(d)_{ijk}&=d_{ij}\otimes g_{ijk},\\
B_1&=Js,&(B_1d)_{jk}&=(sd)_j\otimes u_{jk}.
\end{aligned}
\tag{66.18}
$$

所有等式量化全部实输入；$s\ge0$、$w>0$、$\tau_Aw=1$，且不对 $g$ 添加归一化约束。

证明。在这些坐标中 $\alpha(a)_{ij}=a_i\otimes I_j$、$\eta(d)_{ijk}=d_{ij}\otimes I_k$。矩阵 Jordan 算子满足 $[\ell_x,\ell_y]z=[[x,y],z]/4$；环境算子交换迫使矩阵交换子中心，迹零又使它为零。故 $U$ 属于完整第一矩阵代数的交换子，必为 $I_i\otimes u_{ij}$；$G$ 同理为 $I_i\otimes I_j\otimes g_{ijk}$。$\tau_D(U^{-1})=n^2$ 正是 (66.14)。$C_E=C_GP_{\sqrt{\eta(U)}}$ 给 (66.15)，恢复等式消去 $L$ 前两腿上的 $C_D^{-1}$，得到 (66.16)。

$Q_0(a,b,c)_{ijk}=a_i\otimes b_j^{T^{\varepsilon_{ij}}}\otimes c_k^{T^{\delta_{ijk}}}$ 实张满每个完整 $E_{ijk}$，而 $p_0Q_0=\tau_A(a)F(b,c)$ 唯一迫使 (66.17) 第一式。它没有在纠缠方向上的未定延拓。再代入 $p=C_Dp_0C_E^{-1}$ 得第二式；求 $s=\beta^*C_D^{-1}$、$w=s\omega$ 得 (66.18)。逆权重必须先夹乘、再作偏迹后的指定转置；外层 $A_{jk}$ 位于求和和转置之后，无须 $u_{jk}$ 与 $g_{ijk}$ 交换。

为显式核对腿数，对任意完整二腿矩阵 $d_{ij}$，

$$
W_{ijk}L(d,c)_{ijk}W_{ijk}
 =\left[(I_i\otimes u_{ij}^{-1/2})d_{ij}
 (I_i\otimes u_{ij}^{-1/2})\right]\otimes c_k^{T^{\delta_{ijk}}}.
\tag{66.19}
$$

偏迹将第一括号变为 $u_{ij}^{-1/2}(\operatorname{Tr}_id_{ij})u_{ij}^{-1/2}$；末腿的两个转置合成为 $T_k^{\varepsilon_{jk}}$，故 $pL(d,c)=M(sd,c)$。同理 $sM(a,b)=\tau_A(a)b$。权重平衡给 $\tau_Aw=1$，其余内部映射立即恢复。$\square$

### 66.6 无交叉时全锥正性恰好保留哪些方向

**定理 66.6（首腿丢弃的精确正性判据）。** (66.17) 中 $p_0$ 全锥正，当且仅当

$$
\boxed{\delta_{ijk}=\varepsilon_{ij}\oplus\varepsilon_{jk}
 \quad\text{对每个 }i,j,k\text{ 满足 }n_j,n_k\ge2.}
\tag{66.20}
$$

当 $j$ 或 $k$ 为标量时，不由 $p_0$ 强制任何额外位等式。原始 $p$ 全锥正与此完全等价。

证明。对 $r,s\ge2$，$T_r^e\otimes T_s^f$ 正当且仅当 $e=f$：两位都零为恒等，两位都一为整块转置，均正；两位不等时，在两个二维子空间上取 Bell 投影 $q=|\Phi\rangle\langle\Phi|$、$\Phi=(|00\rangle+|11\rangle)/\sqrt2$，单腿转置得到 $q^{T_2}=\mathrm{Swap}/2$，在反对称向量上的特征值为 $-1/2$。$r=1$ 或 $s=1$ 时，剩余转置是恒等或唯一非平凡因子的整块转置，两者均正。

固定源块 $(i,j,k)$，令其余块为零。$\operatorname{Tr}_i$ 满射到整个保留块 PSD 锥：给任意 $x\ge0$，取迹一本原 $q_i$ 并用 $q_i\otimes x$。因此第一式 (66.17) 的该块正性恰为
$T_j^{\varepsilon_{ij}}\otimes T_k^{\delta_{ijk}\oplus\varepsilon_{jk}}$ 正，给出 (66.20)。只激活一个源块使不同 $i$ 的求和不能掩盖负值。反之每个源块映射正则求和正，故充分。无论位如何，偏迹和转置都保迹，所以 $p_0$ 保迹；这不等于原 $p$ 保迹。两端滤波及其逆都是全锥正序同构，给原 $p$ 的等价性。

特别地，当仅一条保留腿非标量时，整块转置仍合法，不能强行补上 (66.20) 的等式。这里没有出现 $\varepsilon_{ik}$；任何有序 $\varepsilon$ 都可在活跃 $j,k$ 上令 $\delta=\varepsilon_{ij}\oplus\varepsilon_{jk}$，其余 $\delta$ 自由选取，再由下述逆向构造实现。无 C13 时不能据此推出端点余循环。$\square$

### 66.7 完整逆向必须从同一个实际读回重算

**定理 66.7（无 C13 原始系统的双向分类）。** 任取有限非空 $I$、整数 $n_i\ge1$、满足 (66.20) 的有序位、满足 (66.14) 的正定 $u_{ij}$ 及任意正定 $g_{ijk}$。在 (66.9) 的完整矩阵直和锥、全部总迹一态及全部效应上，只供应 (66.16) 的 $L$ 和 (66.17) 的 $p$。则定义 66.1 的每条保留条件均成立，并且从原 $\omega=1_D/n^2$ 用同一个 $p$ 两次生成的实际 $M$ 正是 (66.16)。因此 (66.14)、(66.20) 是所述未校准系统的全部参数限制。

证明。先暂把 (66.16) 第一式记为 $\widehat M$，它不是额外供应的准备。对全部实 $d,c,a,b$，(66.19) 及转置抵消直接给

$$
pL(d,c)=\widehat M(sd,c),\qquad
s\widehat M(a,b)=\tau_A(a)b.
\tag{66.21}
$$

用原 $\omega$ 计算 $w=s\omega$，得到 (66.18) 的正定 $w_j$，而 (66.14) 给 $\tau_Aw=1$。于是第一次实际读回给 $K(a)=\widehat M(w,a)$、$sK(a)=a$，第二次使用同一个实际 $p$ 给

$$
M(a,b)=pL(K(a),b)
 =\widehat M(sK(a),b)=\widehat M(a,b).
\tag{66.22}
$$

这验证内部构造，不以一个独立供应的 $M$ 代替它。实际 $J,H,Q,\mathcal B,B_1$ 因而都是 (66.16)、(66.18) 所列映射。

$L$ 在整个 $D_+\times A_+$ 上正：每块是完整正矩阵 $d_{ij}$ 与 $c_k$ 的转置后正合同像的张量积。$d_{ij}$ 可在前两腿任意纠缠。定理 66.6 和两端正序同构证明 $p$ 对整个 $E_+$ 正。Hermitian 简单张量实张成完整 Hermitian 空间；固定输入中心支撑可分别选取每个有序块，转置与正定合同可逆，所以 $M(A,A)$、$L(D,A)$ 分别实张满 $D,E$。此论证不声称每个正元可分离。

对正 $a,b$，每项 $\operatorname{Tr}(a_ib_i)\ge0$，故若原配对之和为零，则各项皆零，从而

$$
\langle Ja,Jb\rangle_D
 =\sum_{i,j}\operatorname{Tr}(a_ib_i)\operatorname{Tr}(u_{ij}^2)=0.
\tag{66.23}
$$

同样，对整个实际 $D_+$ 中任意 $d,d'$，各 $\operatorname{Tr}(d_{ij}d'_{ij})\ge0$；配对为零给

$$
\langle Hd,Hd'\rangle_E
 =\sum_{i,j,k}\operatorname{Tr}(d_{ij}d'_{ij})
 \operatorname{Tr}(g_{ijk}^2)=0.
\tag{66.24}
$$

因此精确 $D_J,D_H$ 均成立，包括全部纠缠二级输入。$B_1=Js$ 及 (66.21) 给全部实输入的

$$
B_1M(a,b)=\tau_A(a)Jb,\qquad
pQ(a,b,c)=\tau_A(a)M(b,c).
\tag{66.25}
$$

最后在三个载体上逐一验证完整有限 $S$。纯态 $q$ 是一个简单块内的迹一本原投影。若 $0\le e\le1$ 且 $\langle e,q\rangle=1$，则 $r=1-e\ge0$ 与 $q$ 正交，处于互补支持面；所以
$r=P_{1-q}r\le P_{1-q}1=1-q$，即 $e\ge q$。取 $e=q$ 达到下界，故

$$
T_q(x)=\langle q,x\rangle,\qquad
T_q\left(\sum_\ell v_\ell q_\ell\right)
 =\sum_\ell v_\ell\langle q,q_\ell\rangle
 =\sum_\ell v_\ell T_{q_\ell}(q).
\tag{66.26}
$$

这包括跨中心扇区的任意有限纯制备，不要求跨扇区强对称性。所有保留条件现已分别检查；前向从实际数据抽取参数，反向又从相同原定义重建实际数据，故无其他隐藏参数条件。$\square$

### 66.8 原状态基与辅助滤波不能混同

**推论 66.8（C13 之前的原始 Born 几何）。** 每个原载体的全部态、效应和实际概率已为

$$
\rho_\lambda\ge0,\quad\sum_\lambda\operatorname{Tr}\rho_\lambda=1,\qquad
0\le e_\lambda\le I_\lambda,\qquad
\Pr(e\mid\rho)=\sum_\lambda\operatorname{Tr}(e_\lambda\rho_\lambda).
\tag{66.27}
$$

$A$ 的块标签为 $i$，$D$ 为全部 $(i,j)$，$E$ 为全部 $(i,j,k)$。$A$ 的纯态空间为 $\coprod_i\mathbb{CP}^{n_i-1}$，同区比较为 $|\langle\psi,\phi\rangle|^2$，异区为零。$D,E$ 的全部纠缠正态都保留。

证明。(66.3) 忠实对应原态基与原全效应，后续只用了保迹 Jordan 坐标，故 (66.9) 给出 (66.27)。$C_D,C_E$ 则是另一种操作：它们用来分解原始映射，一般不保迹，不能将其像当作原总迹一基，亦不因序可逆就取得物理可用性或成本结论。原始权重 $u,g$ 因此不能借“归一化”名称消去。

全标量情形可明确写为 $A=\mathbb R^r$、$D=\mathbb R^{r^2}$、$E=\mathbb R^{r^3}$，$u_{ij},g_{ijk}>0$、$\sum_{i,j}u_{ij}^{-1}=r^2$，并有

$$
M(a,b)_{ij}=a_i u_{ij}b_j,\qquad
L(d,c)_{ijk}=d_{ij}g_{ijk}c_k,\qquad
(pz)_{jk}=u_{jk}\sum_i\frac{z_{ijk}}{u_{ij}g_{ijk}}.
$$

此时方向不可见，C13 自动成立；但权重仍可使原始映射不保单位或不保迹。一般矩阵情形中，$`J^*J`$ 在 $A_i$ 上乘以 $\sum_j\operatorname{Tr}(u_{ij}^2)$，$`H^*H`$ 在 $D_{ij}$ 上乘以 $\sum_k\operatorname{Tr}(g_{ijk}^2)$。所以 $D_J,D_H$ 的零比较保持不等同于固定这些系数的范数校准。

例如辅助系统确实满足

$$
\mathcal B_0(d,c)=p_0N(d,c)=F(\beta^*d,c),\quad
K_0(a)=F(1_A/n,a),\quad
\mathcal B_0(K_0(a),b)=F(a,b),
\tag{66.28}
$$

这是推论 65.7 在同一原 $\omega$ 下的结果；实际系统则使用
$\mathcal B(d,c)=M(sd,c)$、$K(a)=M(w,a)$，一般 $w\ne1_A/n$。两组“同一读回两次”分别成立，不允许彼此替换。$\square$

### 66.9 从实际准备之逆计算 13 插入

**定理 66.9（C13 的精确新增条件与伴随方向）。** $\widetilde M$ 已由上述接口可逆，现在且仅现在定义

$$
T_{\rm raw}(a,c)=L(M(a,1_A),c),\qquad
I_{13}^{\rm raw}=\widetilde T_{\rm raw}\widetilde M^{-1}:D\to E.
$$

令 $\operatorname{ins}_j$ 在端点块 $H_{n_in_k}$ 中插入中间 $I_j$，保持因子顺序为 $i,j,k$。则

$$
\begin{aligned}
(I_{13}^0z)_{ijk}
 &=\operatorname{ins}_j\left[
 (\operatorname{id}_i\otimes T_k^{\delta_{ijk}\oplus\varepsilon_{ik}})z_{ik}\right],\\
I_{13}^{\rm raw}&=C_EI_{13}^0C_D^{-1}:D\to E,\\
(I_{13}^{\rm raw})^*&=C_D^{-1}(I_{13}^0)^*C_E:E\to D.
\end{aligned}
\tag{66.29}
$$

因此原 C13 当且仅当

$$
\boxed{\delta_{ijk}=\varepsilon_{ik}
 \quad\text{当 }n_i,n_k\ge2,\quad\text{对每个 }j\text{，包括 }n_j=1.}
\tag{66.30}
$$

若首尾有一腿标量，则无额外等式。

证明。取 $T_0(a,c)=Q_0(a,1_A,c)$，其 $(i,j,k)$ 块为 $a_i\otimes I_j\otimes c_k^{T^{\delta_{ijk}}}$。实际逆映射满足 $\widetilde M^{-1}=\widetilde F^{-1}C_D^{-1}$；$F_{ik}^{-1}$ 必须先撤去端点第二腿的 $T^{\varepsilon_{ik}}$。故 $I_{13}^0=\widetilde T_0\widetilde F^{-1}$ 正是 (66.29) 的首式，原始恢复给第二式，自伴随滤波给第三式。这里用实际 $F$ 的逆，不能把端点方向预先设为零。

两端滤波是双向全锥正，故 C13 等价于 $I_{13}^0$ 在整个 $D_+$ 上正。非标量端点的单腿转置由 Bell 投影检出负特征值 $-1/2$；插入任何中间 $I_j$ 后，在中间任意单位向量上取期望仍保留负值，故每个 $j$ 都必须满足 (66.30)，标量中间腿没有例外。反向若端点剩余位为零则插入正；若端点有标量腿，剩余操作是恒等或端点整块转置，仍正。独立选择输入块和输出块给逐块必要性。

$I_{13}^01_D=1_E$，故在 C13 下 $p_{13}^0=(I_{13}^0)^*$ 全锥正保迹，且由 $F,N$ 等距及张成有

$$
p_{13}^0Q_0(a,b,c)=\tau_A(b)F(a,c).
\tag{66.31}
$$

但是实际伴随是 (66.29) 第三式，一般不保迹，也没有由 (66.31) 自动得到的原始丢弃恒等式。它与给定 $p$ 是不同对象，且方向与插入相反。例如全标量 $A=D=E=\mathbb R$、$u=1$、$g>0$ 时，原插入及其伴随均为 $g\operatorname{id}$；$g\ne1$ 即非保迹，虽然 C13 成立。$\square$

### 66.10 活跃余循环与含标量的整块坐标变化

**推论 66.10（加回 C13 后的同时方向消除）。** 记 $I_+=\{i:n_i\ge2\}$。条件 (66.20)、(66.30) 共同给出

$$
\varepsilon_{ik}=\varepsilon_{ij}\oplus\varepsilon_{jk}
\quad(i,j,k\in I_+),\qquad
\varepsilon_{ij}=t_i\oplus t_j\quad(i,j\in I_+).
\tag{66.32}
$$

存在兼容全部标量边界的保单位、保迹整块转置坐标，使 $F,N$ 同时为普通产品，$p_0$ 为普通首腿偏迹求和；原始 $u,g$ 仍为正权重。

证明。全部有序三重块存在，故重复标签也可代入余循环，给 $\varepsilon_{ii}=0$、$\varepsilon_{ij}=\varepsilon_{ji}$。若 $I_+\ne\varnothing$，固定 $h\in I_+$，令 $t_i=\varepsilon_{hi}$；对标量扇区取 $t_i=0$。于是得 (66.32)，没有额外的“活跃图断开”情形。若 $I_+=\varnothing$，所有矩阵块均标量，全部位都不可见。

明确令

$$
\ell_{ij}=\begin{cases}
t_i,&n_i\ge2,\\
\varepsilon_{ij}\oplus t_j,&n_i=1, n_j\ge2,\\
0,&n_i=n_j=1,
\end{cases}\qquad
r_{ijk}=\begin{cases}
\ell_{ij},&n_in_j\ge2,\\
\delta_{ijk}\oplus t_k,&n_i=n_j=1, n_k\ge2,\\
0,&n_i=n_j=n_k=1.
\end{cases}
\tag{66.33}
$$

采用整块坐标变化

$$
a'_i=a_i^{T^{t_i}},\qquad
d'_{ij}=d_{ij}^{T^{\ell_{ij}}},\qquad
z'_{ijk}=z_{ijk}^{T^{r_{ijk}}}.
\tag{66.34}
$$

它们都是所在完整简单块的 Jordan 序自同构，保持单位和规范迹。$F$ 的两腿剩余位分别为 $t_i\oplus\ell_{ij}$、$\varepsilon_{ij}\oplus t_j\oplus\ell_{ij}$；每条非标量腿上的位都为零。$N$ 的第一因子非标量时 $r_{ijk}=\ell_{ij}$；若末腿也非标量，须且有

$$
\delta_{ijk}=\ell_{ij}\oplus t_k.
\tag{66.35}
$$

当 $i$ 活跃时，C13 及 (66.32) 直接给它，包括标量 $j$；当 $i$ 标量、$j$ 活跃时，(66.20) 及 (66.32) 给它。若前两腿均标量，(66.33) 的第二分支消去末腿方向；若 $k$ 标量，末腿转置本无作用。故所有混合边界都闭合，得到

$$
F'(a,b)_{ij}=a_i\otimes b_j,\qquad
N'(d,c)_{ijk}=d_{ij}\otimes c_k,\qquad
(p'_0z)_{jk}=\sum_i\operatorname{Tr}_i z_{ijk}.
\tag{66.36}
$$

最后一式由 $Q'_0$ 张成和全实读回恒等式唯一确定。权重变为
$u'_{ij}=u_{ij}^{T^{\ell_{ij}}}$、$g'_{ijk}=g_{ijk}^{T^{r_{ijk}}}$，仍严格正且满足原逆迹平衡；它们不被迫为单位。因此 C13 增加的是这些接合的相对方向相容性，不是原复数状态几何的选择，也不恢复原始校准。$\square$

### 66.11 全部保留条件下的复 qubit 控制

**命题 66.11（全锥正保迹读回仍不能推出 C13）。** 取单扇区

$$
A=H_2(\mathbb C),\quad D=H_4(\mathbb C),\quad E=H_8(\mathbb C),\qquad
u=g=I_2,\quad\varepsilon=1,\quad\delta=0,
$$

以及全部 PSD 锥、总迹一态、效应，定义

$$
L(d,c)=d\otimes c,\qquad p(z)=(\operatorname{Tr}_1z)^T,
\tag{66.37}
$$

其中 $T$ 是保留的两腿合成的 $4\times4$ 块的整体转置。它满足定义 66.1 的所有条件，乃至 $U=1_D$、$G=1_E$、原 $p$ 保迹及 $`J^*J=2\operatorname{id}_A`$、$`H^*H=2\operatorname{id}_D`$，但 C13 失败。

证明。逆迹平衡为 $2\operatorname{Tr}I_2=4$，方向平衡为 $0=1\oplus1$。直接使用同一个 $p$ 得

$$
\begin{aligned}
\omega&=I_4/4,&s(d)&=(\operatorname{Tr}_1d)^T,\\
\mathcal B(d,c)&=(\operatorname{Tr}_1d)^T\otimes c^T,&
K(a)&=(I_2/2)\otimes a^T,\\
M(a,b)&=\mathcal B(K(a),b)=a\otimes b^T,&
Q(a,b,c)&=a\otimes b^T\otimes c,\\
J(a)&=a\otimes I_2,&H(d)&=d\otimes I_2,\\
B_1d&=(\operatorname{Tr}_1d)^T\otimes I_2,&
B_1M(a,b)&=\operatorname{Tr}(a)b\otimes I_2.
\end{aligned}
\tag{66.38}
$$

$p$ 是偏迹后接整块转置，故在整个 $E_+$ 上正且保迹；$L$ 对整个 $D_+\times A_+$ 正。矩阵实张量基证明两条张成；$J,H$ 的配对分别乘以 $2$，故 $D_J,D_H$ 乃至所述校准都成立，$H$ 的计算包含任意纠缠 $d$。最后一式给全实 $Z$；完整有限 $S$ 已由 (66.26) 在三个完整载体上成立。

然而从实际 $M$ 的逆得到

$$
I_{13}^{\rm raw}z=I_{13}^0z
 =\operatorname{ins}_2[(\operatorname{id}\otimes T)z].
\tag{66.39}
$$

对端点 Bell 投影，单腿转置为 $\mathrm{Swap}/2$；取端点反对称向量并在中间取任意单位向量，输出特征值为 $-1/2$。所以插入不正。该模型严格区分原完整 Born 状态几何与接合方向相容性，并显示即使添加这些校准也不能由保留条件推出 C13。$\square$

### 66.12 完整中文候选与保持的条件边界

**推论 66.12（状态几何与接合方向的不同结论）。** 完整候选可以这样表述：在三个非零有限维的实际系统中，保留全部状态和全部效应，用“确定接受一个纯参照时，对另一状态最少会接受多少”定义比较，并要求任意有限随机纯制备后的比较都等于交换端点后逐项比较再平均；采用所引完整比较律到一般 Jordan 几何及忠实归一化的条件纸面桥，只给整个双份正锥上的正接合和整个三份正锥上的同一个正读回，用原比较单位给出的参考连续两次调用这个读回，要求两级结果分别实张满实际载体，两个指定单位切片保持零比较且第二个覆盖全部实际双份正元，并要求形成双份结果后的固定读回在全部实输入上只按第一输入的总权重缩放第二输入的插入方向，那么三个原系统的全部状态、效应和概率已经具有有限复矩阵直和的 Born 几何；所有实际映射恰由上述严格正权重、有序转置位、唯一逆迹平衡及非标量保留两腿的方向条件给出，反过来每组这样的参数都满足所有保留要求；若再要求由实际准备之逆定义的 13 插入在整个双份正锥上为正，恰好进一步排除端点纠缠态上的不相容转置，并允许在兼容标量扇区的整块坐标中同时消除接合方向，原始正权重仍然存在；因此这里区分了原状态几何与接合方向的一致性，没有把静态比较互反解释为实际测量先后次序可交换，也没有完成原有完整兼容组合或物理起源目标。

证明。定理 66.3 在两个前交叉接口上确定载体；命题 66.4 及定理 66.5–66.7 给全部原始映射的双向分类；推论 66.8 保持原状态基；定理 66.9、推论 66.10 给 C13 的精确增量；命题 66.11 给保留全部前件而违反 C13 的模型。

这里的完整有限比较律不能压缩成仅有端点互反。以正方形全态空间 $[-1,1]^2$ 及全部仿射效应为例，不同顶点间最少确认值皆为零，端点表对称。但对 $a=(1,1)$、$b=(1,-1)$、$c=(-1,1)$、$d=(-1,-1)$，中心既是 $(a+d)/2$ 又是 $(b+c)/2$。任何确认 $a$ 的效应在中心至少为 $1/2$，坐标效应达到该值；反向端点表沿后一个制备给平均零，因此不满足完整 $S$。制备一致性是额外信息。

静态互反也不同于时间操作交换。在标准复 qubit 上取 $P=|0\rangle\langle0|$、$R=|+\rangle\langle+|$，有 $\operatorname{Tr}(PR)=\operatorname{Tr}(RP)=1/2$。但选择性分支 $\Phi_P(\rho)=P\rho P$、$\Phi_R(\rho)=R\rho R$ 满足

$$
\Phi_R\Phi_P(P)=\tfrac12R,\qquad
\Phi_P\Phi_R(P)=\tfrac14P.
\tag{66.40}
$$

故实际两次选择性操作及其成功概率都可随顺序不同。

所引单系统 $S$ 桥、前交叉二元接口及扇区论证是明确标条件的仓内纸面推导（repo-derived）；EJA 谱、Peirce、秩维数分类、二次表示和 Xu–Zheng–Fošner 的秩一保持定理为所引已有文献结果（literature-attested），只作为上述新综合推导的中间接口使用。本节的新增综合内容是无 C13 的完整原始权重与方向分类、全锥正性的精确标量边界、同一实际 $p$ 两次的逆向闭合，以及 C13 的精确端点判据和整块坐标检验（repo-derived）。不将 Barnum–Hilgert 的 spectrality 加 strong symmetry 定理直接套到本节较弱前件，也不将 Müller–Ududec 的 bit symmetry 定理冒称完整 $S$ 桥；这些条件性纸面推导均不冒称 Lean 内核验证、文献新颖性或优先性。

定义 66.1 仅从第 65 节删除 C13；第 64 节及 Part III §§62–63 的独立桥、单位配对、保迹等较强原始校准仍按原文适用，辅助滤波不证明它们与本节是相同原始数据的等价公理包。这里没有证明更小的独立或最少公理集，也不从条件条目的数量比较推出公理最小性。

有限复直和仍包含经典与混合扇区，不选择单一非经典扇区；此结论不证明参考、滤波及序坐标具有物理可用性、免费实现或物理等价性。全锥正性不自动供应任意扩张的 CP、仪器、测量更新、动力学、时间、Hamiltonian 或 $\hbar$。本节不识别独立给定的右括号载体，不证明四份、任意多份或无限维一致性，不由实张成推出任意三体态可由两两边缘重建，也不从静态比较导出共同物理历史或三维空间来源。原始完整兼容组合及物理起源目标因此仍未由本节完成。$\square$

## 67. 第二插入的零比较、双迹可行域与共同尺度刚性

### 67.1 同一实际数据上的保留条件

**定义 67.1（不含第二范数律和归一化上界的基底）。** 记 $\mathcal B$ 为以下全部条件。三个实际载体 $X=A,D,E$ 非零、有限维，分别具有闭尖生成正锥、严格正归一化泛函 $u_X$、紧全态基底 $K_X=\{x\in X_+:u_X(x)=1\}$ 和全部对偶效应 $[0,u_X]$。纯态是 $K_X$ 的极点；对全部纯态 $\xi$ 及全部态 $x$，比较仍定义为

$$
T_\xi(x)=\inf\{f(x):0\le f\le u_X,\ f(\xi)=1\}.
$$

每个载体均要求定义 64.1 的完整有限混合律：对每个 $\ell\ge1$、纯态 $\xi,\eta_1,\ldots,\eta_\ell$ 及 $w_j\ge0$、$\sum_jw_j=1$，

$$
T_\xi\!\left(\sum_jw_j\eta_j\right)=\sum_jw_jT_{\eta_j}(\xi).
$$

完整比较入口正是定义 66.1 的 (66.1)–(66.3)；直接复用其中已承接定义 65.1 及 (65.3)–(65.4) 的完整 $S$ 到规范迹 EJA 条件纸面桥和忠实归一化，得到保原归一化的坐标、整个平方锥、所有规范迹一态和全部效应 $[0,1_X]$。原比较配对、原单位、原态及原效应分别对应规范迹内积、$1_X$、全态基及全效应区间；每个简单扇区的每个本原幂等元迹一，不允许调节扇区迹权。这里的 Jordan 入口由所引既有纸面结果供应，不另列独立 Jordan 假设，也不将这条桥计为本节新成果。内积、参考和秩仍为

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
\tag{67.1}
$$

$M$ 内两次使用同一个实际 $p$。要求 $\operatorname{span}_{\mathbb R}M(A,A)=D$、$\operatorname{span}_{\mathbb R}L(D,A)=E$，并保留

$$
\begin{gathered}
\mathrm{(D_J)}\quad a,b\ge0,\ \langle a,b\rangle_A=0
\ \Longrightarrow\ \langle Ja,Jb\rangle_D=0,\\
\mathrm{(Z)}\quad B_1M(a,b)=\tau_A(a)Jb\qquad(a,b\in A).
\end{gathered}
\tag{67.2}
$$

定义 64.3 的全正、实张成、正保迹二元边缘接口及其精确适用条件继续保留；有限 EJA 分类、定理 64.6 所用乘积秩一保持接口也继续保留。它们只在各自输入已经得到以后使用。$\mathcal B$ 不含 $W_H$、归一化上界 $N$、联合校准 $C_{\rm joint}$、$p$ 保迹、第二单位律、Bell 条件或 C13。加入下述 $D_H$ 后，实际数据恰满足定义 66.1 的无 C13 保留条件；这里只使用该定义明列的条件纸面桥和工具，不增加新的物理输入。

相对于基底，另保留第二个二元零关系

$$
\mathrm{(D_H)}\quad d,d'\in D_+,\quad\langle d,d'\rangle_D=0
\ \Longrightarrow\ \langle Hd,Hd'\rangle_E=0.
\tag{67.3}
$$

设 $R=n^3$，并记

$$
Z=H1_D,\qquad Y=p^*1_D,\qquad
\delta=\tau_E(Z),\qquad\gamma=\tau_D(p1_E)=\tau_E(Y).
\tag{67.4}
$$

这里正元 $Z$ 与关系 $\mathrm{(Z)}$ 以字体和类型区分。$\delta$、$\gamma$ 都是原实际映射在原单位参考上的读数。

**引理 67.2（本原零关系的等价测试）。** $D_H$ 等价于只对正交本原幂等元 $q,q'\in D$ 要求 $\langle Hq,Hq'\rangle_E=0$。

**证明。** 必要性直接。反向，把任意 $d,d'\ge0$ 谱分解为 $d=\sum_s a_sq_s$、$d'=\sum_t b_tq'_t$，只保留正系数。自对偶性给出 $\langle q_s,q'_t\rangle\ge0$。若 $\langle d,d'\rangle=0$，则每个 $a_sb_t\langle q_s,q'_t\rangle=0$，故每个出现的本原对正交；假设使其像也零配对，双线性求和即得 $D_H$。此测试遍及实际 $D$ 的所有本原元，并不限于第一接口的乘积本原元；在复矩阵表示中，纠缠秩一方向仍全部包括。$\square$

### 67.2 无范数输入的完整支持面

**命题 67.3（已获无 C13 接口的支持面形式）。** 在 $\mathcal B+D_H$ 下，直接采用命题 66.2 的 $F,N,s$ 及同一实际 $p$ 的恢复接口。存在全锥正 $s:D\to A$、$t=sp:E\to A$，使

$$
\begin{gathered}
m=n^2,\quad V=U^{-1}>0,\quad\tau_D(V)=m,\\
tL(d,a)=\langle V,d\rangle_Da.
\end{gathered}
\tag{67.5}
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
\tag{67.6}
$$

$K_q$ 是序同构，$\Theta_q=P_{z_q^{-1/2}}K_q$ 是到面 $F_q$ 的保单位 Jordan 同构。因此每个 $F_q$ 秩为 $n$；任意完整 $D$ 本原框架的 $P_q$ 两两正交且和为 $1_E$，从而 $R_E=mn=R$。这里没有 $\|z_q\|^2=n$ 的结论。

**证明。** 命题 66.2 在这些前提下直接适用。其全部输入正是这里的完整比较入口、全锥正 $L,p$、同一个 $p$ 两次形成的 $M$、两条实张成、$D_J,D_H$ 和全实 $\mathrm{(Z)}$。将其中 $G,C_G,N$ 分别写为 $Z,C_Z=P_{\sqrt Z},N_Z=C_Z^{-1}L$，已有 $Z>0$、$\eta=C_Z^{-1}H$ 为保单位 Jordan 嵌入、$Z$ 与 $\eta(D)$ 算子交换，以及

$$
V=U^{-1}>0,\quad \tau_DV=m=n^2,\qquad
tL(d,a)=\langle V,d\rangle_Da.
$$

后一个式子也可直接从 (66.8) 的 $pL(d,a)=M(sd,a)$、$sM(b,a)=\tau_A(b)a$ 和 $s^*1_A=U^{-1}$ 读出。对每个实际本原 $q$，命题 66.2 已供应整个本原角的等式与 Jordan 同构

$$
P_q=\eta(q),\qquad E_1(P_q)=N_Z(q,A),\qquad
N_Z(q,-):A\longrightarrow E_1(P_q).
$$

故 $z_q=C_ZP_q$、$K_q=P_{\sqrt{z_q}}N_Z(q,-)$，于是 $K_q(A)=F_q$、$\Theta_q=N_Z(q,-)$；由 $tK_q=v_q\operatorname{id}_A$ 得所示正逆。其已获二次交织给 $P_{P_q}N_Z(d,a)=\langle q,d\rangle_DN_Z(q,a)$；$C_Z$ 与该角压缩交换，立即给 (67.6)。满角、交织和满迹等距均是命题 66.2 的接口，不把正左逆单独当成满射。

Jordan 同构保持继承的规范迹、秩及元素行列式；完整框架经 $\eta$ 的像和为 $1_E$，故每个角秩为 $n$，总秩为 $mn=n^3$。$Hq=C_Z\eta(q)$ 也表明 $H$ 无非零正核。不同角之间仍允许非零 Peirce 半空间，不把这些面误作整个 $E$ 的向量空间直和。这些支持、载体和恢复事实均为第 66 节的既有结果，本节不将其计作新增内容。$\square$

### 67.3 没有范数的循环行列式与双谱

**定理 67.4（两份正谱的总乘积一）。** 在命题 67.3 下，存在完整实际 $D$ 本原框架 $\mathcal Q$，使 $Y_q=\Pi_qY$ 是 $F_q$ 内点，$\ell_q=K_q^*Y$ 是 $A$ 内点，并有

$$
\det_{F_q}(Y_q)=\frac{\det_A(\ell_q)}{\det_{F_q}(z_q)},\qquad
\prod_{q\in\mathcal Q}\det_A(\ell_q)=1.
\tag{67.7}
$$

令 $\zeta_1,\ldots,\zeta_R$ 为各 $z_q$ 的合并本原正谱表，$\eta_1,\ldots,\eta_R$ 为各 $Y_q$ 的合并面内正谱表，则

$$
\prod_{\alpha=1}^R\zeta_\alpha\prod_{\alpha=1}^R\eta_\alpha=1,
\qquad\sum_\alpha\zeta_\alpha=\delta,\qquad
\sum_\alpha\eta_\alpha=\gamma.
\tag{67.8}
$$

**证明。** 直接取定理 66.3 的原始复直和载体、命题 66.4 的有序正规形及定理 66.5 的原始权重公式，不作扇区交换或 C13 假设。写 $A=\bigoplus_iH_{n_i}$、$D=\bigoplus_{i,j}H_{n_in_j}$、$n=\sum_i n_i$，权重为 $u_{ij}>0$，第一接口转置位为 $\varepsilon_{ij}$，第二接口位为 $\delta_{ijk}$。由 (66.16)、(66.18) 的实际 $pL(d,a)=M(sd,a)$ 及其规范迹，任意本原 $q\in D_{ij}$ 满足

$$
(\ell_q)_k=v_q u_{jk}^{T^{\varepsilon_{jk}}},\qquad
v_q=\operatorname{Tr}\!\left(u_{ij}^{-1}\operatorname{Tr}_iq\right)>0.
\tag{67.9}
$$

这里 $sq$ 只在扇区 $j$ 非零，其迹为 $v_q$；对 (66.16) 的 $M(sq,a)$ 取迹即得所示 $\ell_q$，不使用 $H$ 的范数、第二单位律或交叉正性。由 $K_q=P_{\sqrt{z_q}}\Theta_q$、$\Theta_q$ 的迹等距性和 $K_q(A)=F_q$，有

$$
Y_q=P_{z_q^{-1/2}}\Theta_q(\ell_q)>0\quad\hbox{于 }F_q.
$$

因此 $\ell_q$、$Y_q$ 均可逆。通过 $\Theta_q$，每个面已识别为 $A$ 的复矩阵直和；逐块使用 $\det(z^{-1/2}\ell z^{-1/2})=\det(\ell)/\det(z)$，即得 (67.7) 第一式。这是元素的 Jordan 行列式，分母幂次是一，不是二次表示算子的行列式或其维数幂次。

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
\tag{67.10}
$$

第一括号中，每个本征值重复 $n_i$ 次。第二括号中，固定 $j$ 的框架元数为 $\sum_i n_in_j=nn_j$；因此每个有序 $\det(u_{ab})$ 在两括号中的指数恰为 $-nn_a$、$+nn_a$。这里只改名求积的哑指标，没有交换数据 $u_{ij},u_{ji}$。转置不改行列式。定理 64.8 的循环消去由此完整保留，未用任何范数值。

命题 67.3 使两份谱各有 $R$ 项；$Z=\sum_qz_q$ 的谱是第一份合并谱。第二份的迹满足

$$
\sum_q\tau_E(Y_q)=\sum_q\langle P_q,Y\rangle_E
=\langle1_E,Y\rangle_E=\gamma.
$$

结合 (67.7) 即得 (67.8)。两份谱不要求逐项互为倒数，且此时不要求 $Y$ 没有面间 Peirce 分量。$\square$

### 67.4 锐利迹权衡及非负校准余量

**定理 67.5（双迹下界和精确余量）。** 在 $\mathcal B+D_H$ 下，$\delta,\gamma>0$，并有

$$
\delta\gamma\ge R^2,\qquad\delta+\gamma\ge2R,
\qquad\frac\delta c+c\gamma\ge2R\quad(c>0).
\tag{67.11}
$$

置 $\varphi(x)=x-1-\log x$。对定理 67.4 所选谱和任意 $c>0$，有精确非负恒等式

$$
\frac\delta c+c\gamma-2R
=\sum_{\alpha=1}^R\varphi(\zeta_\alpha/c)
 +\sum_{\alpha=1}^R\varphi(c\eta_\alpha).
\tag{67.12}
$$

特别取 $c=1$，这就是 $\delta+\gamma-2R$ 的精确非负谱余量。还成立

$$
\left\|\sqrt{Z/c}-1_E\right\|_2^2
+\sum_{q\in\mathcal Q}
 \left\|\sqrt{cY_q}-P_q\right\|_2^2
\le\frac\delta c+c\gamma-2R.
\tag{67.13}
$$

第二项在相应面内开平方，范数来自固定规范迹。

**证明。** 令 $G=(\prod_\alpha\zeta_\alpha)^{1/R}$。两次普通 AM–GM 与 (67.8) 给出 $\delta\ge RG$、$\gamma\ge R/G$，故乘积至少 $R^2$；再对 $\delta/c,c\gamma$ 用两数 AM–GM 即得其余下界。两份缩放谱的总乘积仍为一，故它们的对数和为零，展开 $\varphi$ 就得到 (67.12)。$\log x\le x-1$ 使每项非负。最后

$$
\varphi(x)-(\sqrt x-1)^2
=2(\sqrt x-1-\log\sqrt x)\ge0.
$$

对两份谱求和即为 (67.13)。取 $c=\sqrt{\delta/\gamma}$ 时右端是 $2(\sqrt{\delta\gamma}-R)$。该估计只控制 $Z$ 及所选 $Y_q$ 的平方根谱偏差；它不控制完整 $Y$ 的面间分量、完整映射的算子范数误差或任何物理资源成本。$\square$

### 67.5 乘积等号的全局共同尺度

**定理 67.6（精确尺度刚性）。** 在 $\mathcal B+D_H$ 下，以下条件等价：

$$
\begin{aligned}
&\delta\gamma=R^2;\\
&\text{存在 }c>0:\ U=1_D,\quad H1_D=c1_E.
\end{aligned}
\tag{67.14}
$$

此时 $c$ 唯一，$c=\delta/R=R/\gamma=\sqrt{\delta/\gamma}$，并强制

$$
\begin{gathered}
p^*1_D=c^{-1}1_E,\qquad\tau_Dp=c^{-1}\tau_E,
\qquad H^*H=c^2n\operatorname{id}_D,\\
hL(d,a)=c^2\tau_A(a)d,\qquad tL(d,a)=\tau_D(d)a,\\
\tau_Dh=c\tau_E,\qquad\tau_At=c^{-1}\tau_E.
\end{gathered}
\tag{67.15}
$$

第一接口完全归一化：$M=F$、完整 I、$W_J$、$r,s$ 全锥正保迹、$r\omega=s\omega=e$ 及完整 III 都成立。派生尺度坐标

$$
L_0=L/c,\quad p_0=cp,\quad H_0=H/c,\quad h_0=h/c,\quad t_0=ct
\tag{67.16}
$$

满足第 64 节全部归一化的探针之前结论；其内部 $B,K,M,J,U$ 与原实际数据逐点相同。反之，任意满足第 64 节归一化探针之前条件的数据，取实际 $L=cL_0,p=c^{-1}p_0$，便得到此等号类。对指定 $c>0$，$\delta/c+c\gamma=2R$ 当且仅当 (67.14) 以此 $c$ 成立。

**证明。** 乘积等号迫使定理 67.5 证明中的两次 AM–GM 分别等号，故每个 $\zeta_\alpha=c$、每个 $\eta_\alpha=c^{-1}$。对所选框架，这给出

$$
z_q=cP_q,\qquad Y_q=c^{-1}P_q,\qquad Z=c1_E.
$$

因而 $K_q=c\Theta_q$，$\ell_q=K_q^*Y_q=1_A$。将此代入 (67.9)，保留定理 66.5 的全部有序权重及命题 66.4 的第一接口转置位，得到

$$
u_{jk}^{T^{\varepsilon_{jk}}}=\lambda_{ij,s}I_{n_k}
\qquad\text{对每个 }i,j,s,k.
\tag{67.17}
$$

固定 $j$ 并任选 $i,s$，出行 $j$ 的全部矩阵均为同一正标量 $a_j$ 乘单位。于是 $u_{ij}=a_iI_{n_j}$，其每个本征值为 $a_i$；代回 (67.17) 得 $a_j=a_i$ 对全部有序 $i,j$ 成立。故 $U=a1_D$。已有的 (66.14)，即 $\tau_D(U^{-1})=m$，强制 $a=1$。这一步消去的是内部权重，不消去外部尺度 $c$；它不止证明中心性，且包括单扇区、标量扇区和 $n=1$。

接着只假定 $U=1_D,Z=c1_E$，给出剩余全局结论，也同时证明反向。现在命题 66.2 中 $C_D=\operatorname{id}$，第一接口为实际 $M=F$，$r=\alpha^*$、$s=\beta^*$；其满迹等距、乘积单位和 (66.8) 给出完整 I、$W_J$、保迹、$r\omega=s\omega=e$ 及完整 III。

必须对任意本原 $q\in D$ 重新使用 $D_H$，而不局限于所选框架。两个正元 $Hq,H(1_D-q)$ 支撑正交且和为 $c1_E$，故 $Hq=cP_q$。命题 67.3 的 $K_q/c$ 现在自身就是保单位 Jordan 同构，保持继承的规范迹。因此

$$
\tau_EL(q,a)=c\tau_A(a),\qquad
\tau_EL(d,a)=c\tau_D(d)\tau_A(a)
\tag{67.18}
$$

对全部本原 $q$ 和全部实 $d,a$ 成立，第二式由本原元实张成而来。另一方面，$pL(d,a)=M(sd,a)$ 及第一接口保迹给出

$$
\tau_DpL(d,a)=\tau_D(d)\tau_A(a).
$$

比较并用实际 $L(D,A)$ 张成整个 $E$，才得到 $\tau_Dp=c^{-1}\tau_E$ 和 $Y=c^{-1}1_E$。仅由所选 $Y_q=c^{-1}P_q$ 不能推出这个全局结论。

再对任意本原 $q$ 使用 (67.6)，有

$$
\begin{aligned}
\langle q,hL(d,a)\rangle_D
&=\langle Hq,L(d,a)\rangle_E\\
&=c\langle P_q,\Pi_qL(d,a)\rangle_E\\
&=c^2\langle q,d\rangle_D\tau_A(a).
\end{aligned}
$$

本原元张成给出 (67.15) 的第二插入公式；取 $a=1_A$ 得 $H^*H=c^2n\operatorname{id}$。$tL$ 由 $V=1_D$ 得到；两个全局迹式分别由 $H1_D=c1_E$ 和 $t=sp$、$s$ 保迹得到。

因此 $(L_0,h_0,t_0)$ 在整个锥上正、两个边缘全局规范保迹，满足全部实方向的两条丢弃律及实际实张成。直接使用命题 66.2 的精确恢复：$U=1_D,Z=c1_E$ 时 $C_D=\operatorname{id}$、$C_E=c\operatorname{id}_E$，其 $N=L_0$、辅助读回为 $p_0=cp$。命题 66.2 直接给出 $F,N$ 的满迹等距、乘积单位和全效应配对。第一接口的 $\widetilde M$ 满等距使 $\widetilde Q_0$ 也满等距；原实际线性化则满足

$$
\widetilde M^*\widetilde M=\operatorname{id},\qquad
\widetilde L^*\widetilde L=c^2\operatorname{id},\qquad
\widetilde Q^*\widetilde Q=c^2\operatorname{id}.
$$

它们均满射。又 $p_0L_0=pL$，所以两次同一个读回产生的内部 $M$ 没有改变。特别是 $H_0^*H_0=n\operatorname{id}$、$p_0$ 保迹及 $\gamma_0=R$，故第 64 节所有探针之前结论均适用。若从 $U=1_D,Z=c1_E$ 出发，(67.18) 和全局读回迹式给出 $\delta=cR,\gamma=R/c$，完成反向。反向缩放构造的正性、张成、内部定义、$D_J,Z,D_H$ 同样逐项保留。最后指定尺度的和等号由 (67.12) 每项为零刻画。式 (67.16) 是尺度分类；原来的实际映射仍明确是 $L=cL_0,p=c^{-1}p_0$，$c\ne1$ 时没有把它们称为已归一化。$\square$

### 67.6 一条共同参考读数与原条件的同数据等价

**定理 67.7（第二范数律和单独上界的精确替换）。** 仍记原第二范数律为 $W_H:H^*H=n\operatorname{id}_D$、原归一化上界为 $N:\gamma\le R$；这里的条件 $N$ 与命题 66.2 的辅助双线性映射按类型区分。在同一 $\mathcal B$ 的实际数据上，

$$
\bigl(W_H\ \&\ N\bigr)
\quad\Longleftrightarrow\quad
\bigl(D_H\ \&\ C_{\rm joint}\bigr),\qquad
C_{\rm joint}:\ \delta+\gamma\le2R.
\tag{67.19}
$$

右侧强制 $\delta=\gamma=R$、$c=1$，故 $U=1_D$、$H1_D=1_E$、$p^*1_D=1_E$ 及定理 64.9 全部结论成立。

**证明。** 新方向由

$$
2R\ge\delta+\gamma\ge2\sqrt{\delta\gamma}\ge2R
$$

迫使全部等号，再用定理 67.6，得到 $c=1$、$W_H$ 及 $N$。反向，$W_H$ 对全部实方向的配对恒等式立即给出 $D_H$。此时可用命题 67.3 和定理 67.4，但尚不使用定理 64.9：对所选完整框架，$W_H$ 给出

$$
\sum_\alpha\zeta_\alpha^2=\sum_{q\in\mathcal Q}\|Hq\|^2=mn=R.
$$

$R$ 项 Cauchy–Schwarz 使 $\delta\le R$，而原 $N$ 给出 $\gamma\le R$，故 $C_{\rm joint}$ 成立。两方向保持同一 $A,D,E,L,p$，不存在换模型或暗中重标度。此等价只在全部保留前提下成立，不是条件独立性、最少公理或完整模型类严格扩大的定理。$\square$

### 67.7 固定简单矩阵载体上的完整双迹可行域

**定理 67.8（锐利双曲可行域的显式实现）。** 固定 $n\ge2$ 和数学载体 $A=H_n$、$D=H_{n^2}$、$E=H_{n^3}$，均取全部矩阵正锥、标准迹、全态和全效应。满足 $\mathcal B+D_H$ 的数据的双迹像恰好是

$$
\{(\delta,\gamma)\in(0,\infty)^2:\delta\gamma\ge n^6\}.
\tag{67.20}
$$

对任意正定 $w\in H_n$，一个实现族为

$$
\begin{aligned}
L_w(d,a)&=d\otimes w^{1/2}aw^{1/2},\\
p_w(X)&=(I_n\otimes w^{-1/2})\operatorname{Tr}_1(X)
             (I_n\otimes w^{-1/2}),
\end{aligned}
\tag{67.21}
$$

其中 $\operatorname{Tr}_1$ 丢弃三份中的第一份。此族满足

$$
\delta=n^2\operatorname{Tr}w,\qquad
\gamma=n^2\operatorname{Tr}w^{-1}.
\tag{67.22}
$$

**证明。** 这个族直接取定理 66.7 的单扇区参数 $n_1=n$、$u_{11}=I_n$、$g_{111}=w$，并取有序位 $\varepsilon_{11}=\delta_{111}=0$；(66.14) 为 $n\operatorname{Tr}I_n=n^2$，(66.20) 也成立。(66.16)–(66.18) 的 $L,p$ 恰为 (67.21)，所以整个实际锥上的正性、两条实张成、同一个 $p_w$ 两次的内部定义、$D_J,D_H,Z$ 和完整比较入口，均直接由该既有无 C13 逆定理供应，包含纠缠方向。取零位还由定理 66.9 的 (66.30) 得到这个实现族的整锥插入正性。该族的分类与存在性不是本节新成果，也不把这个带 C13 的充分实现族用于普遍无 C13 迹下界的证明。为计算新迹读数，直接将 (66.18) 的对应内部映射列为

$$
\begin{aligned}
B_w(d,a)&=(\operatorname{Tr}_1d)\otimes a,\\
K_w(a)&=(I_n/n)\otimes a=e\otimes a,\\
M_w(a,b)&=a\otimes b,\qquad J_w(a)=a\otimes I_n,\\
H_w(d)&=d\otimes w.
\end{aligned}
\tag{67.23}
$$

单位上 $H_w1_D=I_{n^2}\otimes w$、$p_w1_E=nI_n\otimes w^{-1}$，取原规范迹即得新的 (67.22)。正定谱的 Cauchy–Schwarz 给出 $\operatorname{Tr}w\operatorname{Tr}w^{-1}\ge n^2$，等号恰为 $w$ 标量，符合定理 67.6。

为实现任意 $d_0,g_0>0$ 且 $d_0g_0\ge n^6$，令

$$
c=\sqrt{d_0/g_0},\qquad S=\frac{\sqrt{d_0g_0}}{n^2}\ge n,
\qquad t=S-n+2\ge2.
$$

取 $x=(t+\sqrt{t^2-4})/2\ge1$，则 $x+x^{-1}=t$。置

$$
w=c\operatorname{diag}(x,x^{-1},1,\ldots,1).
$$

两迹分别为 $cS,c^{-1}S$，所以 (67.22) 恰为 $\delta=d_0,\gamma=g_0$。这是显式手算恒等式，不依赖搜索或数值枚举。定理 67.5 给出所有允许数据的必要区域，此固定载体族实现整个区域，故 (67.20) 为精确像。$n=1$ 时，第一二元接口及支持面秩使 $A=D=E=\mathbb R$；$U=1$ 和内部定义使实际数据为 $L(d,a)=cda,p(x)=c^{-1}x$，只有 $\delta\gamma=1$ 的边界。经典和一般直和情形仍由前述普遍定理覆盖；这里的满区域实现专指 $n\ge2$ 的固定简单矩阵载体。该族构造数学映射，不构造原始 $\Omega$ 的实际准备或设备。$\square$

### 67.8 必须保留的零关系、尺度和 Bell 控制

**命题 67.9（遗漏控制的精确读数）。** 单独的联合迹校准不能替代 $D_H$；单独的最小迹乘积不能固定实际插入尺度；二者归一化后仍不能删除定理 64.10 的独立整输出 Bell 条件。

**证明。** 第一项复用 (62.44)–(62.46) 的经典例。取 $A=\mathbb R^2,D=\mathbb R^4,E=\mathbb R^8$，$P=\left(\begin{smallmatrix}3/4&1/4\\1/4&3/4\end{smallmatrix}\right)$，$L(d,a)=((P\otimes\operatorname{id})d)\otimes a$、$p=\operatorname{Tr}_1$。原例已经给出全锥正性、两条张成、同一个 $p$ 的内部普通张量 $M$、$D_J,Z$ 及全锥交叉插入正性。$P1=1$ 且 $p$ 保迹，故 $Z=1_E$、$\delta=\gamma=8$，正好满足联合校准。可是对任意坐标本原 $e_j\in\mathbb R^2$，两个正交本原元 $q=e_0\otimes e_j$、$q'=e_1\otimes e_j$ 的像满足

$$
\langle Hq,Hq'\rangle
=\left(\frac34\frac14+\frac14\frac34\right)\langle e_j,e_j\rangle
 \langle1_2,1_2\rangle=\frac34>0.
\tag{67.24}
$$

所以 $D_H$ 失败。原 $P^{\mathsf T}P$ 的非零交叉项也使 $W_H$ 和完整 II 失败。这是已有控制的新零关系读数，不重复计作新的模型构造。

第二项可取 (67.21) 的 $w=\lambda I_n$，或任意标准直和张量数据的全局尺度族 $L=\lambda L_{\rm tens}$、$p=\lambda^{-1}p_{\rm tr}$，$\lambda>0$。两次内部读回仍产生相同 $M$，$D_H$ 保持，而

$$
\delta=\lambda R,\quad\gamma=R/\lambda,\quad
\delta\gamma=R^2,\quad
\delta+\gamma=R(\lambda+\lambda^{-1}),\quad
H^*H=\lambda^2n\operatorname{id}.
\tag{67.25}
$$

因此 $W_H$ 当且仅当 $\lambda=1$；$\lambda>1$ 时甚至仍满足旧 $N$，却未固定实际尺度。迹和的最小值恰好排除这一个自由度。

第三项直接复用命题 66.11 的复 qubit 全锥正保迹转置控制：它满足旧 $W_H,N$，故由定理 67.7 满足新 $D_H,C_{\rm joint}$，但 (66.39) 在端点 Bell 投影的整个插入输出上仍有负本征值 $-1/2$。定理 64.11 的有序跨扇区和标量中间旁观者控制同样保留。零关系及迹校准只恢复探针之前的接口，没有免除交叉插入的独立条件。$\square$

### 67.9 完整静态候选与同数据复量子对应

**定义 67.10（双零关系与联合参考校准的完整候选）。** 完整输入是定义 67.1 的每一项：三个实际有限全态全效应比较入口及完整有限混合 $S$，其原比较单位、全态全效应及规范迹 Jordan 几何由既有 §66.1 的忠实条件纸面桥供应，不重复增加独立 Jordan 输入；全锥正的实际 $L,p$；同一个 $p$ 两次内部定义的 $M$；$M,L$ 两条实际实张成；全部量词下的 $D_J,\mathrm{(Z)}$。增加 $D_H,C_{\rm joint}$，保留定义 64.3 的二元纸面接口、有限 Jordan 分类和乘积秩一保持工具。命题 66.2、定理 66.3 及推论 66.8 已在校准与 C13 之前供应两个辅助接口和原始 Born 状态几何；定理 67.7 使这两个接口就是同一实际数据的归一化接口。随后按第 64 节 3.3 的规则预选实际正迹一 $\sigma_*$，最后只增加一个条件

$$
I_{13}(\sigma_*)\in E_+,\qquad
I_{13}=\mathcal T\widetilde M^{-1},\qquad
\mathcal T(a\otimes c)=Q(a,1_A,c).
\tag{67.26}
$$

该预选规则使用 $M$ 的允许初始正规形及每个有序非标量端点对的两维 Bell 投影，等权直和；没有活跃端点对时用 $1_D/m$。选取不读取 $Q,I_{13}$ 或测试输出。要求的是整个 $E$ 输出为正，覆盖每个中间扇区，包括标量旁观者；它不是一次标量概率条件，也不附赠实际制备该探针的能力。

**定理 67.11（同数据等价、唯一读回及静态量子几何）。** 定义 67.10 的完整候选与定理 64.12 的完整候选在完全相同的实际 $A,D,E,L,p$ 上等价。它推出全部定理 64.9–64.13 的结论，特别是完整 I、II、III、全局 $p$ 保迹、整锥 $I_{13}$ 正性和唯一正保迹读回

$$
p_{13}=I_{13}^*,\qquad
p_{13}Q(a,b,c)=\tau_A(b)M(a,c)\quad(a,b,c\in A).
\tag{67.27}
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
\tag{67.28}
$$

全态、全效应与配对为 $\rho_i\ge0$、$\sum_i\operatorname{Tr}\rho_i=1$、$0\le f_i\le I_{n_i}$ 和 $\Pr(f\mid\rho)=\sum_i\operatorname{Tr}(f_i\rho_i)$。纯态空间为 $\coprod_i\mathbb{CP}^{n_i-1}$，同扇区最小确认比较是平方重叠、异扇区为零；单一 $n_i=2$ 扇区的全态为 Bloch 球。这里 $\mathbb{CP}^{n_i-1}$ 表示复射影空间，不是操作的完全正性假设。

**证明。** §66.1 的忠实条件纸面桥在完全相同的完整比较入口上供应旧候选所列的保归一化 Jordan 桥，故这里删除重复输入不改变其条件适用域。定理 66.3 和推论 66.8 已在 C13 及联合校准之前给出上述原始复直和全态几何；本定理不把这一已获结论计作迹校准的新作用。定理 67.7 首先给出旧 $W_H,N$ 和定理 64.9，完全不使用 (67.26)。故 $\widetilde M$ 可逆、两个二元接口和 $Q$ 满等距已经成立，定理 64.10 的完整前提此时才齐备。其精确块公式 (64.32)、方向 $U_{ik}^*\beta_{ik}U_{ik}=b_{ik}$ 及每个有序输出块的 Bell 负本征值，证明 (67.26) 等价于整个 $D_+$ 上的插入正性；没有把一次输出的某个迹代替全算子正性。

由于 $I_{13}1_D=1_E$，自对偶性给出其伴随正保迹。$Q$ 等距给出

$$
\langle M(x,y),I_{13}^*Q(a,b,c)\rangle_D
=\tau_A(b)\langle x,a\rangle_A\langle y,c\rangle_A.
$$

$M$ 张成得到 (67.27)，$Q$ 张成使满足该读回律的实线性映射唯一。对同一实际 $M,L$，定理 66.9 的 (66.29)–(66.30) 直接给出交叉插入及伴随的准确方向；此时 $C_D=C_E=\operatorname{id}$，其辅助对象就是原实际对象。全锥读回的 (66.20) 与 Bell 条件所得的 (66.30) 合用，直接由推论 66.10 在含重复标签和全部标量位置的整块保迹 Jordan 坐标中同时 untwist，得到 (67.28)。原全态全效应和 Born 配对仍是推论 66.8 的几何；定理 64.12–64.13 的静态消费者结论因而全部接回。逆向，旧完整候选的 $W_H,N$ 给出新 $D_H,C_{\rm joint}$，其 $M$ 及预选探针规则逐点不变。标准直和矩阵数据满足两个完整候选，包括全标量经典扇区和 $A=\mathbb R$。故这是同实际数据的双向等价。$\square$

**推论 67.12（乘积边界上的带尺度对应）。** 若只用 $\delta\gamma=R^2$ 代替 $C_{\rm joint}$，再要求同一预选 Bell 输出正，则定理 67.6 的 $L_0,p_0$ 满足完整归一化候选。在相同固定矩阵坐标中，原实际 $M$ 仍为普通张量，而原实际 $L=cL_{\rm tens}$、$p=c^{-1}p_{\rm tr}$。此时 $I_{13}=cI_{13,0}$，正尺度使 Bell 条件与归一化条件等价。若要求实际缩放 $Q=cQ_0$ 的读回仍满足 (67.27) 的右端，唯一读回为

$$
p_{13}^{(c)}=c^{-1}I_{13,0}^*=c^{-2}I_{13}^*;
$$

它的迹尺度是 $c^{-1}$，只有 $c=1$ 时才是规范保迹读回。

**证明。** $p_0L_0=pL$ 保持内部 $M$，因此探针的预选不变，$Q=cQ_0$ 使交叉插入乘以 $c$。应用定理 67.11 于归一化数据，再缩放读回律，得到所示公式；唯一性仍来自实际 $Q$ 张成。此处没有把未校准的实际 $I_{13}^*$ 错当成原读回。$\square$

### 67.10 几何解释、来源与原始来源边界

**几何解释。** 零比较只问原来互不重叠的两个正方向，插入后是否仍互不重叠，并不规定它们的长度。命题 66.2 的已有无 C13 支持接口说明：正读回保证任何非零正方向不会被插入抹掉，实际张成保证每个本原方向承载一个完整的 $A$ 支持面，所有支持单位铺满环境单位。面之间仍可有量子相干的 Peirce 半空间，不能把这幅图理解为整个系统被拆成互不相干的经典格子。一般正滤波并不只是共同尺度；本节的乘积等号才强制 $U=1_D$、$H1_D=c1_E$。

循环内部定义使插入谱和读回压缩谱的总乘积为一。一边缩小，另一边必须补偿；方向之间不均匀还会增加迹的代价。双迹的普遍下界因而是一条双曲线；在定理 67.8 固定的简单矩阵载体且 $n\ge2$ 时，显式矩阵权重实现线上及线上方的每个点，$n=1$ 则只有边界。双曲线边界上，所有方向只能共享一个尺度；联合迹和的最小值才把这个尺度固定为一。原始复 Born 全态几何在此之前已经成立；固定尺度之后，一个预选 Bell 合成态的整个输出正性继续负责排除相对转置错误，普通张量接合及其静态读回才完整接回。

**来源与归属。** 有限 EJA 的谱分解、自对偶、支撑及二次表示，保单位序同构的 Jordan 性、规范迹和元素行列式，复矩阵分类、乘积秩一保持以及 AM–GM、Cauchy–Schwarz、$\log x\le x-1$ 都是成熟工具。所用 EJA 与分类文献和精确接口见定义 64.3、定理 64.6、64.13 的原始出处链接。循环行列式及预选整输出 Bell 规则复用第 64 节；经典模糊控制来自 (62.44)–(62.46)。完整有限 $S$、规范迹 EJA 及原单位、态、效应的忠实对应直接复用 §66.1 及其已引 §65.1、Library 条件纸面来源。前交叉 $F,N$、全支持角、张成与同一实际 $p$ 的恢复直接复用命题 66.2；原始复载体、两个有序正规形及原始 $u,g$ 公式分别复用定理 66.3、命题 66.4、定理 66.5；全锥方向限制及完整同数据逆向复用定理 66.6–66.7。原始 Born 全态几何已由推论 66.8 在 C13 之前取得；交叉插入和伴随的精确方向及同时 untwist 直接复用定理 66.9、推论 66.10；校准不能推出 C13 的控制复用命题 66.11。第 65 节较强的含 C13 结果保持其原范围。这些已获接口、原始分类、逆向及单扇区 $w$ 实现族均不计作本节新成果。本节新增仓内综合内容是锐利双迹权衡及精确谱余量、全局共同尺度等号分类、同数据联合校准替换与固定矩阵载体的完整双迹像；不作全球新颖性、优先权、Lean 或完整量子起源声明。

**范围。** 本节是纸面条件定理，不含 Lean 形式核验。没有从原始 $\Omega$ 定义推出 $D_H$、$C_{\rm joint}$ 或探针的实际可获得性，也没有以条件名称变短证明原始来源上的实现更容易。所有原始对象、准备、事件、过程、参考、副本及相关联合，零质量和不等质量，时钟、单位、控制、ready 与 flags，全部记录、失败、停止、破坏、返回及未来，以及既有全菜单、固定支持和每个已量化中间切割义务，均按原有域保留；本节不结算其中尚未结清的义务。实际 acceptance 23.7 与 active Return 164 的原始连接仍未在此构造；不能从矩阵实现推断它们已成立。

数学上的单位、规范迹、二次表示、$w$、坐标、Bell 态和读回尺度，不附赠实际准备、相干控制、复制、参考或设备；没有用 Born 或完全正性循环定义原始输入。静态 Born 配对不推出任意独立操作的完全正性、参考扩张、仪器、Kraus 实现或态更新，也不推出过程误差、动力学、Hamiltonian、时钟或 $\hbar$。未构造新的原始 analyzer/menu/source incidence，未识别独立给定的右载体，未增加高份数、无限维或完整量子起源结论。此前来源及过程成果保持其各自已述适用域，不能由这里的归一化和可行域扩大其范围。

## 追加锚（本行以下为增补区）

## 68. 未校准全滤波类的单态等价与固定一态的量词障碍

本章在同一原始模型上，把定义 65.2 的整锥交叉插入条件换成一个预选原态的完整输出正性。预选态依赖实际 $M$，保留第 65 节全部正滤波自由度。随后在固定的 $H_2,H_4,H_8$ 上证明：每个事先固定的双份态，都能被某个满足其余全部条件、却不满足整锥插入正性的模型放行。这两个结论分别具有“每个模型先选态”和“每个固定态存在坏模型”的量词，彼此相容。

证明只复用已经发表的定义 64.1–64.3、定理 64.6、64.9–64.10 及定义 65.1、定理 65.3–65.11、推论 65.12。这里的编号均指带编号的定义、定理或推论，不以其所在小节号代替。本章不使用第 66 节，也不重新主张 $S$ 到规范 EJA 或完整未校准分类。

### 68.1 完整保留的前置系统与实际内部对象

**定义 68.1（PRE）。** 对每个 $X=A,D,E$，给定非零有限维实向量空间、闭尖生成锥 $C_X$、在 $C_X\setminus\{0\}$ 上严格正的线性泛函 $u_X$。态集和效应集分别是完整的

$$
K_X=\{x\in C_X:u_X(x)=1\},\qquad [0,u_X],
\qquad P_X=\operatorname{ext}K_X.
$$

要求 $K_X$ 紧。对每个纯参照 $\xi\in P_X$ 和每个 $x\in K_X$，定义

$$
T^X_\xi(x)=\inf\{f(x):0\le f\le u_X,\ f(\xi)=1\}.
$$

三个载体各自满足完整有限混合律：对所有整数 $\ell\ge1$、所有纯态 $\xi,\eta_1,\ldots,\eta_\ell$ 和所有 $w_j\ge0$、$\sum_jw_j=1$，

$$
T^X_\xi\left(\sum_jw_j\eta_j\right)
 =\sum_jw_jT^X_{\eta_j}(\xi).
\tag{68.1}
$$

沿用定义 65.1 明确引用的完整 $S$ 纸面定理，得到忠实的规范迹 EJA 坐标 $\Phi_X$。它们满足

$$
\tau_X\Phi_X=u_X,\qquad
B_X(x,y)=\tau_X(\Phi_Xx\circ\Phi_Xy),\qquad
\Phi_XU_X=1_X.
\tag{68.2}
$$

这里 $B_X$ 是该定理导出的比较配对，$B_X(U_X,-)=u_X$；每个简单扇区的本原幂等元规范迹为一。$\Phi_X$ 双射整个原锥与原态基到规范锥与规范迹一基，$f\mapsto f\Phi_X^{-1}$ 双射全部原效应到规范效应区间，保留全部效应概率。以下就在这些忠实坐标中写 $X_+$、$\tau_X$、$1_X$ 及 $\langle x,y\rangle_X=\tau_X(x\circ y)$；所有线性映射伴随均取这些规范迹内积。这一步是对定义 65.1 的复用，未增加独立 Jordan 桥或扇区迹重标度。

唯一原始映射是实双线性 $L:D\times A\to E$ 和实线性 $p:E\to D$。要求

$$
L(d,c)\in E_+\quad(d\in D_+,\ c\in A_+),\qquad
p(z)\in D_+\quad(z\in E_+).
\tag{68.3}
$$

这些量词覆盖完整实际锥，包括矩阵表示中的全部纠缠正元。令

$$
\begin{gathered}
n=\tau_A1_A,\qquad m=\tau_D1_D,\qquad
e=1_A/n,\qquad\omega=1_D/m,\\
\mathcal B(d,c)=pL(d,c),\qquad K(a)=\mathcal B(\omega,a),\\
M(a,b)=\mathcal B(K(a),b)=pL\bigl(pL(\omega,a),b\bigr),\\
J(a)=M(a,1_A),\quad H(d)=L(d,1_A),\quad B_1=pH,\\
Q(a,b,c)=L(M(a,b),c),\qquad U=M(1_A,1_A).
\end{gathered}
\tag{68.4}
$$

两次 $p$ 是同一个原始读回，$\omega$ 始终由原比较单位给出；$J,H$ 插入未归一化单位。再要求

$$
\operatorname{span}_{\mathbb R}M(A,A)=D,\qquad
\operatorname{span}_{\mathbb R}L(D,A)=E,
\tag{68.5}
$$

以及下列完整量词的关系：

$$
\begin{aligned}
D_J:\quad &a,b\in A_+,\ \langle a,b\rangle_A=0
 \ \Longrightarrow\ \langle Ja,Jb\rangle_D=0,\\
D_H:\quad &d,d'\in D_+,\ \langle d,d'\rangle_D=0
 \ \Longrightarrow\ \langle Hd,Hd'\rangle_E=0,\\
Z:\quad &B_1M(a,b)=\tau_A(a)Jb\qquad(a,b\in A).
\end{aligned}
\tag{68.6}
$$

以上恰为定义 65.1–65.2 除 C13 外的全部条件，统称 PRE。两条实张成不要求全正锥由正乘积生成。PRE 不含原 $p$ 保迹、原 $M,H$ 保单位、原 $W_H$ 或总标定上界。

对双线性映射加波浪号表示其在实张量积上的线性化；此处不预设张量正锥。定理 65.3 在 PRE 下已保证 $\widetilde M$ 可逆，故可定义同一个实际交叉插入

$$
T(a,c)=L(Ja,c),\qquad
I_{13}^{\mathrm{raw}}=\widetilde T\widetilde M^{-1}:D\longrightarrow E.
\tag{68.7}
$$

旧条件仍记为 $\mathrm{C13}: I_{13}^{\mathrm{raw}}(D_+)\subseteq E_+$。下面给出它的单态替代，所有辅助映射和探针均为导出对象。

### 68.2 使用定理 64.10 之前的完整对接

**引理 68.2（PRE 的辅助系统）。** 在 PRE 下，不使用 C13，令 $\ell_x(y)=x\circ y$、$P_x=2\ell_x^2-\ell_{x^2}$，并定义

$$
\begin{gathered}
C_D=P_{\sqrt U},\quad F=C_D^{-1}M,\quad
\alpha=F(-,1_A),\quad\beta=F(1_A,-),\\
G=H1_D,\quad C_G=P_{\sqrt G},\quad
\eta=C_G^{-1}H,\quad N=C_G^{-1}L,\quad\zeta=N(1_D,-),\\
C_E=C_GP_{\sqrt{\eta(U)}},\quad
Q_0(a,b,c)=N(F(a,b),c),\quad p_0=C_D^{-1}pC_E.
\end{gathered}
\tag{68.8}
$$

则在同一个 $A,D,E$、同一规范迹、同一 $\omega$ 上，以 $L_{\mathrm{aux}}=N$、$p_{\mathrm{aux}}=p_0$ 代入，得到满足定理 64.10 全部测试前提的辅助系统。特别地，用同一个 $p_0$ 两次按原定义算出的第一准备恰为 $F$。

**证明。** 先记录定理 65.3–65.6 在 C13 之前给出的数据。$U,G$ 为正可逆元；$C_D,C_E$ 是自伴随锥自同构，逆也全锥正。$G$ 与 $\eta(D)$ 算子交换，故 $C_G$ 与 $P_{\sqrt{\eta(U)}}$ 交换，这保证 (68.8) 中 $C_E$ 的上述性质。两个线性化 $\widetilde F,\widetilde N$ 都是满规范迹等距，$m=n^2$、$\tau_E1_E=n^3$，且

$$
\begin{gathered}
F(1_A,1_A)=1_D,\qquad N(1_D,1_A)=1_E,\\
\alpha^*F(a,b)=\tau_A(b)a,\qquad
\beta^*F(a,b)=\tau_A(a)b,\\
\eta^*N(d,c)=\tau_A(c)d,\qquad
\zeta^*N(d,c)=\tau_D(d)c.
\end{gathered}
\tag{68.9}
$$

四个伴随边缘全锥正、全局保迹。两个接口均保持本原乘积，$\alpha,\beta,\eta,\zeta$ 是保单位 Jordan 单射；同一接口的两个像在整个输出上算子交换。另有全部实输入的

$$
\begin{aligned}
M&=C_DF,& L(d,c)&=C_EN(C_D^{-1}d,c),\\
Q&=C_EQ_0,&p&=C_Dp_0C_E^{-1},\\
p_0Q_0(a,b,c)&=\tau_A(a)F(b,c).
\end{aligned}
\tag{68.10}
$$

$N$ 全正且实张成 $E$，$p_0$ 在整个 $E_+$ 上正。为说明其保迹并未循环使用交叉插入，$\widetilde Q_0=\widetilde N(\widetilde F\otimes\mathrm{id}_A)$ 是满等距且把三个单位送到 $1_E$，所以

$$
\tau_EQ_0(a,b,c)=\tau_A(a)\tau_A(b)\tau_A(c)
 =\tau_Dp_0Q_0(a,b,c).
$$

$Q_0$ 实张成 $E$，于是 $\tau_Dp_0=\tau_E$ 在整个 $E$ 上成立。以上只使用定理 65.3–65.6。

逐项对接旧定理还须保留内部定义，不能直接把 $F$ 宣告成辅助准备。令

$$
\mathcal B_0=p_0N,\qquad K_0(a)=\mathcal B_0(\omega,a),\qquad
M_0(a,b)=\mathcal B_0(K_0(a),b).
$$

由 (68.9)–(68.10) 及 $F$ 实张成，

$$
\mathcal B_0(d,c)=F(\beta^*d,c).
$$

$\beta^*1_D=n1_A$，$m=n^2$，故

$$
K_0(a)=F(1_A/n,a),\qquad
\beta^*K_0(a)=a,\qquad M_0(a,b)=F(a,b).
\tag{68.11}
$$

这也重述并核对了推论 65.7 的同一 $p_0$、同一原参考结论。由此旧系统的内部对象逐一是

$$
\begin{gathered}
J_0=\alpha,\quad H_0=\eta,\quad U_0=1_D,\quad
Q_{\mathrm{aux}}=Q_0,\quad B_{1,0}=p_0\eta,\\
r_0=J_0^*=\alpha^*,\quad s_0=\beta^*,\quad
h_0=H_0^*=\eta^*,\quad t_0=\zeta^*=\beta^*p_0.
\end{gathered}
\tag{68.12}
$$

最后一个等式可在全部 $N(d,c)$ 上由 (68.9)、$\mathcal B_0=F(\beta^*-, -)$ 验证，再由张成延拓。

现在检查定义 64.1–64.3 及定理 64.9–64.10 的各项输入和所用结论。

* 全态、全效应、完整 $S$ 和每本原迹一的规范 EJA 几何，由 (68.1)–(68.2) 及定义 65.1 供应。旧定义 64.1 所需的 EJA 数据因而已经存在，无须再加一条独立桥。
* 原始类型与全锥正性正确：$N:D\times A\to E$ 全正，$p_0:E\to D$ 全锥正；$F=C_D^{-1}M$ 实张成 $D$，$N=C_G^{-1}L$ 实张成 $E$。滤波可逆，故输入域仍是整个实际锥。
* 同一个辅助读回两次及原 $\omega$ 已由 (68.11) 检查。$e,\omega$ 未变，且 $r_0\omega=s_0\omega=e$。
* $\alpha^*\alpha=n\mathrm{id}_A$，$\eta^*\eta=n\mathrm{id}_D$，分别来自两个满迹等距。因此辅助 $D_J,D_H$ 以及旧 $W_J,W_H$ 全部成立，后者是在整个实空间上的等式。这里没有给原 $J,H$ 加上范数律。
* 对全部实 $a,b,c$，有 $p_0N(F(a,b),c)=\tau_A(a)F(b,c)$；取 $c=1_A$ 就是 $B_{1,0}F(a,b)=\tau_A(a)J_0b$。故旧 $Z$ 及完整 III 成立。
* 旧总标定条件 $\mathrm{(N)}$ 的标量是 $\gamma_0=\tau_D(p_01_E)=\tau_E1_E=n^3$，恰满足其上界。此 $\mathrm{(N)}$ 与映射 $N$ 不是同一个对象，等式只约束辅助系统。
* 旧完整 I、II、两个接口的单位、正保迹边缘及全部实方向的丢弃律，正是 (68.9)–(68.12)；$\widetilde F,\widetilde N,\widetilde Q_0$ 的满等距也已建立。尚未要求 $p_{13}^0$ 正。

所以旧定理的测试前提齐备。此处只使用定理 64.6 的早期扇区结论和 (64.27)–(64.29) 的独立初始正规形；不用定理 65.9 的同时消转置坐标。$\square$

### 68.3 只按实际第一接口预选原态

**定义 68.3（合格规约及滤波探针）。** 在测试之前，固定只使用 $A,D$ 的比较几何、标签、基及实际 $M$ 的坐标规约。先由 $M$ 取 $U$、$C_D$ 和 $F$。由定理 64.6 的早期结论，可以在 $A,D$ 选择保迹 Jordan 序坐标

$$
A=\bigoplus_{i\in\Lambda}H_{n_i},\qquad
D=\bigoplus_{(i,k)\in\Lambda^2}H_{n_in_k},\qquad
D_{ik}=\operatorname{span}F(A_i,A_k),
\tag{68.13}
$$

其中 $H_q=\operatorname{Herm}_q(\mathbb C)$，$n_i\ge1$，$\Lambda$ 有限非空，$n=\sum_i n_i$。相同维数的不同中心标签仍分开。记初始坐标为 $\theta_A^0,\theta_D^0$。仅用 $F$ 的系数选择每块的酉 $V_{ik}$ 和位 $\varepsilon_{ik},\delta_{ik}\in\{0,1\}$，使

$$
F(a,c)_{ik}=V_{ik}
 \bigl(a_i^{T^{\varepsilon_{ik}}}\otimes
 c_k^{T^{\delta_{ik}}}\bigr)V_{ik}^*.
\tag{68.14}
$$

$T^0$ 为恒等、$T^1$ 为固定基下的整个转置；$V_{ik}$ 不与实际单位输出 $U$ 混淆。(68.14) 是把旧 (64.28) 用于 $M_0=F$，并非测试后得到的同时正规形。

允许任意事先固定的合格选择。如需单值，先固定标签与矩阵元顺序，按 $(00,01,10,11)$ 取首个非空酉解集的位对，再依顺序逐项最小化矩阵元的实部、虚部。有限基乘积上的等式足以规定解集；它是酉群中的非空闭紧集，逐项极小化后仍非空紧，最终确定全部矩阵元。这只规定数学选择，不承诺其算法复杂度或物理实现。

令 $\mathcal P=\{(i,k):n_i,n_k\ge2\}$、$r=|\mathcal P|$。对每个有序 $(i,k)\in\mathcal P$，在固定基的前两维取

$$
v_{ik}=\frac{|0_i0_k\rangle+|1_i1_k\rangle}{\sqrt2},\qquad
b_{ik}=v_{ik}v_{ik}^*,\qquad
\beta_{ik}=(\theta_D^0|_{D_{ik}})^{-1}
 \bigl(V_{ik}b_{ik}V_{ik}^*\bigr),
$$

其中 $\beta_{ik}$ 在其他中心块为零。定义

$$
\sigma_*(F)=
\begin{cases}
\displaystyle\frac1r\sum_{(i,k)\in\mathcal P}\beta_{ik},&r>0,\\
1_D/m,&r=0,
\end{cases}
\qquad
h_*:=\tau_D(C_D\sigma_*),\qquad
\rho_*:=\frac{C_D\sigma_*}{h_*}.
\tag{68.15}
$$

每个 $\beta_{ik}$ 是正迹一元，故 $\sigma_*\ge0$、$\tau_D\sigma_*=1$。又 $C_D1_D=U$ 且 $C_D$ 自伴随，所以

$$
h_*=\langle U,\sigma_*\rangle_D>0.
\tag{68.16}
$$

严格性可直接由 $U\ge\epsilon1_D$、$\epsilon>0$ 得 $h_*\ge\epsilon$。因此 $\rho_*\in D_+$、$\tau_D\rho_*=1$；它可以在锥边界。原坐标中的态是 $\Phi_D^{-1}\rho_*$，其原归一化 $u_D$ 恰为一。

整个规则只读 $A,D$ 的原比较几何、预选规约和实际 $M$；没有读取 $E,N,Q_0,I_{13}^0,I_{13}^{\mathrm{raw}}$ 或测试结果。后面的 $E$ 初始坐标仅用于证明。不同合格规约可以给出不同的态，定理对每个这样的规约分别成立。

### 68.4 一份原态等价于整个 C13

**定理 68.4（未校准的单态等价）。** 对每个 PRE 模型及每个定义 68.3 的合格预选规约，

$$
\boxed{
I_{13}^{\mathrm{raw}}(\rho_*)\in E_+
\quad\Longleftrightarrow\quad
I_{13}^{\mathrm{raw}}(D_+)\subseteq E_+.
}
\tag{68.17}
$$

两边指向同一个原始 $L,p$、同一个原参考和同一个实际插入。左边记为 $\mathrm{P}_*$；它要求一个输入的完整输出正性，不要求输出迹一。

**证明。** 在 PRE 下先定义

$$
T_0(a,c)=N(F(a,1_A),c),\qquad
I_{13}^0=\widetilde T_0\widetilde F^{-1}.
$$

由 (68.10)，$T=C_ET_0$、$\widetilde M=C_D\widetilde F$。因此不论插入是否正，都有定理 65.8 的代数等式

$$
I_{13}^{\mathrm{raw}}=C_EI_{13}^0C_D^{-1}.
\tag{68.18}
$$

由于两端滤波及其逆保持整个锥，C13 等价于 $I_{13}^0(D_+)\subseteq E_+$。引理 68.2 允许对 $(N,p_0)$ 应用定理 64.10，而该定理按 $M_0=F$ 选出的态正是 (68.15) 中的 $\sigma_*$，所以

$$
I_{13}^0(\sigma_*)\in E_+
\quad\Longleftrightarrow\quad I_{13}^0(D_+)\subseteq E_+.
\tag{68.19}
$$

为明确此步没有从测试后结论倒选探针，写出其关键结构。在 $E$ 上另取仅供证明的独立初始坐标。旧 (64.29)–(64.32) 给出酉 $R_{ijk}$、三元转置位 $t_1,t_2,t_3$，使

$$
\begin{aligned}
(I_{13}^0d)_{ijk}
 &=\operatorname{Ad}(R_{ijk})\,
 \operatorname{ins}_{13,j}\left[
 (T^{u_{ijk}}\otimes T^{v_{ijk}})
 \bigl(\operatorname{Ad}(V_{ik}^*)d_{ik}\bigr)\right],\\
u_{ijk}&=\varepsilon_{ik}\oplus t_1,\qquad
v_{ijk}=\delta_{ik}\oplus t_3.
\end{aligned}
\tag{68.20}
$$

这里 $\operatorname{Ad}(R)x=RxR^*$，$\operatorname{ins}_{13,j}$ 在端点之间插入未归一化 $I_{n_j}$，即把 $x\otimes I_{n_j}$ 作固定因子置换。$R,t$ 只参与证明。

若一个端点为标量，(68.20) 的端点操作至多是一个整个矩阵转置，自动正。两端非标量时，$u=v$ 给恒等或整个转置；$u\ne v$ 给单腿转置。在两维 Bell 子空间内，

$$
(\mathrm{id}\otimes T)b_{ik}
 =(T\otimes\mathrm{id})b_{ik}=\tfrac12\mathsf S_2,
\qquad
\mathsf S_2\frac{|01\rangle-|10\rangle}{\sqrt2}
 =-\frac{|01\rangle-|10\rangle}{\sqrt2}.
\tag{68.21}
$$

$\mathsf S_2$ 是该四维子空间的交换算子。预选输入在 (68.20) 中先被正确解开为 $V_{ik}^*(V_{ik}b_{ik}V_{ik}^*)V_{ik}=b_{ik}$，故任何坏块在 $I_{13}^0\sigma_*$ 中产生 $-1/(2r)$，按 $n_j$ 重复。不同有序端点块处于不同输出中心块，不能抵消；$n_j=1$ 也保留负方向。因此测试迫使每个活跃有序端点对和每个中间标签都满足 $u_{ijk}=v_{ijk}$，从而整锥正。反向由 $\sigma_*\ge0$ 立即得出。$r=0$ 时全为标量块，插入自动正。这就是 (68.19) 的既有 Bell 机制。

最后，(68.15)–(68.18) 给

$$
I_{13}^{\mathrm{raw}}(\rho_*)
 =\frac1{h_*}C_EI_{13}^0(\sigma_*).
\tag{68.22}
$$

$h_*>0$，$C_E$ 有全正逆，故 (68.22) 为正当且仅当 $I_{13}^0\sigma_*$ 为正。与 (68.19) 及整锥滤波等价合并，得到 (68.17)。$\square$

在辅助系统中 $\tau_EI_{13}^0(\sigma_*)=n$，这是定理 64.10 的迹结论；一般的原 $I_{13}^{\mathrm{raw}}\rho_*$ 没有固定输出迹。正确的伴随方向为

$$
(I_{13}^{\mathrm{raw}})^*=C_D^{-1}p_{13}^0C_E,
\qquad p_{13}^0=(I_{13}^0)^*.
\tag{68.23}
$$

只有 $\mathrm{P}_*$ 已推出 C13 后，才使用定理 65.8 的正保迹 $p_{13}^0$ 及 $p_{13}^0Q_0(a,b,c)=\tau_A(b)F(a,c)$；原伴随一般不保迹。

### 68.5 完整单态候选及原模型类不变

**定义 68.5（单态完整候选）。** 完整候选由定义 68.1 的全部数据、完整量词和关系，加上定义 68.3 的预选规则及唯一追加条件

$$
\mathrm{P}_*:\qquad I_{13}^{\mathrm{raw}}(\rho_*)\in E_+
\tag{68.24}
$$

组成。$\Phi_X$ 和 Jordan 运算来自定义 65.1 的已引纸面结论；$\mathcal B,K,M,J,H,B_1,Q,U,T,I_{13}^{\mathrm{raw}}$ 按 (68.4)、(68.7) 内部定义；$F,C_D$ 和 $\rho_*$ 按 (68.8)、(68.13)–(68.16) 导出。$G,C_G,\eta,N,\zeta,C_E,Q_0,p_0,T_0,I_{13}^0,p_{13}^0$ 是证明与结论中的辅助对象，不增加原始映射。特别没有独立供给 $p_{13}$、物理滤波器或新的参考设备。

**推论 68.6（同一实际元组上的精确替换）。** 对固定合格规约，定义 68.5 与定义 65.1–65.2 的完整候选在每个原始元组 $(A,D,E,C_X,u_X,L,p)$ 上逐点等价。因此定理 65.9–65.11 和推论 65.12 原封适用，全部未校准滤波参数均保留。

**证明。** 两者有相同 PRE，而定理 68.4 对每个 PRE 模型给出 $\mathrm{P}_*\Longleftrightarrow\mathrm{C13}$。因此首先由 $\mathrm{P}_*$ 得到 C13，然后才用定理 65.9 取得同时 Born 坐标，再用定理 65.10–65.11 的正反分类。反向任一该分类的原始模型满足 PRE 和 C13，其预选 $\rho_*$ 是正迹一原态，故自动满足 $\mathrm{P}_*$。整个替换不改变原态、原效应、原概率、$\omega,L,p$；不同合格规约只改变所选见证，所得模型集合相同。$\square$

为准确说明保留的参数范围，定理 65.10–65.11 的结论是：在测试后得到的同时坐标中，载体是 (65.23) 的全部有序单份、双份、三份复矩阵块。每个有序 $(i,j)$ 有 $u_{ij}\in H_{n_j}$ 正定，每个有序 $(i,j,k)$ 有 $g_{ijk}\in H_{n_k}$ 正定，参数仅受

$$
\sum_{i,j}n_i\operatorname{Tr}(u_{ij}^{-1})=n^2
\tag{68.25}
$$

约束。其实际 $M,L,Q,p$ 以及全部内部映射分别由 (65.29)–(65.33) 给出。这些公式覆盖整个实输入域与整个正锥；$u_{jk}$ 和 $g_{ijk}$ 无须交换，不要求跨块对称或共同对角化。固定同时坐标后 $U,G$ 分别确定全部 $u,g$。

逆向中的同一 $p$ 约束没有因改写而减弱：按 (65.30)–(65.31) 只给 $L,p$，暂记该式的第一准备为 $\widehat M$，用 (65.32) 的 $s$，则 (65.34) 给

$$
pL(d,c)=\widehat M(sd,c),\qquad
s\widehat M(a,b)=\tau_A(a)b.
$$

原 $\omega=1_D/n^2$ 给 $w=s\omega$，(68.25) 恰保证 $\tau_Aw=1$。于是实际 $K(a)=\widehat M(w,a)$、$sK(a)=a$，同一个 $p$ 第二次调用给 $M(a,b)=\widehat M(a,b)$。其余 PRE 和 C13 的逆向检查直接复用定理 65.11，随后由定理 68.4 得本候选。这说明保留的是全部原始映射类，不只是某个归一化代表。

原单位与保迹的边界也仍是 (65.37)：原 $M$ 保单位恰在全部 $u_{ij}=I_j$ 时成立，原 $H$ 保单位恰在全部 $g_{ijk}=I_k$ 时成立；原 $p$ 保迹还须满足该式独立列出的矩阵等式。$\mathrm{P}_*$ 不强制这些条件。例如单标量扇区的 $u=1,g>0$ 任意，给 $L(d,c)=gdc$、$p(z)=z/g$、$M(a,b)=ab$、$I_{13}^{\mathrm{raw}}=g\mathrm{id}$，全都满足本候选；$g\ne1$ 时 $H$ 不保单位且 $p$ 不保迹。非均匀、非交换矩阵滤波同样保留，见推论 65.12。

### 68.6 在固定原载体上，任意固定一态均可被坏模型放行

**定理 68.7（模型无关固定一态的严格障碍）。** 固定 $A=H_2,D=H_4,E=H_8$ 的全部 PSD 态锥、总迹一态、全部效应和标准迹比较，固定产品基及原参考 $\omega=I_4/4$。对每个 $W\in U(4)$ 定义原始映射

$$
L_W(d,c)=(W^*dW)\otimes c^{\mathsf T},\qquad
p_W(z)=W\bigl(\operatorname{Tr}_1z\bigr)^{\mathsf T}W^*.
\tag{68.26}
$$

其中 $\operatorname{Tr}_1:H_8\to H_4$ 迹掉首个二维因子，$p_W$ 的转置作用在偏迹后整个四维矩阵上。则每个模型均满足 PRE，甚至满足旧 $W_H,\mathrm{(N)}$、原 $p_W$ 保迹和两个原单位律，但其实际插入不全锥正。并且

$$
\forall\rho\in D_+,\ \operatorname{Tr}\rho=1,
\quad\exists W\in U(4):\quad
I_W(\rho)\ge0\quad\text{且}\quad I_W(D_+)\nsubseteq E_+,
\tag{68.27}
$$

这里 $I_W$ 按 (68.7) 从该模型的实际 $M_W,L_W$ 定义。

**证明。** 首先检查全域正性和比较入口。$d\mapsto W^*dW$、整个转置及偏迹均保持完整 PSD 锥；两个正矩阵的张量积为正。因此 $L_W(D_+,A_+)\subseteq E_+$，且 $p_W$ 对整个 $E_+$ 为正并保迹。这里没有只检查乘积 $z$。每个载体的纯态为秩一投影 $q$，最小确认效应为 $q$：若 $0\le f\le I$、$\operatorname{Tr}(fq)=1$，则 $I-f$ 支撑在 $q$ 的正交补上，从而 $f\ge q$。因此 $T_q(x)=\operatorname{Tr}(qx)$，完整有限混合律 (68.1) 成立；原几何就是标准规范迹几何。

对全部实 $d,c$ 直接计算，注意偏迹后的整个转置同时作用于两个保留因子：

$$
\mathcal B_W(d,c)
 =W\left[\bigl(\operatorname{Tr}_1(W^*dW)\bigr)^{\mathsf T}
 \otimes c\right]W^*.
\tag{68.28}
$$

此式内 $\operatorname{Tr}_1:H_4\to H_2$ 迹掉双份矩阵的首因子。由于 $W^*\omega W=I_4/4$，原参考给

$$
\begin{aligned}
K_W(a)&=W(I_2/2\otimes a)W^*,\\
M_W(a,b)&=\mathcal B_W(K_W(a),b)
 =W(a^{\mathsf T}\otimes b)W^*.
\end{aligned}
\tag{68.29}
$$

两行由同一个 $p_W$ 依次算出；没有另行指定 $M_W$。所以

$$
\begin{gathered}
J_W(a)=W(a^{\mathsf T}\otimes I_2)W^*,\qquad
H_W(d)=(W^*dW)\otimes I_2,\\
Q_W(a,b,c)=a^{\mathsf T}\otimes b\otimes c^{\mathsf T},\qquad
U_W=I_4,\quad G_W=I_8.
\end{gathered}
\tag{68.30}
$$

Hermitian 实简单张量张成全部 Hermitian 张量矩阵；转置和酉共轭可逆，故 $M_W(A,A)$ 实张成 $D$，$L_W(D,A)$ 实张成 $E$。对整个相应实空间都有

$$
\langle J_Wa,J_Wb\rangle_D=2\operatorname{Tr}(ab),\qquad
\langle H_Wd,H_Wd'\rangle_E=2\operatorname{Tr}(dd').
\tag{68.31}
$$

这同时给 $D_J$、包括所有纠缠输入的 $D_H$，以及 $W_J,W_H$。再取 (68.28) 中 $c=I_2$，代入实际 $M_W$ 得

$$
B_{1,W}M_W(a,b)=\operatorname{Tr}(a)J_W(b)
\qquad(a,b\in H_2).
\tag{68.32}
$$

因而全实 $Z$ 成立。更一般 $p_WQ_W(a,b,c)=\operatorname{Tr}(a)M_W(b,c)$，所以完整 III 也成立。$p_W$ 保迹给旧 $\gamma_W=\operatorname{Tr}(p_WI_8)=8=2^3$，满足 $\mathrm{(N)}$。至此 PRE 及声称的额外校准条件均已检查；其内在 $C_D,C_E$ 都是恒等。

令 $\operatorname{ins}_{13}$ 在两端之间插入 $I_2$，作用的因子顺序与 (68.20) 相同。从 (68.29) 得 $\widetilde M_W$ 可逆，而 $T_W(a,c)=a^{\mathsf T}\otimes I_2\otimes c^{\mathsf T}$。在 $d=M_W(a,c)$ 上计算，再由实张成延拓到全部 $d\in H_4$，得到实际插入

$$
I_W(d)=\operatorname{ins}_{13}
 \left[(\mathrm{id}\otimes T)(W^*dW)\right].
\tag{68.33}
$$

现在固定任意 $\rho\ge0$、$\operatorname{Tr}\rho=1$。有限维 Hermitian 谱定理允许选 $W$，使 $W^*\rho W$ 在事先固定的产品基 $\{|00\rangle,|01\rangle,|10\rangle,|11\rangle\}$ 中为非负对角矩阵。重根和零特征值均不妨碍选取正交本征基。这个对角矩阵在第二因子转置下不变；插入 $I_2$ 保持正性，故 (68.33) 给 $I_W(\rho)\ge0$。

对于同一个 $W$，取 $v=(|00\rangle+|11\rangle)/\sqrt2$、$b=vv^*$ 和正迹一元 $d_W=WbW^*$。由 (68.21)，

$$
I_W(d_W)=\operatorname{ins}_{13}(\mathsf S_2/2).
$$

它在每个归一化向量 $(|0,k,1\rangle-|1,k,0\rangle)/\sqrt2$（$k=0,1$）上有本征值 $-1/2$。故 $I_W$ 对整个 $D_+$ 不正，证明 (68.27)。$\square$

这里的 $W$ 改变同一原载体上的实际 $L_W,p_W,M_W$；原 $\rho$、比较、效应、产品基和 $\omega$ 始终固定。没有同时把 $\rho$ 也搬走。因此 (68.27) 严格排除了下述可能：在这些固定载体上存在一个与模型无关的正迹一态，使它的完整输出正性对所有 PRE 模型都等价于 C13。反例已位于全校准子类内，故同样阻止在更大的未校准类中采用这种固定一态。

这不妨碍定理 68.4。对 (68.26)，可取第一接口初始形 $V=W$、$(\varepsilon,\delta)=(1,0)$；其模型适配探针恰为 $WbW^*$，会检出上述负方向。任意其他合格规约也由定理 68.4 得出相同失败结论。$W=I_4$ 是定理 64.11 的既有控制；本章增加的是对每个固定 $\rho$ 选取模型的严格量词结论，所用谱定理和 Bell 部分转置均是标准机制。

对角化一步只是说明每个固定谱都存在一个产品基对角代表；它不声称该谱的所有酉轨道都可分或都为 PPT，也不把此存在量词叫作绝对可分性。定理没有声称一个坏模型通过所有 $\rho$，没有排除任意有限探针族，也没有给出最小测量或最小探针数。

### 68.7 几何、量子对应与精确边界

几何上，完整比较律已经把态与全效应放到同一个自对偶迹几何中。PRE 的两个完整二元接口再把交叉插入的剩余缺陷限制成各中心块的相对转置。$\sigma_*$ 在每个有序非标量端点对中放一个两级 Bell 投影；任何单腿方向错误都会在独立输出块留下负方向。原 $C_D$ 把这个辅助锥中的态送回实际锥，再用严格正的 $h_*$ 截回原迹一基；$C_E$ 改变输出权重，却不能把锥外点变成锥内点。这是可逆锥几何中的等价，不要求滤波保持迹一截面。

反事实也很具体。若删去 $\mathrm{P}_*$，(68.26) 的模型仍满足其余条件，甚至已校准，却保留负插入。若把预选态换成与 $M$ 无关的任意固定一态，定理 68.7 使某个这样的坏模型通过。若只测有序对中的对角块或漏掉标量中间，定理 64.11 的跨扇区控制仍可逃过；本章探针明确覆盖所有有序活跃端点对和每个中间标签。

本章压缩的恰是 C13 的输入全称量词。它保留完整 $S$、全态全效应、$L,p$ 的全锥正性、$D_H$ 的整个双份锥量词、全部实 $Z$、两条张成及同一个 $p$ 两次。$\mathrm{P}_*$ 仍要求整个输出属于 $E_+$；由自对偶性，这等价于它对全部输出效应的配对非负。它不是一个预定标量效应的非负、一次测量或一份有限统计数据。输入态数为一不等于实验成本为一。

其单态充分性也不适用于任意线性映射。若 $\dim D>1$，对任一固定态 $\rho$ 可取非零实线性泛函 $\lambda$ 满足 $\lambda(\rho)=0$。因为 $D_+$ 生成 $D$，某个 $x\in D_+$ 有 $\lambda(x)\ne0$；改变符号后令其为负。取非零 $y\in E_+$，则 $\Lambda(d)=\lambda(d)y$ 满足 $\Lambda(\rho)=0\in E_+$，却有 $\Lambda(x)\notin E_+$。定理 68.4 的充分性来自 PRE 对特定插入族的结构限制。

通过 $\mathrm{P}_*$ 后，原系统与通常有限静态量子结构的对应如下，均由推论 68.6 及推论 65.12 得到。

| 对象 | 在原归一化和原概率下的对应 |
| --- | --- |
| 全态与纯态 | 每个载体为直和 PSD 块，$\rho_\lambda\ge0$、$\sum_\lambda\operatorname{Tr}\rho_\lambda=1$；单份纯态空间为 $\coprod_i\mathbb{CP}^{n_i-1}$，允许经典标量扇区及多扇区混合。 |
| 全效应与 Born 规则 | 每块 $0\le f_\lambda\le I_\lambda$，原概率为 $\sum_\lambda\operatorname{Tr}(f_\lambda\rho_\lambda)$；同扇区纯比较是 $|\langle\psi,\phi\rangle|^2$，异扇区为零。 |
| 有限复合 | 辅助 $F,N$ 在测试后同时坐标中为通常分块复张量，$p_0$ 为首偏迹；实际 $M,L,p$ 保留 (65.28)–(65.33) 的全部滤波。双份、三份的全部纠缠态均在原态集中。 |
| 张成和读回 | 实张成给接口层析，并使规定的全实读回唯一；它不声称任意三体态由三个两两边缘唯一确定。 |

这里得到的有限张量条件只涉及指定的单份、双份、三份载体。它不识别另行给定的右括号复合，也不提供四份、任意高份数或无限维的一致性；单一非经典扇区仍需额外选择。

过程问题须另定契约。上述特定映射的矩阵公式和全锥正性，不选出一般物理过程集合，不把任意参考扩张下的 CP 原则、TP 信道、仪器、测量更新或连续动力学当作结论；原 $p$ 尤其一般非 TP。本章也没有产生时钟、Hamiltonian、$\hbar$ 或物理可逆群。纯端点比较互反并非时间中的测量交换，亦不排除几何相位。

从实际来源到这些数学输入，还需说明完整比较律、全部效应、全锥关系和张成为何适用于目标系统，以及原参考、$\rho_*$ 与滤波如何获得、准备和计价。精确锥判定若要改为有限误差的实验认证，还需测量和误差理论。这些是从本章完整条件模型走向物理应用的具体桥，不改变本章在所列前提内的双向数学结论。

本章的来源层次是明确的：规范 EJA 入口、两个接口、早期正规形、定理 64.10 的 Bell 拼合及定理 65.3–65.8 的滤波恢复均为已发表纸面输入；本章完成的是它们在同一 PRE 上的逐项衔接、$\rho_*=C_D\sigma_*/\tau_D(C_D\sigma_*)$ 的原态拉回、同一原始模型类的等价替换，以及定理 68.7 的模型适配量词障碍。有限维谱分解、可逆正合同和 Bell 部分转置的负谱属于成熟工具；部分转置的标准文献背景见 [Peres, *Separability Criterion for Density Matrices*](https://doi.org/10.1103/PhysRevLett.77.1413)。此处不使用 PPT 等价于可分的断言，也不把本条件称作一般 Choi 判 CP。新综合的文献新颖性、独立性或最少性不在这些证明的结论中。

**完整候选的朴素表述。** 先在真实给定的单份、双份和三份有限系统中保留所有数学态及所有效应，用“一个测试若确定接受某个纯参照，对另一态最少会误接受多少”定义比较，并要求任何有限随机纯制备都服从交换端点后再平均的同一规则。沿用已有结果，这确定状态与测试共用的规范几何。再只给一个对全部双份正输入有效的准备和同一个对全部三份正输入有效的读回，从原参考连续调用这个读回两次来定义第一准备，保留两个实张成、两个单位切片的零比较保持及全部实方向的关系。最后，从这个实际第一准备先取出正权重，数学上去掉权重；按事先固定的单份、双份坐标，在每一种有顺序的非标量端点组合中放一个两级 Bell 态，合成一份态，再放回原权重并归一化。只要求原交叉插入把这一份预选原态送到整个正锥。任何错接的单腿方向都会在对应输出块留下无法被别块抵消的负方向，所以这个条件恰好等价于原来的整锥条件，同时完整保留所有未校准正滤波。若把这份态改成完全不看实际第一准备的固定态，总能选一个仍满足其余全部条件的坏模型放行它；因此模型适配是这里证明的一部分。所得结论是原有全部有限复 Born 态、效应和滤波模型的完整等价候选，物理准备、一般过程、时间及更多份的一致性仍由各自的桥连接。

## 追加锚（本行以下为增补区）

## 69. 原始旁观者操作的概率预算与弱共同重置补全

### 69.1 条件源、原始迹与固定的旁观者族

**定义 69.1（实际原始操作模型）。** 复用定理 65.9–65.11 在完整有限比较律 $S$、定义 65.2 的实际映射条件及 C13 下给出的同时矩阵坐标；也可从第 66 节加回 C13 后的同一普通乘积方向读取这些坐标。本节不重新证明该条件性静态分类。固定有限非空扇区集 $I$、整数 $n_i\ge1$，记 $H_i=\mathbb C^{n_i}$、$n=\sum_i n_i$，取

$$
A=\bigoplus_i\operatorname{Herm}(H_i),\qquad
D=\bigoplus_{i,k}\operatorname{Herm}(H_i\otimes H_k),\qquad
u_{ik}>0,\qquad \sum_{i,k}n_i\operatorname{Tr}(u_{ik}^{-1})=n^2.
\tag{69.1}
$$

所有有序块都在，正锥是各整个 PSD 锥，迹是原来的各块普通迹之和；任意纠缠正元均在量词内。$u_{ik}\in\operatorname{Herm}(H_k)$ 不要求交换、标量、对称或等维。第 65 节三份侧的全部 $g_{ijk}>0$ 仍任意，本节不添加关于 $g$ 的约束。令

$$
\begin{aligned}
S_{ik}&=I_i\otimes\sqrt{u_{ik}},&
(C_DX)_{ik}&=S_{ik}X_{ik}S_{ik},\\
m(a,b)_{ik}&=a_i\otimes b_k,&
M(a,b)&=C_Dm(a,b).
\end{aligned}
\tag{69.2}
$$

$C_D$ 及其逆都是全锥正的可逆合同，且关于迹内积自伴随；它们通常不保迹。它们只是分解实际 $M$ 的数学坐标滤波，不另定义态的归一化，也不被指定为物理装置。旁观者始终是同一个实际 $D$ 的第二腿。

### 69.2 实张成唯一固定原始延拓

**定理 69.2（唯一旁观者延拓）。** 对任意实线性 $\Phi:A\to A$，以 $\Phi_{ji}$ 同时记其输入 $i$、输出 $j$ 块在全矩阵上的唯一复线性保 Hermitian 延拓。定义

$$
(T_\Phi X)_{jk}=\sum_i(\Phi_{ji}\otimes\operatorname{id}_{H_k})(X_{ik}).
$$

唯一满足 $\Psi_\Phi M(a,b)=M(\Phi(a),b)$、量化全部实 $a,b$ 的实线性映射是

$$
\boxed{\ \Psi_\Phi=C_DT_\Phi C_D^{-1}.\ }
\tag{69.3}
$$

证明。Hermitian 简单张量实张成每个完整块，选取中心支持可分别张成每个有序 $(i,k)$ 块。可逆 $C_D$ 保持张成。右式在每个 $M(a,b)$ 上有要求的值，故存在且唯一。这一步不使用 $\Phi$ 的正性或迹条件。$\square$

### 69.3 一个带完整输入标签的实际归一参考

**定理 69.3（原始参考与完整 Choi 恢复）。** 固定每个 $H_i$ 的基、$w_i>0$ 及 $\sum_iw_i=1$。令

$$
|\phi_i\rangle=\frac1{\sqrt{n_i}}\sum_{r=1}^{n_i}|r\rangle\otimes|r\rangle,
\quad q_i=|\phi_i\rangle\langle\phi_i|,\quad
(\Omega_w)_{ik}=\begin{cases}w_iq_i&i=k,\\0&i\ne k.\end{cases}
$$

一个指定的实际正迹一态为

$$
\rho_w=\frac{C_D\Omega_w}{Z},\qquad
Z=\operatorname{Tr}_D(C_D\Omega_w)
 =\sum_i\frac{w_i}{n_i}\operatorname{Tr}(u_{ii})>0.
\tag{69.4}
$$

定义未归一 Choi 块及实际输出 $Y=\Psi_\Phi(\rho_w)$，则

$$
\begin{aligned}
Q_{ji}&=\sum_{r,s=1}^{n_i}\Phi_{ji}(|r\rangle\langle s|)
                         \otimes|r\rangle\langle s|,\\
Y_{ji}&=\frac{w_i}{n_iZ}(I_j\otimes\sqrt{u_{ji}})
                    Q_{ji}(I_j\otimes\sqrt{u_{ji}}),\\
Q_{ji}&=\frac{n_iZ}{w_i}(I_j\otimes u_{ji}^{-1/2})
                    Y_{ji}(I_j\otimes u_{ji}^{-1/2}),\\
\Phi_{ji}(X)&=\operatorname{Tr}_{H_i}
                    [Q_{ji}(I_j\otimes X^{\mathsf T})].
\end{aligned}
\tag{69.5}
$$

因而下列条件等价：每个 $\Phi_{ji}$ 为 CP；$\Psi_\Phi$ 为 CP；$\Psi_\Phi$ 在整个实际 $D_+$ 上正；这个指定参考的整个输出 $Y$ 为 PSD。

证明。将 (69.3) 作用于 (69.4)，用已有归一接口的 Choi 块公式，得到 (69.5)。正定合同及严格正系数使 $Y\ge0$ 当且仅当每个 $Q_{ji}\ge0$；直接应用 [Watrous 条目的实际参考接口及定理 2.22](../../../Library/Quantum/watrous2018theory.md#one-actual-self-reference-for-finite-sector-operations)，后者当且仅当每个矩形块 CP。块 CP 使 $T_\Phi$ CP，而 $C_D,C_D^{-1}$ 都是 CP 合同，所以 $\Psi_\Phi$ CP。CP 蕴含整锥正，整锥正又可测试实际 $\rho_w$，闭合等价。$\square$

输出 $(j,i)$ 中的 $i$ 是保留的输入扇区标签，不合并等维扇区。零块可用空 Kraus 列表；$n_i=1$ 的参考是标量，$n_j\ne n_i$ 时仍用同一个矩形 Choi 公式。参考第二边缘忠实不等于联合态满秩。这里测试的是一个指定输入的整个联合 PSD 输出，不是一个标量读数、任意 $D\to D$ 映射的完整辨识、有效层析或实际参考制备可用性的结论。

### 69.4 两种迹预算与非交换滤波顺序

**定理 69.4（局部预算与原始联合预算）。** 设每个 $\Phi_{ji}$ CP，复用其矩形 Kraus 表示，记

$$
\Phi_{ji}(X)=\sum_\ell K_{ji,\ell}XK_{ji,\ell}^*,\qquad
F_{ji}=\Phi_{ji}^*(I_j)=\sum_\ell K_{ji,\ell}^*K_{ji,\ell}\ge0.
$$

从输入 $(i,k)$ 到输出 $(j,k)$ 的原始 Kraus 算子恰为

$$
V_{ji,k,\ell}=K_{ji,\ell}\otimes
                 (\sqrt{u_{jk}}\,u_{ik}^{-1/2}).
\tag{69.6}
$$

局部 $A$ 上迹非增（TNI）或保迹（TP）分别当且仅当

$$
\sum_jF_{ji}\le I_i\quad\text{或}\quad\sum_jF_{ji}=I_i
\qquad(\forall i).
\tag{69.7}
$$

原始 $D$ 上 TNI 或 TP 则分别当且仅当

$$
\sum_j F_{ji}\otimes u_{jk}\le I_i\otimes u_{ik}
\quad\text{或}\quad
\sum_j F_{ji}\otimes u_{jk}=I_i\otimes u_{ik}
\qquad(\forall i,k).
\tag{69.8}
$$

证明。代入两端合同得到 (69.6)，其中两个旁观者矩阵的乘法顺序不可颠倒。求整个直和映射的效应得

$$
(\Psi_\Phi^*1_D)_{ik}
 =\sum_jF_{ji}\otimes
          (u_{ik}^{-1/2}u_{jk}u_{ik}^{-1/2}).
\tag{69.9}
$$

正映射在所有正输入上迹非增当且仅当其效应不超过单位；等号情形就是保迹。对 (69.9) 作 $S_{ik}$ 合同得到 (69.8)。对局部效应作同样的迹对偶论证得到 (69.7)。这是两个完整算子预算，均测试整个相应正锥，不只测试乘积态。$\square$

数学分支可容许性在此独立定义为块 CP 加上所要求的局部、原始 TNI 预算；它不预先意味着存在一个完整仪器。对一般 $u$，两个预算应分别核对。原始输出 $Y$ 的一次总迹等于一或普通参考边缘不变，都不代替 (69.8)。

### 69.5 参考归一不能代替整锥预算

**命题 69.5（原始迹与局部迹的区分控制）。** 下面均为两标量扇区，矩阵 $u$ 的行是输入 $i$，列是旁观者 $k$，每例都有 $\sum_{i,k}u_{ik}^{-1}=4=n^2$，并可取任意允许的 $g$。

首先取

$$
u=\begin{pmatrix}2&1/2\\2&1\end{pmatrix},\qquad
\Phi(a_1,a_2)=(0,a_1+a_2).
\tag{69.10}
$$

该局部重置 TP。$\rho_w$ 只在 $(1,1),(2,2)$ 有质量 $2w_1/Z,w_2/Z$；重置分别送到 $(2,1),(2,2)$ 而质量不变。所以 $Y\ge0$、$\operatorname{Tr}Y=1$，且普通参考边缘与 $\rho_w$ 完全相同。但实际输入 $(1,2)$ 的质量被乘二，故原始映射不是 TNI。若只交换 $u_{12}$ 与 $u_{22}$，逆迹平衡仍成立，同样保留该参考的迹及普通边缘，而输入 $(1,2)$ 的质量乘 $1/2$；此时原始映射 TNI 但不是 TP。

反过来取

$$
u=\begin{pmatrix}3/2&3/2\\3/4&3/4\end{pmatrix},\qquad
\Phi(a_1,a_2)=(0,2a_1+a_2).
\tag{69.11}
$$

两个输入的加权和分别是 $2(3/4)=3/2$ 与 $3/4$，故原始映射 TP；第一局部输入的效应为 $2$，局部却不 TNI。以上都是全部有序块上的直接预算计算，证明两个方向及参考读数的替代均不成立。$\square$

### 69.6 指定有限族的共同补全判据

**定理 69.6（同一旁观者族的双预算补全）。** 给定有限个块 CP 分支 $\Phi_r$，记其效应为 $F^r_{ji}$，并令

$$
\begin{aligned}
E_{ji}&=\sum_r F^r_{ji},&
\Delta A_i&=I_i-\sum_jE_{ji},\\
\Delta U_{ik}&=I_i\otimes u_{ik}-\sum_jE_{ji}\otimes u_{jk}.
\end{aligned}
\tag{69.12}
$$

部分仪器必须对这个聚合 $E$ 施加 $\Delta A_i\ge0$、$\Delta U_{ik}\ge0$；仅每个分支分别 TNI 不足以保证概率总和不超过一。按同一 (69.3) 规则增加有限个局部 CP 分支，使局部和原始总映射都 TP，当且仅当存在同一组 $G_{ji}\ge0$，满足

$$
\boxed{\quad
\sum_jG_{ji}=\Delta A_i\quad(\forall i),\qquad
\sum_jG_{ji}\otimes u_{jk}=\Delta U_{ik}\quad(\forall i,k).
\quad}
\tag{69.13}
$$

只要可行，一个失败结果的局部 CP 映射已经足够；完整仪器的总通道不必是恒等通道。

证明。必要性取全部新增分支的聚合效应，再用 (69.7)–(69.8)。充分性在每个输出扇区任选密度 $\tau_j\ge0$、$\operatorname{Tr}\tau_j=1$，定义一个新增结果

$$
\Gamma_{ji}(X)=\operatorname{Tr}(G_{ji}X)\tau_j.
\tag{69.14}
$$

其 Choi 块为 $\tau_j\otimes G_{ji}^{\mathsf T}\ge0$，效应恰为 $G_{ji}$，故 CP。与原分支合并后，(69.13) 恰好填平两边预算；所有分支的效应为正，完整预算也自动给各分支 TNI。该证明不需要任何 $u$ 交换。$\square$

若仅要求原始 $D$ 完备，删除 (69.13) 的第一组等式；这不再保证局部完备。还须区分任意 $D$ 上的 CP 补映射：给定聚合原始 CP TNI 映射 $\Psi$，任选实际 $D$ 的密度 $\tau_D$，则

$$
X\longmapsto\operatorname{Tr}[(1_D-\Psi^*1_D)X]\tau_D
\tag{69.15}
$$

是一个使总映射 TP 的 CP 补映射。然而它未必是任何局部 $\Gamma$ 的同族 $\Psi_\Gamma$，也不供应局部 TP。两个缺额分别为正并不证明存在 (69.13) 的共同解。

### 69.7 固定弱重置的独立预算

**命题 69.7（正成功份额的精确范围）。** 固定一个输出扇区 $j_0$ 和该扇区任意密度 $\sigma$，允许 $\sigma$ 不满秩。令

$$
R(a)_j=\delta_{j,j_0}\Bigl(\sum_i\operatorname{Tr}a_i\Bigr)\sigma,
\qquad B=cR.
\tag{69.16}
$$

$R$ 为局部 CPTP，$B$ 同时满足局部及原始分支预算，当且仅当

$$
0\le c\le c_*:=\min_{i,k}\lambda_{\min}
 (u_{j_0k}^{-1/2}u_{ik}u_{j_0k}^{-1/2}),
\qquad 0<c_*\le1.
\tag{69.17}
$$

证明。重置块的 Choi 矩阵为 $\sigma\otimes I_i$，效应为 $\delta_{j,j_0}I_i$，所以 $R$ 局部 CPTP。$c<0$ 时非零重置不正；$c\ge0$ 时 $B$ CP，局部 TNI 恰为 $c\le1$，原始预算恰为 $cu_{j_0k}\le u_{ik}$。正定合同把后者化为 (69.17)。有限多个正定矩阵给 $c_*>0$；$i=j_0$ 的项为单位，故 $c_*\le1$，已包含局部上界。$\square$

因此数学上总能选择一个正但足够弱的共同重置满足两边预算；小成功份额只解决分支可容许性，尚未解决共同补全，更未证明有相应物理设备。

### 69.8 一个弱共同重置与整个局部仪器菜单

**定理 69.8（弱重置补全的精确等价）。** 固定任意 $j_0$、任意上述 $\sigma$ 及任意 $0<c\le1$。在同一个 (69.1)–(69.3) 模型中，下列条件等价：

1. 分支 $cR$ 能以同一旁观者扩展规则补成局部及原始两边都 TP 的有限 CP 仪器。
2. 对每个 $k$，$u_{ik}=v_k$ 与输入扇区 $i$ 无关。
3. 这个固定的完整重置 $R$ 的原始延拓 TP。
4. 每个局部 CPTP 映射的原始延拓 TP。
5. 每个有限局部 CP 完备仪器的原始延拓都是完备仪器。

证明。先证 1 蕴含 2。对含 $cR$ 的完整仪器取总效应 $F_{ji}$，则

$$
F_{ji}\ge0,\quad \sum_jF_{ji}=I_i,\quad
F_{j_0i}\ge cI_i,\quad
\sum_jF_{ji}\otimes u_{jk}=I_i\otimes u_{ik}.
\tag{69.18}
$$

令 $p_{ij}=\operatorname{Tr}(F_{ji})/n_i$。这里必须除以实际输入维数 $n_i$，才能对不等维扇区得到同一个行随机矩阵。对最后的等式施加首腿归一偏迹，得

$$
\sum_jp_{ij}=1,\qquad p_{ij_0}\ge c,\qquad
u_{ik}=\sum_jp_{ij}u_{jk}\quad(\forall i,k).
\tag{69.19}
$$

把每个行元组放在同一个实向量空间

$$
\mathbf v_i=(u_{ik})_{k\in I}\ \in\ V=\bigoplus_k\operatorname{Herm}(H_k).
$$

$V$ 不依赖输入维数 $n_i$；(69.19) 就是 $\mathbf v_i=\sum_jp_{ij}\mathbf v_j$，且每行共有至少 $c$ 的同一锚点质量。若 $0<c<1$，写

$$
p_{ij}=c\delta_{j,j_0}+(1-c)q_{ij},\qquad
\mathbf v_i=c\mathbf v_{j_0}+(1-c)z_i,\qquad
z_i=\sum_jq_{ij}\mathbf v_j\in\operatorname{conv}\{\mathbf v_j\}.
\tag{69.20}
$$

这里 $q$ 也是行随机矩阵。任选 $V$ 上的范数，令 $d=\max_{i,l}\|\mathbf v_i-\mathbf v_l\|$。凸包中任意两点之差是 $\mathbf v_j-\mathbf v_h$ 的凸平均，故其距离至多 $d$。所以 $d\le(1-c)d$，推出 $d=0$。若 $c=1$，随机行只能集中于 $j_0$，直接得所有 $\mathbf v_i=\mathbf v_{j_0}$。这就是共同锚点的有限凸包收缩论证；它不需要不可约性、同时对角化、等维、$\sigma$ 满秩或逆迹平衡。

若 2 成立，$C_D$ 只作用在旁观者上，跨扇区也与每个 $T_\Phi$ 交换，于是

$$
\Psi_\Phi=T_\Phi,\qquad
\sqrt{u_{jk}}\,u_{ik}^{-1/2}=I_k.
\tag{69.21}
$$

两个预算完全对应，得到 4、5；用 $\Gamma=(1-c)\operatorname{id}_A$ 或 $\Gamma=(1-c)R$ 即构造 1 的一个失败结果。总映射分别为 $cR+(1-c)\operatorname{id}_A$ 或 $R$，均是通道，不要求等于恒等。4 蕴含 3；3 的原始预算是 $u_{j_0k}=u_{ik}$，故蕴含 2。5 包含只有一个结果的局部通道，故也蕴含 4，闭合全部等价。$\square$

几何上，行元组是一个具有共同锚点列的随机平均的调和向量；正共同份额消去所有非恒定行。它是已知有限随机收缩方法在此预算关系上的应用，不是新的随机矩阵定理。一个正权弱重置补全只是整个局部菜单闭包的更短等价见证，不能据此宣称独立公理减少。

### 69.9 可容许不等于可补全，局部完备不能删去

**命题 69.9（两个逆迹平衡的严格区分）。** 第一，取

$$
u=\begin{pmatrix}1/2&1\\2&2\end{pmatrix},\qquad j_0=2,\qquad c=1/4.
\tag{69.22}
$$

逆迹和为 $2+1+1/2+1/2=4$，$c_*=1/4$。$cR$ 的原始迹比率按 $(i,k)$ 排列为

$$
\begin{pmatrix}1&1/2\\1/4&1/4\end{pmatrix},
$$

局部效应为 $1/4$，故同时满足两个 TNI 预算。若存在共同补全，对输入 1 的总效应必须满足

$$
F_{11}+F_{21}=1,\qquad
\tfrac12F_{11}+2F_{21}=\tfrac12,\qquad F_{21}\ge\tfrac14.
$$

前两个等式迫使 $F_{21}=0$，矛盾。甚至仅原始同族补全也失败：输入 1 的两个原始缺额是 $0,1/2$，失败效应应满足

$$
\tfrac12G_{11}+2G_{21}=0,\qquad
G_{11}+2G_{21}=\tfrac12,\qquad G_{11},G_{21}\ge0.
$$

第一式迫使两者都为零，与第二式矛盾。

第二，取

$$
u=\begin{pmatrix}2&2\\2/3&2/3\end{pmatrix},\qquad j_0=1,\qquad c=1/4.
\tag{69.23}
$$

逆迹和为 $1/2+1/2+3/2+3/2=4$，行不相同。取总局部效应

$$
F_{11}=1,\qquad F_{12}=1/3,\qquad F_{21}=F_{22}=0.
$$

它们含有 $cR$ 的效应，减去 $1/4$ 后的新增效应非负，可用 (69.14) 实现。每个 $k$ 的原始等式为 $2F_{11}=2$、$2F_{12}=2/3$，所以是同族原始完备仪器。第二局部输入的总效应却仅为 $1/3$。它还满足聚合局部 TNI，唯独不局部 TP；因此删除局部完备就不能推出行一致。$\square$

$c=0$ 时零分支加恒等即可对任意 $u$ 完整补全，不提供行一致信息；$c=1$ 时定理 69.8 的直接锚点论证适用。单扇区时行一致自动成立；全标量扇区与任意不等维扇区均已包括。奇异 $u$、零维扇区和无限扇区不属于本节模型。

### 69.10 剩余滤波与每对制备的归一化

**推论 69.10（行一致严格弱于单位滤波）。** 定理 69.8 的行一致条件使静态逆迹平衡恰化为

$$
\sum_k\operatorname{Tr}(v_k^{-1})=n.
\tag{69.24}
$$

它不迫使 $v_k=I_k$。两标量扇区的相同行 $(2,2/3)$ 满足 (69.24)；单个复 qubit 扇区的 $v=\operatorname{diag}(2,2/3)$ 也满足 $\operatorname{Tr}v^{-1}=2$。只有总维数一时此平衡强制 $u=1$。

对一般原始模型，额外要求 $M$ 将每一对局部正迹一输入都送到实际正迹一态，当且仅当所有 $u_{ik}=I_k$。证明是

$$
\operatorname{Tr}_D M(a,b)
 =\sum_{i,k}\operatorname{Tr}(a_i)\operatorname{Tr}(u_{ik}b_k).
\tag{69.25}
$$

将 $a,b$ 分别支持于任意 $i,k$，并遍历 $H_k$ 的所有密度矩阵，就要求 $\operatorname{Tr}(u_{ik}b_k)=1$ 对所有这些矩阵成立；秩一态分离 Hermitian 矩阵，故 $u_{ik}=I_k$。反向代入即得。特别地，行一致后仍有 $\operatorname{Tr}M(a,b)=\operatorname{Tr}(a)\sum_k\operatorname{Tr}(v_kb_k)$，不能把它默认为一。$\square$

逆迹平衡用于保证参数属于第 65 节的实际静态模型；它没有参与共同锚点的必要性证明或同族补全构造。行一致、每对制备归一化及三份侧 $g$ 的校准是不同信息。

### 69.11 与标准有限仪器、概率及更新的对应

**命题 69.11（同族仪器的完整参数接口）。** 在行一致之前，有限兼容仪器恰为块 Kraus 族

$$
(\Phi_r a)_j=\sum_{i,\ell}K_{r,ji,\ell}a_iK_{r,ji,\ell}^*,
\qquad F^r_{ji}=\sum_\ell K_{r,ji,\ell}^*K_{r,ji,\ell},
$$

同时满足

$$
\sum_{r,j}F^r_{ji}=I_i\quad(\forall i),\qquad
\sum_{r,j}F^r_{ji}\otimes u_{jk}=I_i\otimes u_{ik}\quad(\forall i,k).
\tag{69.26}
$$

等价地，可取任意 PSD Choi 块 $Q^r_{ji}$，令 $F^r_{ji}=(\operatorname{Tr}_{H_j}Q^r_{ji})^{\mathsf T}$，并施加同样的两个总预算；实际原始 Kraus 由 (69.6) 给出。行一致后，两式合为普通局部 Kraus 完备式，原始 Kraus 就是 $K_{r,ji,\ell}\otimes I_k$，因此恰恢复整个有限局部 CP 仪器菜单。

证明。直接复用 Watrous 条目的矩形 Choi/Kraus 对应、定理 2.26 与已有有限仪器接口，再应用定理 69.4。这里新增的是原始预算与该标准接口的对应，不重新证明标准表示定理。$\square$

对实际局部密度 $a$，结果概率是 $p_r=\operatorname{Tr}_A\Phi_r(a)$；对实际联合密度 $\rho$，则是 $p_r=\operatorname{Tr}_D\Psi_r(\rho)$。各自完整仪器的概率和为一，正概率时的条件输出分别为 $\Phi_r(a)/p_r$、$\Psi_r(\rho)/p_r$。这些都是已有 Born 迹规则和分支归一化。复合及粗粒化满足

$$
\Psi_\Theta\Psi_\Phi=C_DT_{\Theta\circ\Phi}C_D^{-1},\qquad
\sum_{r\in B}\Psi_{\Phi_r}=\Psi_{\sum_{r\in B}\Phi_r}.
\tag{69.27}
$$

两个双预算完整仪器的顺序复合仍在同族并完整；对非零历史概率按联合分支迹归一。该对应不要求先后操作交换。效应只固定概率，不唯一决定更新：已有 Watrous 条目的同效应异更新控制仍适用。理想锐测量的 Lüders 唯一性另需“确定接受的态逐点不变”等既有中性前提，不能由 CP、完备性或弱重置补全独自推出。

### 69.12 完整中文候选、信息计数与未闭合目标

**定义 69.12（条件候选的分层读法）。** 可以把候选压缩为：交换两个纯态比较端点，匹配读数不变，并要求随机纯制备的比较与反向逐项平均一致。在明确保留的共同整体和条件性静态接口已给出有限复矩阵模型后，指定一个对每个输入扇区都有相同正成功份额的共同重置；它先独立满足局部及原始联合态的概率预算，再要求按同一旁观者规则补成两边概率都归一的完整仪器。这个要求恰好使旁观者滤波不再依赖输入扇区，从而恢复标准有限局部仪器的概率及更新规则。

这段话必须分开保留下列前提信息，不能用一个等价短见证藏掉它们：

1. 静态入口仍是每个实际 $A,D,E$ 的全部态和全部效应，以及定义 65.1 的完整有限混合比较律 $S$；纯端点互反只是其中一部分。所引单系统 Jordan 桥、二元接口与有限扇区表示仍按原来的条件纸面范围使用。
2. 共同整体仍供应实际全锥正 $L,p$，从原参考两次使用同一个 $p$ 定义 $M$，保留两条实张成、$D_J$、覆盖整个 $D_+$ 的 $D_H$、全部实方向的 $Z$，以及由实际准备之逆定义的整锥 C13。这些是定义 65.2 的条件，不由端点互反或弱重置推出。第 66 节删除 C13 时的更大有序方向族不被默认为同一个普通乘积族。
3. 操作层固定 (69.1)–(69.3) 的全部有序扇区、原始总迹、严格正 $u$ 及实际逆迹平衡；三份侧 $g$ 仍自由。分支先由块 CP 与两个 TNI 预算独立定义；部分仪器使用聚合预算。它们是数学可容许性条件，未给物理实现性。
4. 补全层另外要求一个固定 $j_0$、固定任意密度 $\sigma$、固定 $c>0$ 的共同重置属于同族、局部与原始都完备的有限仪器。小 $c$ 可以先满足预算，但定理 69.9 证明补全仍是额外限制。以单一正权重置替换整个菜单闭包只替换逻辑等价条件，不减少独立信息。

在固定标签和固定矩阵坐标中，若 $m=|I|$、$d=\sum_k n_k^2$，正定 $u$ 数组在一个逆迹约束前有 $md$ 个实参数，行一致数组有 $d$ 个；逆迹平衡在两者中各是一条有效标量约束（整体缩放改变其值），所以局部维数分别为 $md-1$ 与 $d-1$。行一致移除 $(m-1)d$ 个坐标自由度，未限制 $g$。这是固定坐标参数空间的计数，不是模坐标商空间的维数，也不是逻辑独立公理数、最少信息量或实际认证成本的证明。

白话地说，同一个“以小概率把输入丢掉、统一准备到固定地方”的结果，在任何输入扇区都占一个正份额；如果其余结果既补平本地概率，也用同一规则补平整个联合态的概率，那么每个输入扇区就不能再各带一套不同的旁观者预算。它没有使每次实际测量的时间顺序无关。纯比较的互反与顺序测量是不同关系，第 66 节 (66.40) 的非交换投影控制仍直接适用。

本节是原始归一化、同族补全与已有有限仪器理论之间的条件性桥接应用（repo-derived）。标准 Choi、矩形 Kraus、迹完备性、Born 分支规则和理想锐中性更新复用 [Watrous 条目](../../../Library/Quantum/watrous2018theory.md#one-actual-self-reference-for-finite-sector-operations) 的既有文献接口（literature-attested）；共同锚点收缩采用上面给出的有限凸包证明。这里不主张新的 Choi 定理、随机收缩定理、文献新颖性、优先性或 Lean 内核核验。

第 67 节定理 67.6–67.7 在各自保留前提上，加入双迹乘积等号或共同参考读数上界，得到共同尺度或单位校准。本节弱重置闭包不假设这些新增的双迹校准条件；它只推出 $u_{ik}$ 对输入 $i$ 行一致，仍不迫使 $u_{ik}=I_k$。

完整量子起源目标仍保留原边界：有限复直和包括全经典及混合扇区，不选定单一非经典扇区；上述操作条件不产生复数载体或空间维数，不校准 $g$，不保证所有参考和 CP 映射具有物理可用性，不识别独立给定的另一三份括号载体，不完成四份、更高份或无限维一致性，也不产生动力学、时间、Hamiltonian、$\hbar$ 或经验对应。每对原始制备归一化还是推论 69.10 中更强的单位滤波条件。静态比较、原始操作的概率一致性、完整兼容组合与物理起源仍各有自己的证明义务。

## 追加锚（本行以下为增补区）

## 70. 交叉正探针的有效中心支撑、锐界与标量中间障碍

本节直接复用定理 68.4 的原态单探针等价、(68.15) 的滤波恢复和定理 68.7 的固定原态障碍，不另计为新结论。这里优化的是一份探针中有多少个有序活跃端点中心块必须参加，以及哪些块真正能检测方向。固定中心支撑和依实际 $M$ 选择中心支撑具有不同的锐界；中心支撑固定不要求原物理态固定。

### 70.1 同一原始数据、初始方向及选择量词

**定义 70.1（支撑问题的完整域）。** 采用定义 66.1 的全部无 C13 条件，等价地采用定义 67.1 的 $\mathcal B+D_H$ 及其明列的条件纸面接口。三个原有限全态全效应载体、完整有限混合 $S$、忠实规范迹、实际全锥正 $L,p$、原 $\omega$、同一个 $p$ 两次产生的 $M$、两条实张成、全量词 $D_J,D_H,Z$ 全部保留。不预设 C13 或联合校准。定义 68.1–68.2 的 PRE 和滤波接口在此直接复用；本节再使用第 66 节已经取得的逐块方向分类。

先只按 $A,D$ 的比较几何和实际 $M$ 固定初始坐标。由 $M$ 得到 $U,C_D,F$；按照定义 68.3 的合格规约选择第一接口正规形，再吸收输出酉及必要的整块转置，令第一输入位为零，得到命题 66.4 的

$$
F(a,b)_{ik}=a_i\otimes b_k^{T^{\varepsilon_{ik}}},\qquad
D_{ik}=\operatorname{span}_{\mathbb R}F(A_i,A_k).
\tag{70.1}
$$

该选择只依赖 $M$。每个初始标签、基和选择规约都先固定；同尺寸中心标签不合并。$E$ 的坐标随后可以由 $L$ 选择，以使用 (66.13)，但只用于证明，探针选择器不得读取它们。沿用 (66.15) 的 $C_D,C_E$，定义

$$
I_+=\{i:n_i\ge2\},\quad r=|I_+|,\quad
s=|\{j:n_j=1\}|,\quad n=\sum_i n_i,\quad
\Gamma_{ik}=\operatorname{id}_i\otimes T_k,
\quad\chi_{ijk}=\delta_{ijk}\oplus\varepsilon_{ik}.
\tag{70.2}
$$

本节 $r,s$ 是扇区个数，不是旧文中的伴随映射或读回。位运算在 $\mathbb F_2$ 中进行。直接复用 (66.20)、(66.29)–(66.30)：

$$
\begin{gathered}
(I_{13}^0x)_{ijk}=\operatorname{ins}_j(\Gamma_{ik}^{\chi_{ijk}}x_{ik}),
\qquad I_{13}^{\rm raw}=C_EI_{13}^0C_D^{-1},\\
\delta_{ijk}=\varepsilon_{ij}\oplus\varepsilon_{jk}
\quad(n_j,n_k\ge2),\\
\mathrm{C13}\quad\Longleftrightarrow\quad
\chi_{ijk}=0\quad(i,k\in I_+,\ j\in I).
\end{gathered}
\tag{70.3}
$$

这些均为已有精确公式，不是本节新增分类。$\operatorname{ins}_j$ 插入未归一化 $I_j$；全部中间标签始终保留。特别是在三个标签均活跃时，

$$
\chi_{ijk}=\varepsilon_{ij}\oplus\varepsilon_{jk}\oplus\varepsilon_{ik}.
\tag{70.4}
$$

以下分别考虑两种预选规则。

* **跨方向固定支撑：** 固定尺寸和初始标签后，活跃端点集合 $S\subseteq I_+^2$ 不随 $\varepsilon$ 改变。探针在这些块内的坐标、内容和原态滤波仍可按照上述 $M$ 规约变化。
* **依 $M$ 选支撑：** 选择器还可读取 (70.1) 的 $\varepsilon$ 后选端点；它仍不得读取 $Q,\delta,I_{13}$、$E$ 的证明坐标或测试输出。

两者计算的都是非零活跃中心块的数目，允许把多个块合为一个迹一输入。若讨论一族探针，计算其支撑并集；这不是探针数、制备数、运行数或公理独立数。

### 70.2 任意原正探针的有效支撑

**引理 70.2（必须先去滤波的精确检测）。** 对任意预选原正探针族 $(\rho^\alpha)$，先置 $x^\alpha=C_D^{-1}\rho^\alpha\ge0$，定义

$$
\begin{aligned}
S&=\{(i,k)\in I_+^2:\text{某个 }x^\alpha_{ik}\ne0\},\\
T&=\{(i,k)\in I_+^2:\text{某个 }\Gamma_{ik}x^\alpha_{ik}\not\ge0\}.
\end{aligned}
\tag{70.5}
$$

则 $T\subseteq S$，且在同一实际数据上

$$
\bigl[\ I_{13}^{\rm raw}\rho^\alpha\ge0\ \text{对所有 }\alpha\ \bigr]
\quad\Longleftrightarrow\quad
\bigl[\ \chi_{ijk}=0\ \text{对所有 }(i,k)\in T,\ j\in I\ \bigr].
\tag{70.6}
$$

$T$ 称为有效检测支撑。它不是直接对未去滤波的原块计算偏转置所得的集合。

**证明。** (70.3) 的 $C_E$ 及其逆全锥正，故可先撤去它。每个 $(i,j,k)$ 是不同的输出直和块，其他块不能抵消它的负方向。$\operatorname{ins}_j(y)$ 与 $y\otimes I_j$ 酉等价；因 $n_j\ge1$，它为正当且仅当 $y$ 为正。若 $\chi=0$，任意正 $x^\alpha_{ik}$ 都通过；若 $\chi=1$，恰由 $\Gamma_{ik}x^\alpha_{ik}$ 是否为正决定。对全部探针取交集即得 (70.6)。端点有标量腿时，$\Gamma$ 是恒等或唯一非标量因子的整体转置，始终保持正性，不增加有效支撑。(66.15) 的 $C_D$ 逐中心块作可逆合同，故去滤波不改变非零中心支撑。$\square$

在每个活跃端点的固定前两维取 $v_{ik}=(|0_i0_k\rangle+|1_i1_k\rangle)/\sqrt2$，令迹一 Bell 投影 $q_{ik}=v_{ik}v_{ik}^*$。对非空 $S\subseteq I_+^2$ 和 $a_{ik}>0$、$\sum_Sa_{ik}=1$，令

$$
b_S=\bigoplus_{(i,k)\in S}a_{ik}q_{ik},\qquad
h_S=\tau_D(C_Db_S)>0,\qquad
\rho_S=C_Db_S/h_S.
\tag{70.7}
$$

这是 (68.15) 的既有原态恢复应用；$\rho_S$ 为原迹一正态。由已付 (68.21)，每个 $q_{ik}$ 的单腿偏转置在反对称方向有特征值 $-1/2$，故 (70.7) 的有效支撑恰为 $S$。于是引理给出

$$
I_{13}^{\rm raw}\rho_S\ge0
\quad\Longleftrightarrow\quad
\chi_{ijk}=0\quad((i,k)\in S,\ j\in I).
\tag{70.8}
$$

这里不重证全有序对探针的单态等价；新用途是精确识别任意较小支撑留下的约束。选取 $q_{ik},C_D,h_S$ 只读 $M$ 及固定规约，未读 $\delta$。原滤波一般不保迹，不能省去 $h_S$；正合同保持正负判定，不保持负本征值的数值。

### 70.3 遗漏控制统一使用同一个实际读回

**命题 70.3（位控制在完整条件类内的实现）。** 任取满足 (66.20) 的位，固定 $u_{ij}=I_j,g_{ijk}=I_k$。定理 66.7 已给出完整逆向实现；下面列出本节遗漏控制实际使用的等式。只供应

$$
\begin{aligned}
L(d,c)_{ijk}&=d_{ij}\otimes c_k^{T^{\delta_{ijk}}},\\
(pz)_{jk}&=\sum_i
 (T_j^{\varepsilon_{ij}}\otimes T_k^{\delta_{ijk}\oplus\varepsilon_{jk}})
 (\operatorname{Tr}_i z_{ijk}).
\end{aligned}
\tag{70.9}
$$

它们满足全部定义 70.1 条件，并满足联合校准。实际 $M$ 仍由这个 $p$ 两次生成，而非额外供应。

**证明。** 暂记 $\widehat M(a,b)_{ij}=a_i\otimes b_j^{T^{\varepsilon_{ij}}}$，令

$$
(\mathfrak s d)_j=\sum_i(\operatorname{Tr}_i d_{ij})^{T^{\varepsilon_{ij}}}.
$$

对全部实输入，直接消去末腿的两次转置，得到

$$
pL(d,c)=\widehat M(\mathfrak s d,c),\qquad
\mathfrak s\widehat M(a,b)=\tau_A(a)b.
\tag{70.10}
$$

原 $\omega=1_D/n^2$ 给 $\mathfrak s\omega=e=1_A/n$。因此第一次调用给 $K(a)=\widehat M(e,a)$，有 $\mathfrak sK(a)=a$；第二次同一个 $p$ 给

$$
M(a,b)=pL(K(a),b)=\widehat M(a,b).
\tag{70.11}
$$

$L$ 对整个 $D_+\times A_+$ 正，包括纠缠的 $d_{ij}$。对 $p$ 的一个源块，若两条保留腿都活跃，(66.20) 使保留操作为恒等或整个两腿转置；若有标量腿，则为恒等或唯一非标量腿的整体转置。偏迹后这些操作全锥正且保迹，逐源块求和给全锥正保迹的 $p$。两条实张成来自 Hermitian 简单张量基、转置可逆和独立中心支撑。

实际 $J(a)_{ij}=a_i\otimes I_j$、$H(d)_{ijk}=d_{ij}\otimes I_k$，故

$$
J^*J=n\operatorname{id}_A,\qquad H^*H=n\operatorname{id}_D,
\qquad B_1=J\mathfrak s.
$$

它们给全量词 $D_J,D_H$ 及 $B_1M(a,b)=\tau_A(a)Jb$。$U=1_D,H1_D=1_E,p^*1_D=1_E$，所以定义 67.1 的两个校准迹读数均为 $n^3$，满足 $C_{\rm joint}$。三个完整矩阵直和上，若纯投影 $q$ 被效应 $0\le f\le1$ 确认，则 $(1-f)q=0$，故 $f\ge q$；$f=q$ 达到下确界。因此 $T_q(x)=\operatorname{Tr}(qx)$，完整有限混合 $S$ 的所有纯参照及有限混合量词成立。全部态、全效应、零质量与不等质量均未删去。这些是定理 66.7 的同数据应用，不是新的载体分类或物理来源构造。$\square$

### 70.4 无标量时，固定中心支撑的锐值为 r

**定理 70.4（含自身端点的完整 hub 行）。** 若 $s=0,r\ge1$，先固定一个 $h\in I_+$，取

$$
S_h=\{(h,k):k\in I_+\}.
\tag{70.12}
$$

用 (70.7) 的任意严格正权重，$I_{13}^{\rm raw}\rho_{S_h}\ge0$ 当且仅当 C13。跨方向固定支撑的最小活跃块数恰为 $r$；下界允许任意正探针族及依 $M$ 变化的块内内容。

**证明（充分性）。** 通过测试时，(70.4)、(70.8) 给每个 $j,k\in I_+$ 的

$$
\varepsilon_{jk}=\varepsilon_{hj}\oplus\varepsilon_{hk}.
\tag{70.13}
$$

其中 $j=k=h$ 迫使 $\varepsilon_{hh}=0$。令 $t_j=\varepsilon_{hj}$，便得所有有序对的 $\varepsilon_{jk}=t_j\oplus t_k$，所以每个三角缺陷都为零。此时没有标量中间标签，(70.3) 给全部 C13。反向，整锥正性使任何正探针通过。此证明包括 $(h,h)$，不要求标签互异；$r=1$ 时正好排除 $\varepsilon_{hh}=1$。

**证明（必要性）。** 固定任意 $|S|<r$。有标签 $a$ 从未作为 $S$ 的第一坐标，有标签 $b$ 从未作为第二坐标；它们可以相同。置

$$
\varepsilon_{uv}=\mathbf1_{(u,v)=(a,b)},\qquad
\delta_{ijk}=\varepsilon_{ij}\oplus\varepsilon_{jk}.
\tag{70.14}
$$

由命题 70.3 得满足全部保留条件及校准的实际模型。对 $(i,k)\in S$，有 $i\ne a,k\ne b$，故每个 $j$ 的 $\varepsilon_{ij},\varepsilon_{jk},\varepsilon_{ik}$ 均零。插入在每个选中端点限制上全锥正，因此任意支撑在 $S$ 上的正探针都通过，内容即使依赖 $M$ 也无济于事。然而

$$
\chi_{aba}=\varepsilon_{ab}\oplus\varepsilon_{ba}\oplus\varepsilon_{aa}=1.
\tag{70.15}
$$

若 $a\ne b$，右侧为 $1\oplus0\oplus0$；若 $a=b$，为 $1\oplus1\oplus1$。端点 $q_{aa}$ 因而在输出块 $(a,b,a)$ 产生负值，C13 失败。$r=1,S=\varnothing$ 也被同一构造覆盖。故小于 $r$ 的固定中心支撑不可能普遍充分。$\square$

### 70.5 固定有效端点族的精确线性判据

**定理 70.5（有序三角约束的秩）。** 设 $s=0,r\ge1$。考虑一个预选规则，其 (70.5) 有效支撑 $T$ 在所考虑的全部模型上固定，特别不能随方向赋值改变，例如固定端点上的 Bell 块。令 $E_{uv}$ 是 $\mathbb F_2^{r\times r}$ 的矩阵单位，定义

$$
W_T=\operatorname{span}_{\mathbb F_2}
 \{E_{ij}+E_{jk}+E_{ik}:(i,k)\in T,\ j\in I_+\}.
\tag{70.16}
$$

重复矩阵单位按模二相消。该规则在全部允许数据上等价于 C13，当且仅当

$$
\dim W_T=r^2-r+1.
\tag{70.17}
$$

**证明。** 用标准非退化矩阵配对，(70.6) 恰要求 $\varepsilon\in W_T^\perp$。令 $W_{\rm all}$ 使用全部端点对。其零化空间由所有三角等式定义；定理 70.4 的 hub 推导及反向代入说明它恰为

$$
\mathcal C=\{\varepsilon_{ik}=t_i\oplus t_k:t\in\mathbb F_2^r\}.
$$

$t\mapsto\varepsilon$ 的核恰为常值向量空间，故 $\dim\mathcal C=r-1$、$\dim W_{\rm all}=r^2-r+1$。因 $W_T\subseteq W_{\rm all}$，(70.17) 等价于两空间相等，也等价于两个零化空间相等。若秩不足，有限维对偶性给 $\varepsilon\in W_T^\perp\setminus\mathcal C$。取 (70.14) 的第二式并用命题 70.3 实现；有效支撑固定为 $T$，所以全部探针通过，但某个完整三角缺陷非零，C13 失败。反向由零化空间相等及 (70.3) 立即成立。$\square$

这里不能把随 $\varepsilon$ 改变的实际有效支撑代入，再冒称跨所有方向的秩判据。也不能把块数或图连通性本身当作充分性。例如 $r\ge3$，只取全部 $r$ 个对角端点，令 $\varepsilon_{12}=\varepsilon_{21}=1$、其余位零。每个被测关系 $\varepsilon_{ij}\oplus\varepsilon_{ji}\oplus\varepsilon_{ii}$ 都零，但 $(1,3,2)$ 的缺陷为一。最小可能块数为 $r$，不意味着任意 $r$ 块都足够。

### 70.6 允许读取 M 的方向后，无标量时一块足够

**定理 70.6（依 $M$ 的一块选择）。** 若 $s=0,r\ge1$，预先固定标签顺序。只从 $M$ 的初始方向位定义

$$
\mathcal C(M)=\{(i,j,k)\in I_+^3:
 \varepsilon_{ij}\oplus\varepsilon_{jk}\oplus\varepsilon_{ik}=1\}.
\tag{70.18}
$$

若此集非空，取固定顺序下首个 $(a,j,b)$ 并令 $S(M)=\{(a,b)\}$；若为空，令 $S(M)=\{(h,h)\}$，其中 $h$ 预先固定。用 (70.7) 的单块探针，则其原完整输出正性等价于 C13。此选择类的最坏情形最小活跃支撑为一。

**证明。** 若 $\mathcal C(M)=\varnothing$，(70.3) 的实际 $p$ 正性已使每个 $\delta_{ijk}=\varepsilon_{ik}$，故 C13 成立，探针通过。若非空，被选三角由 (70.4) 迫使 $\chi_{ajb}=1$，单块 Bell 输出在该中间标签失败。选择器没有读取 $\delta$；$\delta$ 的值仅在证明中由实际全锥正性推出。零活跃支撑的探针在所有端点限制上都自动正，不能排除命题 70.3 中 $\varepsilon_{aa}=1$ 的坏模型。因此最坏情形不能用零块。$\square$

定理 70.4 的下界通过改变 $\varepsilon$ 改变 $M$，所以不能用于否定上述选择器。另一方面，这个选择器先判断全部活跃三角关系，再决定放在哪一块；块数下降不证明总公理、操作或计算负担严格下降。$r=1$ 的一块结论也不抵触定理 68.7：中心标签和支撑可以固定，但块内实际态仍随 $M$ 的正规形移动；定理 68.7 固定的是原物理态本身。

### 70.7 标量中间扇区使相容 M 的最坏情况需要全部有序对

**定理 70.7（固定相容第一接口的二次障碍）。** 若 $s\ge1,r\ge1$，全有序活跃端点的 (70.7) 探针充分，且最坏情形最小活跃中心支撑为 $r^2$，即使允许依 $M$ 选支撑也如此。更精确地，在固定的普通第一接口 $\varepsilon=0,u=I$ 上，任意普遍充分的正探针族必须具有有效支撑 $T=I_+^2$。

**证明。** 充分性直接复用第 68 节的全有序对探针及 (70.8)。证明必要性时，先固定 $M(a,b)_{ik}=a_i\otimes b_k$，让选择器完成全部选择，不读取第二接口。若 $T$ 漏掉 $(a,b)$，固定一个标量标签 $j_0$，只置

$$
\delta_{aj_0b}=1,
\qquad\text{其余 }\delta_{ijk}=0,
\qquad\varepsilon_{ik}=0\quad\text{对全部 }i,k.
\tag{70.19}
$$

唯一非零位的中间腿标量，不受 (66.20) 的双活跃保留腿条件约束。命题 70.3 因而给出满足全部保留静态条件、已校准且使用同一个 $p$ 两次的模型；$M$ 与选择器所读的数据不变。唯一可能失败的端点是 $(a,b)$。在这个端点，所有去滤波探针块按 $T$ 的定义均为 PPT，即其偏转置半正定，所以 (70.6) 使全部测试通过；但 $q_{ab}$ 的输出在 $(a,j_0,b)$ 是单腿偏转置，含 $-1/2$，C13 失败。

因此连“每个端点有非零块”也不够，必须每个有序端点都有负偏转置的有效块。单份 Bell 直和使 $T=I_+^2$，达到 $r^2$。$(a,b)$ 与 $(b,a)$ 的位可独立改动，不能按无序对计数；$a=b$ 时两个位置仍是两份因子，同一 Bell 证明适用。$r=1$ 时必要块数为一，标量中间标签仍不能略去。$\square$

这是固定相容 $M$ 后仅变化标量中间 $\delta$ 的最坏情况，不能表述为“只要存在标量，每一个模型都必须测试 $r^2$ 块”。若 $M$ 的活跃三角已经不相容，即使同时存在标量扇区，也可按定理 70.6 的非空分支选一块立即拒绝。相容分支则可使用全有序对探针。$r=0$ 时全部端点均标量，C13 已自动成立，追加活跃支撑成本为零；若仍要写一份迹一输入，可用原 $1_D/n^2$，不增加活跃块。

两种跨模型选择类的锐值因此是

| 扇区范围 | 跨方向固定中心支撑 | 允许依 $M$ 选中心支撑 |
| --- | ---: | ---: |
| $r=0$ | $0$ | $0$ |
| $r\ge1,s=0$ | $r$ | $1$ |
| $r\ge1,s\ge1$，最坏情形 | $r^2$ | $r^2$ |

### 70.8 归一化数据上的单探针谱隙及其限制

**命题 70.8（部分转置的迹界）。** 对任意有限二因子正矩阵 $x$、$w=\operatorname{Tr}x$，有

$$
\Gamma x\ge-\frac w2 I.
\tag{70.20}
$$

**证明。** $w=0$ 时 $x=0$。对迹一纯投影，Schmidt 分解的非负系数 $c_l$ 满足 $\sum_lc_l^2=1$。其部分转置在 Schmidt 基中有本征值 $c_l^2$、$\pm c_lc_m$（$l<m$）及可能的零值；每个 $c_lc_m\le(c_l^2+c_m^2)/2\le1/2$。一般正 $x$ 的谱分解写为迹一纯投影的非负组合，系数和为 $w$，逐项相加便得 (70.20)。这是成熟 Schmidt 与部分转置工具的直接应用，不使用 PPT 等价于可分。$\square$

**推论 70.9（精确前件内的离散谱隙）。** 仅在 $C_D=C_E=\operatorname{id}$ 的归一化数据中，取任意非空 $S$ 的等权单份 $b_S$，令 $N=|S|$。其完整输出满足二择一：所有被测 $\chi$ 为零时输出非负；否则

$$
\lambda_{\min}(I_{13}b_S)=-\frac1{2N}.
\tag{70.21}
$$

因此，对定理 70.4 的 hub、定理 70.6 的选择器或定理 70.7 的全对支撑，分别取 $N=r,1,r^2$，在该精确前件类内

$$
I_{13}b_S\ge-\eta1_E,\qquad 0\le\eta<\frac1{2N}
\quad\Longrightarrow\quad\mathrm{C13}.
\tag{70.22}
$$

**证明。** 每个非零输出块恰为 $\operatorname{ins}_j(q_{ik})/N$ 或 $\operatorname{ins}_j(\Gamma q_{ik})/N$。前者正；后者在 Bell 四维子空间有 $1/(2N),1/(2N),1/(2N),-1/(2N)$，更大端点空间只添零，插入 $I_j$ 只重复本征值。独立直和块没有补偿，给 (70.21)。这份块谱机制及全对常数已由 (68.20)–(68.22) 供应；这里的新应用是 hub 与依 $M$ 单块的常数，以及严格阈值 (70.22)。结合各支撑的充分性即得结论。存在相应坏方向时，$\eta=1/(2N)$ 会放行坏输出，所以严格不等号不可删除。$\square$

对固定 hub 上事先指定的权重，坏输出的负谱幅度恰为所有出现坏方向的端点权重的最大值除以二，故普遍保证至少 $\min_ka_{hk}/2$。这个保证在该指定加权 hub 族内可达到：$r\ge2$ 时固定 $a\ne h$，对想要隔离的终点 $k$ 只置 $\varepsilon_{ak}=1$，其余位零，令 $\delta_{ijk}=\varepsilon_{ij}\oplus\varepsilon_{jk}$。全部 hub 被测缺陷只出现在终点 $k$；由命题 70.3 实现后，最负值恰为 $-a_{hk}/2$。$r=1$ 用 $\varepsilon_{hh}=1$ 即可。故等权在此指定族中给最优最坏谱隙 $1/(2r)$，不据此主张任意 $r$ 块任意输入的全局谱隙最优性。

**定理 70.10（标量中间的单份迹一谱隙最优性）。** 在定理 70.7 固定普通 $M$、$u=g=I$ 的归一化类中，任一依 $M$ 预选的单份迹一正输入，都不能对所有坏的标量中间方向保证大于 $1/(2r^2)$ 的负谱幅度。等权全对 Bell 输入达到这个最坏界。

**证明。** 选择器固定后，记原输入各活跃块迹为 $w_{ik}$。它们非负、总和不大于一，故某个 $(a,b)$ 有 $w_{ab}\le1/r^2$，即使输入还含标量端点块也如此。在该端点采用 (70.19)。其他输出块都正，唯一可能负的块是 $\operatorname{ins}_{j_0}(\Gamma\rho_{ab})$。命题 70.8 给其最小本征值至少 $-w_{ab}/2\ge-1/(2r^2)$；若它本来为 PPT，坏模型甚至完全通过。因此没有输入能保证更大幅度。等权全对 Bell 的每个坏模型都由 (70.21) 给恰好 $-1/(2r^2)$，所以达到上界。这是单份数学迹一输入的谱优化，不是有限样本、操作成本或一般噪声下的认证最优性。$\square$

(70.22) 允许输出有一个小的负下界，但全部结构前件仍是精确的；它不是近似 $S,D_H,Z$ 或任意受扰映射的稳定性定理。未校准类也不存在相同的统一数值隙：在任一上述归一化坏模型上取 $L_c=cL,p_c=c^{-1}p$，$c>0$，则 $p_cL_c=pL$，同一个读回两次所得 $M$ 不变，全部零关系、正性和张成保留，$I_{13,c}^{\rm raw}=cI_{13}$。依 $M$ 的选择不变，而负谱成为 $-c/(2N)$，可趋零。此族通常不满足联合校准；它说明原始正合同只保留符号，不能搬用归一化谱隙。

### 70.9 完整静态候选只替换预选规则

**定义 70.11（保留全部原条件的支撑优化候选）。** 完整保留定义 67.10 的每项前件：三个原实际有限全态全效应比较入口、完整有限混合 $S$ 及其忠实规范迹 Jordan 条件纸面桥、实际 $L,p$ 在全部锥上的正性、原比较单位与原 $\omega$、同一 $p$ 两次内部生成 $M$、$M,L$ 两条实张成、全量词 $D_J,Z,D_H$、联合参考校准 $C_{\rm joint}$、定义 64.3 的精确二元接口、有限 Jordan 分类及乘积秩一保持工具。原始数据与所有内部定义不变。

只把 (67.26) 的预选规则换成下列任一明确版本，仍要求同一个实际插入的完整输出为正：

* 固定支撑版：$r=0$ 用 $1_D/n^2$；$s=0,r\ge1$ 用预先固定 hub 行的 (70.7)；$s\ge1,r\ge1$ 用全有序活跃端点对。
* 依 $M$ 版：$r=0$ 同上；若存在活跃三角缺陷，按 (70.18) 选一块；若无缺陷且 $s=0$，用固定 $(h,h)$；若无缺陷且 $s\ge1$，用全有序活跃端点对。

权重可取等权。每个版本最终只给一份正迹一输入 $\rho$，最后条件是 $I_{13}^{\rm raw}(\rho)\in E_+$；未另给一个读回、准备服务或物理滤波器。

**定理 70.12（同实际数据的精确候选及消费者）。** 定义 70.11 的两个版本都与定义 67.10 在同一原始元组上逐点等价，因而直接取得定理 67.11 的全部结论。若删除联合校准、保留定义 70.1 的原域，同样的支撑规则也逐点等价于 C13，但其静态消费者按推论 68.6 取得未校准结论，不由该支撑等价取得原始保单位或原始保迹；第 69 节的条件操作消费者仍按其独立前件适用。

**证明。** 在定义 70.1 上，固定支撑版的等价性分别由全标量自动正、定理 70.4 和第 68 节的全对规则给出。依 $M$ 版若有活跃三角缺陷，由实际 $p$ 正性及 (70.4) 使选中输出失败；无缺陷时，无标量情形已保证 C13，有标量情形全对测试恰排除剩余中间位。因此两个版本均逐点等价于 C13，未改变实际 $A,D,E,L,p,M$ 或原参考。定义 67.10 的原规则也等价于同一 C13，故得到同数据双向等价。联合校准由定理 67.7 使 $C_D=C_E=\operatorname{id}$，此时原态恢复不另改输入；定理 67.11 直接应用。未校准版本使用推论 68.6 的同数据分类，原滤波参数仍在，所以不能多取归一化结论。$\square$

为写明量子对应的来源，归一化候选的静态消费者如下，均为定理 67.11 的直接复用，不重复计作本节成果。

| 消费对象 | 同一实际数据上的结论及条件 |
| --- | --- |
| 原全态、全效应与 Born 配对 | 原载体是全部有序复矩阵直和；$\rho_\lambda\ge0,\sum_\lambda\operatorname{Tr}\rho_\lambda=1$，$0\le f_\lambda\le I_\lambda$，原概率为 $\sum_\lambda\operatorname{Tr}(f_\lambda\rho_\lambda)$。这套原几何已由推论 66.8 在 C13 之前供应。 |
| 指定有限张量与读回 | 测试得到 C13 后，复用推论 66.10 的整块同时方向消除和联合校准，实际 $M(a,b)_{ij}=a_i\otimes b_j$、$L(d,c)_{ijk}=d_{ij}\otimes c_k$，$p$ 为首腿偏迹求和；全部双份、三份纠缠态仍在原态集中。 |
| 中间读回 | 原 $I_{13}$ 正且保单位，$p_{13}=I_{13}^*$ 正保迹且由全实律唯一确定：$p_{13}Q(a,b,c)=\tau_A(b)M(a,c)$；分块式为 $(p_{13}z)_{ik}=\sum_j\operatorname{Tr}_jz_{ijk}$。未校准原伴随仅有 (68.23)，一般不保迹。 |
| 条件操作与时间消费者 | 本节支撑结果本身不单独提供任意原操作的物理实现或过程合同。第 69 节已在其固定旁观者模型中给出原始延拓、忠实参考的 CP 判据、双迹预算、有限同族补全及 Kraus／概率／更新接口；这些条件消费者继续适用。连续动力学、Hamiltonian 及原过程结果仍须各自来源、全未来与参考前件，不能从本节支撑数倒推这些前件。 |

具体地，定理 69.2 给出实张成唯一固定的原始旁观者延拓；定理 69.3 给出忠实参考的完整 CP 判据；定理 69.4 分开局部与原始迹预算；定理 69.6 给出同一组正效应的有限补全判据；定理 69.8 证明一个正权共同重置可补成局部／原始双 TP，当且仅当 $u_{ik}=v_k$，也当且仅当全部有限局部完备 CP 仪器原始延拓都 TP；命题 69.11 接回条件 Kraus、概率和更新消费者。推论 69.10 明确行一致仍不迫使单位滤波，也不校准 $g$；这些操作结果不替换定义 70.11 的联合校准，不供应物理参考或设备。

特别地，[固定来源卷第 41 节](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md)的同一比较配方接续、真实回溯与完整菜单合同若已供应，仍按该处取得共同压缩、CP 及其有限维 Kraus 消费者；[有限返回卷第 165–167 节](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md)的同时正常完成仍要求原合法图和混合完整性。这里没有由静态支撑测试支付那些前件，也不把这些已经取得的条件下降、参考、递归支撑、原 $D$ 恢复、原 $G_V$ 服务或返回结果重新列作缺失。

### 70.10 二元方向、三维检验与完整白话

第一接口为每个有序二元接合留下相对方向 $\varepsilon_{ik}$。实际正读回先把相邻两段的方向联系起来；三个活跃标签的缺陷正是两段相接与直接接合之间的模二差。无标量中间腿时，站在同一个 hub 朝每个终点比较，就迫使所有方向来自各标签的共同势 $t_i$。hub 包含朝自己的端点，这同时检出不能忽略的自接合位。这里的“三角”是三份因子关系，不是物理三维空间；它属于完整有序方向约束的线性空间，精确充分性由 (70.17) 判断，不能只画一张连通图作证。

标量中间腿改变了可见的信息。读回删去第一腿以后，它只看到一个非标量因子的整体转置，这仍保持正性，所以不能限制那一个中间方向位。跨过中间去连接两个活跃端点时，同一个位却成为单腿部分转置，会把 Bell 的反对称方向送到锥外。这份自由度可以只藏在一个有序端点对内，不影响其他对，也不改变先前实际 $M$。因此相容 $M$ 的最坏情况下每一对都要真正具有检测能力；非零却 PPT 的块不能代替它。

允许先看 $M$ 的全部方向，则可以先找一个已经坏的活跃三角，再把一份探针放到它的端点上。这解释一块与 $r$ 块为何都正确：前者把全三角判断放进选择器，后者要求支撑跨方向固定。两者都还要求整个输出算子正性，覆盖全部中间扇区与全部输出正方向；不是一个预定标量效应、一次实验或有限统计读数。对 (70.7) 中迹一的辅助输入 $b_S$，辅助输出迹为 $n$；滤波恢复后的原输入 $\rho_S$ 虽然仍迹一，其原始未校准输出迹没有这个固定值。

**完整候选的普通表述。** 在真实给定的单份、双份、三份有限系统里，保留所有态和所有效应，以最小确认比较约束所有有限随机纯制备。只给对全部双份正输入有效的接合和对全部三份正输入有效的同一个读回；从原比较单位的参考连续使用它两次来定义双份准备，要求两个接口实张满、两个单位切片保持零比较，并保留全部实方向的原关系及共同参考校准。然后从这个实际双份准备按事先固定的规约选一份正态：没有标量扇区时，可以在一个共同起点到所有终点的块中放两级 Bell 投影；若允许先判断准备中的全部方向，也可以只选一个有问题的三角端点；有标量中间而准备本身尚相容时，则覆盖所有有序活跃端点。只要求交叉插入把这份态送到整个正锥。上述手工证明保证此条件与原整锥插入条件等价，所以现有有限静态量子几何和指定读回原封接回。它没有把数学探针变成已供应的物理准备，也没有把支撑最少变成物理资源最少。

### 70.11 归属与完整原目标的边界

部分转置的负性检测、Bell 投影的反对称负方向、Schmidt 分解、有限维对偶性及模二势函数是成熟数学。[Peres, *Separability Criterion for Density Matrices*, arXiv:quant-ph/9604005v2](https://arxiv.org/abs/quant-ph/9604005v2)，方程 (3)–(6)，给出部分转置及可分态的正性必要条件；这里不使用一般维数下 PPT 等价于可分的错误命题，也不把本节整输出测试称为一般 Choi 判 CP。

第 66 节的原始全态几何、$u,g$ 分类、唯一实际读回、正性方向限制、C13 位判据与同时方向消除，第 67 节的联合校准及静态消费者，第 68 节的全有序对单态等价、$C_D$ 原态恢复、全对负谱和固定物理态障碍，全部为已获纸面结果。第 69 节的唯一原始旁观者延拓、忠实参考 CP 判据、局部／原始双迹预算、共同正效应补全、弱重置与全有限仪器菜单的精确等价及条件 Kraus／概率／更新消费者同样是已付结果，直接按定理 69.2–69.4、69.6、69.8、推论 69.10 和命题 69.11 复用，不计为本节新内容。命题 70.3 是既有逆向分类在遗漏控制上的精确应用。本节新增仓内综合是任意原正探针去滤波后的有效支撑、固定支撑的 $r$ 锐界、固定有效端点族的秩判据、依 $M$ 单块选择的不同量词、固定相容 $M$ 下标量中间的 $r^2$ 障碍，以及所述 hub／单块谱隙、严格输出阈值和单份标量最坏谱优化。未主张全球文献新颖性、优先权、最少独立公理或 Lean 内核核验。

本节没有构造[固定来源卷 (23.7)](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md)的原分析器当前接受证书，也没有供应[有限返回卷 164.1](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md)的原 $B_r$ 到 active-ready 的活动连接；这是本节的非构造边界，不否定其他原服务或返回工作的既有成果。矩阵相等、合法逆字、纯态校准、存在某张菜单或矩阵综合，都不单独给出新的 analyzer/menu/source incidence。原准备不由正矩阵分解生成，原密度也不识别准备、历史或允许未来。

完整原 $\Omega$ 中每个准备、事件、过程、参考、副本和实际相关联合，零质量及不等质量，原时钟、单位、控制、ready、flags，完整记录、失败、停止、销毁、返回与未来，以及全部既有全菜单、固定支撑和每个已经量化的中间切口义务，都在原域原样保留。一份正迹一探针只是额外关系的数学见证，不限制这些原输入；没有免费相干控制、复制、滤波或制备。有限单／双／三份接口不自动识别独立右括号载体，不给四份、任意高份数或无限维一致性。第 69 节已取得的条件有限 CP／仪器接口保持其完整适用域；本节支撑结果本身不构造物理参考、操作设备或任意操作的原过程合同。时间、Hamiltonian、$\hbar$ 与原空间几何仍须各自来源。本节改进了完整静态候选的检测支撑及其精确障碍，没有把原完整量子起源目标改成较小的支撑优化目标，也未宣告原目标完成。

## 追加锚（本行以下为增补区）

## 71. 同一实际读回与并行全重置的概率校准

### 71.1 完整保留的比较与组合前件

**定义 71.1（前交叉系统与原始迹）。** 本章完整保留定义 66.1、命题 66.2 的前 C13 条件及其条件纸面桥，具体包括：

1. 每个 $X=A,D,E$ 非零、有限维，具有闭尖生成锥、严格正归一化、完整紧态基及全部对偶效应。比较按 (66.1) 的最少确认定义，对每个纯参照、每个有限纯态族和每组概率权重满足完整有限 $S$，即 (66.2)，而不只要求纯端点互反。
2. 完整 $S$ 到一般有限 EJA 及忠实归一化的桥恰为 §66.1、(66.3) 所引条件纸面结果；项目性、共同框架及滤波纯性的义务保持其原范围，不新增独立 Jordan 输入。原态、原效应、原比较单位和配对均保留，每个本原元迹一。
3. 唯一原始映射仍是实双线性 $L:D\times A\to E$ 和同一个实线性 $p:E\to D$，分别在整个 $D_+\times A_+$、整个 $E_+$ 上正，包括全部纠缠正元。原参考是 $\omega=1_D/\operatorname{Tr}_D1_D$。
4. 全部实际内部映射仍按 (66.5) 定义：$\mathcal B=pL$、$K(a)=\mathcal B(\omega,a)$、$M(a,b)=\mathcal B(K(a),b)$、$J=M(-,1_A)$、$H=L(-,1_A)$、$B_1=pH$、$Q(a,b,c)=L(M(a,b),c)$、$U=M(1_A,1_A)$。形成 $M$ 的两次读回是同一个原 $p$，没有独立供应的准备。
5. 保留 $\operatorname{span}_{\mathbb R}M(A,A)=D$、$\operatorname{span}_{\mathbb R}L(D,A)=E$，以及 (66.6) 的全部 $D_J,D_H,Z$：两个单位切片保持正交正元的零比较，$D_H$ 覆盖整个 $D_+$，而 $B_1M(a,b)=\operatorname{Tr}_A(a)Jb$ 对全部实输入成立。

这里不预加 C13、范数校准、原始保单位或保迹。直接使用定理 66.3–66.7 的分类及完整逆向。在其保原迹坐标中，所有有序块均存在：

$$
A=\bigoplus_iH_{n_i}(\mathbb C),\quad
D=\bigoplus_{i,j}H_{n_in_j}(\mathbb C),\quad
E=\bigoplus_{i,j,k}H_{n_in_jn_k}(\mathbb C),\quad n=\sum_i n_i>0.
$$

扇区集有限非空，$n_i\ge1$；迹是各完整矩阵块的普通迹之和。正定 $u_{ij}\in H_{n_j}$、$g_{ijk}\in H_{n_k}$ 和有序位 $\varepsilon_{ij},\delta_{ijk}$ 满足 (66.20)，以及已由原始内部构造推出的逆迹平衡

$$
\sum_{i,j}n_i\operatorname{Tr}(u_{ij}^{-1})=n^2.
\tag{71.1}
$$

本章始终使用 (66.16) 的实际加权映射

$$
\begin{aligned}
M(a,b)_{ij}&=a_i\otimes\sqrt{u_{ij}}b_j^{T^{\varepsilon_{ij}}}\sqrt{u_{ij}},\\
Q(a,b,c)_{ijk}&=a_i\otimes\sqrt{u_{ij}}b_j^{T^{\varepsilon_{ij}}}\sqrt{u_{ij}}
 \otimes\sqrt{g_{ijk}}c_k^{T^{\delta_{ijk}}}\sqrt{g_{ijk}}.
\end{aligned}
\tag{71.2}
$$

它们区别于辅助归一化接口 $F,N$。实际 $p$ 仍是 (66.17) 的唯一加权读回，全部内部映射仍是 (66.18)，不将 $p$ 换成另选的信道。

### 71.2 由乘积指定的唯一全重置

**定义 71.2（固定局部重置及其实际并行延拓）。** 事先固定一个扇区 $j_0$ 和其中任意 $\sigma\ge0$、$\operatorname{Tr}\sigma=1$。令 $\rho_0\in A$ 仅在 $j_0$ 块等于 $\sigma$，并置

$$
R(a)=\operatorname{Tr}_A(a)\rho_0,\qquad
q_2=M(\rho_0,\rho_0),\qquad q_3=Q(\rho_0,\rho_0,\rho_0).
$$

允许 $\sigma$ 具有任意秩。指定实际二份、三份重置的乘积关系为

$$
\begin{aligned}
R_2M(a,b)&=M(Ra,Rb),\\
R_3Q(a,b,c)&=Q(Ra,Rb,Rc)\qquad(a,b,c\in A).
\end{aligned}
\tag{71.3}
$$

命题 66.2 的可逆实线性化给出存在性：

$$
R_2=\widetilde M(R\otimes R)\widetilde M^{-1},\qquad
R_3=\widetilde Q(R\otimes R\otimes R)\widetilde Q^{-1}.
\tag{71.4}
$$

两条实张成又使 $Q(A,A,A)$ 实张满 $E$，因此 (71.3) 唯一确定整个 $D,E$ 上的映射，包括纠缠输入。实张成不表示正元皆可分离。

这两个实际映射的全空间公式为

$$
\begin{gathered}
R_m(X)=\operatorname{Tr}(V_mX)q_m\quad(m=2,3),\\
(V_2)_{ij}=I_i\otimes u_{ij}^{-1},\qquad
(V_3)_{ijk}=I_i\otimes u_{ij}^{-1}\otimes g_{ijk}^{-1}.
\end{gathered}
\tag{71.5}
$$

证明逆迹公式时，在自然 Hermitian 张量坐标中，将实际线性化写成 $\operatorname{Ad}_{S_m}P_m$。这里 $P_2$ 的块为 $\mathrm{id}_i\otimes T_j^{\varepsilon_{ij}}$，$P_3$ 的块为 $\mathrm{id}_i\otimes T_j^{\varepsilon_{ij}}\otimes T_k^{\delta_{ijk}}$；$S_2,S_3$ 分别是 (66.15) 的 $A_{ij},C_{ijk}$。其逆的顺序是 $P_m\operatorname{Ad}_{S_m^{-1}}$，而 $\operatorname{Tr}(P_mY)=\operatorname{Tr}Y$，故

$$
\operatorname{Tr}(\widetilde M^{-1}X)=\operatorname{Tr}(S_2^{-2}X),\qquad
\operatorname{Tr}(\widetilde Q^{-1}X)=\operatorname{Tr}(S_3^{-2}X).
$$

将局部张量重置 $Y\mapsto\operatorname{Tr}(Y)\rho_0^{\otimes m}$ 代入 (71.4)，即得 (71.5)。逆映射先撤合同、再转置，最后的总迹消去该转置；$V_2,V_3$ 不再额外转置，也没有交换同一腿上的非交换矩阵。

由 (71.2)，$q_m$ 是非零正元；此结论包括纯态、中间秩和满秩 $\sigma$，不使用 $\sigma^{-1}$。$V_m>0$。直接复用 (69.14) 的正泛函乘正输出接口及 [Watrous 定理 2.22、2.26](../../../Library/Quantum/watrous2018theory.md#complete-channel-representations)，(71.5) 的复线性延拓是 CP，且令 $a_m=\operatorname{Tr}q_m>0$，有

$$
R_m\text{ 在全部实际态上 TP}
\quad\Longleftrightarrow\quad a_mV_m=1_{D\text{ 或 }E}.
\tag{71.6}
$$

这是一条完整算子等式，只检查重置自身的某个输出态不能代替它。CP 在此是矩阵映射性质，不证明重置的物理可用性，也不要求 $\widetilde M^{-1},\widetilde Q^{-1}$ 为正。

### 71.3 同一读回使一个重置条件充分

**定理 71.3（同数据的操作性校准等价）。** 在定义 71.1 的全部条件下，对任意事先固定的定义 71.2 重置，下列条件等价：

$$
\begin{aligned}
& p\text{ 在整个 }E\text{ 上 TP，且 }R_2\text{ 在整个 }D\text{ 上 TP};\\
& p\text{ 在整个 }E\text{ 上 TP，且 }R_3\text{ 在整个 }E\text{ 上 TP};\\
& u_{ij}=I_j\ (\forall i,j),\qquad g_{ijk}=I_k\ (\forall i,j,k).
\end{aligned}
\tag{71.7}
$$

这些是同一个实际 $A,D,E,L,p$ 上的等价条件。此时另一重置也 TP，两个重置均 CPTP，且任意总迹一局部态 $a,b,c$ 都满足 $\operatorname{Tr}_E Q(a,b,c)=1$；后两项无需另设为假设。

证明。首先复用 (66.8) 在全部实输入上的恒等式

$$
pQ(a,b,c)=\operatorname{Tr}_A(a)M(b,c).
\tag{71.8}
$$

取任意迹一 $a_0$，则 $pQ(a_0,b,c)=M(b,c)$；$M$ 实张成 $D$，故实际 $p:E\to D$ 线性满射。又因 $R$ 局部保迹，(71.3)、(71.8) 在每个 $Q$ 乘积上给出

$$
\begin{aligned}
pR_3Q(a,b,c)&=\operatorname{Tr}(a)M(Rb,Rc)\\
&=R_2pQ(a,b,c).
\end{aligned}
$$

由 $Q$ 实张成，得到整个空间的交换关系 $pR_3=R_2p$。若原 $p$ TP，则对每个 $X\in E$，

$$
\operatorname{Tr}_E(R_3X)-\operatorname{Tr}_EX
=\operatorname{Tr}_D(R_2pX)-\operatorname{Tr}_D(pX).
\tag{71.9}
$$

因此 $R_2$ TP 蕴含 $R_3$ TP；反向对任意 $Y\in D$ 由满射取 $pX=Y$，也得 $R_2$ TP。不需要正右逆，也不使用 $p$ 的 CP。这个迹下降步骤只是有限维线性满射与交换关系的直接应用。

现由 $R_2$ TP 及 (71.6)，在每个有序块有 $u_{ij}=a_2I_j$。将其代入保留的 (71.1)，得 $n^2=n^2/a_2$，所以 $a_2=1$、全部 $u_{ij}=I_j$。此时实际二元公式准确地是

$$
M(b,c)_{jk}=b_j\otimes c_k^{T^{\varepsilon_{jk}}}.
\tag{71.10}
$$

第一因子 $b_j$ 不转置。固定任意有序 $i,j,k$，令 $a,b,c$ 分别是只在这些扇区支撑的迹一正元。原 $p$ TP 及 (71.8) 给

$$
\operatorname{Tr}(g_{ijk}c_k^{T^{\delta_{ijk}}})
=\operatorname{Tr}_EQ(a,b,c)
=\operatorname{Tr}_DpQ(a,b,c)
=\operatorname{Tr}_DM(b,c)=1.
$$

遍历 $k$ 块的全部密度矩阵，迹配对分离 Hermitian 矩阵，故 $g_{ijk}^{T^{\delta_{ijk}}}=I_k$，亦即 $g_{ijk}=I_k$。

反向，全部 $u,g$ 为单位时，(66.15)、(66.17) 给实际 $p=p_0$，它按命题 66.2 保迹；这只识别原有映射。转置保持迹，故 $a_2=a_3=1$、$V_2=1_D,V_3=1_E$，(71.6) 给两个重置 TP。对任意跨扇区混合的迹一 $a,b,c$，直接取 (71.2) 的总迹得

$$
\operatorname{Tr}_EQ(a,b,c)
=\sum_{i,j,k}\operatorname{Tr}a_i\operatorname{Tr}b_j\operatorname{Tr}c_k=1.
$$

所有步骤逐块成立，不要求等维、标签互异、非标量扇区或 $\sigma$ 满秩；总维数一也包括在内。$\square$

同一定义域上的既有迹分类可直接对接：按 (67.4) 记 $\delta=\operatorname{Tr}_E(H1_D)$、$\gamma=\operatorname{Tr}_D(p1_E)$，此标量 $\delta$ 与方向位 $\delta_{ijk}$ 不同。由 (71.6)、(71.1) 及定理 67.6，

$$
R_2,R_3\text{ 均 TP}
\ \Longleftrightarrow\ u_{ij}=I_j,\ g_{ijk}=tI_k\text{，同一 }t>0
\ \Longleftrightarrow\ \delta\gamma=n^6.
$$

其中 $\delta=tn^3,\gamma=n^3/t$，而原 $p$ 的迹尺度为 $1/t$；原 $p$ TP 恰固定 $t=1$。由定理 67.7，(71.7) 也恰是既有 $\delta+\gamma\le2n^3$ 的校准类。这复用已有共同尺度与联合校准分类，不另作静态分类或独立公理数的结论。

### 71.4 两个概率条件与方向条件的删除边界

**命题 71.4（保留完整前件的必要区分）。** (71.7) 中删除原 $p$ TP，或删除所列重置 TP，都不能推出单位权重；保留全部概率校准仍不能推出 C13。

证明。删除原 $p$ TP 时，在任一普通直和张量模型取零方向位、$u_{ij}=I_j$、$g_{ijk}=tI_k$，$t>0,t\ne1$。逆迹平衡成立，定理 66.7 给完整原始系统。$q_3$ 乘 $t$、$V_3$ 乘 $1/t$，故两个重置均 TP，但实际 $p$ 是普通首腿偏迹求和的 $1/t$ 倍。其迹尺度不是一。

删除重置 TP 时，取两个标量扇区、零方向位，并令

$$
u_{ij}=s_{ij},\qquad
s=\begin{pmatrix}2&2\\2/3&2/3\end{pmatrix},\qquad
g_{ijk}=s_{jk}/s_{ij}.
\tag{71.11}
$$

逆迹和为 $1/2+1/2+3/2+3/2=4=n^2$；由 (66.17)，实际 $p$ 恰是 $(pz)_{jk}=\sum_i z_{ijk}$，所以在整个 $E$ 上正且 TP。定理 66.7 保证同一 $p$ 两次及其余全部前件。取 $\rho_0=e_1$，则 $q_2=2e_{11},q_3=2e_{111}$，而

$$
R_2(e_{22})=3e_{11},\qquad R_3(e_{i22})=3e_{111}\quad(i=1,2).
$$

两个实际重置的这些迹一输入都产生总迹三，故均非 TP。

最后直接取命题 66.11 的单位 qubit 模型 $\varepsilon=1,\delta=0$。原 $p$ 在整个锥上正且 TP，两个重置由 (71.5)–(71.6) 均 CPTP，但原 (66.39) 的 13 插入在端点 Bell 投影上仍有特征值 $-1/2$。这里使用原式插入的未归一化中间单位。概率校准没有排除相对转置错误。$\square$

### 71.5 完整方向预选与有限量子对应

**推论 71.5（带完整 Bell 条件的同数据候选）。** 在定义 71.1 全部条件上，增加 (71.7) 的任一操作性条件，再保留定义 67.10、定义 68.3 的完整模型依赖预选规则与整个输出正性，则得到定理 67.11 的同一实际有限静态量子结构。

证明。定理 71.3 先给单位权重，故 $C_D=C_E=\mathrm{id}$、$F=M$；此时定理 67.7 的同数据校准条件齐备。预选规则仍只读取 $A,D$ 的比较几何、预定标签及基和实际 $M$，在每个有序非标量端点对 $(i,k)$ 的两维子空间取 Bell 投影 $b_{ik}$，用初始正规形 (68.14) 的 $V_{ik}$ 送回实际块，得到 $\beta_{ik}$。令 $r$ 为这些有序对的数目，并取

$$
\sigma_*=\begin{cases}r^{-1}\sum_{(i,k)}\beta_{ik},&r>0,\\1_D/n^2,&r=0.\end{cases}
$$

所有同维而不同标签的块仍分开；规约在测试前固定，不读取 $Q,I_{13}$ 或输出。在一般未校准系统中须按 (68.15) 使用 $\rho_*=C_D\sigma_*/\operatorname{Tr}(C_D\sigma_*)$；这里单位权重使它正好等于 $\sigma_*$。要求的额外条件完整地是

$$
I_{13}(\sigma_*)\in E_+,\qquad
I_{13}=\widetilde{\mathcal T}\widetilde M^{-1},\quad
\mathcal T(a,c)=Q(a,1_A,c).
\tag{71.12}
$$

它覆盖每个中间扇区，包括标量旁观者，要求整个输出 PSD。由定理 68.4 或定义 67.10 所用定理 64.10，(71.12) 等价于这个实际 $I_{13}$ 的整锥正性。定理 67.11 随即给出保原迹 Jordan 坐标中的普通 $M(a,b)_{ij}=a_i\otimes b_j$、$L(d,c)_{ijk}=d_{ij}\otimes c_k$，原 $p$ 为普通首腿偏迹求和；其余两个读回是 (67.28) 的偏迹求和，$p_{13}=I_{13}^*$ 正且 TP。没有选择一个对所有模型通用的固定 Bell 态；定理 68.7 的固定一态障碍仍成立。

原全态、全效应及概率仍是 (66.27)：直和 PSD 块总迹一、各块效应 $0\le e\le I$、Born 迹配对；纯态为 $\coprod_i\mathbb{CP}^{n_i-1}$，同区比较是平方重叠、异区为零。全标量经典扇区、经典与量子混合扇区及全部纠缠态均允许。逆向，标准有限直和张量数据满足定义 71.1、两个实际重置 TP、原 $p$ TP 和此预选整输出条件，故候选在同一实际数据上双向闭合。$\square$

### 71.6 完整中文候选与几何范围

**定义 71.6（关系校准候选的朴素表述）。** 在真实给定的单份、双份、三份非零有限系统中，保留所有状态和所有效应，用确定接受纯参照时的最少接受率定义比较，要求任意有限随机纯制备与交换端点后逐项平均一致。沿用 §66.1 明确的条件 Jordan 桥并忠实保留原归一化、单位和配对；只给整个双份正锥上的正接合与整个三份正锥上的同一个正读回，从原参考两次使用它定义第一准备。保留两条实张成、两个单位切片的零比较保持（第二个覆盖全部双份正元）、全部实方向的 $Z$，以及由这些原始关系推出的逆迹平衡。然后要求这个原读回保持整个三份系统的总概率，并要求：把所有局部输入统一重置到一个事先固定扇区内的任意固定态时，按实际乘积关系唯一延拓的二份或三份并行全重置保持整个输入态空间的总概率。另一份数的全重置和所有归一化乘积三元输出的总概率由此推出。最后仍按实际第一准备预选所有有序活跃端点的合成 Bell 态，并要求实际交叉插入的整个输出为正；这才接回同时相容的普通有限张量与读回。

几何上，重置读取的是整个实际空间的正迹泛函 $\operatorname{Tr}(V_m-)$；概率守恒要求其密度乘准备总量恰为单位。原逆迹平衡消去二份共同尺度，同一个保迹读回再固定三份权重。方向相容性则由完整 Bell 输出的锥归属判断，不能由这些总量等式替代。纯端点互反也不等于时间中的操作交换，(66.40) 的控制仍适用。

本章的关系应用是实际加权乘积所确定的重置、与同一读回的交换关系及同数据校准等价（repo-derived）。有限复载体、原始分类及逆向、双迹刚性、模型适配 Bell 规则分别复用第 66、67、68 节；正泛函乘正输出的 CP 与全态 TP 判据复用 (69.14) 和上述 Watrous 文献接口（literature-attested）。有限维线性满射与迹对偶只是推导中间步骤，不另立一般新定理。这些对应不证明独立公理减少、最少性或文献新颖性。

该条件候选不从物理来源推出完整比较律、全部效应、全锥关系或实张成，不证明参考、探针、滤波、重置及一般 CP 映射的物理可用性。不选择单一非经典扇区，不识别独立给定的另一三份括号载体，不提供四份、任意多份或无限维一致性，也不产生动力学、时间、Hamiltonian、$\hbar$ 或经验对应；有限静态量子结构与完整物理起源之间的这些桥仍须分别建立。

## 追加锚（本行以下为增补区）
