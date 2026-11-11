# QUANTUM ORIGIN: ENDOGENOUS CUT ATLAS AND DISCRETE RECONSTRUCTION BOUNDARIES IV

本卷给出一个整合的有限候选：先用两个单位切片恢复完整二元读回律，再用一次标量迹条件恢复 $p$ 的全局保迹和第二个二元接口，最后用一个预先选定的纠缠 Bell 探针恢复交叉插入的整锥正性。所有结论都是在所列纸面条件和引用接口内的条件性数学推导；它们不替代 Lean 真值，也不主张文献定理、原创性、独立性或最小公理数。

## 1. 入口、顺序与两个单位切片

对三个实际的非零有限有序载体 $A,D,E$，取闭尖生成锥、严格正归一化和紧的全态基底，并保留对偶效应 $[0,u_X]$。对纯态 $\xi$ 定义

$$
T_\xi(x)=\inf\{f(x):0\le f\le u_X,\ f(\xi)=1\},
$$

并要求对任意纯态、有限纯态族和概率权重成立有限混合律 $S$。另行保留 $S$ 到规范迹 Euclidean Jordan 几何的保归一化条件桥；$S$ 本身不替代这条桥。桥后，三个实际载体都是带平方锥的有限 EJA，所有正迹一元都是状态，所有 $0\le f\le1_X$ 都是效应，每个扇区本原幂等元的规范迹为一。记

$$
\langle x,y\rangle_X=\tau_X(x\circ y),\qquad
n=\tau_A(1_A)>0,\quad m=\tau_D(1_D)>0,
\quad e=1_A/n,\quad \omega=1_D/m.
\tag{64.1}
$$

唯一的原始映射是实双线性
$L:D\times A\to E$ 和实线性 $p:E\to D$。要求

$$
L(D_+,A_+)\subseteq E_+,\qquad p(E_+)\subseteq D_+,
$$

其中 $L$ 的第一个量词包括任意纠缠的 $d\in D_+$，并暂不假设 $p$ 保迹。用同一个 $p$ 两次定义

$$
\begin{aligned}
B(d,c)&=pL(d,c),& M(a,b)&=B(B(\omega,a),b),\\
Q(a,b,c)&=L(M(a,b),c),&J(a)&=M(a,1_A),&r&=J^*,\\
H(d)&=L(d,1_A),&h&=H^*.
\end{aligned}
\tag{64.2}
$$

两个单位都是未归一化的 $1_A$。保留

$$
\operatorname{span}_{\mathbb R}M(A,A)=D,\qquad
\operatorname{span}_{\mathbb R}L(D,A)=E,
\tag{64.3}
$$

以及对所有实 $a,b,c\in A$ 的

$$
\begin{gathered}
\mathrm{(W_J)}\quad J^*J=n\,\operatorname{id}_A,\qquad
\mathrm{(W_H)}\quad H^*H=n\,\operatorname{id}_D,\\
\mathrm{(III)}\quad pQ(a,b,c)=\tau_A(a)M(b,c).
\end{gathered}
\tag{64.4}
$$

这里没有把 $p$ 的全局保迹作为入口条件。Part III 的[定理 63.2（第一切片恢复完整 I）](QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_III.md#63-两个单位切片与完整读回律)正好适用：$W_J$ 给出完整

$$
\begin{gathered}
U:=M(1_A,1_A)=1_D,\qquad m=n^2,\\
\mathrm{(I)}\quad rM(a,b)=\tau_A(b)a,\qquad
sM(a,b)=\tau_A(a)b,\\
\tau_A r=\tau_D=\tau_A s,
\end{gathered}
\tag{64.5}
$$

以及 $\mathcal M:A\otimes_{\mathbb R}A\to D$，$a\otimes b\mapsto M(a,b)$ 的满迹内积等距同构。这里的 $s$ 是

$$
 s=r\,pL(\mathord\cdot,e),
$$

而不是新增原始映射。该定理的归一化阶段只用正性、$W_J$、(III)、$M$ 的实张成和二元纸面接口：由 (III) 得到 $sM(a,b)=\tau_A(a)b$ 及

$$
B(d,c)=M(sd,c),\qquad \tau_A(s\omega)=1.
\tag{64.6}
$$

具体地，$sM(a,b)=r,pQ(a,b,e)=\tau_A(a)rM(b,e)=\tau_A(a)b$；在 $d=M(a,b)$ 上，(III) 再给出 $B(d,c)=M(sd,c)$，随后由 $M$ 张成延拓到全部 $d$。把它代回两次同一个 $p$ 的定义，得到

$$
M(a,b)=M\bigl(sM(s\omega,a),b\bigr)=\tau_A(s\omega)M(a,b).
$$

存在非零 $M$-乘积，故确有 $\tau_A(s\omega)=1$；这两个量都是 full III 与 $W_J$ 的结果，而不是对 $p$ 保迹的隐藏使用。

因此 $s^*1_A$ 与 $1_D$ 在所有 $M$-乘积上的配对相同。它没有使用 $p$ 保迹、$W_H$、$L$ 的实张成或任何插入正性。尤其，下面的标量候选从未把 $p$ 保迹偷换成前提；它要由支持面证明推出它。

## 2. 标量 $C$：支持面、秩和全局保迹

### 2.1 标量条件及其可用的内部恒等式

在 (64.5) 之后保留完整 $W_H$ 和 (64.3)–(64.4)，以唯一标量条件替代全局保迹：

$$
\mathrm{(C)}\qquad \tau_D\bigl(p(1_E)\bigr)=\tau_E(1_E)=:R,
\tag{64.7}
$$

其中 $R=\operatorname{rank}(E)$ 是实际 EJA 的秩。$C$ 是一个总迹数，不是向量方程 $p^*1_D=1_E$。设

$$
 t=sp:E\to A.
$$

由 (64.6)、(III) 和 $M$ 张成，先得到对所有实 $d,c$

$$
B(d,c)=M(sd,c),\qquad tL(d,c)=\tau_D(d)c.
\tag{64.8}
$$

同时由 (64.5) 的保迹性，

$$
\tau_DpL(d,c)=\tau_A(sd)\tau_A(c)=\tau_D(d)\tau_A(c).
\tag{64.9}
$$

(64.9) 只是当前内部的复合迹式，不是 $p$ 对任意 $E$ 元素的保迹断言。

在后面的支持论证中需要一个零配对事实。若 $F$ 是有限 EJA，$q$ 是幂等元，$F=F_1(q)\oplus F_{1/2}(q)\oplus F_0(q)$ 是 Peirce 分解，且 $z=x^2\ge0$，则

$$
\langle q,z\rangle
=\langle L_qx,x\rangle
=\|x_1\|^2+\tfrac12\|x_{1/2}\|^2.
\tag{64.10}
$$

所以零配对把 $z$ 放进 $F_0(q)$。对正元作谱展开，就得到：若 $a,b\ge0$ 且 $\langle a,b\rangle=0$，则它们的支持幂等元正交。这里使用的二次表示

$$
P_x=2\ell_x^2-\ell_{x^2}
$$

对所有有限 EJA 都正，且 $P_{x^{-1}}$ 在可逆支撑面上是 $P_x$ 的逆；这正是 [van de Wetering 的 Proposition 2.21、2.25](https://arxiv.org/html/1912.01903v1#S2.counter21) 的条件，而不是矩阵专属假设。有限 EJA 的谱分解、规范迹为本原谱值之和以及正迹一态基底，分别是 [Barnum–Hilgert 的 Theorem 4.2、Definition 4.3、Proposition 4.4](https://arxiv.org/html/1904.03753v1#S4) 所用的条件。

### 2.2 每个本原方向的支持面

取 $D$ 的任意本原幂等元 $q$，令

$$
 w=Hq=L(q,1_A)\ge0,\qquad P=\operatorname{supp}(w),\qquad F=E_1(P).
$$

$w\ne0$，因为若 $w=0$，则 $Hq=0$ 与 $W_H$ 矛盾。由 $W_H$，$Hq$ 与 $H(1_D-q)$ 正交。设 $y\in F_+$。正映射 $h=H^*$ 给出

$$
\langle 1_D-q,hy\rangle_D
=\langle H(1_D-q),y\rangle_E=0.
$$

因为 $q$ 本原，$D_1(q)=\mathbb Rq$；零配对规则遂给出

$$
 hy=\langle w,y\rangle_E q.
\tag{64.11}
$$

现在固定 $c\in A_+$，取 $\alpha$ 使 $0\le c\le\alpha1_A$，并令
$L_c(d)=L(d,c)$。全锥正性给出正映射序

$$
0\le L_c\le\alpha H,\qquad
0\le L_c^*y\le\alpha hy\quad(y\in F_+).
\tag{64.12}
$$

由 (64.11)，$L_c^*y$ 落在极射线 $\mathbb R_+q$；另一方面
$0\le K_q(c):=L(q,c)\le\alpha w$，故 $K_q(c)\in F_+$。对任意 $d\in D$ 和 $y\in F_+$，先在正元上使用 (64.12)，再由锥生成性线性化，得到

$$
\langle y,L(d,c)\rangle_E
=\langle L_c^*y,d\rangle_D
=\langle q,d\rangle_D\langle y,K_q(c)\rangle_E.
$$

$F$ 的内积非退化，故

$$
P_P L(d,c)=\langle q,d\rangle_D K_q(c)
\qquad(d\in D,\ c\in A).
\tag{64.13}
$$

这一步同时处理了所有实 $d,c$，没有把 $d$ 限制为准备出的乘积。

由于 $L(D,A)$ 实张成 $E$，(64.13) 的左端覆盖 $F$，从而
$K_q(A)=F$。另一方面 (64.8) 给出

$$
 tK_q(c)=c\qquad(c\in A).
\tag{64.14}
$$

所以 $K_q:A\to F$ 是满射、单射的正线性双射，且 $t|_F$ 是其正逆。

### 2.3 支持面上的 Jordan 规范化

$w$ 在 $F$ 内部；在 $F$ 内以其单位 $P$ 写

$$
\Theta_q=P_{w^{-1/2}}K_q:A\longrightarrow F.
\tag{64.15}
$$

$P_{w^{-1/2}}$ 是正的可逆锥自同构，故 $\Theta_q$ 和其逆都正，且
$\Theta_q(1_A)=P$。有限 EJA 的区间 $[0,1]$ 的极点正好是幂等元，序区间同构保持这些极点。于是 $\Theta_q$ 把 $A$ 的完整正交本原框架送到 $F$ 的完整正交幂等框架；谱展开给出

$$
\Theta_q(x^2)=\Theta_q(x)^2,
\qquad
\Theta_q(x\circ y)=\Theta_q(x)\circ\Theta_q(y).
\tag{64.16}
$$

逆映射同样保持幂等元，故它是保单位 Jordan 同构。它保持本原性和规范迹，因而

$$
\operatorname{rank}(F)=\operatorname{rank}(A)=n,
\qquad
t|_F=\Theta_q^{-1}P_{w^{-1/2}},
$$

并且精确的逆迹方向是

$$
\tau_A(tP)=\tau_F(w^{-1}).
\tag{64.17}
$$

这里是先用 $K_q=P_{w^{1/2}}\Theta_q$，再取逆；不能把 $P_{w^{-1/2}}$ 与 $P_{w^{1/2}}$ 的方向互换。

### 2.4 一个标量压平全部谱值

取 $D$ 的完整本原框架 $(q_i)_{i=1}^m$，令 $w_i=Hq_i$、$P_i=\operatorname{supp}(w_i)$。$W_H$ 给出

$$
\langle w_i,w_j\rangle_E=n\delta_{ij}.
$$

故 $P_i$ 两两正交。$V=H1_D=\sum_iw_i$ 是 $E_+$ 的内点：若正元与 $V$ 零配对，则由
$0\le L(d,c)\le\lambda\mu V$ 消去所有 $L$-乘积，再由 $L$ 张成性消去整个 $E$。因此

$$
\sum_iP_i=1_E,\qquad R=\operatorname{rank}(E)=mn=n^3.
\tag{64.18}
$$

写 $w_i$ 在 $F_i=E_1(P_i)$ 中的正谱值为 $\lambda_{ij}$，其中 $1\le i\le m$、$1\le j\le n$。由 $W_H$ 和 (64.18)，

$$
\sum_{i,j}\lambda_{ij}^2=mn=R.
\tag{64.19}
$$

由 (64.17) 和标量条件 (64.7)，

$$
\sum_{i,j}\lambda_{ij}^{-1}
=\sum_i\tau_A(tP_i)
=\tau_A(t1_E)=R.
\tag{64.20}
$$

而对每个 $\lambda>0$，

$$
\lambda^2+\frac2\lambda-3
=\frac{(\lambda-1)^2(\lambda+2)}{\lambda}\ge0.
\tag{64.21}
$$

将 (64.19)、(64.20) 代入 (64.21) 的总和，得到零；所以所有 $\lambda_{ij}=1$，从而

$$
H1_D=1_E,\qquad Hq_i=P_i.
\tag{64.22}
$$

这说明 $C$ 真正恢复了单位律，而不是从 $W_H$ 直接声称单位律。

### 2.5 在第二次分类前推出 pTP 与完整 II

由 (64.22)，每个 $K_{q_i}$ 已经是单位 Jordan 同构到 $F_i$，故

$$
\tau_E L(q_i,c)=\tau_A(c)\qquad(c\in A).
$$

对 $D$ 的谱展开线性化，得到所有实 $d,c$

$$
\tau_E L(d,c)=\tau_D(d)\tau_A(c).
\tag{64.23}
$$

与 (64.9) 比较，并使用 $L(D,A)$ 实张成，遂有

$$
\tau_D(pz)=\tau_E(z)\qquad(z\in E).
\tag{64.24}
$$

因此 $p$ 的全局保迹是推论，而非入口假设；$t=sp$ 也保迹。

同时 (64.22) 使 $h=H^*$ 保迹。对本原 $q$ 和本原幂等元 $f\in A$，$\rho=L(q,f)$ 是 $F_q$ 中的本原幂等元。$h\rho$ 正、迹一，并满足
$\langle q,h\rho\rangle=1$；零配对规则将其限制在 $D_1(q)=\mathbb Rq$，故 $h\rho=q$。双重谱展开给出完整的

$$
 hL(d,c)=\tau_A(c)d\qquad(d\in D,c\in A).
\tag{64.25}
$$

这时才把二元纸面接口用于 $(L,h,t)$：它具有全锥正、规范保迹的两个边缘、全部实向量丢弃律和 $L$ 张成性，因而得到 $\mathcal L$ 的满迹等距同构；与 $\mathcal M$ 合成得到 $\mathcal Q$。第二次二元分类、初始矩阵正规形和任何插入测试都排在 (64.24)–(64.25) 之后。

**标量归一化的中文结论。** 在保留有限全态全效应系统、混合律 $S$、另行的规范迹 Jordan 桥、全锥正的 $L,p$、两条张成、$W_J,W_H$ 和全实向量 $\mathrm{III}$ 后，只要求未归一化单位满足一次总迹等式 $\tau_Dp(1_E)=\operatorname{rank}(E)$，便可通过本原方向的支持面、正序同构和逆迹谱恒等式把所有谱权重压到一。于是先得到 $H1_D=1_E$，再得到 $p$ 全局保迹和完整 $hL(d,c)=\tau_A(c)d$，然后才进入第二个二元接口。这里没有预设 $p$ 保迹，也没有用交叉插入正性或第二次分类帮助标量证明。

### 2.6 标量条件不可删除的完整控制

取 $A=\mathbb R^2,D=\mathbb R^4,E=\mathbb R^8$ 的坐标正锥，规范迹为坐标和，指标取 $i,j,k\in\{0,1\}$。令 $w=(7/5,1/5)$，于是 $\sum_kw_k^2=2$，并定义

$$
L(d,c)_{ijk}=d_{ij}w_kc_k,\qquad
p(z)_{jk}=\sum_i z_{ijk}/w_k.
\tag{64.26}
$$

两映射在全锥上正；非零权给出 $L$ 张成。两次同一个 $p$ 给出

$$
B(d,c)_{jk}=\Bigl(\sum_i d_{ij}\Bigr)c_k,\qquad
M(a,b)_{ij}=a_ib_j,
$$

因而 $M$ 张成，$r(d)_i=\sum_jd_{ij}$，且 $rM(a,b)=\tau_A(b)a$、$W_J$、$\mathrm{III}$ 和 $W_H$ 全部成立。交叉插入为

$$
(I_{13}z)_{ijk}=w_kz_{ik},
$$

在整个坐标正锥上正；但是
$\tau_Dp(e_{000})=5/7\ne1$，并且
$\tau_Dp(1_E)=160/7\ne8=\operatorname{rank}(E)$。此外
$hL(d,c)=(\sum_kw_k^2c_k)d$，在 $c=e_0$ 时违反完整 II。故删去 $C$ 会留下精确的经典反例。

## 3. 一次预选纠缠探针恢复整锥插入正性

### 3.1 正规形只在归一化之后取得

由第 2 节的 (64.24)–(64.25)，$p$ 已全局保迹，$h,t$ 已规范保迹，$M,L$ 的两个二元接口和 $Q$ 的等距性已经成立；这一步仍未使用 $I_{13}$ 正性。现在才使用已有的有限扇区证明。它先从实际自复合的秩平方条件得到复杂矩阵扇区：对每个非标量 $A_i$，实际 $D_{ii}$ 是秩大于一的简单 EJA，并具有平方秩、平方维数；使用 [van de Wetering arXiv:1803.11139v3 Proposition 40](https://arxiv.org/pdf/1803.11139v3) 的这一充要条件，得到

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

这里的 $W_{ijk}$ 吸收 $U_{ik}$；若 $L$ 的第一个输入先转置，则使用
$(U\,x\,U^*)^{\mathsf T}=\overline U\,x^{\mathsf T}U^{\mathsf T}$，没有把纠缠 $U$ 与部分转置错误地交换。到此只得到初始正规形，尚未作同时 untwist，也未使用跨扇区约束或插入正性。

### 3.2 交叉插入的精确块公式

在 $\mathcal M$ 已可逆后定义

$$
\mathcal T(a\otimes c)=Q(a,1_A,c),\qquad
I_{13}=\mathcal T\mathcal M^{-1}:D\to E.
\tag{64.30}
$$

对 $x\in H_{n_in_k}$，令 $\iota_j(x)$ 把未归一化的中间单位插入第三张量位置：若 $S_j$ 把 $|a,c,b\rangle$ 送到 $|a,b,c\rangle$，则

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

是带顺序的端点对，重复标签按有序出现，$N=|\mathcal P|$。对每个 $(i,k)\in\mathcal P$，在固定的初始基中取

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

若 $N=0$，令 $\sigma_*=1_D/m$。这是实际载体中的正迹一态；没有对 $b_{ik}$ 使用 $\mathcal M^{-1}$ 来宣称物理性。初始坐标和正规形在测试前固定，且选择规则只依赖 $M$ 的系数、标号中心块和固定基：允许任意一个满足 (64.28) 的选择；若需要单值规则，可按固定基元顺序取解集的首个闭紧酉解并逐项最小化实部、虚部。该规则不读取 $Q,W,I_{13}$ 或测试结果。

**定理 64.1（一次预选态等价于整锥插入正性）。** 对上述任意预先固定的初始正规形选择，

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

在 $A=H_q,D=H_{q^2},E=H_{q^3}$ 中取

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
$|0,k,1\rangle-|1,k,0\rangle$ 的归一化向量本征值为 $-1/2$。这证明整锥插入条件仍有实质作用，不能由两个单位切片或 $C$ 删除。

还可检验有序跨扇区和标量中间不能被对角测试代替。令
$A=H_2\oplus H_3\oplus\mathbb R$，标签为 $u,v,s$，取标准分块 $D,E$。令
$\chi_{ijk}=1$ 当且仅当 $(i,j,k)=(u,s,v)$，其余为零，并定义

$$
L(d,c)_{ijk}=d_{ij}\otimes c_k^{T^{\chi_{ijk}}},\qquad
(pz)_{jk}=\sum_i\bigl(\operatorname{Tr}_1z_{ijk}\bigr)^{T^{\chi_{ijk}}}.
\tag{64.38}
$$

每个分块的映射都在全锥上正并保迹，$L,p$ 张成，内部 $M$ 是普通张量，$H(d)_{ijk}=d_{ij}\otimes I_{n_k}$ 且 $H^*H=6\operatorname{id}_D$。所有对角端点测试都通过，反向交叉也没有缺陷；但从 $D_{uv}$ 到 $E_{usv}$ 的插入在标量中间 $s$ 的旁观下对 $v$ 作部分转置。四个有序非标量端点对等权时，(64.36) 给出负本征值 $-1/8$。所以探针必须覆盖所有有序端点对和标量中间，而不是只选一个自复合块。

**一次探针的中文结论。** 在 $C$ 已恢复 $p$ 保迹、完整 II 和两个二元接口之后，先在尚未同时 untwist 的标号矩阵坐标中按 $M$ 预选每个有序非标量端点对的 Bell 态，再等权组成一个实际正迹一态。解开 $U^*\beta U$ 后，任何单因子转置的错误都会在相应的输出直和块留下负本征值；中间扇区即使是标量也不消除它。因此一个整态测试等价于整锥 $I_{13}$ 正性，且结论覆盖任意允许的初始正规形选择。

## 4. 整合候选、严格恢复与几何范围

### 4.1 完整候选和严格同载体等价

整合候选的入口条件逐项是：三个实际非零有限全态全效应载体及其有限混合 $S$；三个载体各自的保归一化规范迹 Jordan 桥；每扇区本原迹一；全域正的 $L:D\times A\to E$ 和全域正的 $p:E\to D$；同一个 $p$ 两次定义的 $B,M,Q$；两条实张成；全部实方向的 $W_J,W_H,\mathrm{III}$；标量条件 $C$；以及定理 64.1 的一个预选 Bell 测试。$p$ 的全局保迹、$M(1_A,1_A)=1_D$、完整 I、完整 II、$h,t$ 保迹和所有张量等距性都不是独立入口条件，而按上面的顺序推出。

在推出 (64.24)–(64.25) 后，定义 (64.30) 良好。仅在这时，把一次 Bell 测试等价换成
$ I_{13}(D_+)\subseteq E_+$。自对偶性给出

$$
 p_{13}=I_{13}^*:E\to D,
$$

它全锥正且保迹。等距性和全实向量律给出，对全部 $x,y,a,b,c$

$$
\begin{aligned}
\langle M(x,y),p_{13}Q(a,b,c)\rangle_D
 &=\langle Q(x,1_A,y),Q(a,b,c)\rangle_E\\
 &=\tau_A(b)\langle x,a\rangle_A\langle y,c\rangle_A.
\end{aligned}
$$

$M$ 张成且配对非退化，故

$$
 p_{13}Q(a,b,c)=\tau_A(b)M(a,c).
\tag{64.39}
$$

$Q$ 张成使它在全部 $E$ 上唯一。用 (64.39)、(64.8)、$r\omega=e$ 和
$sM(e,a)=a$，得到

$$
 pL\bigl(p_{13}L(\omega,a),b\bigr)=M(a,b).
\tag{64.40}
$$

所以旧的混合 $p_{13}$ 定义与整合候选中的两次同一个 $p$ 定义逐点相同。

于是固定的 Part III 定理 62.5 才有全部前提：它在不改变实际 $A,D,E,L,p$ 的条件下，严格恢复旧三映射条件、$p_{13}$ 的唯一性和同一载体上的三份表示。反向地，从旧模型出发，完整 I 的 $b=1_A$ 切片给出 $W_J$，$p$ 保迹给出 $C$，且旧的整锥插入正性通过定理 64.1 的探针；两次同一个 $p$ 的 $M$ 保持不变。因此“忘掉 $p_{13}$”与“按探针恢复并加入唯一 $p_{13}$”在同一实际载体、同一实际 $L,p$ 上互为严格逆，而不是只在坐标同构类上等价。

**整合候选的中文结论。** 这一个候选只把原先的全局 $p$ 保迹和全锥交叉插入检验改造成有明确顺序的推导：$W_J$ 先恢复完整 I、$r,s$ 保迹和 $m=n^2$；支持面与标量 $C$ 再恢复秩、$H1_D=1_E$、全局 $p$ 保迹和完整 II；只有这些旧前提全部复原后，Bell 探针才恢复整锥插入正性。由此保留同一实际 $A,D,E,L,p$ 和严格唯一的 $p_{13}$，不声称剩余条件独立或最少。

### 4.2 几何和 Born 对应

恢复旧前提后，直接使用 Part III 定理 62.7 及其既有二元、三映射接口，不重复分类。在同一实际载体的保迹 Jordan 坐标中，存在有限非空指标集和 $n_i\ge1$，使

$$
A\simeq\bigoplus_iH_{n_i},\qquad
D\simeq\bigoplus_{i,j}H_{n_in_j},\qquad
E\simeq\bigoplus_{i,j,k}H_{n_in_jn_k}.
\tag{64.41}
$$

同一实际映射在这些坐标中为

$$
\begin{aligned}
M(a,b)_{ij}&=a_i\otimes b_j,&
L(d,c)_{ijk}&=d_{ij}\otimes c_k,\\
(r d)_i&=\sum_j\operatorname{Tr}_2d_{ij},&
(hz)_{ij}&=\sum_k\operatorname{Tr}_3z_{ijk},\\
(pz)_{jk}&=\sum_i\operatorname{Tr}_1z_{ijk},&
(p_{13}z)_{ik}&=\sum_j\operatorname{Tr}_2z_{ijk}.
\end{aligned}
\tag{64.42}
$$

$L$ 的公式对整个实际 $D$ 成立，包括纠缠正元。全态和全效应为

$$
\rho_i\ge0,\qquad \sum_i\operatorname{Tr}\rho_i=1,\qquad
0\le F_i\le I_{n_i},\qquad
\Pr(F\mid\rho)=\sum_i\operatorname{Tr}(F_i\rho_i).
\tag{64.43}
$$

纯态分支是 $\coprod_i\mathbb{CP}^{n_i-1}$；同扇区比较为
$\operatorname{Tr}(\xi\eta)=|\langle\psi,\phi\rangle|^2$，异扇区为零。标量经典扇区仍在，单独选择一个非经典扇区需另加条件。恢复之后可以在同一个 $E$ 上构造所选右准备、恒等重括号和 $S_3$ 标签自同构；这不是入口给定的独立右载体。

### 4.3 边界和未推出的物理内容

三量子比特的

$$
|G_\pm\rangle=(|000\rangle\pm|111\rangle)/\sqrt2
$$

是不同的正迹一态，却有相同的三个两两约化态；实张成、唯一读回和构造的右准备不提供任意三份态的两两层析。端点比较互反、标签置换和括号交换也不等于不相容测量的时间顺序交换，不给出共同的经典联合结果律。

整个候选没有推出完全正性、参考扩张、仪器、态更新、动力学、时钟、Hamiltonian 或 $\hbar$；数学上的 $\omega$、单位插入和二次表示没有承诺物理准备、滤波器、Bell 态获取、参考装置或成本。也没有识别一个独立给定的右载体，没有无限维延拓、四份一致性或无界份数的相干组合。所有这些边界与 (64.41)–(64.43) 的有限静态几何同时成立。

## 追加锚（本行以下为增补区）
