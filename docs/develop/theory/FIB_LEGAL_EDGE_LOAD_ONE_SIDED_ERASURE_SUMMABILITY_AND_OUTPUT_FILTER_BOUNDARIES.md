# FIB 合法边调和负载：单侧擦除可和性与输出滤波边界

本卷在完整 no11 开放路径域和一个实际的有限边发射律上工作。它证明实际可见遍历分量上的单侧平方缺陷精确分解，给出矩形词和双向 flag-block 两条带有明确附加前提的期望指数界，并把原联合律的隐藏滤波 TV 误差转移为原输出后验的平方误差。两个符号族说明这些前提的作用范围：一个有无限可见记忆且满足后验带的 renewal 子族，和一个没有矩形词、没有 flag 词但输出擦除根和仍有限的相位复制表示。全体有限隐藏参数域上的根和命题、后验带上的普遍命题以及原始精确达到问题仍未解决。

## 1. 完整目标、实际律与擦除字段

**定义 1.1（完整开放路径目标）。** 对 $n\ge1$ 令

$$
B_n=\{w\in\{0,1\}^n:w_iw_{i+1}=0\ (1\le i<n)\},
$$

并令 $\Gamma_n$ 的顶点为全部 $B_n$，边为全部合法 Hamming 一位差词对。端点测试使用
$w_0=w_{n+1}=0$，首尾不相接。对整个单纯形 $\mathcal P(B_n)$ 置

$$
h(s,t)=\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}\qquad
\Phi_n(\mu)=\sum_{\{w,z\}\in E(\Gamma_n)}h(\mu_w,\mu_z),\qquad
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu),\qquad
c_\star=\lim_{n\to\infty}\kappa_n/n .
$$

零质量不删除顶点、边或接缝；全部合法词和开放端点都保留。

**定义 1.2（一个实际有限边发射律）。** 对 $N\ge1$，保留完整参数域

$$
\Theta_N=\{(\lambda,M_0,M_1):\lambda\ge0,\ \lambda\mathbf1=1,
\ M_0,M_1\ge0,\ A=M_0+M_1,\ A\mathbf1=\mathbf1,
\ \lambda A=\lambda,\ \lambda M_1^2\mathbf1=0\}.
\tag{1.1}
$$

$\lambda$ 是行向量，$M_0,M_1$ 是精确实数矩阵。最后一个条件是标量条件；本卷不把它替换为逐项的 $M_1^2=0$。给定 $\theta\in\Theta_N$，唯一使用的实际联合律由

$$
J_\theta(H_a=h_a,\ldots,H_{b+1}=h_{b+1},X_a=x_a,\ldots,X_b=x_b)
=\lambda_{h_a}\prod_{i=a}^bM_{x_i}(h_i,h_{i+1})
\tag{1.2}
$$

定义，其可见边缘为

$$
P=P_\theta,\qquad P([w]_a)=\lambda M_w\mathbf1,\qquad
M_w=M_{w_1}\cdots M_{w_n},\quad M_\varnothing=I.
\tag{1.3}
$$

结构零、零平稳质量、可约性、周期性和冗余表示都允许。任意接缝 $uv$ 的质量是
$\lambda M_uM_v\mathbf1$，从不拆成两个边缘的乘积；坐标仍是原始发射位钟。

**定义 1.3（实际后验与单侧擦除）。** 令

$$
\mathsf X=\{x\in\{0,1\}^{\mathbb Z}:x_ix_{i+1}=0\},\qquad
\mathcal E_0=\sigma(X_i:i\ne0),\qquad q_0=\mathbb E_P[X_0\mid\mathcal E_0].
$$

对 $j\ge0$ 定义

$$
\begin{aligned}
\mathcal L_j&=\sigma(X_{-j},\ldots,X_{-1},X_1,X_2,\ldots),\\
\mathcal R_j&=\sigma(X_i:i\le-1,\ X_1,\ldots,X_j),\\
p^L_j&=\mathbb E_P[X_0\mid\mathcal L_j],\qquad
p^R_j=\mathbb E_P[X_0\mid\mathcal R_j],\\
e_L(j)&=\mathbb E_P(q_0-p^L_j)^2,\qquad
e_R(j)=\mathbb E_P(q_0-p^R_j)^2,\\
A_P(R)&=\sum_{j\ge R}\bigl(\sqrt{e_L(j)}+\sqrt{e_R(j)}\bigr),\\
\tau_P(R)&=\sum_{j\ge R}\bigl(e_L(j)+e_R(j)\bigr).
\end{aligned}
\tag{1.4}
$$

在 $j=0$，$\mathcal L_0$ 没有有限左侧位而仍含有整个右半线，$\mathcal R_0$ 对偶地仍含有整个左半线。有限零似然纤维上的版本任取，其加权项为零。由条件期望投影，$e_L(j),e_R(j)$ 各自随 $j$ 不增并趋于零；这不蕴含根和收敛。

**定义 1.4（必要后验带）。** 置 $F_i=\{X_{i-1}=X_{i+1}=0\}$。本卷将

$$
\mathsf B(P):\quad q_i=0\text{ 于 }F_i^c,\qquad
\frac14\le q_i\le\frac12\text{ 于 }F_i,\quad P\text{-几乎处处、对所有 }i\in\mathbb Z
\tag{1.5}
$$

作为明确前提。供应卷给出 $d(P)=c_\star$ 时的必要性；本卷不把它升级为充分性。这里的 $q_i$ 是同一原始律 $P$ 的平移版本。

**约定 1.5（实际分量）。** 原始联合律的有限隐藏链去除瞬态后分解为有限个正权闭不可约类。合并相同的可见律，写成

$$
P=\sum_{\ell=1}^Lw_\ell R_\ell,\qquad w_\ell>0,\quad\sum_\ell w_\ell=1,
\tag{1.6}
$$

其中 $R_\ell$ 是互异的实际可见平稳遍历律。周期隐藏类仍产生一步平移遍历的可见律；标签只按可见半线频率使用，不把隐藏周期相位当成可见标签。

## 2. 实际分量上的精确仿射性

**定理 2.1（单侧平方缺陷的实际分量分解）。** 对每个 $j\ge0$ 和 $d\in\{L,R\}$，令 $e_d^{R_\ell}(j)$ 使用 $R_\ell$ 自身的 $q_0,p_j^d$ 定义。则

$$
e_d^P(j)=\sum_{\ell=1}^Lw_\ell e_d^{R_\ell}(j).
\tag{2.1}
$$

在扩展非负实数中，若 $A_{R_\ell}=A_{R_\ell}(0)$，则

$$
\max_\ell\sqrt{w_\ell}\,A_{R_\ell}\le A_P
\le\sum_{\ell=1}^L\sqrt{w_\ell}\,A_{R_\ell}.
\tag{2.2}
$$

因此 $A_P<\infty$ 当且仅当每个正权分量的 $A_{R_\ell}<\infty$。这同样适用于尚未合并的正权隐藏闭类；相同可见律的重复只改变分解的写法。

**证明。** 对每个有限可见词，遍历定理使其正半线经验频率在 $R_\ell$ 下几乎处处等于 $R_\ell$ 的柱概率。可数多个词的频率同时定义一个事件 $E_\ell^+$，它属于 $\sigma(X_i:i\ge1)$，在 $R_\ell$ 下满测，在其他互异可见律下零测。逆平移给出 $E_\ell^-\in\sigma(X_i:i\le-1)$。这些是实际可见标签；隐藏相位若在同一可见律下不可见，不被分开。

取 $A\in\mathcal L_j$。由于 $E_\ell^+\in\mathcal L_j$，混合律的条件期望恒等式在 $A\cap E_\ell^+$ 上给出

$$
0=\int_{A\cap E_\ell^+}(X_0-p_j^L)\,dP
=w_\ell\int_A(X_0-p_j^L)\,dR_\ell.
$$

故 $p_j^L$ 在 $R_\ell$ 下也是同一字段的条件期望版本。取 $A\in\mathcal E_0$ 得 $q_0$ 的对应结论。对 $p_j^R$ 使用 $E_\ell^-\in\mathcal R_j$，完全同样成立，包括 $j=0$。于是把平方差在混合律下积分即得 (2.1)。

令 $a_{\ell,j}=e_d^{R_\ell}(j)$。逐项有

$$
\sqrt{\sum_\ell w_\ell a_{\ell,j}}
\ge\sqrt{w_k a_{k,j}},\qquad
\sqrt{\sum_\ell w_\ell a_{\ell,j}}
\le\sum_\ell\sqrt{w_\ell a_{\ell,j}}.
$$

对 $j$ 和两个方向求和，得到 (2.2)。分量数有限，所以左侧有限当且仅当所有分量根和有限。零平稳质量的隐藏状态未被补成正质量；不可约类只通过原联合律的实际正权出现。若若干闭类的可见律相同，它们的 $q_0,p_j^d,e_d(j)$ 作为可见律的泛函完全相同，重新合并不改变等式。$\square$

若 $P$ 满足 $\mathsf B(P)$，则每个 $R_\ell$ 也满足同一带条件：在 $E_\ell^+$ 或 $E_\ell^-$ 上用上述条件版本恒等式即可。这个传递仍不涉及有限可见阶，也不涉及有限窗口风险 $D_r$ 的仿射性。

## 3. 同一律的滤波误差到输出擦除误差

**引理 3.1（二元后验的同测度 TV 不等式）。** 设 $\mu,\nu$ 是 $\{0,1\}\times Y$ 上的概率律，$Y$ 为标准 Borel 空间；记二元条件概率为 $a(y),b(y)$，$Y$ 边缘为 $\mu_Y,\nu_Y$。则

$$
\int|a-b|\,d\mu_Y\le2\,\operatorname{TV}(\mu,\nu),
\qquad \operatorname{TV}(\mu,\nu)=\sup_B|\mu(B)-\nu(B)|.
\tag{3.1}
$$

**证明。** 用 $\nu$ 的条件核和 $\mu_Y$ 构造 $\widetilde\nu(dx,dy)=\nu(dx\mid y)\mu_Y(dy)$。同一 $Y$ 边缘下，二元 Bernoulli 距离给出

$$
\operatorname{TV}(\mu,\widetilde\nu)=\int|a-b|\,d\mu_Y.
$$

另一方面，保持 $\nu(dx\mid y)$ 不变只改变 $Y$ 边缘，所以
$\operatorname{TV}(\nu,\widetilde\nu)=\operatorname{TV}(\nu_Y,\mu_Y)\le\operatorname{TV}(\mu,\nu)$，最后一个不等式是投影的数据处理。三角不等式即得 (3.1)。该不等式对条件概率核在 $\nu_Y$ 零集上的每个可测延拓均成立；若另有 $\mu_Y\ll\nu_Y$，则左侧积分不依赖于此延拓。$\square$

**定理 3.2（隐藏滤波 TV 到实际输出平方缺陷）。** 在原联合律 $J_\theta$ 下定义

$$
\begin{aligned}
\alpha_\infty&=\mathcal L(H_0\mid X_{-\infty:-1}),&
\alpha_j&=\mathcal L(H_0\mid X_{-j:-1}),\\
\beta_\infty&=\mathcal L(H_1\mid X_{1:\infty}),&
\beta_j&=\mathcal L(H_1\mid X_{1:j}),
\end{aligned}
\tag{3.2}
$$

其中 $j=0$ 的有限侧字段为空。则对所有 $j\ge0$，

$$
e_L(j)\le2\,\mathbb E_{J_\theta}\operatorname{TV}(\alpha_\infty,\alpha_j),\qquad
e_R(j)\le2\,\mathbb E_{J_\theta}\operatorname{TV}(\beta_\infty,\beta_j).
\tag{3.3}
$$

这一步不要求后验带、隐藏非退化或任何滤波稳定性假设。

**证明。** 先证左式。令 $U=X_{-\infty:-1}$、$Y=X_{1:\infty}$。给定 $H_0=s$，原标记链的 Markov 分离给出一个核 $K_s$，它是 $(X_0,Y)$ 的条件律。给定完整过去 $U$ 时，$(X_0,Y)$ 的律为 $\alpha_\infty K$；给定最后 $j$ 个过去位时，其律为 $\alpha_jK$。对每个实际过去记录，这两个律在 $\{0,1\}\times Y$ 上的 TV 距离不超过 $\operatorname{TV}(\alpha_\infty,\alpha_j)$，因为 Markov 核收缩 TV。

在这两个联合律中，$X_0$ 给定 $Y$ 的条件概率分别是 $q_0$ 和 $p_j^L$：前者还给定完整过去，后者只给定长度 $j$ 的过去，而两者都给定整个未来。用引理 3.1，并按真实完整过去的分布积分，得

$$
\mathbb E_P|q_0-p_j^L|\le2\mathbb E_{J_\theta}\operatorname{TV}(\alpha_\infty,\alpha_j).
$$

因为两个概率都在 $[0,1]$，有 $(q_0-p_j^L)^2\le|q_0-p_j^L|$，即得左式。

右式对反射的实际联合律作同样论证。也可直接以边界状态 $H_1$、完整左半线 $X_{-\infty:-1}$ 为 $Y$，使用原 Markov 链的时间反向条件分离；这只是在同一 $J_\theta$ 上改变条件积分顺序。零质量状态上的核任意延拓即可，不作除法。并且 $\alpha_j=\mathbb E[\alpha_\infty\mid X_{-j:-1}]$，故有限侧零后验事件不会给正质量无限侧分布赋予虚假的支持；$\beta$ 同理。$\square$

如果某个方向有实际期望界 $\mathbb E\operatorname{TV}\le K\rho^j$，则由 (3.3)

$$
\sum_{j\ge0}\sqrt{e_d(j)}\le\frac{\sqrt{2K}}{1-\sqrt\rho}.
\tag{3.4}
$$

只知道几乎处处 $C\rho^j$ 且 $C$ 无可用矩，不足以推出 (3.4)。

## 4. 矩形词：任意外部似然下的期望指数根和

**定义 4.1（实际分量的矩形词前提）。** 对每个正权闭不可约隐藏类 $C$，假设存在一个非空发射词 $w_C$，使 $B_C=M_{w_C}|_{C\times C}$ 的正支撑为

$$
\{(s,t):B_C(s,t)>0\}=I_C\times J_C,
\qquad\varnothing\ne I_C,J_C\subseteq C.
\tag{4.1}
$$

这是原矩阵上的额外充分前提。$M_0,M_1,A$ 可有结构零；本前提不由有限维、后验带或达到性推出。

**定理 4.2（矩形词的原律根和界）。** 固定一个满足 (4.1) 的类 $C$。令 $n_C=|C|$、$m=|w_C|$，并置

$$
u=\min_{I_C\times J_C}B_C(s,t)>0,\quad
v=\max_{I_C\times J_C}B_C(s,t),\quad
\rho=1-u/v<1,\quad b=m+n_C.
$$

固定任一 $r\in I_C$，对每个 $h\in C$ 选一条从 $h$ 到 $r$ 的带发射标签的正路径：若 $w_C$ 首位为 $0$，取简单正 $A$-路径，长度至多 $n_C-1$；若 $w_C$ 首位为 $1$，先取一条到某个 $u$ 的简单正路径，再接一条正的 $0$-边 $u\to r$，长度至多 $n_C$。令 $d_h$ 为沿选定标签的矩阵项乘积，$d_r=1$（从块起点直接发词时不需要前置边）。这种选择总能做到：若 $w_C$ 首位为 $1$，$r$ 有正的 $1$-出边；若所有入 $r$ 的正边都发射 $1$，便得到正的相邻 $11$ 路径，和正权类上的标量 no11 条件矛盾，故存在正的 $0$-入边。定义

$$
\varepsilon=\min_{h\in C}d_h(B_C\mathbf1)(r)>0,\qquad
\eta=1-\varepsilon(1-\rho^2)\in[0,1).
\tag{4.2}
$$

对该类条件可见律 $P_C$ 的所有 $j\ge0$，

$$
e_L^{P_C}(j),e_R^{P_C}(j)\le\eta^{\lfloor j/b\rfloor}.
\tag{4.3}
$$

用 $0^0=1$，则

$$
\begin{aligned}
A_{P_C}(R)&\le\frac{2b\,\eta^{\lfloor R/b\rfloor/2}}{1-\sqrt\eta},
&\tau_{P_C}(R)&\le\frac{2b\,\eta^{\lfloor R/b\rfloor}}{1-\eta},\\
A_{P_C}(0)&\le\frac{2b}{1-\sqrt\eta}.
\end{aligned}
\tag{4.4}
$$

**证明。** 记原联合律条件于类 $C$ 后为 $\mathbb J_C$，其平稳行为 $\pi$，可见边缘为 $P_C$；本证明中的矩阵和状态均限制在 $C$ 上。记 $M_{x_{p:q}}=M_{x_p}\cdots M_{x_q}$，空区间的乘积为单位矩阵。先证明一次词出现的条件收缩。给定词右侧任意非负似然列 $z$，若其在 $J_C$ 上的和为正，则从 $s\in I_C$ 出发穿过该词后的条件核为

$$
K_z(s,t)=\frac{B_C(s,t)z_t}{(B_Cz)_s}.
$$

对 $t\in J_C$，有

$$
K_z(s,t)\ge\frac uv\frac{z_t}{\sum_{a\in J_C}z_a}.
\tag{4.5}
$$

故所有可行行共享质量 $u/v$ 的同一概率次测度，Dobrushin 收缩系数至多 $\rho$。若 $s\notin I_C$，该词的行全为零，因而不会出现在正似然条件下。对任意非负左似然行 $a$，反向核同理满足

$$
K_a^{\rm back}(t,s)=\frac{a_sB_C(s,t)}{(aB_C)_t}
\ge\frac uv\frac{a_s}{\sum_{r\in I_C}a_r},
\tag{4.6}
$$

所以前向和后向均有同一个 $\rho$，且与两侧外部似然无关。这些收缩只作用于正分母的可行行；反向可行终点属于 $J_C$。若 $\sum_{J_C}z=0$ 或 $\sum_{I_C}a=0$，相应含词记录的似然为零。任意非负外部消息，包括有零坐标的消息，只须所比较的条件事件有正概率。

对左擦除，取有限 $k\ge j\ge0$、$n\ge1$，在正概率记录上比较

$$
P_C(X_0=1\mid X_{-k:-1},X_{1:n})\quad\text{与}\quad
P_C(X_0=1\mid X_{-j:-1},X_{1:n}).
$$

置

$$
y=M_{x_{1:n}}\mathbf1,\qquad z_0=Ay,\qquad
z_t=M_{x_t}z_{t+1}\quad(-j\le t\le-1),\qquad
a=\pi M_{x_{-k:-j-1}}.
$$

由原联合律的乘积分解，两种条件下 $H_{-j}$ 的分布分别为

$$
\mu(s)=\frac{a_s z_{-j}(s)}{a z_{-j}},\qquad
\bar\mu(s)=\frac{\pi_s z_{-j}(s)}{\pi z_{-j}}.
$$

较短观测事件包含较长观测事件，故两个分母均为正。在 $z_t(s)>0$ 的状态上，两种条件下从 $H_t$ 到 $H_{t+1}$ 的共同转移为

$$
T_t(s,h)=\frac{M_{x_t}(s,h)z_{t+1}(h)}{z_t(s)}
\quad(-j\le t\le-1).
$$

递推式使每行和为一，且转移只到达下一步的正分母状态；额外过去只改变 $\mu$，不改变这些核。因此 $H_0$ 的两个条件律恰为 $\mu T_{-j}\cdots T_{-1}$ 和 $\bar\mu T_{-j}\cdots T_{-1}$。中心缺失边保留位值 $e\in\{0,1\}$ 的共同转移及其位读出为

$$
U_0(s;e,h)=\frac{M_e(s,h)y_h}{(Ay)_s},\qquad
g(s)=\sum_h U_0(s;1,h)=\frac{(M_1y)_s}{(Ay)_s}\in[0,1].
$$

对 $e$ 求和得到 $A(s,h)y_h/(Ay)_s$，即原中心 $A$ 边在这些观测下的条件转移；两个待比较后验恰为上述两个 $H_0$ 条件律对同一 $g$ 的积分。

对右擦除，比较

$$
P_C(X_0=1\mid X_{-n:-1},X_{1:k})\quad\text{与}\quad
P_C(X_0=1\mid X_{-n:-1},X_{1:j}).
$$

置

$$
\ell=\pi M_{x_{-n:-1}},\qquad a_1=\ell A,\qquad
a_{t+1}=a_tM_{x_t}\quad(1\le t\le j),\qquad
\xi=M_{x_{j+1:k}}\mathbf1.
$$

两种条件下 $H_{j+1}$ 的分布分别为

$$
\nu(h)=\frac{a_{j+1}(h)\xi_h}{a_{j+1}\xi},\qquad
\bar\nu(h)=\frac{a_{j+1}(h)}{a_{j+1}\mathbf1}.
$$

从 $H_{t+1}$ 反向到 $H_t$ 的共同随机核为

$$
Q_t(h,s)=\frac{a_t(s)M_{x_t}(s,h)}{a_{t+1}(h)}
\quad(t=j,\ldots,1),
$$

在 $a_{t+1}(h)>0$ 上每行和为一，且只到达正分母状态。额外右侧观测只改变起始律 $\nu$，这些核只使用共同左消息和共同的较早观测。故 $H_1$ 的两个条件律为 $\nu Q_j\cdots Q_1$ 和 $\bar\nu Q_j\cdots Q_1$。中心缺失边的反向核及位读出为

$$
V_0(h;e,s)=\frac{\ell_sM_e(s,h)}{(\ell A)_h},\qquad
g^{\rm back}(h)=\sum_s V_0(h;1,s)=\frac{(\ell M_1)_h}{(\ell A)_h}\in[0,1].
$$

对 $e$ 求和得到 $\ell_sA(s,h)/(\ell A)_h$，仍为原中心 $A$ 边的反向条件转移。这两个后验恰为两个 $H_1$ 条件律对同一 $g^{\rm back}$ 的积分，不作平稳密度除法。

在一段完整的 $w_C$ 上，$T_t$ 的乘积约去中间似然，恰为 (4.5) 的 $K_z$，其中 $z$ 是词右端消息；反向的 $Q_t$ 乘积恰为 (4.6) 的 $K_a^{\rm back}$，其中 $a$ 是词左端消息。因此每段这样的词在可行状态间给出因子至多 $\rho$，其余共同随机转移的因子至多为一。这是对已经条件化的两个起始概率律施加共同线性随机核：起始 TV 至多为一，不对从原先验到 $\mu,\bar\mu$ 或 $\nu,\bar\nu$ 的 Bayesian 归一化主张收缩。上述乘积分解和约去对任意使分母为正的非负外部消息均成立。

现在明确计数的可见事件。令 $q=\lfloor j/b\rfloor$，在两侧分别固定原始位块

$$
D_i^L=[-qb+(i-1)b,-qb+ib-1],\qquad
D_i^R=[1+(i-1)b,ib]\quad(1\le i\le q).
$$

两侧未入整块的位仍通过上述共同随机核传递。对任一块 $D=[d,d+b-1]$，定义

$$
S_D=\bigcup_{t=0}^{b-m}\{X_{d+t:d+t+m-1}=w_C\},\qquad
I_D=\mathbf1_{S_D},\qquad
K_j^L=\sum_{i=1}^q I_{D_i^L},\quad K_j^R=\sum_{i=1}^q I_{D_i^R}.
$$

$S_D$ 是同一个只依赖块内发射位的成功事件，不依赖隐藏起点。在每个成功块中选最早的一次完整出现；不同块中的所选词区间不交叠，每个成功块恰支付一次收缩。两对有限后验差的绝对值分别不超过 $\rho^{K_j^L}$ 和 $\rho^{K_j^R}$：起始 TV 至多为一，而同一 $[0,1]$ 值读出的期望差至多为终端 TV，故不引入因子二。

左侧先令 $k\to\infty$，再令 $n\to\infty$；右侧先补齐右侧令 $k\to\infty$，再补齐左侧令 $n\to\infty$。每一步标量条件期望均由有界鞅收敛而几乎处处及在 $L^2$ 中收敛，两个可见块数保持不变。令 $K=K_j^L$，得到

$$
|q_0-p_j^L|\le\rho^K\quad P_C\text{-几乎处处}.
\tag{4.7}
$$

同理 $|q_0-p_j^R|\le\rho^{K_j^R}$。可数个有限记录及指标可共用一个零集约定；零概率观测柱和未用的零分母状态均不贡献质量，不需要归一化无限似然向量。

支付成功概率时，使用原联合律的时间顺序。对块起点 $d$ 置 $\mathcal F_d=\sigma(H_i:i\le d;\ X_i:i<d)$。给定 $\mathcal F_d$ 且 $H_d=h$，沿定理所选长度 $t_h\le n_C$ 的带标签路径到 $r$，再发射 $w_C$；$h=r$ 时取空前缀，$t_r=0,d_r=1$。这段事件的条件概率为 $d_h(B_C\mathbf1)(r)\ge\varepsilon$。余下 $b-t_h-m$ 位任意求和为一，因为 $A\mathbf1=\mathbf1$。该隐藏事件包含于同一个 $S_D$，因为 $t_h+m\le b$；隐藏起点只选择了证明下界的子事件，未改变所计数的可见成功事件。

这里的接缝仍由原标量 no11 条件支付：$\pi$ 在 $C$ 上严格为正，故类内没有正的连续两条 $1$ 边。若词首位为 $1$，$r$ 有正的 $1$ 出边，所以任何正入 $r$ 的边都不能发射 $1$；不可约性给出一条正的 $0$ 入边。到其起点的简单路径再接该边长至多 $n_C$；在 $h=r$ 的空前缀情形，一个实际到达 $r$ 的过去也不可能刚发射 $1$。词首位为 $0$ 时，长至多 $n_C-1$ 的简单路径已经足够。所选正路径和词内部的所有接缝同样合法。这些都是正权类内的结论，不把全局标量条件加强为额外假设。

因此 $\mathbb J_C(S_D\mid\mathcal F_d)\ge\varepsilon$，并有

$$
\mathbb E_{\mathbb J_C}[\rho^{2I_D}\mid\mathcal F_d]
=1-(1-\rho^2)\mathbb J_C(S_D\mid\mathcal F_d)
\le1-\varepsilon(1-\rho^2)=\eta.
$$

两侧的块都按 $i=1,\ldots,q$ 的时间先后顺序平均；此前块的指标在下一块起点的 $\mathcal F_d$ 中可测。逐块迭代条件期望，得到

$$
\mathbb E_{\mathbb J_C}\rho^{2K_j^L}\le\eta^q,\qquad
\mathbb E_{\mathbb J_C}\rho^{2K_j^R}\le\eta^q.
$$

右侧虽反向传递条件律，成功概率仍按前向时间顺序平均，所以使用同一个 $\varepsilon$。此处不要求块独立，也不要求额外给定未来后仍有成功概率下界。对两个点态后验界平方并按同一实际律积分，即得 (4.3)。

$j=0$ 时转移乘积和块列均为空，$K_j^L=K_j^R=0$，界为一，且各自仍条件于另一侧整条半线。约定 $0^0=1$；若 $\rho=0$，一次成功就使传递后的两个律相同。$0<\varepsilon\le1$ 且 $0\le\rho<1$，故 $\rho^2\le\eta<1$；若 $\eta=0$，则 $\varepsilon=1,\rho=0$，每块几乎必然成功，$j\ge b$ 时两个缺陷均为零。每个 $\lfloor j/b\rfloor$ 的值至多出现 $b$ 次，从 $\lfloor R/b\rfloor$ 起分别求和平方界及其平方根即得 (4.4)，包括上述零值情形。$\square$

由定理 2.1，若每个正权类都满足矩形词前提，令 $b=\max_Cb_C$、$\eta=\max_C\eta_C<1$，则对原律

$$
e_L^P(j),e_R^P(j)\le\eta^{\lfloor j/b\rfloor},\qquad A_P\le\frac{2b}{1-\sqrt\eta}.
\tag{4.8}
$$

更精确的加权尾界为

$$
A_P(R)\le2\sum_C\frac{\sqrt{w_C}\,b_C\eta_C^{\lfloor R/b_C\rfloor/2}}{1-\sqrt{\eta_C}},\qquad
\tau_P(R)\le2\sum_C\frac{w_Cb_C\eta_C^{\lfloor R/b_C\rfloor}}{1-\eta_C}.
\tag{4.9}
$$

这些是指定实际律的常数；不构成对 $\Theta_N$、后验带域或参数闭包的统一估计。

## 5. 两向 flag-block 路线与 Travers 转移

**定义 5.1（双向 flag-block 前提）。** 在每个正权闭不可约类上，分别对原始前向标记矩阵和精确时间反向矩阵假设：存在共同长度 $m\ge1$，与该类隐藏周期互素；对每个目标态 $k$ 存在正概率发射词 $v_k\in B_m$，使对所有能以该词产生正质量的起点 $i$，均有

$$
(M_{v_k})(i,k)>0.
\tag{5.1}
$$

前向和反向是两个独立的附加条件。它不等同于整个词矩阵正，也不由后验带或有限维推出。

**定理 5.2（flag-block 的原律根和界）。** 在定义 5.1 的一个方向上，设该类有 $n$ 个隐藏态、平稳行 $\pi$。把该方向选定的 $m$ 个原始发射位只在证明中分组，令 $Q^v=M_v$，分组链的转移矩阵为 $A^m$。置

$$
\begin{aligned}
p_k&=\frac{\sum_i\pi_iQ^{v_k}(i,k)}{\pi_k},\qquad
q_k=\min_{i:(Q^{v_k}\mathbf1)(i)>0}\frac{Q^{v_k}(i,k)}{(Q^{v_k}\mathbf1)(i)},\\
p_*&=\min_kp_k,\qquad q_* =\min_kq_k,\qquad
r_* =\min_{i,h}\frac{\pi_i}{\pi_h},\\
\alpha_1&=\exp\!\left(-\frac{p_*^2r_*^2}{2n^2}\right),\qquad
\alpha_2=(1-q_*^2)^{p_*r_*/(2n)}.
\end{aligned}
\tag{5.2}
$$

则该方向的平方缺陷满足，对 $k=\lfloor j/m\rfloor$，

$$
e_d(j)\le\min\{1,\,2(\alpha_1^k+\alpha_2^k)\}.
\tag{5.3}
$$

因而

$$
\begin{aligned}
\sum_{j\ge R}\sqrt{e_d(j)}
&\le\sqrt2\,m\left(
\frac{\alpha_1^{\lfloor R/m\rfloor/2}}{1-\sqrt{\alpha_1}}
+\frac{\alpha_2^{\lfloor R/m\rfloor/2}}{1-\sqrt{\alpha_2}}\right),\\
\sum_{j\ge R}e_d(j)
&\le2m\left(
\frac{\alpha_1^{\lfloor R/m\rfloor}}{1-\alpha_1}
+\frac{\alpha_2^{\lfloor R/m\rfloor}}{1-\alpha_2}\right),
\end{aligned}
\tag{5.4}
$$

其中 $0^0=1$。对左擦除取原始前向条件，对右擦除把同一论证施加于反向律；两者不能由单一方向的 flag 条件互推。

**证明。** 先取 $j=mk$。对每个正概率输出词 $u$，从起点 $i$ 的端点后验为

$$
\varphi_i(u)=\frac{\delta_iM_u}{\delta_iM_u\mathbf1}
$$

（正分母上）。给定 $H_{-j}=i$ 和该 $j$ 位词，完整更远过去只改变起点 $i$ 的混合权重；因此 $\alpha_\infty$ 与 $\alpha_j$ 都是同一族可行 $\{\varphi_i(u)\}$ 的凸组合。它们的 TV 距离不超过该族直径。

分组后的 $u$ 服从分组链 $A^m$ 的平稳 $k$-词律；分组没有改变任何接缝质量。Travers 的 Section 3.1 equation (5)、Lemma 1 与 Lemma 2 在 flag 条件下给出集合 $G_k$，满足

$$
P(G_k^c)\le\alpha_1^k,\qquad
\operatorname{diam}_{\rm TV}\{\varphi_i(u):\delta_iM_u\mathbf1>0\}\le\alpha_2^k\quad\text{对每个 }u\in G_k.
\tag{5.5}
$$

故

$$
\mathbb E_{J_\theta}\operatorname{TV}(\alpha_\infty,\alpha_{mk})
\le\alpha_1^k+\alpha_2^k.
\tag{5.6}
$$

定理 3.2 给出 $e_L(mk)\le2(\alpha_1^k+\alpha_2^k)$。当 $j\ge mk$ 时，$\mathcal L_{mk}\subseteq\mathcal L_j$，所以实际平方投影误差单调不增，(5.3) 对所有 $j$ 成立。$k=0$ 时使用 $e_L(j)\le1$。

对右方向，在正权类上定义

$$
\check M_x(i,h)=\frac{\pi_hM_x(h,i)}{\pi_i}.
\tag{5.7}
$$

则 $\check A\mathbf1=\mathbf1$、$\pi\check A=\pi$，并且

$$
\check M_{x_1}\cdots\check M_{x_r}
=\operatorname{diag}(\pi)^{-1}(M_{x_r}\cdots M_{x_1})^{\mathsf T}\operatorname{diag}(\pi).
\tag{5.8}
$$

反射联合律 $\check H_i=H_{1-i}$、$\check X_i=X_{-i}$ 的可见律满足 $\check P([x_1\cdots x_r])=P([x_r\cdots x_1])$，并保留标量 no11 合法性。反射律的左擦除正是原律的右擦除；将 (5.5)–(5.6) 用于反向 flag 词得到右式。这里反向律只是同一 $J_\theta$ 的证明坐标，不是另一个优化生产者。

最后使用 $\sqrt{s+t}\le\sqrt s+\sqrt t$，并注意每个 $k$ 至多对应 $m$ 个原始位，即得 (5.4)。$\square$

Travers Section 3.2 Definition 8 与 Lemma 5 的路径合并构造还表明：若该方向任意两态都有一个词能从两者正概率到达同一目标，则可得到与类周期互素的 flag 分组长度。因此路径合并可以作为定义 5.1 的另一条明确充分前提；它不是有限状态、后验带或达到性的自动结论。

## 6. 两个原始域符号构造与边界

**命题 6.1（无限可见记忆的 renewal 子族）。** 取 $0<a<b<1$、$0<p<1$，在态 $\{R,U,V\}$ 上置

$$
M_0=\begin{pmatrix}0&p&1-p\\0&1-a&0\\0&0&1-b\end{pmatrix},\qquad
M_1=\begin{pmatrix}0&0&0\\a&0&0\\b&0&0\end{pmatrix},\qquad
Z=1+\frac pa+\frac{1-p}{b},\quad
\lambda=\frac1Z\left(1,\frac pa,\frac{1-p}{b}\right).
\tag{6.1}
$$

这是 $\Theta_3$ 中的原始生产者。其可见律没有有限 Markov 阶。实际发射 $1$ 的矩形支撑为 $\{U,V\}\times\{R\}$，所以定理 4.2 直接支付 $A_P<\infty$。

**证明。** $M_0+M_1$ 每行和为一；站立方程为

$$
\lambda_Ua=\lambda_Rp,\quad\lambda_Vb=\lambda_R(1-p),\quad
\lambda_R=\lambda_Ua+\lambda_Vb,
$$

按 (6.1) 全部成立。$M_1^2=0$，故标量 no11 条件成立。图不可约且 $U,V$ 有正的零自环，因此非周期。每个 $1$ 之后状态回到 $R$，随后先发一个确定的 $0$，再以概率 $p$ 或 $1-p$ 进入 $U$ 或 $V$。相邻可见 $1$ 的距离独立同分布，且

$$
f(n)=pa(1-a)^{n-2}+(1-p)b(1-b)^{n-2},\qquad n\ge2.
\tag{6.2}
$$

这些是同一 $J_\theta$ 中由重置态 $R$ 产生的 renewal 间隔，不是另选的可见律。

令 $s=1-a$、$k=pa+(1-p)b$。若显式加入

$$
\frac{p^2a^2}{ks^2}\ge\frac13,\qquad
\frac{k^2}{pas^2}\le1,
\tag{6.3}
$$

则该族满足 $\mathsf B(P)$。这组参数非空：先取

$$
\frac{5-\sqrt{21}}2<a<\frac{3-\sqrt5}2,
$$

使 $1/3<a/(1-a)^2<1$，再取任意 $b\in(a,1)$，最后令 $p\uparrow1$；(6.3) 由连续性在充分接近 $1$ 时严格成立。

在自由事件 $F_0$ 上，设左右最近的 $1$ 距中心距离分别为 $\ell,r\ge2$。renewal 分解和条件期望极限给出

$$
\frac{q_0}{1-q_0}=\frac{f(\ell)f(r)}{f(\ell+r)}.
\tag{6.4}
$$

由于

$$
pa\,s^{n-2}\le f(n)\le k\,s^{n-2},
$$

右侧在 $p^2a^2/(ks^2)$ 与 $k^2/(pas^2)$ 之间，故 (6.3) 使 $1/3\le q_0/(1-q_0)\le1$，即 $q_0\in[1/4,1/2]$；强制事件上 $q_0=0$。平移给出全部坐标的带条件。

另一方面，条件事件 $X_{-n}=1,X_{-n+1:-1}=0^{n-1}$ 的下一位概率为

$$
\frac{pa\,s^{n-2}+(1-p)b(1-b)^{n-2}}
{p\,s^{n-2}+(1-p)(1-b)^{n-2}},\qquad n\ge2.
\tag{6.5}
$$

因为 $(1-b)/s<1$ 且 $b>a$，(6.5) 随 $n$ 严格变化。若有有限可见阶 $m$，所有 $n>\max(m,1)$ 的这些正概率历史有相同的最后 $m$ 个零，塔性质将迫使下一位概率相同，矛盾。矩形词定理支付根和，但这里没有声称达到、严格分离或 $\mathsf Z(P)$。$\square$

**命题 6.2（相位复制的无矩形词和滤波边界）。** 取可见两态律

$$
A^a=\begin{pmatrix}1-a&a\\1&0\end{pmatrix},\qquad
\lambda^a=\left(\frac1{1+a},\frac a{1+a}\right),\qquad 0<a<1,
\tag{6.6}
$$

并令隐藏态为 $(v,z)$，$z\in\{0,1\}$，每个原始发射位都翻转相位：

$$
M_x((v,z),(v',z'))=\mathbf1_{\{x=v\}}A^a(v,v')\mathbf1_{\{z'=1-z\}},\qquad
\lambda(v,z)=\lambda^a(v)/2.
\tag{6.7}
$$

该 $\Theta_4$ 生产者的可见律正是 (6.6) 的 $R^a$，其实际隐藏类不可约且周期二。若 $a/((1-a)^2+a)\in[1/4,1/2]$，它满足可见后验带，并且

$$
e_L(j)=e_R(j)=0\quad(j\ge1),\qquad
e_L(0)=e_R(0)=\frac{a^3(1-a)}{(1+a)(1-a+a^2)}.
\tag{6.8}
$$

因此 $A_P<\infty$，但不存在矩形词或 flag 词；隐藏滤波在不同初始相位之间可以永久不稳定，而输出擦除误差仍在一步后消失。

**证明。** (6.7) 的行和为一，$\lambda$ 平稳；可见求和消去相位得到 $\lambda^a$ 与 $A^a$，所以可见律为原 $R^a$。相位每步翻转，且可见链有足够长的两种奇偶路径，故四态图不可约、周期二。对任意非零词 $w$，

$$
M_w=M_w^{\rm vis}\otimes F^{|w|},
$$

其中 $F$ 是两态翻转矩阵。每个可行可见起点的两个相位副本都产生该词，但各自只到达一个相位终点；交叉相位条目为零。因此非零词矩阵的支撑不是非空矩形。对任一目标相位，两个起始相位都能产生同一词而仅一个能到达目标，故 flag 条件也失败。

可见自由后验为

$$
q_0=\frac a{(1-a)^2+a}\quad\text{于 }F_0,\qquad q_0=0\quad\text{于 }F_0^c.
$$

当 $j\ge1$，两种单侧字段都包含两个即时邻居，故已等于 $q_0$。当 $j=0$，例如 $p_0^L=\mathbb E[X_0\mid X_{1:\infty}]$ 在 $X_1=0$ 时为 $a$、在 $X_1=1$ 时为零。由

$$
P(X_{-1}=0,X_1=0)=\frac{1-a+a^2}{1+a},\qquad
P(X_{-1}=1,X_1=0)=\frac{a(1-a)}{1+a},
$$

以及 $q_0=a/(1-a+a^2)$，直接展开 $(q_0-p_0^L)^2$ 得 (6.8)；时间反射给出右式。

若以已知初始相位启动隐藏链，相位在每个时刻都被确定；以平稳初始律启动时，观察对相位无信息，滤波保持两相位均匀。因此这两种初始化的隐藏滤波 TV 距离至少为 $1/2$，但同一实际输出律的 $e_L,e_R$ 在 $j\ge1$ 为零。该差异不构成原域发散根尾的反例，也不把隐藏相位当作可见分量标签。$\square$

## 7. 对既有损失、响应和二阶问题的精确消费

当指定原律的每个正权实际分量满足定理 4.2 或定理 5.2 的相应前提时，(4.4) 或 (5.4) 支付 $A_P(R)$ 和 $\tau_P(R)$。若另有后验带 $\mathsf B(P)$，既有合法替换与损失 cocycle 的估计可以直接使用同一原律：对长度 $L$ 的块 $C$，

$$
\mathbb E_P\sum_i|\ell_i(X)-\ell_i(Z_CX)|
\le L+2(1+2^{L/2})A_P.
\tag{7.1}
$$

这里 $q_i$ 和 $\ell_i$ 在替换后仍是原始 $P$ 的函数；没有重算替换律的后验。

既有二阶局部理论的同一误差项可取为

$$
\varepsilon_{C,R,r}=2(1+2^{L/2})\left[A_P(R)+(L+2R)\sqrt{D_r(P)-d(P)}\right].
\tag{7.2}
$$

在假设达到性并保留其全部必要预算时，第二项可进一步用 $\sqrt{\bar c/(r+1)}$ 控制；本卷支付的只是第一项。若一个独立的 intrinsic-null 方向已经给出非零全响应，既有有限检测式可使用 $\tau_P(R)$；根和定理本身不给出非零方向、非零响应或达到性。

这些消费保留以下未付义务：独立的 RP/响应路线、二阶平方残差是否必须为零或能否非零、所有高阶条件空间和秩保持、多个修改的平稳连续构造，以及任何从这些局部事实到原始风险目标的桥接。单个固定局部 tilt 的平移平均回到 $P$，不构成新的全局继续律。

## 8. 归属、主要来源与边界

本卷新增的是：(i) 定理 2.1 的实际可见分量平方缺陷仿射性及根和等价；(ii) 定理 4.2 的原矩形词、任意外部似然、有限状态出现概率和期望根尾支付；(iii) 定理 3.2 的因子 $2$ 同一律 TV 到输出后验 $L^2$ 转移；(iv) 定理 5.2 对 Travers flag-block 估计的双向原钟应用；(v) 命题 6.1–6.2 的符号边界族。完整目标、$\Theta_N$、$J_\theta/P_\theta$、实际分量、后验带、合法替换与损失 cocycle、intrinsic kernel、二阶局部消费和固定 tilt 平均均按下列接口使用，未在此卷重新归属。

| 来源 | 本卷精确使用 |
| --- | --- |
| *FIB 合法边调和负载：普适后验缺陷与有限隐藏维数分离* [U]；文件 FIB_LEGAL_EDGE_LOAD_UNIVERSAL_POSTERIOR_DEFECT_AND_FINITE_HIDDEN_SEPARATION.md；定义 1.1–4.2、定理 3.1、5.1、6.2 | 完整 no11 目标、实际 $\Theta_N/J_\theta/P_\theta$、必要后验带、实际闭类分解、有限维固定-$N$ 等价与原始未决量词。 |
| *FIB harmonic-edge load: exterior localization and actual loss-cocycle balance* [E]；文件 FIB_LEGAL_EDGE_LOAD_EXTERIOR_LOCALIZATION_AND_ACTUAL_LOSS_COCYCLE_BALANCE.md；定理 3.1、4.2、5.1 | 兼容纤维、原始后验下的合法替换、绝对损失 cocycle、全长度外部定位和 pair 路线。 |
| *FIB harmonic-edge load: second-order loss localization and local tilt averaging obstruction* [S]；文件 FIB_LEGAL_EDGE_LOAD_SECOND_ORDER_LOSS_LOCALIZATION_AND_LOCAL_TILT_AVERAGING_OBSTRUCTION.md；定理 3.1–7.1 | $L^2$ 损失差、中心化分数、平方残差定位、有限预测误差、$C^2$ tilt 与固定 tilt 平均的下游消费。 |
| Juri Lember, *On approximation of smoothing probabilities for hidden Markov models*, arXiv:0910.4636v3 | 只作为隐藏平滑近似的条件范围和随机前因子边界；其有限随机因子未被当作期望矩。 |
| Juri Lember and Joonas Sova, *Exponential forgetting of smoothing distributions for pairwise Markov models*, arXiv:2103.05474v1 | Section 3.1 的矩形端点条件和期望界的对应背景；本卷定理 4.2 直接在原标记矩阵上证明。 |
| Nicholas F. Travers, *Exponential Bounds for Convergence of Entropy Rate Approximations in Hidden Markov Models Satisfying a Path-Mergeability Condition*, arXiv:1211.6181v2，Section 3.1 equation (5)、Lemmas 1–2、Section 3.2 Definition 8、Lemma 5 | 提供 (5.5) 的 good-set 概率与 flag 条件收缩、以及路径合并到互素分组长度的范围。熵率结论未被替换为输出擦除结论；原 edge-emitting clock、分组词矩阵和反向律映射按 (5.2)、(5.7)–(5.8) 明确核对。 |
| 条件期望投影、TV 数据处理、Dobrushin 收缩、有限链词出现、遍历频率、signed-measure 唯一性 | 作为成熟证明工具使用，不宣称本卷原创。 |

Travers 的使用仅在有限不可约平稳 edge-emitting 类、每个目标有 flag symbol、并按 Definition 8 选择与周期互素的分组长度的范围内成立。矩形词路线不要求该 primary 结果；两条路线也都不推出全体有限隐藏律的统一常数。

## 9. 未决的原始目标

对全体 $\Theta_N$ 的固定律命题

$$
\mathsf Q_{\rm full}:\quad A_{P_\theta}<\infty\text{ 对每个有限 }N\text{ 和每个 }\theta\in\Theta_N
$$

仍 open。加上 (1.5) 的命题 $\mathsf Q_{\rm band}$ 也仍 open；带条件 renewal 子族只证明存在满足带和根和的无限记忆实例。若要否定其中任一命题，必须给出原始完整 no11 域中的具体 $\theta$，并对其同一 $q_0,p_j^L,p_j^R$ 手工证明发散根和；隐藏滤波不稳定、没有本卷充分词或非周期失败都不够。

原始有限达到问题仍完整保留。令

$$
C_N=\sup_{\theta\in\Theta_N}d(P_\theta),\qquad
U_{N,r}=\max_{\theta\in\Theta_N}D_r(P_\theta).
$$

仍需决定是否存在有限 $N$ 和 $\theta$ 使 $d(P_\theta)=c_\star$，或是否每个有限 $N$ 都有 $C_N<c_\star$；后者等价于

$$
\forall N\ge1\ \exists r,m\ge1:\qquad U_{N,r}<\frac{\kappa_m}{m+1}.
\tag{9.1}
$$

本卷没有证明、反驳或替换这一完整量词目标，也没有作 kernel truth、经验机器学习收益或 worldwide originality 的声明。

## 追加锚（本行以下为增补区）
