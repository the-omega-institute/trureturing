# AURIC 全部探针与环境耦合的固定输出延续 II：零模耦合为零的可行闭区间

本卷承接[前卷 §17](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md#17-全部原探针的共同六维读取支撑) 的共同读取与全正泛函提升、[§27](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md#27-全有限类的联合探针与环境系数判据) 的原联合二次型、[§27A](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md#27a-满行秩原四维族的线性尺度正预算排除域) 的四维排除域、[§28](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md#28-原输入的齐次核与环境零模像上的值域障碍) 的核与值域条件、[§29](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md#29-平衡零模像线的有限核反例与整类残量刚性) 和 [§30A](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md#30a-非零零模像上全部原-pb-消去两个独立对角残量) 的非零零模像结论，以及 [§30](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md#30-零模耦合为零的三矩实现与最小真实环境) 的零模耦合为零分支。下文编号为 §32；未加前缀的旧式号均指前卷。这里在 (30.30) 的可实现三矩域中给出一条固定矩族：一个与 Schur 块小扰动无关的 PB 半径包含该族的整个原 P2 闭区间。

## 32. 同一四维实际环境的全部原 PB 与精确 P2 交

**定义 32.1（固定三矩的四维族）。** 在完整 $M_4(\mathbb C)$ 上取演员与环境各为 $\mathbb C^2$，固定

$$
\begin{gathered}
C=\operatorname{diag}(1,2),\qquad T_A=\operatorname{diag}(1,-2),
\qquad J_A=\begin{pmatrix}0&1\\1&0\end{pmatrix},\\
c=C\oplus0_2,\qquad P=I_2\oplus0_2,\qquad V=D_{\rm env}=C,\\
H_h=2C+hJ_A,\qquad B_h=H_h+C,\qquad
t_h=\begin{pmatrix}B_h&C\\C&C\end{pmatrix},\qquad
s=\rho T_A\oplus0_2,\qquad h,\rho\in\mathbb R .
\end{gathered}
\tag{32.1}
$$

沿用 (1.1)–(1.2)、(17.1) 的原 P2、原 PB 与全部实际探针 $x=X\oplus0_2$，其中 $X=X^*$。取向 $\sigma$ 的输出仍为 $g_\sigma=\sigma i[c,t_h]/2+s$。因 $D_{\rm env}$ 可逆，$W=V|_{\ker D_{\rm env}}=0$。按 (30.2) 有 $F=C$、$G=I_2$，故原三矩恰为 $(M_0,M_1,M_2)=(C^2,C,I_2)$，Schur 块恰为 $H_h$。环境块与三个矩在全族中固定。

**定理 32.2（统一 PB 半径与闭区间的两个端点）。** 存在 $h_*,\rho_*>0$，使对每个 $|h|<h_*$，同一 (32.1) 输入在每个 $|\rho|<\rho_*$ 时满足两个取向的全部原 PB。对每个 $0<h<h_*$ 以及任意实 $\rho$，以下结论等价：该输入在两个取向均满足原 P2 与全部原 PB；该输入在任一个分别固定的取向满足原 P2 与全部原 PB；以及

$$
\boxed{\quad -\frac{\sqrt2\,h}{3}\ \le \rho\le\ \frac{\sqrt2\,h}{3}.\quad}
\tag{32.2}
$$

这里所有预算都在完整原代数上对全部正复线性泛函成立，包括任意指定正有限质量与零质量。区间的两个非零端点均严格位于 $|\rho|<\rho_*$ 内。特别地，可固定 $h=h_*/2$ 和 $\rho=\sqrt2\,h/3$，在同一份 $t_h,s$ 上同时得到两个取向的非零残量解。

**证明：原带符号二次型。** 暂写 $B=B_h$、$H=H_h$、$t=t_h$，并记 $\iota=\sigma i$。对复数 $z$ 定义 $\operatorname{Im}_\iota z$ 为 $z$ 在基 $1,\iota$ 下的虚系数。固定 (27.6) 的任意索引 $\theta$，即单位演员 $u$、绝对值符号 $\epsilon\in\{1,-1\}$ 及两对有限参数 $\alpha_\delta>0,\ \beta_\delta\in\mathbb R$。在同一原向量 $\xi=(u,y)$、同一实际 $X=X^*$ 上写 $\mathbf R_\delta=R_\delta\xi$、$\mathbf S_\delta=S_\delta\xi$，其中 $S_\delta=t+\delta(r+g_\sigma)$ 是 (27.10) 的原算子。置

$$
\begin{aligned}
\zeta_\delta&=\beta_\delta-\delta\epsilon\iota\alpha_\delta
             =\iota+\nu+\delta\ell,\qquad
E_\delta=\mathbf S_\delta-\zeta_\delta\mathbf R_\delta,\qquad
S_0=\sum_{\delta=\pm1}\alpha_\delta^{-1}\|E_\delta\|^2,\\
\mathcal D_\rho&=\sum_{\delta=\pm1}
  \left(\alpha_\delta\|\mathbf R_\delta\|^2+
        \alpha_\delta^{-1}\|\mathbf S_\delta-\beta_\delta\mathbf R_\delta\|^2\right)
        -2\epsilon\phi_\xi(L).
\end{aligned}
\tag{32.3}
$$

$S_0$ 是同一输入在当前 $\rho$ 上的平方和。把平方展开，其交叉项为
$2\delta\epsilon\operatorname{Im}_\iota(\mathbf R_\delta^*\mathbf S_\delta)$，即 $-2\delta\epsilon\phi_\xi(K_\sigma(R_\delta,S_\delta))$。因此

$$
\mathcal D_\rho-S_0
=2\epsilon\,\phi_\xi\!\left(\sum_\delta\delta K_\sigma(R_\delta,S_\delta)-L\right).
$$

前卷 §1 的原换位恒等式给括号内的零残量部分为零。写 $a=Bu+Vy$、$p=Xu$、$v=a-\iota p$。加入 $s$ 使 $S_\delta$ 增加 $\delta s$、使 $L$ 减去 $2t\circ s$，而 $R_++R_-=2x$。故括号内的改变量是 $2K_\sigma(x,s)+2t\circ s$。其向量读数为 $2\rho\operatorname{Re}(v^*T_Au)$，因为 $\phi_\xi(K_\sigma(x,s))=\rho\operatorname{Re}(\iota p^*T_Au)$。这给出原二次型的精确恒等式

$$
\mathcal D_\rho=S_0+4\epsilon\rho\operatorname{Re}(v^*T_Au).
\tag{32.4}
$$

**证明：实际作用列与加权方差。** 记 $q=XCu$、$d=Fu+D_{\rm env}y$、$U=\iota q+BCu+Cv$。按 (27.4)–(27.5) 在 $\tau=1$ 的原作用列，$\mathbf R_\delta$ 的两块为 $p-\delta U/2$、$-\delta FCu/2$；$\mathbf S_\delta$ 的两块为

$$
a+\delta\left(\frac{Cp+q+\iota Ca-\iota BCu}{2}+\rho T_Au\right),
\qquad d-\frac{\delta\iota}{2}FCu .
$$

代入 $\zeta_\delta$ 后，$E_\delta$ 的演员与环境块分别是

$$
\begin{aligned}
(E_\delta)_{\rm act}&=\mathsf P+\delta\mathsf Q,\qquad
\mathsf P=v-\nu p+\ell U/2,\qquad
\mathsf Q=\iota Cv-\ell p+\rho T_Au+\nu U/2,\\
(E_\delta)_{\rm env}&=d+(\ell+\delta\nu)FCu/2 .
\end{aligned}
\tag{32.5}
$$

令 $r_\ell=|\ell|$、$n=|\nu|$、$A=(\alpha_++\alpha_-)/2$。两条 $\zeta_\delta$ 的虚系数给出

$$
|1+\operatorname{Im}_\iota\nu|<A=-\epsilon\operatorname{Im}_\iota\ell\le r_\ell,
\qquad r_\ell+n\ge1 .
\tag{32.6}
$$

反过来，给定满足 (32.6) 首行的 $\nu,\ell,A$，取 $\alpha_\delta=A-\delta\epsilon(1+\operatorname{Im}_\iota\nu)$、$\beta_\delta=\operatorname{Re}(\nu+\delta\ell)$ 即还原原参数。特别地 $r_\ell>0$。记 $w_\delta=\alpha_\delta^{-1}$、$\omega=(w_+-w_-)/(w_++w_-)$ 及 $e=d+(\ell+\omega\nu)FCu/2$。以 $e$ 为同一对环境列的加权平均，交叉项相消，且 $w_+w_-/(w_++w_-)=1/(2A)$，故

$$
\begin{aligned}
\sum_\delta w_\delta\|(E_\delta)_{\rm env}\|^2
 &=(w_++w_-)\|e\|^2+\frac{n^2}{2A}\|FCu\|^2,\\
a&=Hu+G^*e-\frac{\ell+\omega\nu}{2}\,C^2u .
\end{aligned}
\tag{32.7}
$$

第二行用 $a=Hu+G^*d$、$G^*F=C$。由加权 Cauchy–Schwarz 对 $\mathsf P$ 和 $\mathsf Q$ 的半和、半差分别估计，每项范数至多 $\sqrt{2AS_0}/2$。又 $w_++w_-\ge2/A$，故 $\|e\|\le\sqrt{AS_0/2}$。于是

$$
\|\mathsf P\|+\|\mathsf Q\|+\|e\|\le3\sqrt{r_\ell S_0},
\qquad
\|a\|\le K(1+r_\ell+n+\sqrt{r_\ell S_0}).
\tag{32.8}
$$

下文的 $K$ 可逐式增大，均只依赖固定矩阵与一个预先固定的有界邻域 $\|H-2C\|\le1$，与取向、符号及整个探针索引无关。这里用到 $|\omega|\le1$，没有给任何单个 $\alpha_\delta$ 加正下界。

**证明：一个分离坐标控制残量配对。** 令 $\kappa=\nu/\ell$、$z_0=\ell(1-\kappa^2)-\iota\kappa$、$Z=z_0 I_2-C$。由 (32.5) 消去 $U$ 并代入 $v=a-\iota p$，得到

$$
\mathsf Q-\kappa\mathsf P=(\iota C-\kappa I_2)a-Zp+\rho T_Au.
\tag{32.9}
$$

记 $c_1=1,c_2=2$。至少一个 $j$ 有 $|z_0-c_j|\ge1/2$；只在该坐标上除法。(32.8)–(32.9) 给

$$
|p_j|\le K\left[\left(1+\frac{n}{r_\ell}\right)
 (1+r_\ell+n+\sqrt{r_\ell S_0})+|\rho|\right].
$$

设 $z_j'=\overline{p_j}u_j$。由 $u^*p=u^*Xu\in\mathbb R$，两项 $\operatorname{Im}_\iota z_j'$ 互为相反数，故任取其中一个坐标都有
$|\operatorname{Re}(\iota p^*T_Au)|=3|\operatorname{Im}_\iota z_j'|\le3|p_j||u_j|$。
因此 $|\operatorname{Re}(v^*T_Au)|\le2\|a\|+3|p_j||u_j|$，包括 $u_j=0$。另一个坐标即使恰好共振，也不必估计其幅值。

置 $b_\theta=(r_\ell+n)^2/r_\ell$。由 (32.6)，$b_\theta\ge1$，且

$$
\left(1+\frac{n}{r_\ell}\right)(1+r_\ell+n)\le2b_\theta,
\qquad
\left(1+\frac{n}{r_\ell}\right)\sqrt{r_\ell S_0}=\sqrt{b_\theta S_0}.
$$

以上给 $|\operatorname{Re}(v^*T_Au)|\le K(b_\theta+\sqrt{b_\theta S_0}+|\rho|)$。在 (32.4) 中对 $4K|\rho|\sqrt{b_\theta S_0}$ 用 Young 不等式，耗去至多 $S_0/2+8K^2\rho^2 b_\theta$。由 $b_\theta\ge1$，增大常数后得到

$$
\mathcal D_\rho\ \ge\ \frac{S_0}{2}-K(|\rho|+\rho^2)b_\theta .
\tag{32.10}
$$

**证明：近零比率的大尺度下界。** 先在 $\|H-2C\|\le1,\ |\rho|\le1$ 内取常数。设 $|\kappa|\le\eta_{\rm tail}\le1/2$，记 $\lambda=\ell(1-\kappa^2)$。有 $|\lambda|\ge3r_\ell/4$、$\|C+\iota\kappa I_2\|\le5/2$。当 $r_\ell\ge8$ 时，$Z=\lambda I_2-C-\iota\kappa I_2$ 可逆，$\|Z^{-1}\|\le4/r_\ell$。由 $Z^{-1}-\lambda^{-1}I_2=\lambda^{-1}Z^{-1}(C+\iota\kappa I_2)$，两逆的差范数至多 $K/r_\ell^2$。将 (32.7) 代入 (32.9)，得到

$$
p=-\frac{1+\omega\kappa}{2(1-\kappa^2)}(\iota C-\kappa I_2)C^2u+\mathsf E,
\qquad
\|\mathsf E\|\le K\left(\frac{1+|\rho|}{r_\ell}+\sqrt{S_0/r_\ell}\right).
\tag{32.11}
$$

确切地，$Z^{-1}$ 作用于 $(\iota C-\kappa I_2)(Hu+G^*e)+\rho T_Au-(\mathsf Q-\kappa\mathsf P)$ 的贡献由 (32.8) 给右侧界；用 $\lambda^{-1}I_2$ 替换 $Z^{-1}$ 作用于剩下的 $\ell$ 倍项，误差至多 $K/r_\ell$。主项在 $\kappa=0$ 时为 $-\iota C^3u/2$。在 $|\kappa|\le1/2$ 上，由 $|1-\kappa^2|\ge3/4$ 和 $|\omega|\le1$，主项与 $-\iota C^3u/2$ 的差范数至多 $K|\kappa|$。由于 $u^*C^3u\ge1$，该基准主项与 $u$ 配对的 $\iota$ 虚系数至多 $-1/2$；实际 $u^*p$ 的虚系数为零。先选 $\eta_{\rm tail}>0$ 使 $K\eta_{\rm tail}\le1/8$，再选 $R\ge8$ 使 $2K/R\le1/8$，则 (32.11) 给 $1/4\le K\sqrt{S_0/r_\ell}$。因此某个 $c_{\rm tail}>0$ 满足

$$
S_0\ge c_{\rm tail} r_\ell
\qquad(r_\ell\ge R,\ n\le\eta_{\rm tail}r_\ell).
\tag{32.12}
$$

**证明：有界尺度的基准方程。** 考察 $H=2C,\ \rho=\nu=0$ 的极限方程 $\mathsf P=\mathsf Q=e=0$，允许 $|\operatorname{Im}_\iota\ell|\ge1$，含等号边界。由 $\mathsf Q=0$ 得 $v=-\iota\ell C^{-1}p$；$\mathsf P=0$ 给 $U=2\iota C^{-1}p$。再用 $U$ 的定义、$B=3C$ 以及 (32.7)，得到

$$
q=(\ell I_2+2C^{-1})p+3\iota C^2u,\qquad
a=(2C-\ell C^2/2)u=\iota(I_2-\ell C^{-1})p.
$$

此处 $I_2-\ell C^{-1}$ 可逆。于是逐坐标

$$
p_j=-\iota A_j u_j,\qquad
A_1=\frac{2-\ell/2}{1-\ell}=\frac12+\frac{3}{2(1-\ell)},\qquad A_2=4.
\tag{32.13}
$$

若两坐标均非零，实际探针恒满足 $c_l p_j-q_j=(c_l-c_j)X_{jj}u_j$，其中 $l\ne j$。实对角元 $X_{jj}$ 要求 $(c_l p_j-q_j)/u_j$ 为实数。将 $q_j,p_j$ 的上式代入，利用 $c_l=2/c_j$，恰得 $\operatorname{Re}(\ell A_j)=3c_j^2$。第二坐标强制 $\operatorname{Re}\ell=3$；写 $\ell=3+\iota t_0$，则 $\operatorname{Re}(\ell A_1)=-3/(4+t_0^2)$，与第一坐标所需的 $3$ 矛盾。

在第二轴，(32.13) 使 $u^*p=-4\iota$，违背 Hermitian 条件。在第一轴，$q=p$，故 $(\ell+1)A_1=3$，即 $\ell^2-9\ell+2=0$。两根均为实数，与 $|\operatorname{Im}_\iota\ell|\ge1$ 矛盾。

**证明：有界尺度的一致正下界。** 对 (32.12) 固定的 $R$，存在 $\eta_{\rm comp},\delta_H,\delta_\rho,c_{\rm comp}>0$，使

$$
S_0\ge c_{\rm comp}\qquad
(r_\ell\le R,\ n\le\eta_{\rm comp}r_\ell,\
\|H-2C\|\le\delta_H,\ |\rho|\le\delta_\rho).
\tag{32.14}
$$

否则令四个候选正常数都趋于零，取对应反例序列，则 $H\to2C,\ \rho\to0,\ n/r_\ell\to0,\ S_0\to0$。因 $r_\ell\le R$，有 $\nu\to0$。取子列固定 $\sigma,\epsilon$，使单位 $u$ 和有界 $\ell$ 收敛；(32.6) 给极限 $|\operatorname{Im}_\iota\ell|\ge1$。式 (32.8) 给 $\mathsf P,\mathsf Q,e\to0$；(32.7) 给 $a\to(2C-\ell C^2/2)u$，其中右侧取极限值。由 $\kappa\to0$，(32.9) 中 $Z$ 趋于可逆的 $\ell I_2-C$，故 $p$ 有界；(32.5) 的 $\mathsf P$ 等式在 $\ell$ 远离零时控制 $U$，继而 $U$ 的定义控制 $q$。取收敛子列后，极限满足前述基准方程。

非轴极限上，两条实对角元条件按 $(c_l p_j-q_j)/u_j\in\mathbb R$ 直接取极限，故已被排除。轴向极限上，(32.13) 和基准 $q$ 公式都把极限的 $p,q$ 留在同一轴上。原 Hermitian 探针的两个连续条件 $u^*p\in\mathbb R$ 与 $u^*q=p^*Cu$ 在极限保持；在第 $j$ 轴，它们给 $p=x_0u,\ q=c_jp$，其中 $x_0\in\mathbb R$。这正是上面排除两轴所用的条件。整个论证只对可见的 $p,q$ 取极限，未假设 $X$ 有界；未被读到的对角元可以发散。也未要求 $\alpha_\delta$ 在极限仍为正。矛盾证明 (32.14)。

**证明：统一半径与原全正泛函。** 取 $\eta=\min(\eta_{\rm tail},\eta_{\rm comp})>0$，并把 $\delta_H,\delta_\rho$ 缩到不超过 $1$。在 $n\le\eta r_\ell$ 时有 $b_\theta\le(1+\eta)^2 r_\ell$，故 (32.12) 在 $r_\ell\ge R$ 控制 $b_\theta$，(32.14) 在 $r_\ell\le R$ 以 $b_\theta\le(1+\eta)^2R$ 控制它。余下 $n>\eta r_\ell$ 时，直接由 (32.7) 中的方差，及 $A\le r_\ell$、$\|FCu\|=\|C^2u\|\ge1$，得到

$$
S_0\ \ge\ \frac{n^2}{2r_\ell}
  \ \ge\ \frac{\eta^2}{2(1+\eta)^2}\,b_\theta.
$$

三域给出同一常数 $\gamma>0$，例如取 $c_{\rm tail}/(1+\eta)^2$、$c_{\rm comp}/((1+\eta)^2R)$ 和 $\eta^2/(2(1+\eta)^2)$ 的最小值。在整个原索引域有 $S_0\ge\gamma b_\theta$。选 $0<\rho_*\le\delta_\rho$，使 $K(\rho_*+\rho_*^2)\le\gamma/4$。于是在 $\|H-2C\|\le\delta_H,\ |\rho|<\rho_*$ 下，(32.10) 给

$$
\mathcal D_\rho\ge \frac{S_0}{4}\ge\frac{\gamma b_\theta}{4}>0.
\tag{32.15}
$$

这些常数对两个取向和两个绝对值符号共同有效。参数范围由 (32.6) 完整保留，既没有限制两 $\alpha_\delta$ 的比值，也没有排除一项趋零或 $\beta_\delta$ 无界的序列。

对每个固定的同一 $X,\xi$，将 (32.15) 对全部有限变分参数取下确界，按 (27.12)–(27.13) 得原向量 PB。一般向量若演员分量非零，提取其范数为共同尺度，并同比缩放环境分量，原预算两侧按同一因子变化。若演员分量为零，$\xi=(0,y)$ 给 $x\xi=h_{\rm PB}\xi=r\xi=s\xi=0$，其中 $h_{\rm PB}=K_\sigma(c,x)$。原 $L$ 的读数是 $-2\operatorname{Re}((Vy)^*\iota C Vy/2)=0$，故 PB 自动成立，包括零向量。最后用定理 17.2 的 (17.14)–(17.16) 将同一实际 $X$ 的向量 PB 提升到原全正泛函：谱和的两份预算各用原二阶 Gram 行列式根不等式，左端用三角不等式。谱和保留给定总质量，未将 $\phi$ 归一，也未丢弃环境密度块；零质量仅有零泛函。由 $\|H_h-2C\|=|h|$，半径 $\rho_*$ 可在同一 $h$ 邻域使用。

**证明：原 P2 的精确闭区间。** 对 $h>0$，(30.27)–(30.28) 的对应为

$$
\mathcal A=C^{-1/2}H_hC^{-1/2}=2I_2+\frac{h}{\sqrt2}J_A,\qquad
(\alpha,\beta)=(2,h/\sqrt2),\qquad
U_0=\frac{1}{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}.
$$

原残量参数就是 (30.29) 所用的 $\rho$。以 $M_2=I_2$ 代入 (30.29)，得

$$
Q_M=U_0^*\operatorname{diag}(1/2,1)U_0
=\begin{pmatrix}3/4&-1/4\\-1/4&3/4\end{pmatrix},
\qquad
\omega_{\rm P2}=1,\quad J=0,\quad R_{\rm P2}=3/4,\quad\Delta=1/2 .
$$

这里 $\omega_{\rm P2}$ 和 $R_{\rm P2}$ 分别是 (30.29) 的 $\omega$ 和 $R$，与上面的方差权重及尺度截断无关。于是 $I_+(B_h,M)=I_-(B_h,M)$，共同值正是 (32.2)。取 $h_*=\min(\delta_H,3\rho_*/(2\sqrt2))$。若 $0<h<h_*$，则 $\sqrt2\,h/3<\rho_*$，所以闭区间的每个点，包括两个端点，都满足 (32.15) 的全部原 PB 测试。在区间外，(30.29) 的必要性使原 P2 对每个取向都失败；正有限质量上的失败随原 P2 的二次齐次性保留。由此得到精确的 P2 与 PB 交及所述固定非零例。∎

本节的 `repo-derived` 结论是固定三矩 $(C^2,C,I_2)$ 的一致 PB 半径及其对整个原 P2 闭区间的覆盖。原 P2 区间直接复用 (30.29)，原正泛函、实／复 Gram 与行列式根的归属沿前卷 §§17、27 及其中所引运输卷 (9.28)–(9.30)。加权方差、Cauchy–Schwarz、Young 不等式及有限维紧性均按其通常形式使用。结论仅分类 (32.1) 在 $0<h<h_*$ 上的 P2 与 PB 之交；不确定该族的最大 PB 半径，也不分类任意 $W=0$ 输入或给出物理实现。

## 追加锚（本行以下为增补区）

## 33. 两矩近邻的一致反二阶矩 PB 半径与实单线极限

本节沿用 §32 的 $C=\operatorname{diag}(1,2)$、$T_A=\operatorname{diag}(1,-2)$、$J_A$、两个取向及原 P2、PB 标签。旧式号 (17.x)、(27.x)、(30.x)、(30A.x)、(31.x) 均指[前卷](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md)。所有平方、Jordan 乘积及正泛函均取同一个完整原矩阵代数；实际探针仍遍取全部 $x=X\oplus0_m$、$X=X^\ast$。本节只取平衡残量 $s=\rho T_A\oplus0_m$，不增加原泛函的归一或环境密度限制。

### 33.1 任意有限环境维数上的共同半径

**定理 33.1（两矩近邻与统一反二阶矩尺度）。** 存在常数 $\delta_0,c>0$，与环境维数和 $L$ 无关，使下述断言成立。任取有限 $m\ge0$、实际 Hermitian 输入
$t=\left(\begin{smallmatrix}B&V\\V^\ast&D_{\rm env}\end{smallmatrix}\right)$，并令

$$
\begin{gathered}
W=V|_{\ker D_{\rm env}}=0,\qquad
F=V^\ast,\qquad G=D_{\rm env}^{\dagger}F,\\
M_0=F^\ast F,\qquad M_1=G^\ast F=F^\ast G,\qquad
M_2=G^\ast G,\qquad H=B-M_1.
\end{gathered}
\tag{33.1}
$$

若 $L\ge1$ 且

$$
\|H-2C\|<\delta_0,\qquad
\|M_1-C\|<\delta_0,\qquad
\|M_2\|\le L,
\tag{33.2}
$$

则同一输入对每个 $|\rho|\le c/L$ 同时满足两个取向的全部原 PB。这里包括每个实际 Hermitian 角探针和完整 $M_{m+2}(\mathbb C)$ 上全部正复线性泛函；在任一指定正有限质量上全称检验也成立，零质量给零等式。

不对 $M_0$ 另加接近性、正下界或上界假设。等价地，任意满足前卷 (30.3) 的兼容三矩，在取 $B=H+M_1$ 后，只要满足 (33.2)，其每份实际实现都有上述结论。兼容性不能删除：本定理不把任意三个形式矩阵当作实际来源。

证明。先在 $\|H-2C\|,\|M_1-C\|\le1$ 内取常数，随后缩小邻域。固定任意原单位演员 $u$、同一 $X=X^\ast$ 和环境向量 $y$；原索引中的 $\sigma,\epsilon=\pm1$、$0<\alpha_\pm<\infty$、$\beta_\pm\in\mathbb R$ 均任意。使用 §32 的 $\iota=\sigma i$、$\nu,\ell,A,w_\pm,\omega$、$\mathsf P,\mathsf Q$、$S_0,\mathcal D_\rho$，并置

$$
r_\ell=|\ell|,\qquad n_0=|\nu|,\qquad
b_\theta=\frac{(r_\ell+n_0)^2}{r_\ell},\qquad
\mathcal S=L S_0.
\tag{33.3}
$$

式 (32.6) 仍给
$|1+\operatorname{Im}_\iota\nu|<A=-\epsilon\operatorname{Im}_\iota\ell\le r_\ell$、
$r_\ell+n_0\ge1$，因而 $r_\ell>0$、$b_\theta\ge1$。没有限制 $\alpha_+/\alpha_-$，也没有对任何单个 $\alpha_\pm$ 取正下界。

在实际环境内令 $d=Fu+D_{\rm env}y$、
$a=Bu+Vy$、
$e=d+(\ell+\omega\nu)FCu/2$。由 $W=0$ 得 $a=Hu+G^\ast d$。因此 (32.4)–(32.5)、(32.9) 保持原式；(32.7) 的准确替换是

$$
\begin{aligned}
\sum_{\tau=\pm1}w_\tau
 \|(E_\tau)_{\rm env}\|^2
 &=(w_++w_-)\|e\|^2+\frac{n_0^2}{2A}\|FCu\|^2,\\
a&=Hu+G^\ast e-\frac{\ell+\omega\nu}{2}M_1Cu,\\
\mathcal D_\rho
 &=S_0+4\epsilon\rho\operatorname{Re}(v^\ast T_Au),
 \qquad v=a-\iota p,\quad p=Xu.
\end{aligned}
\tag{33.4}
$$

这里 $\tau$ 只标两笔原预算。第一行是同一对环境列的加权方差，第二行使用实际恒等式 $G^\ast F=M_1$；没有替换环境度量。

取 $\|M_1-C\|\le1/2$。因 $\|G\|^2\le L$，对任意演员向量 $z$ 有

$$
\|M_1z\|^2=\|G^\ast Fz\|^2\le L\|Fz\|^2,
\qquad
M_0\succeq L^{-1}M_1^2\succeq\frac1{4L}I_2.
\tag{33.5}
$$

特别地 $L\|FCu\|^2\ge1/4$。这就是所需的 $M_0$ 下界，其来源是实际因子而非额外假设。由 (33.4) 的方差及两份演员列的加权半和、半差，得到

$$
\begin{gathered}
\mathcal S\ge\frac{n_0^2}{8r_\ell},\\
\|\mathsf P\|+\|\mathsf Q\|+\|G^\ast e\|
 \le3\sqrt{r_\ell\mathcal S},\\
\|a\|\le K\bigl(1+r_\ell+n_0+\sqrt{r_\ell\mathcal S}\bigr).
\end{gathered}
\tag{33.6}
$$

例如 $\|\mathsf P\|,\|\mathsf Q\|\le\sqrt{AS_0/2}$、
$\|e\|\le\sqrt{AS_0/2}$，而
$\|G^\ast e\|\le\sqrt{L}\|e\|$；这说明 $K$ 不依赖 $m,L$ 或 $\|F\|$。

先证明存在共同的 $\eta_H,\eta_M,\eta_\rho,\gamma_0>0$，使

$$
\mathcal S\ge\gamma_0 b_\theta
\quad\text{当}\quad
\|H-2C\|<\eta_H,\quad
\|M_1-C\|<\eta_M,\quad |\rho|\le\eta_\rho,
\tag{33.7}
$$

对所有 $L\ge1$、所有实际环境及全部原索引成立。这里的强制性只在所列局部 $\rho$ 邻域断言。

若不存在这样的四个常数，就有一列实际输入和原测试，允许其环境维数及 $L$ 变化，使
$H\to2C$、$M_1\to C$、$\rho\to0$ 且
$\mathcal S/b_\theta\to0$。取子列固定 $\sigma,\epsilon$。由 (33.6)，

$$
\frac{\mathcal S}{b_\theta}
 \ge\frac{n_0^2}{8(r_\ell+n_0)^2}
\quad\Longrightarrow\quad
\frac{\nu}{\ell}\to0,\qquad
\liminf r_\ell\ge1,\qquad
\frac{\mathcal S}{r_\ell}\to0.
\tag{33.8}
$$

设 $\kappa=\nu/\ell$，
$Z=[\ell(1-\kappa^2)-\iota\kappa]I_2-C$。原消元式仍是

$$
\mathsf Q-\kappa\mathsf P
 =(\iota C-\kappa I_2)a-Zp+\rho T_Au.
\tag{33.9}
$$

若 $r_\ell\to\infty$，(33.6) 使
$\|\mathsf P\|+\|\mathsf Q\|+\|G^\ast e\|=o(r_\ell)$。
式 (33.4) 给
$a/\ell+C^2u/2\to0$；同时 $Z/\ell\to I_2$。将 (33.9) 除以 $\ell$ 并解出 $p$，得到

$$
p+\frac{\iota}{2}C^3u\longrightarrow0.
\tag{33.10}
$$

但 $u^\ast p=u^\ast Xu$ 必为实数，而
$u^\ast C^3u\ge1$，故 (33.10) 不可能。这一分支没有对发散探针取紧性极限。

若 $r_\ell$ 有界，则 (33.8) 给 $\nu\to0$、$\mathcal S\to0$；
$\mathsf P,\mathsf Q,G^\ast e\to0$。只对单位演员 $u$、有界 $\ell$ 取子列。极限满足
$|\operatorname{Im}_\iota\ell|\ge1$，故 $\ell I_2-C$ 可逆。(33.9) 控制可见列 $p$，再由
$\mathsf P=v-\nu p+\ell U/2$、
$U=\iota q+BCu+Cv$ 控制可见列 $q=XCu$。在极限中 $B\to3C$，恰得到 §32 已排除的基准接触系统：

$$
\begin{gathered}
a=(2C-\ell C^2/2)u=\iota(I_2-\ell C^{-1})p,\\
q=(\ell I_2+2C^{-1})p+3\iota C^2u,\qquad
p_j=-\iota A_j u_j,\\
A_1=\frac{2-\ell/2}{1-\ell}
 =\frac12+\frac{3}{2(1-\ell)},\qquad A_2=4.
\end{gathered}
\tag{33.11}
$$

为明确极限边界，若两个演员坐标均非零，实际 Hermitian 探针给
$(c_l p_j-q_j)/u_j\in\mathbb R$，其中 $c_1=1,c_2=2,l\ne j$。
代入 (33.11) 得
$\operatorname{Re}(\ell A_j)=3c_j^2$。
第二坐标迫使 $\operatorname{Re}\ell=3$；写 $\ell=3+\iota t_0$，第一坐标却给
$\operatorname{Re}(\ell A_1)=-3/(4+t_0^2)$，不能等于 $3$。
在第二演员轴，$u^\ast p=-4\iota$，也不可能。
在第一轴，可见极限列均在该轴，连续恒等式
$u^\ast p\in\mathbb R$、$u^\ast q=p^\ast Cu$ 给 $q=p$。
于是 $(\ell+1)A_1=3$，即 $\ell^2-9\ell+2=0$，其根均为实数，仍矛盾。
这些排除包括 $A=1$ 的极限；不要求极限的两个 $\alpha_\pm$ 仍严格正。整个紧性步骤只涉及演员空间的 $u,p,q,\ell$，不要求 $X$、$y$ 或环境空间有共同紧集。这证明 (33.7)。

最后控制残量项。至少一个 $j$ 满足
$|\ell(1-\kappa^2)-\iota\kappa-c_j|\ge1/2$。
在该坐标上使用 (33.9) 和 (33.6)，按 §32 的同一 Hermitian 实性关系得到

$$
\begin{aligned}
|\operatorname{Re}(v^\ast T_Au)|
 &\le K\bigl(b_\theta+\sqrt{b_\theta\mathcal S}+|\rho|\bigr),\\
\mathcal D_\rho
 &\ge\frac{S_0}{2}
       -K\bigl(|\rho|+L\rho^2\bigr)b_\theta.
\end{aligned}
\tag{33.12}
$$

具体地，$u^\ast p\in\mathbb R$ 使两个
$\operatorname{Im}_\iota(\overline{p_j}u_j)$ 互为相反数，故任选一个坐标都有
$|\operatorname{Re}(\iota p^\ast T_Au)|\le3|p_j||u_j|$。
只需控制上述分离坐标，即使另一坐标共振也无妨。
此外
$(1+n_0/r_\ell)(1+r_\ell+n_0)\le2b_\theta$、
$(1+n_0/r_\ell)\sqrt{r_\ell\mathcal S}=\sqrt{b_\theta\mathcal S}$。
第一行因而成立，包括 $u_j=0$。
第二行对 $4K|\rho|\sqrt{b_\theta L S_0}$ 使用 Young 不等式，并用 $L,b_\theta\ge1$ 吸收余项。

取 $\delta_0\le\min(1/2,\eta_H,\eta_M)$，再取
$0<c\le\eta_\rho$ 使 $K(c+c^2)\le\gamma_0/4$。
当 $|\rho|\le c/L$ 时，(33.7)、(33.12) 给

$$
\mathcal D_\rho
 \ge\frac{S_0}{2}-\frac{\gamma_0b_\theta}{4L}
 \ge\frac{S_0}{4}
 \ge\frac{\gamma_0b_\theta}{4L}>0.
\tag{33.13}
$$

所有常数对两个取向、两个绝对值符号及全部有限变分参数共同有效。对固定的同一 $X,\xi=(u,y)$，用 (27.12) 对四个参数取下确界，即得原向量 PB；退化 Gram 不要求下确界达到。一般非零演员分量按其范数同比缩放，演员分量为零时原 $L$ 的读取为零，PB 自动成立。

对完整原代数上的任意正泛函，取原空间谱分解
$\phi=\sum_j\phi_{\xi_j}$，分别对同一 $R_+,S_+$ 和同一 $R_-,S_-$ 使用 (17.15) 的二阶正 Gram 行列式根不等式，再对左端使用三角不等式，正好得到 (17.16)。这一步保留环境密度块及给定总质量；零质量只有零泛函。证明完成。∎

### 33.2 正定环境中的上阶见证

**命题 33.2（PB 单独的反二阶矩阶最优性）。** 定理 33.1 的共同保证尺度在 $L\to\infty$ 时不能统一改成比 $L^{-1}$ 更大的阶。更准确地，对每个 $L>64/7$，有一份三维环境上的实际完整 $M_5(\mathbb C)$ 输入，且 $D_{\rm env}\succ0$，满足
$H=2C$、$M_1=C$、$W=0$、$\|M_2\|=L$，却在 $\rho=4/L$ 严格违反原 PB。两个取向分别都有同一实际探针上的见证；每份见证的两笔原预算均严格正，并可取得任一指定正有限质量。

证明。在固定两维演员和三维环境上，记 $e_1,e_2$ 为演员标准基，取

$$
\begin{gathered}
D_{\rm env}=\operatorname{diag}(1,2,L^{-2}),\qquad B=3C,\\
V=\left[\sqrt{\frac{L}{L+1}}\,e_1,\ 2e_2,\ \frac{1}{L\sqrt{L+1}}\,e_1\right].
\end{gathered}
\tag{33.14}
$$

环境正定，故 $W=0$。由 $F=V^\ast$、$G=D_{\rm env}^{-1}F$，

$$
M_1=\operatorname{diag}\left(\frac{L}{L+1}+\frac1{L+1},2\right)=C,\qquad
M_2=\operatorname{diag}\left(\frac{L}{L+1}+\frac{L^2}{L+1},1\right)
     =\operatorname{diag}(L,1),\qquad
H=B-M_1=2C.
\tag{33.15}
$$

先取 $\sigma=1$、$\iota=i$、$\epsilon=1$，并取

$$
\begin{gathered}
u=e_1,\qquad X=\operatorname{diag}(3/2,0),\qquad
p=q=\tfrac32e_1,\\
\nu=0,\qquad \ell=-1-2i,\qquad
(\alpha_+,\alpha_-)=(1,3),\qquad
(\beta_+,\beta_-)=(-1,1),\\
a_{\rm act}=(-3+3i)e_1,\qquad
v=(-3+\tfrac32i)e_1,\qquad U=3i e_1.
\end{gathered}
\tag{33.16}
$$

这些参数满足原 (32.6)，且
$\zeta_\tau=i+\tau\ell=\beta_\tau-\tau i\alpha_\tau$。
令

$$
\begin{gathered}
d_0=a_{\rm act}-Hu+\ell M_1Cu/2=(-11/2+2i)e_1,\\
e=GM_2^{-1}d_0,\qquad
G^\ast e=d_0,\qquad \|e\|^2=\frac{137}{4L},\\
y=D_{\rm env}^{-1}\bigl(e-\ell FCu/2-Fu\bigr),\qquad
\xi=(u,y).
\end{gathered}
\tag{33.17}
$$

所有量均有限；此 $X,\xi$ 不依赖 $\rho$。
由 $d=Fu+D_{\rm env}y=e-\ell FCu/2$ 得
$Bu+Vy=Hu+G^\ast d=a_{\rm act}$，故 (33.16) 的演员列由这同一个实际向量精确实现，而不是另行指定的自由列。

逐项代入 (32.5)，有

$$
\mathsf P=v+\ell U/2=0,\qquad
\mathsf Q=iCv-\ell p+\rho T_Au=\rho e_1,\qquad
(E_\tau)_{\rm env}=e.
\tag{33.18}
$$

因而同一实际二次型在全部实 $\rho$ 上恰为

$$
\boxed{\quad
\mathcal D_\rho
 =\frac43\rho^2-12\rho+\frac{137}{3L}.
\quad}
\tag{33.19}
$$

这里 $S_0=(1+1/3)(\rho^2+\|e\|^2)$，
$\operatorname{Re}(v^\ast T_Au)=-3$，故一次项的符号由原 (32.4) 确定。在 $\rho=4/L$，

$$
\mathcal D_{4/L}=\frac{64-7L}{3L^2}<0.
\tag{33.20}
$$

原两笔预算的变分上界之和已经小于
$2\phi_\xi(L)$；由 (27.12)，对参数取下确界只会进一步减小这个上界。因此这是原 PB 的严格违反。

还可直接验证两笔预算严格正。$FCu$ 与 $e$ 分别平行于 $Fe_1$ 与 $Ge_1$，两者的第一、第三环境分量均非零；乘 $D_{\rm env}^{-1}$ 将第三分量与第一分量的比值放大 $L^2$。因此这两个环境列复线性无关。对每个 $\tau$，
$(R_\tau\xi)_{\rm env}=-\tau FCu/2$，
$(S_\tau\xi-\zeta_\tau R_\tau\xi)_{\rm env}=e$；
所以 $R_\tau\xi,S_\tau\xi$ 复线性无关。复 Gram 行列式严格正，其实 Gram 行列式不小于它，故
$B_{\phi_\xi}(R_\tau,S_\tau)>0$。
所有输入和 $X$ 均为实矩阵，对作用列及 $y$ 取复共轭便给 $\sigma=-1$ 的同样见证。最后把 $\phi_\xi$ 乘以 $\mu/\|\xi\|^2$，即可取得任意指定 $\mu>0$，严格违反和两笔严格正预算均保留。∎

当 $L\to\infty$，(33.14) 的原矩阵趋于 (32.1) 在 $h=0$ 添一条未耦合零模的输入。此时 $M_0\to C^2$，而 $H,M_1$ 在整条路径上精确固定。它说明的是整个所列近邻类的 PB 单独共同半径具有 $L^{-1}$ 阶，不确定最优常数。这里 $C^{-1/2}HC^{-1/2}=2I_2$，原 P2 已迫使 $\rho=0$；故 (33.20) 不是 P2 与 PB 联合分类的锐性见证。

### 33.3 同一五维载体上的实单线族

**定义 33.3（实单线正则化）。** 在同一完整 $M_5(\mathbb C)$、分块 $\mathbb C^2\oplus\mathbb C^2\oplus\mathbb C$ 上，取

$$
\begin{gathered}
n=\frac1{\sqrt2}(1,1)^{\mathsf T},\qquad
a=C^{1/2}n=(1/\sqrt2,1)^{\mathsf T},\qquad \|a\|^2=3/2,\\
H_h=2C+hJ_A,\qquad h,\gamma\in\mathbb R,\quad\delta>0,\quad
\lambda=\gamma/\delta,\\
D_{\rm env}=C\oplus\delta,\qquad
V=[C,\gamma a],\qquad
B=3C+hJ_A+\frac{\gamma^2}{\delta}aa^\ast,\\
t_{h,\gamma,\delta}=
\begin{pmatrix}
3C+hJ_A+\gamma^2aa^\ast/\delta&C&\gamma a\\
C&C&0\\
\gamma a^\ast&0&\delta
\end{pmatrix},\qquad
t_h^0=
\begin{pmatrix}
3C+hJ_A&C&0\\
C&C&0\\
0&0&0
\end{pmatrix}.
\end{gathered}
\tag{33.21}
$$

原 $c,P,s$ 分别是 $C\oplus0_3$、$I_2\oplus0_3$、$\rho T_A\oplus0_3$。环境可逆，故 $W=0$，实际矩为

$$
\begin{gathered}
M_0=C^2+\gamma^2aa^\ast,\qquad
M_1=C+\frac{\gamma^2}{\delta}aa^\ast
   =C+\delta\lambda^2aa^\ast,\\
M_2=I_2+\lambda^2aa^\ast,\qquad H=H_h,\qquad
L_\lambda:=\|M_2\|=1+\frac32\lambda^2.
\end{gathered}
\tag{33.22}
$$

**定理 33.4（精确 P2 区间与共同 PB 覆盖条件）。** 对定义 33.3 的每个实 $h,\gamma$ 和每个 $\delta>0$，两个取向各自的原全正 P2 区间均为

$$
I_\lambda(h)=[-r_\lambda(h),r_\lambda(h)],\qquad
r_\lambda(h)=
\frac{\sqrt2\,|h|}{3\sqrt{1+2\lambda^2/3}}.
\tag{33.23}
$$

令 $\mathcal J_\sigma(h,\gamma,\delta)$ 为该同一输入在取向 $\sigma$ 下满足原 P2 与全部原 PB 的实 $\rho$ 集合。若

$$
|h|<\delta_0,\qquad \frac32\delta\lambda^2<\delta_0,
\tag{33.24}
$$

则对每个 $\sigma$ 有

$$
\left[-\min\left(r_\lambda(h),\frac{c}{L_\lambda}\right),
       \min\left(r_\lambda(h),\frac{c}{L_\lambda}\right)\right]
\subseteq\mathcal J_\sigma(h,\gamma,\delta)
\subseteq I_\lambda(h).
\tag{33.25}
$$

特别地，若另外满足

$$
|h|\le
\frac{3c}{\sqrt2}\,
\frac{\sqrt{1+2\lambda^2/3}}{1+3\lambda^2/2},
\tag{33.26}
$$

则 $\mathcal J_+=\mathcal J_-=I_\lambda(h)$，两个取向的联合允许集也等于此闭区间，包括两端点。这里的全正泛函量词可分别限制到任一指定正有限质量；零质量仍是零等式。

证明。先直接消费 (30.29) 的原 P2 判据。对 $h>0$，
$\mathcal A=2I_2+(h/\sqrt2)J_A$ 的有序谱基为 §32 的 $U_0$，第一列恰为 $n$。由 (33.22)，

$$
\begin{aligned}
U_0^\ast C^{-1/2}(I_2+M_2)C^{-1/2}U_0
 &=\begin{pmatrix}3/2+\lambda^2&1/2\\1/2&3/2\end{pmatrix},\\
Q_M&=\frac1{d_\lambda}
 \begin{pmatrix}3/2&-1/2\\-1/2&3/2+\lambda^2\end{pmatrix},
 \qquad d_\lambda=2+\frac32\lambda^2,\\
\Delta&=\frac1{d_\lambda},\qquad
R=\frac{\sqrt{(3/2)(3/2+\lambda^2)}}{d_\lambda},\qquad
J=0,\qquad \beta=\frac{h}{\sqrt2}.
\end{aligned}
\tag{33.27}
$$

因此 $\beta\Delta/R$ 正是 (33.23)。
当 $h<0$，交换两个谱列不改变 $R,\Delta$，仍有 $J=0$，只把 $\beta$ 改为 $|h|/\sqrt2$。
当 $h=0$，归一化 Schur 矩阵为标量，(30.27)–(30.28) 直接给 $\rho=0$，也与 (33.23) 相符。这里保留原 P2 的必要性、充分性及闭端点，没有以 PB 估计替代它。

另一方面，
$\|H_h-2C\|=|h|$、
$\|M_1-C\|=3\delta\lambda^2/2$。
定理 33.1 于是保证 $|\rho|\le c/L_\lambda$ 的全部原 PB，给出 (33.25) 左包含；右包含仅用 P2。式 (33.26) 准确等价于
$r_\lambda(h)\le c/L_\lambda$，故此时两包含合成所述等式。∎

对任意固定有限 $\Lambda\ge0$，可取

$$
\delta_\Lambda=\frac{\delta_0}{3(1+\Lambda^2)},\qquad
h_\Lambda=
\min\left\{\frac{\delta_0}{2},
 \frac{3c}{2\sqrt2(1+3\Lambda^2/2)}\right\}.
\tag{33.28}
$$

于是所有 $|\lambda|\le\Lambda$、
$0<\delta<\delta_\Lambda$、
$|h|<h_\Lambda$ 的原输入都有
$\mathcal J_+=\mathcal J_-=I_\lambda(h)$。
这是同一有界比率族的共同覆盖，不随某个探针或泛函改选输入。

式 (33.26) 还给出无界比率可用的双重缩放条件。事实上

$$
\frac{L_\lambda}{\sqrt{1+2\lambda^2/3}}
 \le\frac32\sqrt{\frac32}(1+|\lambda|).
\tag{33.29}
$$

因此可固定
$c'=\min\{\delta_0/2,c\}>0$；
只要 $0<|h|\le c'/(1+|\lambda|)$ 以及
$3\delta\lambda^2/2<\delta_0$，就有 (33.24)、(33.26)，整个 P2 闭区间均被 PB 覆盖。这个充分条件允许 $|\lambda|\to\infty$，但同时要求 $h$ 缩小；它不确定固定非零 $h$、无界比率时的精确有限阶段联合半径。

### 33.4 原源距离、不同有界比率极限与无界比率挤压

**推论 33.5（同一源极限上的不同联合区间）。** 定义 33.3 的原源距离精确为

$$
\begin{gathered}
t_{h,\gamma,\delta}-t_h^0
 =\delta
 \begin{bmatrix}\lambda a\\0_2\\1\end{bmatrix}
 \begin{bmatrix}\lambda a\\0_2\\1\end{bmatrix}^{\!\ast},\\
\boxed{\quad
\|t_{h,\gamma,\delta}-t_h^0\|
 =\delta\left(1+\frac32\lambda^2\right)
 =\delta+\frac{3\gamma^2}{2\delta}.
\quad}
\end{gathered}
\tag{33.30}
$$

任取两个有限实数 $\lambda_1,\lambda_2$，满足
$|\lambda_1|\ne|\lambda_2|$。取
$\Lambda\ge\max(|\lambda_1|,|\lambda_2|)$，
并固定任一 $0<|h|<h_\Lambda$。
沿 $\gamma=\lambda_j\delta$、$\delta\downarrow0$ 的两条路径，原输入均趋于同一个 $t_h^0$，
$M_0\to C^2$、$M_1\to C$，但两个取向的联合允许集分别等于不同的非退化闭区间
$I_{\lambda_j}(h)$。其相对种子半径为

$$
\frac{r_{\lambda_j}(h)}{r_0(h)}
 =\left(1+\frac23\lambda_j^2\right)^{-1/2}.
\tag{33.31}
$$

更一般地，在同一个有界比率范围内，若 $\lambda\to\lambda_\ast$、$\delta\to0$，则联合区间趋于 $I_{\lambda_\ast}(h)$。

证明。式 (33.30) 是同一个实际矩阵差的秩一展开；因 $\delta>0$，其算子范数等于 $\delta$ 乘该列的平方范数。矩的极限由 (33.22) 得到，联合区间由 (33.28) 得到。式 (33.31) 由 (33.23) 相除；固定非零 $h$ 时，它随 $|\lambda_j|$ 严格减小，故两个绝对比率不同就给不同区间。对收敛有界比率使用同一个共同覆盖及半径公式的连续性即得最后断言。∎

上述路径中，$M_2$ 的路径极限是
$I_2+\lambda_\ast^2aa^\ast$，而极限原输入 $t_h^0$ 自身按谱伪逆计算的第二矩是 $I_2$。因此原源与第一矩收敛并不推出第二矩收敛到极限源的第二矩。仅在定义 33.3 这一单线族内，额外标量记录

$$
n^\ast C^{-1/2}(M_2-I_2)C^{-1/2}n=\lambda^2
\tag{33.32}
$$

对固定的 $h$，已经足以通过 (33.23) 确定 P2 半径。在满足 (33.24) 和 (33.26) 的覆盖条件时，该半径也是联合半径；满足 (33.28) 的有界比率路径已经具备这些条件。这不声称该标量恢复任意来源的 $M_2$，也不声称它是一般输入的最小记录。

现固定非零 $h$，取任意满足

$$
\delta_k\downarrow0,\qquad
|\lambda_k|=|\gamma_k|/\delta_k\to\infty,\qquad
\gamma_k^2/\delta_k\to0
\tag{33.33}
$$

的实单线路径。例如 $\gamma_k=\delta_k^{3/4}$ 满足这些条件。式 (33.30) 仍使原源趋于 $t_h^0$，第一矩仍趋于 $C$。无须假设这一范围的全部 PB 已有精确分类，就有

$$
0\in\mathcal J_\sigma(h,\gamma_k,\delta_k)
 \subseteq I_{\lambda_k}(h),\qquad
\sup_{\rho\in\mathcal J_\sigma(h,\gamma_k,\delta_k)}|\rho|
 \le r_{\lambda_k}(h)\longrightarrow0.
\tag{33.34}
$$

第一项使用标准零残量的 P2 与全部 PB，第二项只使用精确 P2 必要性。因此两个取向的联合允许集及其交都被挤向 $\{0\}$。这里没有断言每个有限 $k$ 的联合集等于 P2 区间，也没有由这个挤压结论分类 PB 单独的允许集。若同时让 $h_k$ 满足 (33.29) 后的双重缩放条件，则定理 33.4 才进一步给每个满足邻域条件的有限阶段的精确联合区间。

### 33.5 真正零模连线的比较

**命题 33.6（同一实方向上的非零零模比较）。** 在同一 $M_5(\mathbb C)$ 上另取

$$
\widehat t_{h,\gamma}=
\begin{pmatrix}
3C+hJ_A&C&\gamma a\\
C&C&0\\
\gamma a^\ast&0&0
\end{pmatrix},
\qquad h\in\mathbb R,\quad\gamma\in\mathbb R\setminus\{0\}.
\tag{33.35}
$$

则 $W\ne0$，两个取向各自的全正 P2 区间恰为

$$
\widehat I_+=\widehat I_-=
[-|\gamma|/\sqrt6,\ |\gamma|/\sqrt6],
\tag{33.36}
$$

但全部原 PB 在任一取向都当且仅当 $\rho=0$。
每个非零 $\rho$ 的 PB 失败均可在任意指定正有限质量上取得同一原泛函下的两笔严格正预算见证。

证明。此时
$D_{\rm env}=C\oplus0$、
$V=[C,\gamma a]$、
$H=2C+hJ_A$，零模连线的归一化演员方向是平衡方向 $n$。
在 (13.5) 取 $e=(1,-1)^{\mathsf T}/\sqrt2$；因 $e,n$ 都是
$C^{-1/2}HC^{-1/2}$ 的特征向量，其交叉元 $b=0$。
按 (13.6) 的原空间两行，第一行的平方范数为
$2e^\ast C^{-1}e=3/2$，第二行的平方范数为 $\gamma^{-2}$，两行正交。故该处的矩阵为

$$
GG^\ast=\operatorname{diag}(3/2,\gamma^{-2}),\qquad
Q=\operatorname{diag}(2/3,\gamma^2),\qquad
R=|\gamma|\sqrt{2/3},\qquad
\Delta=2\gamma^2/3,\qquad J=0.
\tag{33.37}
$$

这里 $G$ 仅指 (13.6) 的两行矩阵，不是 (33.1) 的矩因子。
代入 (13.9) 得 (33.36)，包括闭端点。PB 的单独刚性及正预算见证直接由定理 30A.2 给出，不以 P2 为前件。∎

当 $\gamma\to0$，$\widehat t_{h,\gamma}\to t_h^0$。所以同一个原源极限附近，真正的非零零模连线具有非退化 P2 区间，却在所有非零 $\rho$ 上被全部 PB 排除；正则化单线的有界比率路径则在所列小 $h$ 条件下具有非退化联合区间。两者属于不同的实际环境分支，不能用删除零模连线的伪逆操作互相替代。

### 33.6 数学来源与准确范围

原 PB 的同一向量变分恒等式与完整正泛函提升分别复用前卷 (27.12)–(27.13)、(17.14)–(17.16)；兼容三矩和实际实现沿定理 30.1，原加权环境补偿沿 (31.9)–(31.13)。本节使用 §32 的原列代数及基准接触排除，将其扩展为 (33.7) 的维数无关缩放下界，再得到 (33.13)。加权方差、Cauchy–Schwarz、Young 不等式、有限维谱分解和可见演员列的紧性均为成熟工具。原 P2 分类直接沿 (30.29) 和定理 13.1；零模 PB 比较直接沿定理 30A.2。

有限矩阵的秩变化与 Moore–Penrose 逆连续性的背景可参见 J. J. Koliha，[*Continuity and differentiability of the Moore–Penrose inverse in C*-algebras*](https://journals.msp.org/mscand/article/download/885/884/916)，Corollary 1.8，p. 157。该文在这里仅承担常秩与伪逆连续性的背景归属；PB 下界、同一实际五维正定环境见证和本节各条区间极限由上列推导承担。谱伪逆和广义 Schur 工具的归属仍沿前卷所引 Penrose 与 Higham，不把这些成熟工具计作新增结果，也不作外部文献穷尽或历史优先权主张。

本节的仓内综合结论是：无单独 $M_0$ 假设的共同反二阶矩 PB 半径及其 PB 单独阶最优性，和该半径对实单线族精确 P2 区间的覆盖与源极限比较。它们是有限矩阵的纸面数学陈述，不承载 Lean／kernel 认证。这里没有一般 $W=0$ 联合分类、每份输入的最大 PB 半径、最优半径常数、更高演员秩分类或物理实现结论；前卷保留的未知总响应、完整 $\mathsf H$ 和原实际来源义务维持原范围。

## 追加锚（本行以下为增补区）
