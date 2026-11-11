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

## 34. 固定非零 Schur 耦合下，全部原 PB 缩小正定环境的原 P2 允许范围

沿用 §32 的 $C=\operatorname{diag}(1,2)$、$T_A=\operatorname{diag}(1,-2)$、$J_A=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$，以及[前卷](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md)的原 P2、原 PB 与有限变分记号。设 $n=(1,1)^{\mathsf T}/\sqrt2$、$a=C^{1/2}n=(1,\sqrt2)^{\mathsf T}/\sqrt2$、$\beta=h/\sqrt2$。下文在同一个完整 $M_5(\mathbb C)$ 上工作：演员为 $\mathbb C^2$，环境为 $\mathbb C^2\oplus\mathbb C$，原探针是 $x=X\oplus0_3$，其中 $X=X^*$；原输出为 $g_\sigma=\sigma i[c,t_\lambda]/2+s$，其中 $c=C\oplus0_3$、$s=\rho T_A\oplus0_3$。

**命题 34.1（固定 $h$ 的两种尺度）。** 对每个固定的充分小的 $h>0$，存在下文给出的实际输入族，参数为 $\lambda\to+\infty$，满足 $D_{\rm env}\succ0$、$W=0$、$M_1=C$、$H=2C+hJ_A$。写 $L_\lambda=\|M_2\|$，则 $L_\lambda=\tfrac32\lambda^2+O(1)$。两个取向的原 P2 允许区间均为 $[-R_\lambda,R_\lambda]$，其中 $R_\lambda\sim\beta\sqrt{2/3}/\lambda\sim\beta/\sqrt{L_\lambda}$。存在常数 $K_*>0$，使充分大的 $\lambda$ 上，每个 $K_*/\lambda^2\le|\rho|\le R_\lambda$ 都在两个取向分别有严格违反原 PB 的有限见证，每份见证的两笔原预算均严格正。

再取 $h$ 落在定理 33.1 的邻域内，应用其一致反二阶矩下界，则存在 $c'>0$，使充分大的 $\lambda$ 上，两个取向各自的原 P2 与全部原 PB 的联合允许集，以及要求两个取向同时成立的联合允许集 $\mathcal J_\lambda$，均满足同样的双包含。对 $\mathcal J_\lambda$，即
$$
[-c'/\lambda^2,c'/\lambda^2]\ \subseteq\ \mathcal J_\lambda\
\subseteq\ [-K_*/\lambda^2,K_*/\lambda^2].
\tag{34.1}
$$
故在上述 $h$ 范围内，联合允许范围的内外尺度均为 $L_\lambda^{-1}$。

### 34.1 基准演员接触

先固定取向 $\iota=i$，绝对值符号 $\epsilon=1$，并取 $\nu=0$、$\ell=b-it_*$，其中 $b\in\mathbb R$、$t_*=\sqrt6$。这样 $\zeta_\tau=i+\tau\ell=\beta_\tau-\tau i\alpha_\tau$，其中 $\tau=\pm1$，$\beta_\tau=\tau b$、$\alpha_\tau=t_*-\tau>0$。记 $B=3C+hJ_A$、$H=2C+hJ_A$、$p=Xu$、$q=XCu$，以 $a_{\rm act}$ 表示待实现的演员作用列，令 $v=a_{\rm act}-ip$、$U=iq+BCu+Cv$。

为看清接触条件，在实际输入上写 $d=Fu+D_{\rm env}y$、$\xi=(u,y)$、$a_{\rm act}=Bu+Vy$，其中 $F=V^*$。前卷 (27.4)–(27.5) 的原列 $R_\tau\xi$ 的两块为 $p-\tau U/2$、$-\tau FCu/2$；$S_\tau\xi$ 的两块为 $a_{\rm act}+\tau[(Cp+q+iCa_{\rm act}-iBCu)/2+\rho T_Au]$、$d-\tau iFCu/2$。减去 $\zeta_\tau R_\tau\xi$ 后，演员常项为 $a_{\rm act}-ip+\ell U/2$，演员的 $\tau$ 项为 $iCv-\ell p+\rho T_Au$，环境项中的 $\tau iFCu/2$ 抵消。因此 §32 的原缺陷写成
$$
\begin{aligned}
E_\tau&=S_\tau\xi-\zeta_\tau R_\tau\xi
       =(\mathsf P+\tau\mathsf Q,\ d+\ell FCu/2),\\
\mathsf P&=v+\ell U/2,\qquad
\mathsf Q=iCv-\ell p+\rho T_Au .
\end{aligned}
\tag{34.2}
$$
在 $\rho=0$，先由 $\mathsf Q=0$ 解出 $v$，再由 $\mathsf P=0$ 得 $U=-2v/\ell=2iC^{-1}p$，故接触条件等价于
$$
v=-i\ell C^{-1}p,\qquad
a_{\rm act}=i(I_2-\ell C^{-1})p,\qquad
q=(\ell I_2+2C^{-1})p+iBCu .
\tag{34.3}
$$

为使两列由同一个 Hermitian $X$ 产生，取
$$
u=\frac{(\sqrt r,e^{i\theta})^{\mathsf T}}{\sqrt{1+r}},\qquad
r>0,\qquad p_j=z_j u_j,\qquad z_1\in\mathbb R,\ z_2\in\mathbb C .
$$
因 $c_1=1,c_2=2$，从 $p=Xu$、$q=XCu$ 逐行消去非对角元得到
$$
x_{11}=(2p_1-q_1)/u_1,\qquad x_{22}=(q_2-p_2)/u_2 .
$$
这两列可由一个 Hermitian $X$ 实现，当且仅当 $x_{11},x_{22}$ 都为实数，且
$$
r(z_1-x_{11})=\overline{z_2-x_{22}}.
\tag{34.4}
$$
确实，取 $X_{12}=(z_1-x_{11})u_1/u_2$，取 $X_{21}=\overline{X_{12}}$，再代入第二行 $p$ 即得 (34.4)；对角定义随后给回 $q$ 的两行。

在 $h=0$，(34.3) 给 $x_{11}=-\ell z_1-3i$、$x_{22}=\ell z_2+12i$。写 $z_2=B_2+iD_2'$。对角虚部条件是 $t_*z_1-3=0$、$bD_2'-t_*B_2+12=0$。施加这两式后，(34.4) 的虚部给 $D_2'=0$，实部给 $r(1+b)z_1=(1-b)B_2$。故在 $0<b<1$ 上，四个 Hermitian 条件给出
$$
z_j=\frac{3c_j^2}{t_*},\qquad r=\frac{4(1-b)}{1+b}.
\tag{34.5}
$$

接着令 $d_0=a_{\rm act}-Hu+\ell C^2u/2$，要求 $d_0$ 与 $a$ 共线。写 $D_j=(d_0)_j/u_j$；在基准 $h=0$，由 (34.3)、(34.5) 和 $t_*^2=6$ 得
$$
D_j=-5c_j+\frac{b c_j^2}{2}-i\frac{3b c_j}{t_*}.
\tag{34.6}
$$
两实部在 $0<b<1$ 上均严格为负。条件 $(d_0)_2=\sqrt2(d_0)_1$ 的模长方程为 $|D_2|^2=2r|D_1|^2$。由 (34.6)，
$$
\begin{aligned}
|D_1|^2&=25-5b+\tfrac74 b^2,\qquad |D_2|^2=100-40b+10b^2,\\
f(b)&=(1+b)|D_2|^2-8(1-b)|D_1|^2
     =-100+300b-84b^2+24b^3 .
\end{aligned}
\tag{34.7}
$$
$f(0)=-100$、$f(1)=140$，且 $f'(b)=300-168b+72b^2>0$ 于 $[0,1]$，故唯一根 $b_0$ 在 $(0,1)$。在此根取相位 $\theta_0$，使 $e^{i\theta_0}D_2/(\sqrt r D_1)=\sqrt2$。此时 $d_0=\eta a$，其中 $\eta=\sqrt2(d_0)_1\ne0$。又由 (34.3) 得 $\operatorname{Re}(v_j/u_j)=-3c_j$，从而
$$
\zeta:=\operatorname{Re}(v^*T_Au)=\frac{3(4-r)}{1+r}>0 ,
\tag{34.8}
$$
因为 (34.5) 在 $b_0$ 处给 $0<r<4$。这里 $\zeta$ 是实配对，与变分系数 $\zeta_\tau$ 分开。

### 34.2 用实隐函数定理延续到固定非零 $h$

在基准解附近，对实变量 $(z_1,\operatorname{Re}z_2,\operatorname{Im}z_2,r,b,\theta)$，保留两条对角虚部方程、(34.4) 的实部与虚部，以及 $(d_0)_2-\sqrt2(d_0)_1=0$ 的两个实分量。所有方程在 $r>0$ 的局部坐标中光滑；最后一对也可写成 $(d_0)_2/(d_0)_1-\sqrt2=0$，因为基准解的 $(d_0)_1\ne0$。固定 $(b,\theta)$，基准的前四式按 (34.5) 的顺序消元：取对角虚部、左边减右边的非对角虚部与实部，主元依次为 $t_*,-t_*,1,(1+b_0)z_1$，均非零。

消去这四个变量后，在 $h=0$，最后一对方程的复读数为 $Z-\sqrt2$，其中 $Z=e^{i\theta}D_2/(\sqrt r D_1)$。沿消元所得的解，
$$
|Z|^2-2=\frac{f(b)}{(1+b)r|D_1|^2}.
$$
在根处，对 $b$ 的导数非零，所以 $\partial_b Z$ 有非零径向分量；而 $\partial_\theta Z=i\sqrt2$ 是非零切向分量。这给出可逆的剩余实 $2\times2$ 雅可比块，从而全六维实雅可比可逆。有限维实隐函数定理遂给出每个充分小 $h$ 的局部解。用 (34.4) 的构造恢复实际 $X=X^*$，由 (34.3) 得对应作用列。缩小 $h$ 的邻域后，$r>0$、$\eta\ne0$ 和 $\zeta>0$ 由连续性保留。下文固定其中任一 $h>0$；这些演员数据不随 $\lambda$ 或 $\rho$ 变化。

### 34.3 固定 $H,M_1$ 的实际正定环境

对 $\lambda>1$，取
$$
\begin{gathered}
\delta_\lambda=\lambda^{-3},\qquad
P_\lambda=C-\delta_\lambda\lambda^2aa^*,\qquad
D_{\rm env}=C\oplus\delta_\lambda,\\
F=\begin{bmatrix}C^{1/2}P_\lambda^{1/2}\\ \delta_\lambda\lambda a^*\end{bmatrix},
\qquad
V=F^*,\qquad
t_\lambda=\begin{pmatrix}3C+hJ_A&V\\ F&D_{\rm env}\end{pmatrix}.
\end{gathered}
\tag{34.9}
$$
$C^{-1/2}P_\lambda C^{-1/2}=I_2-\lambda^{-1}nn^*\succ0$，所以正平方根存在，且 $F$ 的首块可逆。各输入块为实矩阵；$D_{\rm env}\succ0$ 给 $W=0$。取 $G=D_{\rm env}^{-1}F$，其首块为 $C^{-1/2}P_\lambda^{1/2}$、末行为 $\lambda a^*$。逐块相乘得到
$$
\begin{aligned}
M_1&=G^*F=P_\lambda+\delta_\lambda\lambda^2aa^*=C,\qquad
H=B-M_1=2C+hJ_A,\\
M_2&=G^*G=P_\lambda^{1/2}C^{-1}P_\lambda^{1/2}+\lambda^2aa^* .
\end{aligned}
\tag{34.10}
$$
随 $\lambda\to+\infty$，$P_\lambda\to C$，由正平方根的连续性，$M_2$ 的第一项趋于 $I_2$。由算子范数的三角不等式与反向三角不等式，$L_\lambda=\lambda^2\|a\|^2+O(1)=\tfrac32\lambda^2+O(1)$。同时 $F$ 的首块趋于 $C$，末行趋于零，$D_{\rm env}\to C\oplus0$，所以 $t_\lambda$ 在范数中趋于同一固定 $h$ 的 §32 输入添一条不耦合零模所得的矩阵。这个输入极限不要求探针向量的环境分量有界。

### 34.4 原 P2 的精确读取

$C^{-1/2}HC^{-1/2}=2I_2+(h/\sqrt2)J_A$。取 $n_-=(1,-1)^{\mathsf T}/\sqrt2$，则 $U_0=[n,n_-]$ 按 $2+\beta,2-\beta$ 排列归一化 Schur 矩阵的特征值。前卷 (30.29) 的 $\omega=1$。令 $K=Q_M^{-1}$；由 $C^{-1/2}a=n$，
$$
K=K_{\rm base}+\lambda^2 e_1e_1^*,\qquad
K_{\rm base}\longrightarrow U_0^*\operatorname{diag}(2,1)U_0
 =\begin{pmatrix}3/2&1/2\\1/2&3/2\end{pmatrix},
\tag{34.11}
$$
其中 $e_1=(1,0)^{\mathsf T}$ 是谱坐标中的首轴。$K$ 为实正定矩阵，故 (30.29) 的 $J=0$；又 $d_1=K_{22}/\det K$、$d_2=K_{11}/\det K$、$\Delta=1/\det K$。因此两个取向的精确原 P2 半径相同：
$$
R_\lambda=\frac{\beta}{\sqrt{K_{11}K_{22}}}
 \ \sim\ \frac{\beta\sqrt{2/3}}{\lambda}.
\tag{34.12}
$$

### 34.5 同一实际输入上的两侧原 PB 见证

在 (34.9) 的环境中，使用延续后的 $u,X,\ell,\eta$，取
$$
e=(0,0,\eta/\lambda)^{\mathsf T},\qquad
y=D_{\rm env}^{-1}(e-\ell FCu/2-Fu),\qquad \xi=(u,y).
\tag{34.13}
$$
由 $G$ 的末行，$G^*e=\eta a=d_0$。同一实际向量给出 $d=Fu+D_{\rm env}y=e-\ell FCu/2$，于是
$$
Bu+Vy=Hu+G^*d=Hu+d_0-\ell C^2u/2=a_{\rm act}.
$$
这里用到 $G^*D_{\rm env}=V$、$G^*F=C$。因此演员接触与两条环境缺陷在同一个 $x=X\oplus0_3$、$\xi$ 上实现。由 (34.2)–(34.3)，$\mathsf P=0$、$\mathsf Q=\rho T_Au$，两条环境缺陷都为 $e$。对每个有限 $\lambda$，(34.13) 的向量有限。

写 $\phi_\xi(A)=\xi^*A\xi$，将原 PB 左侧的算子暂记为 $L_{\rm PB}$，以区别于 $L_\lambda$。式 (32.3)–(32.4) 的带符号有限代价，是两笔 (27.12) 的所选变分值之和减去 $2\epsilon\phi_\xi(L_{\rm PB})$。展开 $E_\tau$ 的平方时，虚交叉项按 §32 的原换位恒等式消去零残量部分；加入 $s$ 后，剩余改变量为 $4\epsilon\rho\operatorname{Re}(v^*T_Au)$。这里该恒等式只用原作用列，对 (34.9) 仍适用。设 $N=\|T_Au\|^2$、$w=(t_*-1)^{-1}+(t_*+1)^{-1}=2t_* /(t_*^2-1)$，则当前 $\iota=i,\epsilon=1$ 的有限代价恰为
$$
\mathcal D_\rho=w\left(N\rho^2+\frac{|\eta|^2}{\lambda^2}\right)+4\rho\zeta .
\tag{34.14}
$$
这组选取用于 $\rho<0$。对于 $\rho>0$，保持 $\iota=i$ 和同一份实输入及同一个 $\rho$，改取 $(u,\ell,X,\epsilon)=(\overline u,\overline\ell,-\overline X,-1)$，其中右侧为前一组数据。此时 $p,q$ 变为 $-\overline p,-\overline q$，由 (34.3)，$v,a_{\rm act},d_0$ 变为各自的共轭，(34.13) 的 $e,y$ 也随之共轭。新的 $\alpha_\tau=t_*+\tau$ 交换两个正权，$\beta_\tau$ 不变；$\zeta,N,|\eta|$ 都不变。故对正、负两侧分别使用所选见证，统一得到
$$
\mathcal D_\rho=w\left(N\rho^2+\frac{|\eta|^2}{\lambda^2}\right)-4\zeta|\rho|.
\tag{34.15}
$$
另一取向 $\iota=-i$ 由对每侧的全部原列取复共轭得到，同时将 $\iota,\ell$ 共轭，保留该侧的 $\epsilon,\alpha_\tau,\beta_\tau$；原输入和 $\rho$ 为实，范数及实配对不变，故仍为 (34.15)。

由 (34.12)，充分大的 $\lambda$ 满足 $wN R_\lambda\le2\zeta$。取 $K_*=1+w|\eta|^2/(2\zeta)$；在 $K_*/\lambda^2\le|\rho|\le R_\lambda$ 时，
$$
\mathcal D_\rho\le \frac{w|\eta|^2}{\lambda^2}-2\zeta|\rho|
 \le -\frac{2\zeta}{\lambda^2}<0.
\tag{34.16}
$$
按前卷 (27.12)–(27.13)，每笔原预算根的两倍至多为所选的有限变分值。因此 (34.16) 给同一实际 $x,\phi_\xi$ 的严格原 PB 违反，无需让变分参数取极限。

两笔原预算均严格正：对每个 $\tau$，$(R_\tau\xi)_{\rm env}=-\tau FCu/2$，而 $(E_\tau)_{\rm env}=e$。$FCu$ 的首两坐标非零（作为一个二元列），因为 $C^{1/2}P_\lambda^{1/2}$ 可逆且 $Cu\ne0$；$e$ 的首两坐标为零、末坐标非零，因为 $\eta$ 在基准和延续后都非零。故这两条环境列复线性无关，进而 $R_\tau\xi$ 与 $S_\tau\xi=E_\tau+\zeta_\tau R_\tau\xi$ 复线性无关。原预算是这两条原像的实 Gram 行列式，因而严格正。取共轭或更换上述符号时，同一论证成立。向量 $\xi$ 的演员分量为单位向量，故将同一泛函乘以 $\mu/\|\xi\|^2$ 即可取得任一指定正有限质量 $\mu$；严格违反与预算正性均保留。

### 34.6 条件下界与结论范围

两侧排除已经由 (34.16) 给出，区间外则由原 P2 排除。对于内含界，应用定理 33.1：在 $\|H-2C\|,\|M_1-C\|<\delta_0$、$W=0$ 且 $\|M_2\|\le L$、$L\ge1$ 时，$|\rho|\le c/L$ 保证同一输入在两个取向满足全部原 PB。这里 $\|H-2C\|=h$、$M_1=C$、$W=0$；固定 $0<h<\delta_0$ 并取 $L=L_\lambda$，充分大的 $\lambda$ 有 $1\le L_\lambda\le2\lambda^2$。于是可取 $c'=\min(c/2,K_*/2)>0$，得到 $|\rho|\le c'/\lambda^2$ 的全部原 PB；由 (34.12)，这些点最终严格在两个原 P2 区间之内。这就给出 (34.1)，含原下界所覆盖的全部正有限质量及零质量。

本节按通常形式使用实隐函数定理、正平方根的连续性及实 Gram 行列式的变分公式；原列和原 P2 读取分别沿 §32 与前卷 (30.29)，零模与伪逆连续性的背景沿 §33 已列归属。这里给出的是该正定族的两侧排除与依赖 §33.1 的阶数比较，不判定联合允许集的形状或最优常数。

## 追加锚（本行以下为增补区）

## 35. 固定零阶矩的正定环境、临界相位与全部原预算的共同尺度

本节及 §36 固定 §32 的 $C=\operatorname{diag}(1,2)$、$T_A=\operatorname{diag}(1,-2)$、$J_A$ 和 $U_0=2^{-1/2}\left(\begin{smallmatrix}1&1\\1&-1\end{smallmatrix}\right)$。旧式号 (17.x)、(27.x)、(30.x)、(31.x) 指[前卷](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md)。§32 与前卷的引用取共同钉版 `315e167044afd2593b851f6546a82470ca16d446`；§34 的演员接触是本卷纸面前提。以下反二阶矩 PB 下界只使用 §32，不使用 §33.1 的两矩近邻定理。各节陈述均属纸面推导，不构成 Lean／kernel 认证。

### 35.1 原全称条件与固定零阶矩实现

**定义 35.1（同一实际来源上的允许集）。** 在演员为 $\mathbb C^2$、环境为 $\mathbb C^m$ 的完整原代数上，令

$$
\begin{gathered}
t=\begin{pmatrix}B&V\\V^*&D\end{pmatrix}=t^*,\qquad
c=C\oplus0_m,\qquad s_\rho=\rho T_A\oplus0_m,\qquad
x=X\oplus0_m,\quad X=X^*,\\
A\circ B=(AB+BA)/2,\qquad K_\sigma(A,B)=\sigma i[A,B]/2,\qquad
g_{\sigma,\rho}=K_\sigma(c,t)+s_\rho,\\
h_x=K_\sigma(c,x),\quad k=c\circ t,\quad r=c\circ x,\qquad
R_\tau=x+\tau(h_x-k),\quad S_\tau=t+\tau(r+g_{\sigma,\rho}),\quad\tau=\pm1,\\
L_{\rm PB}=-2x\circ(h_x-k)-2t\circ(r+g_{\sigma,\rho}),\\
B_\phi(R,S)=\phi(R^2)\phi(S^2)-\phi(R\circ S)^2.
\end{gathered}
\tag{35.1}
$$

这里 $D=D_{\rm env}$。沿前卷的三矩记号，$F=V^*$、$G=D^\dagger F$、$M_0=F^*F$、$M_1=G^*F$、$M_2=G^*G$、$H=B-M_1$、$W=V|_{\ker D}$，其中 $D^\dagger$ 是 Hermitian 矩阵的谱 Moore–Penrose 逆。符号 $h_x$ 不表示 Schur 扰动参数 $h$。原 P2 是对完整代数的每个正复线性泛函 $\phi$ 都有

$$
\phi(g_{\sigma,\rho})^2\le
\phi(c^2)\phi(t^2)-\phi(c\circ t)^2;
\tag{35.2}
$$

原全部 PB 是对每个这样的 $\phi$ 及每个实际 Hermitian $X$ 都有

$$
|\phi(L_{\rm PB})|\le
\sqrt{B_\phi(R_+,S_+)}+\sqrt{B_\phi(R_-,S_-)}.
\tag{35.3}
$$

分别以 $I_\sigma(t)$、$\mathcal B_\sigma(t)$ 记满足原 P2、全部原 PB 的实参数 $\rho$ 集，定义

$$
\mathcal J_\sigma(t)=I_\sigma(t)\cap\mathcal B_\sigma(t),\qquad
\mathcal J_{\rm both}(t)=\mathcal J_+(t)\cap\mathcal J_-(t).
\tag{35.4}
$$

所有乘积、平方、原像和泛函都属于同一个完整原代数。固定任意正有限质量 $\mu$ 而量化全部 $\phi(I)=\mu$，得到相同允许集；这是前卷 (17.14)–(17.16) 及正齐次性的应用。若只取质量零，则只有零泛函，(35.2)–(35.3) 都是零等式，不能单独定义上述非平凡允许集。

**命题 35.2（固定 $M_0$ 的实际正定实现）。** 给定 $a\in\mathbb C^2\setminus\{0\}$、$\lambda>0$ 和实 $h$，在同一个完整 $M_5(\mathbb C)$ 中取

$$
\begin{gathered}
\delta=\lambda^{-3},\qquad F=\begin{bmatrix}C\\0\end{bmatrix},\qquad V=F^*,\qquad
D=\begin{pmatrix}
C+\delta\lambda^2aa^*&-\delta\lambda a\\
-\delta\lambda a^*&\delta
\end{pmatrix},\\
B=3C+hJ_A,\qquad
t_{h,\lambda,a}=\begin{pmatrix}B&V\\F&D\end{pmatrix},\qquad
G=\begin{bmatrix}I_2\\\lambda a^*\end{bmatrix}.
\end{gathered}
\tag{35.5}
$$

则 $D\succ0$、$DG=F$，并且

$$
\boxed{\quad W=0,\quad M_0=F^*F=C^2,\quad
M_1=G^*F=C,\quad M_2=G^*G=I_2+\lambda^2aa^*,\quad
H=B-M_1=2C+hJ_A.\quad}
\tag{35.6}
$$

若 $|h|<2\sqrt2$，则整个 $t_{h,\lambda,a}\succ0$。设 $t_h^0$ 为 §32 的 $t_h$ 添一条不耦合零模，在环境排序 $\mathbb C^2\oplus\mathbb C$ 下与 (35.5) 比较，则

$$
\|t_{h,\lambda,a}-t_h^0\|=\frac{\|a\|^2}{\lambda}+\lambda^{-3},\qquad
\|t_{h,\lambda,a}-t_0^0\|
=\max\left(|h|,\frac{\|a\|^2}{\lambda}+\lambda^{-3}\right).
\tag{35.7}
$$

证明。对 $D$ 的右下正标量 $\delta$ 作 Schur 补，所得恰为 $C\succ0$，不要求 $\lambda>1$。直接块乘法给 $DG=(C,0)^{\mathsf T}=F$，继而给出全部矩恒等式。对整个 $t$ 作 $D$ 的 Schur 补得到 $H$；它的首主子式为 $2$，行列式为 $8-h^2$，故在所列范围内正定。环境差准确为

$$
D-(C\oplus0)=\delta
\begin{bmatrix}\lambda a\\-1\end{bmatrix}
\begin{bmatrix}\lambda a\\-1\end{bmatrix}^{\!*}.
$$

它是秩一正矩阵，范数为 $\delta(\lambda^2\|a\|^2+1)$。$B,F$ 在同一 $h$ 下不变，给第一式；相对 $h=0$ 的差由演员上的 $hJ_A$ 与该环境差正交直和，给第二式。∎

### 35.2 不共轭环境的同源取向反射

**引理 35.3（同一实际来源上的精确反射）。** 对任一固定实际 $t$ 及 (35.1) 的残量族，

$$
I_-(t)=-I_+(t),\qquad
\mathcal B_-(t)=-\mathcal B_+(t),\qquad
\mathcal J_-(t)=-\mathcal J_+(t).
\tag{35.8}
$$

此结论保留同一个环境、同一个完整正泛函和同一个原向量，不要求 $t$ 为实矩阵。

证明。在同一个 $t$ 上作 $(\sigma,\rho,X)\mapsto(-\sigma,-\rho,-X)$，则 $g'=-g$、$h'_x=h_x$、$k'=k$、$r'=-r$。于是作为完整原算子有

$$
R'_\tau=-R_{-\tau},\qquad S'_\tau=S_{-\tau},\qquad
L'_{\rm PB}=-L_{\rm PB}.
\tag{35.9}
$$

两笔实 Gram 预算交换，左端绝对值不变；$X\mapsto-X$ 是全部 Hermitian 探针的双射，故全部 PB 等价。P2 中仅 $g$ 变号，故亦等价。

为核对后文有限见证，令 $\iota=\sigma i$，采用 (32.3) 的 $\zeta_\tau=\iota+\nu+\tau\ell=\beta_\tau-\tau\epsilon\iota\alpha_\tau$。同步取

$$
(\iota,\epsilon,\rho,X,\nu,\ell)
\mapsto(-\iota,-\epsilon,-\rho,-X,-\nu,\ell),\qquad
\alpha'_\tau=\alpha_{-\tau}>0,\quad\beta'_\tau=-\beta_{-\tau}.
\tag{35.10}
$$

则 $\zeta'_\tau=-\zeta_{-\tau}$，故 $E'_\tau=E_{-\tau}$。在同一 $\xi=(u,y)$ 上，$a_{\rm act}=Bu+Vy$ 不变，$p'= -p$、$q'=-q$，而 $v=a_{\rm act}-\iota p$、$U=\iota q+BCu+Cv$ 均不变。有限带符号代价亦完全不变。这是对原算子对称性的复用；它比较的是不同取向下的 $\rho$ 与 $-\rho$，不把同一个非零 $\rho$ 的两个取向混为一谈。∎

### 35.3 精确 $M_1=C$ 下独立于 §33 的 PB 运输

**定理 35.4（保留全部原探针的 $c_{\rm PB}/L$ 下界）。** 存在 $h_0,c_{\rm PB}>0$，使每份有限实际 $W=0$ 输入，只要

$$
M_1=C,\qquad H=2C+hJ_A,\qquad |h|<h_0,\qquad
\|M_2\|\le L,\quad L\ge1,
\tag{35.11}
$$

就在每个 $|\rho|\le c_{\rm PB}/L$ 满足两个取向的全部原 PB。结论不要求 $M_0$ 的额外界，也不要求 $D$ 可逆；在 (35.5) 中当然适用。

证明。以 $G=D^\dagger F$ 记实际环境映射；$W=0$ 保证 $DG=F$、$G^*D=V$。固定任意原 $X=X^*$、单位演员 $u$、任意环境向量 $y$、两个符号和全部有限参数 $\alpha_\tau>0,\beta_\tau\in\mathbb R$。不优化或更换这份实际测试。令

$$
\begin{gathered}
p=Xu,\quad q=XCu,\quad a_{\rm act}=Bu+Vy,\quad v=a_{\rm act}-\iota p,\quad
d=Fu+Dy,\quad U=\iota q+BCu+Cv,\\
\mathsf P=v-\nu p+\ell U/2,\qquad
\mathsf Q=\iota Cv-\ell p+\rho T_Au+\nu U/2,\\
\chi_\tau=\alpha_\tau^{-1},\quad s_\alpha=\chi_++\chi_-,\quad
\omega_\chi=(\chi_+-\chi_-)/s_\alpha,\quad
\bar b=(\ell+\omega_\chi\nu)/2,\quad e=d+\bar b FCu,\\
\kappa=\frac{|\nu|^2\chi_+\chi_-}{s_\alpha}\ge0,\qquad
A_{\rm act}=\sum_{\tau=\pm1}\chi_\tau\|\mathsf P+\tau\mathsf Q\|^2.
\end{gathered}
\tag{35.12}
$$

注意 $\bar b$ 只是加权复系数的名称，不表示取共轭。由 (32.5)、(31.9)–(31.10) 的原列与加权方差，实际缺陷平方和及配对准确为

$$
S=A_{\rm act}+s_\alpha\|e\|^2+\kappa\|FCu\|^2,\qquad
\mathcal D_\rho=S+4\epsilon\rho R,\quad
R=\operatorname{Re}(v^*T_Au),\quad
a_{\rm act}=Hu+G^*e-\bar b C^2u.
\tag{35.13}
$$

在 §32 的基准环境 $F_b=C,G_b=I_2,D_b=C$ 中，取同一 $B,H,X,u,\rho$ 及全部变分参数，仅定义用于比较的

$$
e_b=G^*e,\qquad d_b=e_b-\bar b C^2u,\qquad
y_b=C^{-1}(d_b-Cu).
\tag{35.14}
$$

则 $Bu+Cy_b=Hu+d_b=a_{\rm act}$。所以演员原列、$\mathsf P,\mathsf Q$ 和 $R$ 完全相同。该基准测试的平方和为

$$
S_b=A_{\rm act}+s_\alpha\|G^*e\|^2+\kappa\|C^2u\|^2\le LS.
\tag{35.15}
$$

最后一步只用三条逐项不等式：$A_{\rm act}\le LA_{\rm act}$、$\|G^*e\|^2\le L\|e\|^2$，以及
$\|C^2u\|^2=\|G^*FCu\|^2\le L\|FCu\|^2$，其中 $\|G\|^2=\|M_2\|\le L$。这不是为不同预算各选一个最优环境：同一个 $e_b,y_b$ 同时比较两条原缺陷。

现明确使用 §32 的常数范围。在其 (32.9)–(32.14) 及 (32.15) 前的统一下界中，存在 $\gamma,K_0,h_0,r_0>0$，可取 $r_0\le1$，使对每个基准测试和 $|h|<h_0,|\rho|\le r_0$ 有

$$
S_b\ge\gamma b_\vartheta,\qquad
|R|\le K_0\bigl(b_\vartheta+\sqrt{b_\vartheta S_b}+|\rho|\bigr),\qquad
b_\vartheta=\frac{(|\ell|+|\nu|)^2}{|\ell|}\ge1.
\tag{35.16}
$$

这里参数合法性正是 (32.6)，$|\ell|>0$；$\vartheta$ 是原变分索引，不是下文外部相位。§32 的大尺度、紧域和方差三域下界对两个取向、两个绝对值符号以及全部有限参数共同成立；配对界是在 (32.10) 之前取得。取闭的较小 $r_0$ 即可保留上述端点。由 $|\rho|\le1\le b_\vartheta$，

$$
|R|\le A_0S_b\le A_0LS,\qquad
A_0=K_0\left(\frac2\gamma+\frac1{\sqrt\gamma}\right),\qquad
c_{\rm PB}=\min\left(r_0,\frac1{8A_0}\right)>0.
\tag{35.17}
$$

于是 $|\rho|\le c_{\rm PB}/L$ 时原有限代价满足

$$
\mathcal D_\rho\ge(1-4A_0L|\rho|)S\ge S/2\ge0.
\tag{35.18}
$$

对固定的同一个实际 $X,\xi$，在全部有限变分参数上取 (27.12) 的下确界，即得原向量 PB，包括下确界不取到的退化 Gram。演员分量非单位时同比缩放整个向量；演员分量为零时，$x\xi=h_x\xi=r\xi=s_\rho\xi=0$，且 $\phi_\xi(L_{\rm PB})=-2\operatorname{Re}((Vy)^*\iota CVy/2)=0$，所以 PB 自动成立。

最后，任意完整原代数正泛函都有 (17.14) 的谱和 $\phi=\sum_j\phi_{\xi_j}$。把 (17.15) 分别用于原两笔实 Gram，结合 $|\sum_j\phi_{\xi_j}(L_{\rm PB})|\le\sum_j|\phi_{\xi_j}(L_{\rm PB})|$，正是 (17.16) 的全正泛函提升。所有环境密度块、全部原 $X$ 和同一实际 $t$ 均保留，任意给定正有限总质量不变，零泛函亦满足零等式。∎

### 35.4 精确临界相位与两个分别取向的 P2 边界

**定理 35.5（固定 $M_0$ 相位族的精确 P2）。** 在 (35.5) 中令

$$
\begin{gathered}
w_\theta=\frac1{\sqrt2}(1,i e^{i\theta})^{\mathsf T},\qquad
a_\theta=C^{1/2}U_0w_\theta
=\frac12(1+i e^{i\theta},\sqrt2(1-i e^{i\theta}))^{\mathsf T},\\
s(\theta)=\|a_\theta\|^2=\frac{3+\sin\theta}{2},\qquad
L_{\lambda,\theta}=\|M_2\|=1+s(\theta)\lambda^2,\qquad
0<h<2\sqrt2,\quad\beta=h/\sqrt2.
\end{gathered}
\tag{35.19}
$$

对每个实 $\theta$、每个 $\lambda>0$，有精确公式

$$
\begin{gathered}
K=Q_M^{-1}=K_0+\lambda^2w_\theta w_\theta^*,\qquad
K_0=\begin{pmatrix}3/2&1/2\\1/2&3/2\end{pmatrix},\qquad
\det K=L_{\lambda,\theta}+1,\\
T=\sqrt{K_{11}K_{22}}=\frac32+\frac{\lambda^2}{2},\qquad
q=\operatorname{Im}K_{12}=-\frac{\lambda^2\cos\theta}{2},\\
d_{\rm w}=T+q=\frac32+\frac{\lambda^2(1-\cos\theta)}2,\qquad
d_{\rm s}=T-q=\frac32+\frac{\lambda^2(1+\cos\theta)}2,\\
\boxed{\quad I_+(t_{h,\lambda,a_\theta})=[-\beta/d_{\rm w},\beta/d_{\rm s}],\qquad
I_-(t_{h,\lambda,a_\theta})=[-\beta/d_{\rm s},\beta/d_{\rm w}].\quad}
\end{gathered}
\tag{35.20}
$$

其中下标 w、s 仅在 $\cos\theta\ge0$ 时分别表示宽侧、短侧。两个取向同时满足 P2 的集合总是

$$
I_+(t)\cap I_-(t)=\left[-\frac\beta{T+|q|},\frac\beta{T+|q|}\right].
\tag{35.21}
$$

固定 $h>0$，若 $\lambda\to\infty$、$\theta_\lambda\to0$ 且扩展实极限
$\lambda^2(1-\cos\theta_\lambda)\to\gamma\in[0,\infty]$ 存在，则分别取向的闭区间按 Hausdorff 距离收敛为

$$
I_+\longrightarrow[-A_\gamma,0],\qquad
I_-\longrightarrow[0,A_\gamma],\qquad
A_\gamma=\frac\beta{3/2+\gamma/2},\quad A_\infty=0.
\tag{35.22}
$$

所有 $A_\gamma\in[0,2\beta/3]$ 都能实现：有限 $\gamma$ 可取 $\theta_\lambda=\sqrt{2\gamma}/\lambda$，无穷 $\gamma$ 可取 $\theta_\lambda=\lambda^{-1/2}$。特别地 $\theta_\lambda=s_*/\lambda$ 给 $A_\gamma=\beta/(3/2+s_*^2/4)$。

证明。归一化 Schur 块为 $2I_2+\beta J_A$，有序谱基为上述实 $U_0$，(30.29) 中 $\omega=1$。由 (35.6)，直接得到
$K=U_0^*C^{-1/2}(2I_2+\lambda^2a_\theta a_\theta^*)C^{-1/2}U_0$，即 (35.20) 的第一式。其非对角元为 $1/2-\lambda^2(\sin\theta+i\cos\theta)/2$；展开二阶行列式得 $\det K=2+s(\theta)\lambda^2$。在 (30.29) 中 $R=T/\det K$、$\Delta=1/\det K$、$J=q/\det K$，于是得到两个精确闭区间及其交。正定性保证分母严格正；这里两分母也都直接不小于 $3/2$。

沿所列相位路径，$d_{\rm w}\to3/2+\gamma/2$，而 $d_{\rm s}\sim\lambda^2$，逐端点给出闭区间极限和实现路径。每个有限阶段的端点都包含在 P2 内；极限端点本身是否最终属于有限阶段的区间，不能由区间收敛自动推出。与此同时 (35.21) 的半径渐近于 $\beta/\lambda^2$，所以两个取向同时满足 P2 的集合已经趋于 $\{0\}$。∎

### 35.5 区分外部相位与演员相位的统一接触延续

**引理 35.6（复相位方向上的有限演员接触）。** 存在 $h_c,\theta_c,\zeta_{\min},\eta_{\min},\eta_{\max}>0$，其中可取 $h_c<2\sqrt2$、$\theta_c\le\pi/6$，以及关于 $(h,\theta)$ 光滑的有限演员数据
$u,X,p,q,a_{\rm act},v,\ell,\eta$，使在 $|h|\le h_c,|\theta|\le\theta_c$ 上

$$
\begin{gathered}
\|u\|=1,\quad u_1u_2\ne0,\quad X=X^*,\quad p=Xu,\quad q=XCu,\qquad
\ell=b-i\sqrt6,\quad b\in\mathbb R,\\
v=-i\ell C^{-1}p,\quad a_{\rm act}=i(I_2-\ell C^{-1})p,\quad
q=(\ell I_2+2C^{-1})p+iBCu,\quad B=3C+hJ_A,\\
d_0:=a_{\rm act}-Hu+\ell C^2u/2=\eta a_\theta,\qquad
\eta_{\min}\le|\eta|\le\eta_{\max},\qquad
\zeta:=\operatorname{Re}(v^*T_Au)\ge\zeta_{\min},\qquad
N:=\|T_Au\|^2\le4.
\end{gathered}
\tag{35.23}
$$

这些数据不依赖 $\lambda$ 或 $\rho$。它们满足原有限参数 $\nu=0$、$\iota=i$、$\epsilon=1$、$\alpha_\tau=\sqrt6-\tau>0$、$\beta_\tau=\tau b$ 下的演员接触 $\mathsf P=\mathsf Q|_{\rho=0}=0$。

证明。沿 §34.1–§34.2 的接触方程，但以 $\varphi$ 记演员相位，保留 $\theta$ 专指外部方向 $a_\theta$。写

$$
u=\frac{(\sqrt r,e^{i\varphi})^{\mathsf T}}{\sqrt{1+r}},\quad
p_j=z_ju_j,\quad z_1\in\mathbb R,\quad z_2\in\mathbb C,\quad r>0,
\tag{35.24}
$$

并由 (35.23) 的前三个接触等式定义 $v,a_{\rm act},q$。两列由同一 Hermitian $X$ 实现的充要条件仍为

$$
x_{11}=(2p_1-q_1)/u_1\in\mathbb R,\quad
x_{22}=(q_2-p_2)/u_2\in\mathbb R,\quad
r(z_1-x_{11})=\overline{z_2-x_{22}}.
\tag{35.25}
$$

这是四个实方程。满足时定义 $X_{12}=(z_1-x_{11})u_1/u_2$、$X_{21}=\overline{X_{12}}$，便同时恢复 $p=Xu,q=XCu$。

在 $h=0$ 时，这四式不依赖 $\varphi$。记 $t_*=\sqrt6$，先由第一条对角虚部得 $z_1=3/t_*$；施加两对角实条件后，非对角方程的虚部给 $\operatorname{Im}z_2=0$；第二条对角虚部给 $\operatorname{Re}z_2=12/t_*$；最后的实部给

$$
z_j=3c_j^2/t_*,\qquad r=4(1-b)/(1+b),\quad 0<b<1.
\tag{35.26}
$$

这些消元的非零系数分别可取 $t_*,1,-t_*,(1+b)z_1$，所以前四式对四变量 $(z_1,\operatorname{Im}z_2,\operatorname{Re}z_2,r)$ 的实雅可比可逆。

如 §34 的 (34.6)–(34.7)，在这条基准解上

$$
\begin{gathered}
D_j=(d_0)_j/u_j=-5c_j+bc_j^2/2-i\,3bc_j/t_*,\\
|D_1|^2=25-5b+7b^2/4,\qquad |D_2|^2=100-40b+10b^2,\\
f(b)=-100+300b-84b^2+24b^3.
\end{gathered}
\tag{35.27}
$$

$f(0)<0<f(1)$ 且 $f'(b)>0$ 于 $[0,1]$，故唯一 $b_0\in(0,1)$ 给 $|D_2|^2=2r|D_1|^2$。两 $D_j$ 的实部均为负，特别地 $D_1\ne0$。此处目标方向是

$$
k(\theta)=\frac{(a_\theta)_2}{(a_\theta)_1}
=\sqrt2\frac{1-i e^{i\theta}}{1+i e^{i\theta}},\qquad k(0)=-i\sqrt2.
\tag{35.28}
$$

分母在零附近非零。选演员相位 $\varphi_0$ 使
$Z=e^{i\varphi}D_2/(\sqrt rD_1)$ 在 $(b_0,\varphi_0)$ 等于 $-i\sqrt2$；相对于 §34 的实方向基准，只是将演员相位减去 $\pi/2$。这不改变前四式、$r$ 或配对
$\zeta=3(4-r)/(1+r)>0$。

将后两个实方程取为 $Z-k(\theta)=0$。沿前四式消元的基准解，有

$$
|Z|^2-2=\frac{f(b)}{(1+b)r|D_1|^2}.
\tag{35.29}
$$

在 $b_0$ 处其 $b$ 导数非零，故 $\partial_bZ$ 有非零径向分量；$\partial_\varphi Z=iZ$ 则是非零切向向量。剩余实 $2\times2$ 块可逆，与前四式组成的六维实雅可比因而可逆。对参数 $(h,\theta)$ 应用有限维实隐函数定理，得到全部接触数据。这里外部相位是参数，演员相位是待解变量，两者没有被设为相同。

取一个闭参数盒，严格位于上述存在邻域内；连续性及紧性给 $r>0$、$u_1u_2\ne0$、$\eta=(d_0)_1/(a_\theta)_1\ne0$ 和 $\zeta>0$ 的共同上下界。最后 $N\le\|T_A\|^2=4$。原参数合法性由 $\alpha_\tau=t_*-\tau>0$ 直接保证。∎

### 35.6 接回固定 $M_0$ 的同一有限原见证

**定理 35.7（宽侧尾部的严格原 PB 排除与两笔正预算）。** 缩小引理 35.6 的正 $h$ 邻域后，存在 $h_U>0$ 及常数 $K_{\rm tail}>0$，使每个固定 $0<h<h_U$、每个 $|\theta|\le\theta_c$、每个 $\lambda\ge2$ 上，(35.5) 的同一来源满足：凡

$$
\rho\in I_+(t),\qquad \rho<0,\qquad |\rho|\ge K_{\rm tail}/\lambda^2,
\tag{35.30}
$$

都有一个有限实际原探针和向量泛函严格违反取向 $+$ 的 PB，且两笔原预算均严格正。取向 $-$ 的对应排除是 $\rho>0$、$\rho\in I_-(t)$、$\rho\ge K_{\rm tail}/\lambda^2$。两取向的对应见证保留同一环境与同一向量，按引理 35.3 反射。

证明。使用引理 35.6 的数据，在固定 $M_0$ 的 (35.5) 中明确取

$$
e=(0,0,\eta/\lambda)^{\mathsf T},\qquad
y=D^{-1}(e-\ell FCu/2-Fu),\qquad \xi=(u,y).
\tag{35.31}
$$

这里 $F$ 的首块是 $C$、末行是零，$G$ 的首块是 $I_2$、末行是 $\lambda a_\theta^*$，所以

$$
G^*e=\eta a_\theta=d_0,\qquad
d=Fu+Dy=e-\ell FCu/2,\qquad
Bu+Vy=Hu+G^*d=a_{\rm act}.
\tag{35.32}
$$

最后一式用 $G^*F=C$，从而 $G^*FCu=C^2u$。这三式把演员接触与两份环境缺陷接到同一个实际 $X,\xi,t$；不需要 §34.3 的可变 $F$ 实现。每个有限 $\lambda$ 的 $D^{-1},y$ 都有限，不对其随 $\lambda$ 的范数作有界假设。

原 (32.5) 于是给 $E_\tau=(\tau\rho T_Au,e)$。由 (31.9) 或 (32.4) 的精确带符号恒等式，当前 $\iota=i,\epsilon=1$ 的所选有限变分代价准确为

$$
\mathcal D_\rho=w_\alpha\left(N\rho^2+\frac{|\eta|^2}{\lambda^2}\right)+4\rho\zeta,
\qquad w_\alpha=(\sqrt6-1)^{-1}+(\sqrt6+1)^{-1}=2\sqrt6/5.
\tag{35.33}
$$

因负侧 P2 总有 $|\rho|\le2\beta/3$，可选 $0<h_U\le h_c$ 使
$8w_\alpha(h_U/\sqrt2)/3\le2\zeta_{\min}$。于是每个所列 $h,\theta,\rho<0$ 都有 $w_\alpha N|\rho|\le2\zeta_{\min}\le2\zeta$。取

$$
K_{\rm tail}=1+\frac{w_\alpha\eta_{\max}^2}{2\zeta_{\min}}.
$$

则在 (35.30) 内

$$
\mathcal D_\rho\le
\frac{w_\alpha\eta_{\max}^2}{\lambda^2}-2\zeta_{\min}|\rho|
\le-\frac{2\zeta_{\min}}{\lambda^2}<0.
\tag{35.34}
$$

所选有限变分和不小于原两笔预算根之和的两倍，正是 (27.12)。因此 $\mathcal D_\rho<0$ 推出同一个 $x,\phi_\xi$ 的原 PB 严格失败，无需达到任何下确界。另一取向用 (35.10)，即 $\rho'=-\rho$、$X'=-X$、$\epsilon'=-1$，保持 $u,y,\ell$ 与复环境不变，代价仍为同一负数。

现在量化两笔原预算的严格正性。在本实现中

$$
(R_\tau\xi)_{\rm env}=-\tau(C^2u,0)^{\mathsf T}/2,\qquad
(E_\tau)_{\rm env}=e=(0,0,\eta/\lambda)^{\mathsf T}.
\tag{35.35}
$$

这两列正交且非零。$S_\tau\xi=E_\tau+\zeta_\tau R_\tau\xi$，故其环境复 Gram 行列式是 $\|C^2u\|^2|\eta|^2/(4\lambda^2)$。加入演员块使复 Gram 矩阵增加半正定矩阵，其二阶行列式不减；实 Gram 行列式又等于复 Gram 行列式加上内积虚部的平方。因此两个原预算逐一满足

$$
B_{\phi_\xi}(R_\tau,S_\tau)\ge
\frac{\|C^2u\|^2|\eta|^2}{4\lambda^2}>0,\qquad \tau=\pm1.
\tag{35.36}
$$

反射只交换两笔预算和一个列的符号，严格正性保留。由于 $\|u\|=1$，将同一 $\phi_\xi$ 乘以 $\mu/\|\xi\|^2$ 即得每个指定正有限质量 $\mu$，严格违反与两笔正预算一同保留。∎

### 35.7 联合允许集的共同尺度与奇异极限边界

**推论 35.8（无 §33 前提的双包含与分别取向比较）。** 固定
$0<h<\min(h_U,h_0,2\sqrt2)$，令 $\beta=h/\sqrt2$。对全部 $|\theta|\le\theta_c$、$\lambda\ge2$，记 $L=L_{\lambda,\theta}$，则存在仅依赖这些固定数据的正常数 $c_{\rm in}(h),K_{\rm out}(h)$，使

$$
\begin{gathered}
[-c_{\rm in}/L,c_{\rm in}/L]\subseteq\mathcal J_\sigma(t)
\subseteq[-K_{\rm out}/L,K_{\rm out}/L],\qquad\sigma=\pm1,\\
[-c_{\rm in}/L,c_{\rm in}/L]\subseteq\mathcal J_{\rm both}(t)
\subseteq[-K_{\rm out}/L,K_{\rm out}/L].
\end{gathered}
\tag{35.37}
$$

特别地，在定理 35.5 的每条临界相位路径上，两个分别取向的联合允许集及同时取向的联合允许集都按 Hausdorff 距离趋于 $\{0\}$。若 $\gamma<\infty$ 且 $0<r_*<A_\gamma$，则充分大的每个有限 $\lambda$ 上，同一实际来源的 $\rho=-r_*$ 属于 $I_+$ 却严格违反该取向 PB；$\rho=r_*$ 对取向 $-$ 有反射后的同一结论，每个违反的两笔原预算均严格正。

证明。由 $\theta_c\le\pi/6$、$\lambda\ge2$，有

$$
\lambda^2\le L\le2\lambda^2,\qquad
\frac\beta{d_{\rm s}}\ge\frac\beta{2\lambda^2}\ge\frac\beta{2L},\qquad
\frac\beta{d_{\rm s}}\le\frac{2\beta}{\lambda^2}.
\tag{35.38}
$$

取 $c_{\rm in}(h)=\min(c_{\rm PB},\beta/2)>0$，定理 35.4 及精确 P2 的短端点共同给内含界。定理 35.7 排除 $+$ 的宽负尾，P2 自身控制其短正尾；取向 $-$ 反射。因此

$$
\mathcal J_+(t)\subseteq[-K_{\rm tail}/\lambda^2,2\beta/\lambda^2],\qquad
\mathcal J_-(t)\subseteq[-2\beta/\lambda^2,K_{\rm tail}/\lambda^2].
\tag{35.39}
$$

可取 $K_{\rm out}(h)=2\max(K_{\rm tail},2\beta)$。这是集合包含，不宣称分别取向的集合是区间或已经找出其宽侧精确端点。

每个原 P2、PB 测试对 $\rho$ 的余量连续，故这些允许集是闭集；它们包含零，且由 (35.37) 有界，遂得上述 Hausdorff 极限。固定严格内点 $-r_*$ 的 P2 成员身份来自 (35.22)，而 $r_*\ge K_{\rm tail}/\lambda^2$ 最终成立，给原有限 PB 排除；反射给另一取向。∎

这里分别取向的比较是实质区别：当 $\gamma<\infty$ 时，各自 P2 保留非零的一侧极限，加入全部 PB 才使该联合集合趋于零。要求两个取向同时成立时，P2 的交本来就已按 $\lambda^{-2}$ 缩小，不能把这种收缩再计作 PB 的额外排除。$h\downarrow0$ 时不存在由本推导支持的、独立于 $h$ 的正常数 $c_{\rm in}$；短 P2 端点本身正比于 $\beta$。在 $h=0$，归一化 Schur 块为标量，前卷 (30.27)–(30.28) 直接迫使 $\rho=0$。

由 (35.7) 与 $1\le s(\theta)\le2$，所有相位路径的实际正定来源均趋于同一个 $t_h^0$。若再固定 $h$ 位于定理 32.2 的范围内，则奇异极限来源本身的两个联合允许集都是 $[-2\beta/3,2\beta/3]$。因此正定路径上联合集趋于零，并不等于极限来源的联合集。没有在原全称量词、变分下确界与奇异来源极限之间交换极限；反例见证始终在有限阶段取得，其环境向量范数可以发散。

### 35.8 可复用的必要接触检验

**命题 35.9（最小范数缺陷给出的有限必要条件）。** 对固定的 $h,a$，若已有一组与 $\lambda$ 无关的合法有限 $\nu=0$ 演员接触数据，使 $\|u\|=1$、$\mathsf P=\mathsf Q|_{\rho=0}=0$、$d_0=\eta a$、$\eta\ne0$，记 $\alpha_a=\|a\|^2$、$s_\alpha=\sum_\tau\alpha_\tau^{-1}$、$N=\|T_Au\|^2$、$\zeta=\operatorname{Re}((a_{\rm act}-\iota Xu)^*T_Au)$。则 (35.5) 的全部 PB 成立的必要条件，是对每组这样的接触都有

$$
s_\alpha\left(N\rho^2+\frac{|\eta|^2\alpha_a}{1+\lambda^2\alpha_a}\right)
+4\epsilon\rho\zeta\ge0.
\tag{35.40}
$$

若某一组使左端严格负，它给同一来源的有限原 PB 违反，且两笔原预算严格正。若沿 $\rho_\lambda=k/\lambda^2$ 全部 PB 最终成立，其中接触数据和 $k$ 固定，则必有

$$
s_\alpha|\eta|^2+4\epsilon k\zeta\ge0.
\tag{35.41}
$$

证明。复用 (31.12) 的实际最小范数缺陷，令

$$
e_{\min}=GM_2^{-1}d_0
=\frac\eta{1+\lambda^2\alpha_a}
\begin{bmatrix}a\\\lambda\alpha_a\end{bmatrix},\qquad
\|e_{\min}\|^2=\frac{|\eta|^2\alpha_a}{1+\lambda^2\alpha_a}.
\tag{35.42}
$$

取 $y=D^{-1}(e_{\min}-\ell FCu/2-Fu)$，仍由 $G^*e_{\min}=d_0$ 给 $Bu+Vy=a_{\rm act}$。两份演员缺陷是 $\tau\rho T_Au$，两环境缺陷都是 $e_{\min}$，故原有限代价正是 (35.40) 左端。它若负，即按 (27.12) 严格违反 PB。$e_{\min}$ 的末坐标为非零数 $\eta\lambda\alpha_a/(1+\lambda^2\alpha_a)$，而 $FCu=(C^2u,0)^{\mathsf T}$；故两条环境列复线性无关，两笔原实 Gram 预算严格正。将 (35.40) 乘以 $\lambda^2$ 取极限即得 (35.41)；若极限严格负，充分大的有限阶段已经失败。∎

本必要检验不保证某个指定方向一定存在接触，也不把全部已测接触代价非负提升成全部 PB 的充分条件。尤其不能由此宣称两个同谱来源在共同 P2 内有相反 PB 结果。

## 36. 同谱正定来源的精确双取向联合区间与相位不可识别性

本节继续用 (35.5) 的固定 $M_0=C^2$ 实现。只有 $D$ 随相位与谱匹配参数变化；演员块 $B=3C+hJ_A$、耦合 $F=(C,0)^{\mathsf T}$ 与 Schur 块 $H$ 始终相同。以下有限阶段结论仅需定理 35.4 和精确 P2，不依赖接触引理的相位邻域大小。

### 36.1 同一全二阶谱下的非共轭相位对

**定理 36.1（精确而严格嵌套的双取向联合区间）。** 固定一次

$$
0<h<\min(h_0,2\sqrt2,c_{\rm PB}/\sqrt2),\qquad\beta=h/\sqrt2,
\tag{36.1}
$$

其中 $h_0,c_{\rm PB}$ 取自定理 35.4，故 $2\beta<c_{\rm PB}$。对任意实 $L\ge16$ 及任意 $\theta\in(0,\pi/6]$，令

$$
\theta_0=0,\quad\theta_1=\theta,\qquad
s_j=(3+\sin\theta_j)/2,\quad
\lambda_j^2=(L-1)/s_j,\quad
t_j=t_{h,\lambda_j,a_{\theta_j}},\quad j=0,1.
\tag{36.2}
$$

该族包含 $\theta=L^{-1/4}$：当 $L\ge16$ 时，$0<L^{-1/4}\le1/2<\pi/6$。这两份实际输入都严格正定、$D_j\succ0$，在同一个完整 $M_5(\mathbb C)$ 上满足相同的

$$
B,\ F,\ H,\ M_0=C^2,\ M_1=C,\ W=0,\qquad
\operatorname{spec}(M_{2,j})=\{1,L\}.
\tag{36.3}
$$

记

$$
b_j=\frac\beta{\displaystyle 3/2+
\frac{(L-1)(1+\cos\theta_j)}{3+\sin\theta_j}}.
\tag{36.4}
$$

则有精确不等式和精确集合等式

$$
\begin{gathered}
b_0=\frac{6\beta}{4L+5}<b_1<\frac{2\beta}{L}<\frac{c_{\rm PB}}L,\\
\boxed{\quad\mathcal J_{\rm both}(t_j)=[-b_j,b_j],\quad j=0,1,\qquad
\mathcal J_{\rm both}(t_0)\subsetneq\mathcal J_{\rm both}(t_1).\quad}
\end{gathered}
\tag{36.5}
$$

两个分别取向的相应短侧也完全确定：

$$
\mathcal J_+(t_j)\cap[0,\infty)=[0,b_j],\qquad
\mathcal J_-(t_j)\cap(-\infty,0]=[-b_j,0].
\tag{36.6}
$$

所有闭端点都属于原全正泛函、全部原探针的联合允许集。

证明。由 $M_{2,j}=I_2+\lambda_j^2a_{\theta_j}a_{\theta_j}^*$，其两个特征值准确为 $1,1+\lambda_j^2s_j= L$，不涉及渐近匹配。其余共享量来自命题 35.2。$3/2\le s_j\le7/4$ 给 $\lambda_j^2\ge60/7>4$；$0\le\theta_j\le\pi/6$ 给 $\cos\theta_j>0$。定理 35.5 因而给两取向 P2 的交正是 $[-b_j,b_j]$。

在 $[0,\pi/6]$ 上，

$$
\frac{d}{d\theta}\frac{1+\cos\theta}{3+\sin\theta}
=-\frac{1+\cos\theta+3\sin\theta}{(3+\sin\theta)^2}<0.
\tag{36.7}
$$

所以 $b_1>b_0$。取 $\theta=0$ 直接得到 $b_0$ 的值。对整个相位范围，$\sin\theta_j\le1/2$、$\cos\theta_j\ge\sqrt3/2$，故 (36.4) 的短侧分母满足

$$
d_{{\rm s},j}\ge\frac32+\frac{2+\sqrt3}{7}(L-1)>\frac L2,
\tag{36.8}
$$

其中 $(2+\sqrt3)/7>1/2$，且 $L-1>0$。从而 $b_j<2\beta/L<c_{\rm PB}/L$。由定理 35.4，整个 $[-b_j,b_j]$ 在两份输入各自的两个取向都满足全部原 PB；P2 的必要性排除其外的双取向联合成员，故得 (36.5)。相同理由在 $+$ 的非负半轴及 $-$ 的非正半轴给 (36.6)。这里无需知道分别取向宽侧的 PB 边界。∎

**推论 36.2（同一个带符号参数的成员与排除）。** 对定理 36.1 的每个 $L\ge16$，取

$$
\rho_L=(b_0+b_1)/2>0.
\tag{36.9}
$$

则同一个 $\rho_L$ 在两份实际输入、两个取向都通过全部原 PB，但在取向 $+$，$t_0$ 不满足原 P2，$t_1$ 满足原 P2；$t_1$ 还同时属于另一个取向的联合允许集。因此相同 $H,M_0,M_1,W$ 及整个 $M_2$ 谱，不能识别双取向联合允许集，也不能识别分别取向的上述短侧联合端点。

证明。$b_0<\rho_L<b_1<c_{\rm PB}/L$ 给两输入、两取向的全部 PB。对 $+$，精确正端点分别是 $b_0,b_1$，而 $\rho_L\in[-b_1,b_1]$ 给 $t_1$ 的双取向成员身份。∎

这一对的全部差异由实际关系而非标量谱决定：归一化 Schur 的有序谱基固定，而 $K$ 的虚非对角读数随方向改变。两份 $M_2$ 不是同一个矩阵；若固定 $H$ 并把 $M_2$ 本身也固定，前卷 (30.29) 就固定了 P2，不能再使用本证明的 P2 分离。

两个分别取向的整个 P2 区间并无这里的严格嵌套。具体地，对 $+$，$\theta_0$ 的负端点为 $-2\beta/3$，$\theta_1$ 的负端点因 $1-\cos\theta_1>0$ 严格向零移动，而正端点由 $b_0$ 严格增至 $b_1$；两区间因而互不包含。(36.5) 的严格嵌套只针对双取向联合集；(36.6) 则只确定各自指定的半轴。

作为本相位支上的相对校准，若在 $L$ 之外再给出关系读数

$$
\tau=\operatorname{tr}\bigl(C^{-1}(M_2-I_2)\bigr)=\lambda^2,
\qquad
\sin\theta=\frac{2(L-1)}\tau-3,
\tag{36.9a}
$$

则 $\theta\in[0,\pi/6]$ 唯一确定，继而由 (36.4) 恢复精确的 $b(\theta)$。第一式用 $a_\theta^*C^{-1}a_\theta=\|w_\theta\|^2=1$，第二式用 $L-1=\lambda^2s(\theta)$。这是相对于固定 $C$ 和所声明相位支的数学恢复；不声称该读数已有物理取得方式，也不声称它是一般来源的最小充分摘要。

### 36.2 任意相位路径的共同来源与固定相位的重标度极限

**命题 36.3（任意相位路径的共同来源极限与不同的重标度联合极限）。** 在 (36.2) 中允许 $\theta_1=\theta(L)$ 为任意取值于 $(0,\pi/6]$ 的相位函数，不要求相位趋于零。两份实际来源在 $L\to\infty$ 时均在范数中趋于同一个固定 $h$ 的 $t_h^0$，并有精确式

$$
\|t_j-t_h^0\|=s_j/\lambda_j+\lambda_j^{-3}\longrightarrow0,
\qquad j=0,1.
\tag{36.10}
$$

逐有限 $L$，两份精确双取向联合区间仍满足 (36.5) 的严格嵌套；两区间都按 Hausdorff 距离趋于 $\{0\}$。若相位固定为任意 $\theta_*\in(0,\pi/6]$，令

$$
R_{\theta_*}=\frac{\beta(3+\sin\theta_*)}{1+\cos\theta_*}>
R_0=\frac{3\beta}{2}.
$$

则重标度后的联合区间有不同的 Hausdorff 极限：这里 $L A=\{L\rho:\rho\in A\}$，且

$$
\begin{gathered}
L b_0\longrightarrow R_0,\qquad L b_1\longrightarrow R_{\theta_*},\\
L\mathcal J_{\rm both}(t_0)\longrightarrow[-R_0,R_0],\qquad
L\mathcal J_{\rm both}(t_1)\longrightarrow[-R_{\theta_*},R_{\theta_*}].
\end{gathered}
\tag{36.10a}
$$

特别地，固定 $\theta_1=\pi/6$ 时，每个有限 $L\ge16$ 都有

$$
\begin{gathered}
s_1=7/4,\qquad\lambda_1^2=4(L-1)/7,\\
b_0=\frac\beta{3/2+2(L-1)/3},\qquad
b_1=\frac\beta{3/2+(L-1)(2+\sqrt3)/7},
\end{gathered}
\tag{36.10b}
$$

因而

$$
\begin{gathered}
L b_0\longrightarrow\frac{3\beta}{2},\qquad
L b_1\longrightarrow\frac{7\beta}{2+\sqrt3}>\frac{3\beta}{2},\\
L\mathcal J_{\rm both}(t_0)\longrightarrow
[-3\beta/2,3\beta/2],\\
L\mathcal J_{\rm both}(t_1)\longrightarrow
\left[-\frac{7\beta}{2+\sqrt3},\frac{7\beta}{2+\sqrt3}\right].
\end{gathered}
\tag{36.10c}
$$

这些不同的重标度极限与相同实际来源极限相容；每个有限 $L$ 上两输入仍共享 $H,M_0,M_1,W$ 及 $\operatorname{spec}(M_2)=\{1,L\}$。固定正相位的两个分别取向 P2 区间均趋于 $\{0\}$，零相位则保留非零的单侧极限：

$$
\begin{gathered}
I_+(t_0)\longrightarrow[-2\beta/3,0],\qquad
I_-(t_0)\longrightarrow[0,2\beta/3],\\
I_+(t_1)\longrightarrow\{0\},\qquad
I_-(t_1)\longrightarrow\{0\}\quad(\theta_1=\theta_*>0).
\end{gathered}
\tag{36.10d}
$$

证明。由 $3/2\le s_j\le7/4$ 及 $\lambda_j^2=(L-1)/s_j$，无论相位函数是否收敛，两份 $\lambda_j$ 都趋于无穷，且 (35.7) 的右侧一致趋于零。这就在同一固定的实际载体与固定演员、耦合块上给出 (36.10)，不需要让探针向量或变分参数有界。由 (36.5)，双取向联合区间半径都小于 $2\beta/L$，故未重标度的极限均为 $\{0\}$。

若 $\theta_1=\theta_*$ 固定，将 (36.4) 的分子分母同除以 $L$，得到 (36.10a) 的端点极限；(36.7) 说明 $R_{\theta_*}>R_0$。闭区间的端点收敛即给所列 Hausdorff 极限。在 $\theta_* =\pi/6$ 代入 $\sin\theta_*=1/2$、$\cos\theta_*=\sqrt3/2$，即得 (36.10b)–(36.10c)。此结论没有把极限来源的允许集代入有限来源的全称条件。

对分别取向的 P2，直接用 (35.20)。零相位有 $d_{\rm w}=3/2$、$d_{\rm s}=3/2+\lambda_0^2$；每个固定正相位有 $1-\cos\theta_*>0$，所以 $d_{\rm w},d_{\rm s}$ 都趋于无穷。这给出 (36.10d)，无需把只适用于趋零相位的 (35.22) 用在固定正相位上。

保留的趋零相位例（$\theta_1=L^{-1/4}$ 的临界相位对照）。该例的共同来源收敛已由上面的任意相位论证覆盖。其临界参数满足

$$
\lambda_0^2(1-\cos\theta_0)=0,\qquad
\lambda_1^2(1-\cos\theta_1)
\sim\frac{L}{3/2}\frac{L^{-1/2}}2
=\frac{\sqrt L}{3}\longrightarrow\infty.
$$

此时可以应用 (35.22)：零相位的两个 P2 极限仍是 (36.10d) 的非零单侧区间，趋零正相位的两个 P2 极限则都是 $\{0\}$。精确双取向联合区间逐有限 $L$ 仍严格不同；但 $L b_0,L b_1$ 都趋于 $3\beta/2$，所以该趋零例的两个重标度联合极限相同。固定正相位族正好给出 (36.10a) 中仍然不同的极限。任意振荡相位函数的共同来源收敛不额外保证其分别取向 P2 区间存在极限。∎

### 36.3 更强谱匹配的共轭对及其限制

**命题 36.4（全来源同谱仍可分离一个取向，但不分离双取向交）。** 仍取 (36.1) 的 $h$。对每个 $L\ge16$，改取

$$
w^\pm=(1,\pm i)^{\mathsf T}/\sqrt2,\qquad
a^\pm=C^{1/2}U_0w^\pm,\qquad
\lambda^2=2(L-1)/3,\qquad t^\pm=t_{h,\lambda,a^\pm}.
\tag{36.11}
$$

则 $t^-=\overline{t^+}$、$D^-=\overline{D^+}$；不仅共享 (36.3) 的数据，整个实际 $t$ 的谱与环境 $D$ 的谱也分别完全相同。$M_0$ 本身固定；两份 $M_2$ 的对角元与逐项实部也相同。对取向 $+$，

$$
I_+(t^+)=[-2\beta/3,b_0],\qquad
I_+(t^-)=[-b_0,2\beta/3],\qquad b_0=6\beta/(4L+5).
\tag{36.12}
$$

同一个 $\rho=2\beta/L$ 在两输入、两取向都通过全部原 PB，属于 $\mathcal J_+(t^-)$ 却不属于 $I_+(t^+)$。然而

$$
\mathcal J_{\rm both}(t^+)=\mathcal J_{\rm both}(t^-)=[-b_0,b_0].
\tag{36.13}
$$

证明。$C,U_0,B,F$ 均为实矩阵，$a^-=\overline{a^+}$，由 (35.5) 直接得到来源与环境的共轭关系；Hermitian 矩阵的共轭具有相同实特征值。此时 $\|a^\pm\|^2=3/2$，故 $M_2$ 谱均为 $\{1,L\}$。其实际演员坐标矩阵为

$$
M_2^\pm=\begin{pmatrix}
1+\lambda^2/2&\ \pm i\lambda^2/\sqrt2\\
\mp i\lambda^2/\sqrt2&1+\lambda^2
\end{pmatrix}.
\tag{36.14}
$$

对应谱坐标的 $q$ 分别是 $-\lambda^2/2,+\lambda^2/2$，给 (36.12)。$b_0<2\beta/L<2\beta/3$，且 $2\beta/L<c_{\rm PB}/L$，分别给取向 $+$ 的成员与排除以及全部 PB。两取向的 P2 交均为 $[-b_0,b_0]$，又完全落入定理 35.4 的 PB 半径，故 (36.13) 精确成立。∎

共轭对中，来源共轭交换取向；这与引理 35.3 在同一来源上反射 $\rho$ 的操作不同。不能从 (36.12) 的一个取向分离推出双取向交的分离；非共轭相位对 (36.2) 才给 (36.5) 的严格嵌套。

### 36.4 数学归属、原量词与未决边界

原 P2 端点读取直接复用前卷 (30.29)。实际原列、有限变分和同一实际环境的缺陷补偿，分别沿 (27.4)–(27.13)、(31.4)–(31.14)；完整正泛函提升沿 (17.14)–(17.16)。定理 35.4 只消费 §32 在整个原索引集上的两条一致估计，不使用 §33.1 的近邻推广。引理 35.6 消费本卷 §34 的演员接触多项式与 Hermitian 重构，并在复目标比值上给出完整的两参数雅可比检验；§34 是该接触延续的纸面数学依赖。在 (35.5) 的实际实现下，§36 的精确同谱联合区间仅用定理 35.4 和定理 35.5 的精确 P2，不依赖接触延续，也不把其局部相位邻域扩大到全部相位。

Schur 补、秩一矩阵范数、加权方差、Cauchy–Schwarz、有限维实隐函数定理、Gram 行列式和正密度谱分解均是复用的成熟数学。Schur 补的来源范围沿前卷 §31 所引 Higham；最小范数缺陷沿同处所引 Penrose 及 (31.12) 的显式证明；实隐函数方法沿 §34 的既定使用。对称性引理 35.3 和单纯端点换算只作证明支撑，不计作独立新理论。本文的 `repo-derived` 增量是固定 $M_0$ 的实际来源构造及其原全称后果：独立于 §33 的精确 $M_1=C$ PB 运输、复临界相位的同源有限正预算排除，以及共享全 $M_2$ 谱时双取向联合集的精确差异。这里没有文献穷尽或历史优先权主张。

所有 PB 包含都遍历原全部实际 Hermitian 探针及完整代数的所有正复线性泛函，没有删去环境密度块。每个声称的 PB 违反均由同一有限实际探针与同一正泛函承担，且同时验证两笔原预算严格正；其质量可取任意指定有限 $\mu>0$。没有用各自可达但不能共同实现的极值替代同源推导，也没有用 $M_2$ 的标量谱代替相对于固定 $H,C$ 的矩阵方向。

尚未建立的是：在一个共同 P2 允许参数上，两份匹配谱的实际来源具有相反的全部 PB 结果。定理 36.1 与命题 36.4 的公共分离参数在两输入都通过全部 PB，排除完全来自其中一份输入的 P2；对共享 P2 区间内的 PB 单独分离不构成证据。一般相位下分别取向联合集的宽侧精确端点、整个集合是否为区间、最优 PB 常数以及任意预先给定较大 $h$ 的对应分类，也都不由本文得到。接触检验的非负只提供必要检验，不能反推全称充分性。本文既无 Lean／kernel 认证，也不作物理实现或外部原创性认证。

## 追加锚（本行以下为增补区）

## 37. 单位演员归一的全部原探针接触闭包极限定理

本节固定式 (35.5) 的来源，使用 §32 的基准强制估计，将 §35.8 的有限接触必要检验扩展为可见列闭包上的序列下极限与恢复定理。数值变分域只对演员分量作单位归一；原 PB 的全部探针、完整正泛函及任意正有限质量均保留。来源方向 $a$、演员作用 $a_{\rm act}$、残量尺度系数 $k$ 与原加权方差系数分别记号。旧式号 (17.x)、(27.x)、(30.x)、(31.x) 取前卷在本卷所引钉版 `315e167044afd2593b851f6546a82470ca16d446` 的含义。

### 37.1 精确来源与完整原条件

固定 $a\in\mathbb C^2\setminus\{0\}$，记 $m=\|a\|^2>0$。固定实数 $h$，使 $H=2C+hJ_A\succ0$ 且 $h$ 位于 §32、(35.16) 的强制估计邻域内。这里

$$
C=\operatorname{diag}(1,2),\qquad
T_A=\operatorname{diag}(1,-2),\qquad
J_A=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad B=H+C.
\tag{37.1}
$$

对每个有限 $\lambda>0$，在同一演员、环境分解 $\mathbb C^2\oplus(\mathbb C^2\oplus\mathbb C)$ 中，来源准确为

$$
\begin{gathered}
\delta_\lambda=\lambda^{-3},\qquad
F=\begin{bmatrix}C\\0\end{bmatrix},\quad V=F^*,\quad
G_\lambda=\begin{bmatrix}I_2\\\lambda a^*\end{bmatrix},\\
D_\lambda^{\rm env}=
\begin{pmatrix}
C+\delta_\lambda\lambda^2aa^*&-\delta_\lambda\lambda a\\
-\delta_\lambda\lambda a^*&\delta_\lambda
\end{pmatrix},\qquad
t_\lambda^{\rm src}=\begin{pmatrix}B&V\\F&D_\lambda^{\rm env}\end{pmatrix}.
\end{gathered}
\tag{37.2}
$$

这正是命题 35.2 的式 (35.5)。对 $v\in\mathbb C^2,z\in\mathbb C$，环境二次型是

$$
v^*Cv+\delta_\lambda|z-\lambda a^*v|^2,
$$

故 $D_\lambda^{\rm env}\succ0$。块乘法及 Schur 补逐一给出

$$
\begin{gathered}
D_\lambda^{\rm env}G_\lambda=F,\qquad
G_\lambda=(D_\lambda^{\rm env})^{-1}F,\qquad
F^*F=C^2,\qquad G_\lambda^*F=C,\\
G_\lambda^*G_\lambda=I_2+\lambda^2aa^*,\qquad
B-F^*(D_\lambda^{\rm env})^{-1}F=H,\qquad t_\lambda^{\rm src}\succ0,\\
F_{3\cdot}=0,\qquad (G_\lambda)_{3\cdot}=\lambda a^*.
\end{gathered}
\tag{37.3}
$$

特别地 $M_0=C^2,M_1=C,M_2=I_2+\lambda^2aa^*$ 精确成立，环境零模像 $W=0$。这些等式只归属于 (37.2)，不使用 §34 的另一条环境实现。

固定一个取向 $\iota=\sigma i$，$\sigma\in\{1,-1\}$；整节对每个取向分别成立。以 $A\circ B=(AB+BA)/2$、$K_\sigma(A,B)=\iota[A,B]/2$ 定义原运算。在完整 $M_5(\mathbb C)$ 中取

$$
\begin{gathered}
c=C\oplus0_3,\quad s_\rho=\rho T_A\oplus0_3,\quad
x=X\oplus0_3,\quad X=X^*,\quad
g=K_\sigma(c,t_\lambda^{\rm src})+s_\rho,\\
h_x=K_\sigma(c,x),\quad k_c=c\circ t_\lambda^{\rm src},\quad r_x=c\circ x,\\
R_\tau=x+\tau(h_x-k_c),\qquad
S_\tau=t_\lambda^{\rm src}+\tau(r_x+g),\quad \tau=\pm1,\\
L_{\rm PB}=-2x\circ(h_x-k_c)-2t_\lambda^{\rm src}\circ(r_x+g),\\
B_\phi(R,S)=\phi(R^2)\phi(S^2)-\phi(R\circ S)^2.
\end{gathered}
\tag{37.4}
$$

原 PB 指：对每个 $X=X^*$ 及完整代数上每个正复线性泛函 $\phi$，

$$
|\phi(L_{\rm PB})|\le
\sqrt{B_\phi(R_+,S_+)}+\sqrt{B_\phi(R_-,S_-)}.
\tag{37.5}
$$

原 P2 指 $\phi(g)^2\le\phi(c^2)\phi((t_\lambda^{\rm src})^2)-\phi(c\circ t_\lambda^{\rm src})^2$，量化相同的完整正泛函。本节的接触定理首先判原 PB；涉及 P2 时另列其实际区间。

### 37.2 单位演员变分域与环境的精确消元

**定义 37.1（归一原域及有限代价）。** 归一原测试遍取

$$
\begin{gathered}
\xi=(u,y),\qquad \|u\|=1,\quad y\in\mathbb C^3,\quad X=X^*\in M_2(\mathbb C),\\
\epsilon\in\{1,-1\},\qquad
\alpha_+,\alpha_->0,\quad \beta_+,\beta_-\in\mathbb R.
\end{gathered}
\tag{37.6}
$$

除 $\|u\|=1$ 外，没有范数、参数比值或预算非退化限制。所有参数在每个有限阶段均有限，但可随 $\lambda$ 逃逸。固定实数 $k$，以后始终令 $\rho=k/\lambda^2$。对 $\phi_\xi(A)=\xi^*A\xi$，定义带符号原有限代价

$$
\mathcal D_\lambda^{\rm orig}=
\sum_{\tau=\pm1}\left(
\alpha_\tau\|R_\tau\xi\|^2+
\alpha_\tau^{-1}\|(S_\tau-\beta_\tau R_\tau)\xi\|^2\right)
-2\epsilon\phi_\xi(L_{\rm PB}).
\tag{37.7}
$$

前卷 (27.12) 的原二列变分恒等式说明：对同一 $X,\xi$，(37.7) 在所有有限参数与两个 $\epsilon$ 上非负，当且仅当该向量满足 PB。恒等式包括 Gram 退化及下确界不取到的情形；某个有限 (37.7) 严格负已经足以给出 PB 严格失败。

为列出精确消元，写

$$
\begin{gathered}
z_\tau=\beta_\tau-\tau\epsilon\iota\alpha_\tau
       =\iota+\nu+\tau\ell,\qquad
A=(\alpha_++\alpha_-)/2=-\epsilon\operatorname{Im}_\iota\ell,\\
A>|1+\operatorname{Im}_\iota\nu|,\qquad
\alpha_\tau=A-\tau\epsilon(1+\operatorname{Im}_\iota\nu),\qquad
\beta_\tau=\operatorname{Re}(\nu+\tau\ell),\\
r=|\ell|>0,\quad n=|\nu|,\quad r+n\ge1,\quad
b=(r+n)^2/r\ge1,\\
w_\tau=\alpha_\tau^{-1},\quad s_\alpha=w_++w_-,\quad
\omega=(w_+-w_-)/s_\alpha\in(-1,1).
\end{gathered}
\tag{37.8}
$$

这里 $\operatorname{Im}_\iota$ 是基 $1,\iota$ 下的虚系数。反过来，上述严格合法性条件与实部公式恰好恢复全部原 $\alpha_\tau,\beta_\tau$，并未缩小变分域。置

$$
\begin{gathered}
p=Xu,\quad q=XCu,\quad a_{\rm act}=Bu+Vy,\quad v=a_{\rm act}-\iota p,\quad
U=\iota q+BCu+Cv,\\
\mathsf P=v-\nu p+\ell U/2,\qquad
\mathsf Q=\iota Cv-\ell p+\rho T_Au+\nu U/2,\qquad
\zeta=\operatorname{Re}(v^*T_Au),\\
t_{\rm req}=a_{\rm act}-Hu+(\ell+\omega\nu)C^2u/2,\qquad
\mathcal A=\sum_{\tau=\pm1}w_\tau\|\mathsf P+\tau\mathsf Q\|^2,\qquad
v_{\rm var}=\frac{|\nu|^2}{2A}.
\end{gathered}
\tag{37.9}
$$

$v_{\rm var}$ 是 (31.10) 的非负方差系数，不是残量系数 $k$。原环境列令 $d=Fu+D_\lambda^{\rm env}y$，$e=d+(\ell+\omega\nu)FCu/2$。由 (37.3) 有 $G_\lambda^*e=t_{\rm req}$。原 (32.5)、(35.13) 的列展开与加权方差恒等式给

$$
\begin{aligned}
((S_\tau-z_\tau R_\tau)\xi)_{\rm act}&=\mathsf P+\tau\mathsf Q,\\
((S_\tau-z_\tau R_\tau)\xi)_{\rm env}
 &=e+(\tau-\omega)\nu FCu/2,\\
\mathcal D_\lambda^{\rm orig}
 &=\mathcal A+s_\alpha\|e\|^2+v_{\rm var}\|C^2u\|^2
   +4\epsilon k\lambda^{-2}\zeta.
\end{aligned}
\tag{37.10}
$$

令 $R_\lambda=(I_2+\lambda^2aa^*)^{-1}$。约束 $G_\lambda^*e=t_{\rm req}$ 的全部解及范数分解是

$$
e=G_\lambda R_\lambda t_{\rm req}+e_0,\qquad
G_\lambda^*e_0=0,\qquad
\|e\|^2=t_{\rm req}^*R_\lambda t_{\rm req}+\|e_0\|^2.
\tag{37.11}
$$

这是正定二次型的正交最小范数公式，直接复用 (31.12)。据此定义

$$
\begin{aligned}
S_\lambda&=\mathcal A+s_\alpha t_{\rm req}^*R_\lambda t_{\rm req}
                    +v_{\rm var}\|C^2u\|^2,\\
\mathcal D_\lambda^{\rm red}&=S_\lambda+4\epsilon k\lambda^{-2}\zeta,\\
\mathcal D_\lambda^{\rm orig}
 &=\mathcal D_\lambda^{\rm red}+s_\alpha\|e_0\|^2.
\end{aligned}
\tag{37.12}
$$

约化域是 (37.6) 去掉 $y$，改让 $a_{\rm act}\in\mathbb C^2$ 任意。这个改变精确保留原域：给定任意约化测试，取 $e=G_\lambda R_\lambda t_{\rm req}$ 及

$$
y=(D_\lambda^{\rm env})^{-1}
\left(e-(\ell+\omega\nu)FCu/2-Fu\right).
\tag{37.13}
$$

于是 $Bu+Vy=Hu+G_\lambda^*e-(\ell+\omega\nu)C^2u/2=a_{\rm act}$。因此同一来源上的两个归一数值下确界精确相同：

$$
f_\lambda(k)=\inf_{\text{归一原测试}}\lambda^2\mathcal D_\lambda^{\rm orig}
            =\inf_{\text{归一约化测试}}\lambda^2\mathcal D_\lambda^{\rm red}.
\tag{37.14}
$$

此时暂允许下确界为 $-\infty$；§37.7 将先证明尾部一致下有界。

### 37.3 可见 Hermitian 图的闭包与零需求排除

**引理 37.2（包括演员轴的可见图闭包）。** 在 $\|u\|=1$ 的有限维空间中，实际图 $(u,Xu,XCu)$、$X=X^*$ 的闭包 $\overline{\mathcal G}$，恰由

$$
u^*p\in\mathbb R,\qquad (Cu)^*q\in\mathbb R,\qquad u^*q=p^*Cu
\tag{37.15}
$$

定义。若 $u_1u_2\ne0$，唯一实际矩阵为 $X=[p\ q][u\ Cu]^{-1}$。若 $u=z e_j$，$|z|=1$，$l\ne j$，则条件恰为 $p_j/z\in\mathbb R$、$q_j=c_jp_j$；$p_l,q_l$ 无额外限制，其中 $c_1=1,c_2=2$。

证明。三条件就是 $[u\ Cu]^*[p\ q]$ 为 Hermitian，故对实际图成立并在极限保留；非轴时反乘可逆矩阵证明充分性。在轴上逐项代入即得所列条件。为证明每个轴点都在闭包，设

$$
d=c_l-c_j,\qquad
s_{\rm ax}=(c_lp_l-q_l)/d,\qquad
t_{\rm ax}=(q_l-c_jp_l)/d.
\tag{37.17}
$$

若 $t_{\rm ax}=0$，令 $X_{lj}=p_l/z$、$X_{jl}=\overline{X_{lj}}$、$X_{jj}=p_j/z$，另一对角元任取实数，即实际实现原列。若 $t_{\rm ax}\ne0$，对 $0<\tau<1$ 取

$$
\begin{gathered}
u_{l,\tau}=\tau t_{\rm ax}/|t_{\rm ax}|,\qquad
u_{j,\tau}=z\sqrt{1-\tau^2},\\
X_{lj,\tau}=s_{\rm ax}/u_{j,\tau},\quad
X_{jl,\tau}=\overline{X_{lj,\tau}},\quad
X_{ll,\tau}=|t_{\rm ax}|/\tau,\quad X_{jj,\tau}=p_j/z.
\end{gathered}
\tag{37.18}
$$

所得 $X_\tau$ Hermitian、$\|u_\tau\|=1$，且

$$
(X_\tau u_\tau)_l=s_{\rm ax}+t_{\rm ax}=p_l,\qquad
(X_\tau Cu_\tau)_l=c_js_{\rm ax}+c_lt_{\rm ax}=q_l.
$$

另两个可见列坐标及 $u_\tau-u$ 都是 $O(\tau)$。这证明闭包描述；没有删除发散的 $X_{ll,\tau}$。∎

**定义 37.3（增广接触与极限代价）。** 对固定 $a,h,\iota$，$\mathcal C_\iota(a)$ 遍取 $\epsilon=\pm1$、$(u,p,q)\in\overline{\mathcal G}$、$\ell\in\mathbb C$、$a_{\rm act}\in\mathbb C^2$、$\eta\in\mathbb C$，满足

$$
\begin{gathered}
A=-\epsilon\operatorname{Im}_\iota\ell>1,\qquad
s(A)=\frac{2A}{A^2-1},\\
a_{\rm act}=\iota(I_2-\ell C^{-1})p,\qquad
q=(\ell I_2+2C^{-1})p+\iota BCu,\\
a_{\rm act}-Hu+\ell C^2u/2=\eta a.
\end{gathered}
\tag{37.19}
$$

保留两个 $\epsilon$。定义

$$
\zeta(c)=\operatorname{Re}((a_{\rm act}-\iota p)^*T_Au),\qquad
J_k(c)=s(A)|\eta|^2+4\epsilon k\zeta(c),\qquad
j(k)=\inf_{c\in\mathcal C_\iota(a)}J_k(c),
\tag{37.20}
$$

空集下确界约定为 $+\infty$。这些定义尚不宣称接触由一个有限轴上 $X$ 精确实现。

**引理 37.4（闭包上的零需求不可能）。** 将 (37.19) 的 $A>1$ 放宽到 $A\ge1$，仍要求其中两条演员接触等式；则

$$
a_{\rm act}-Hu+\ell C^2u/2\ne0.
\tag{37.21}
$$

特别地，每个 $\mathcal C_\iota(a)$ 中的 $\eta$ 非零。

证明。反设需求为零。用引理 37.2 取实际图 $(u_\delta,p_\delta,q_\delta)$ 逼近给定闭包点，误差 $o(\delta)$；实际点可保持不动。令

$$
\ell_\delta=\ell-\epsilon\iota\delta,\quad
A_\delta=A+\delta>1,\quad \nu_\delta=\rho_\delta=0,\quad
\alpha_{\tau,\delta}=A_\delta-\tau\epsilon,\quad
a_{{\rm act},\delta}=Hu_\delta-\ell_\delta C^2u_\delta/2.
$$

在 §32 基准来源 $F_b=D_b=C,G_b=I_2$ 上，这些是合法实际测试，环境需求恰为零，演员缺陷 $\mathsf P_\delta,\mathsf Q_\delta=O(\delta)$。若 $A=1$，较大权重为 $O(\delta^{-1})$；若 $A>1$，权重有界。因此基准平方和 $S_b=O(\delta)$ 趋零。可是 (35.16) 给 $S_b\ge\gamma b_\delta\ge\gamma>0$，矛盾。此论证同时覆盖演员轴和一个 $\alpha_\tau\to0$ 的边界。∎

### 37.4 每个缩放上子水平集的紧性

**定理 37.5（全部归一原测试的序列紧性与下极限）。** 固定上述 $a,h,\iota$ 及任意实 $k,M$。对每个 $\lambda_j\to\infty$ 和归一原测试序列，若

$$
\lambda_j^2\mathcal D_{\lambda_j}^{\rm orig}\le M,
\tag{37.22}
$$

则约化可见数据 $(\epsilon,u,p,q,a_{\rm act},\ell,\nu,\alpha_\pm,\beta_\pm)$ 有收敛子列。每个这样的收敛子列的极限满足 $\nu=0$，并通过 (37.19) 确定一个 $c\in\mathcal C_\iota(a)$；沿该子列都有

$$
\liminf_j\lambda_j^2\mathcal D_{\lambda_j}^{\rm orig}\ge J_k(c).
\tag{37.23}
$$

同一结论对 $\mathcal D^{\rm red}$ 成立。所有尾部上界、正下界和误差常数可依赖固定 $C,H,a,h,k,M$，不依赖 $\lambda_j$ 或所选测试。没有对无界 $k$ 的一致性结论，也不要求 $X_j$ 或 $y_j$ 有界。

证明先控制残量抵消。由 (37.12)，只需处理约化代价。用同一 $u,X,a_{\rm act}$ 和原有限参数在 §32 基准来源上取环境需求 $t_{\rm req}$，其平方和为

$$
S_b=\mathcal A+s_\alpha\|t_{\rm req}\|^2
               +\frac{n^2}{2A}\|C^2u\|^2.
\tag{37.24}
$$

这确实是一个原基准测试：取 $d_b=t_{\rm req}-(\ell+\omega\nu)C^2u/2$，$y_b=C^{-1}(d_b-Cu)$，即可使 $Bu+Cy_b=a_{\rm act}$。由 (35.16) 和秩一逆矩阵的最小特征值，尾部 $|\rho|\le r_0$ 上有

$$
\begin{gathered}
S_b\ge\gamma b,\qquad
|\zeta|\le K\bigl(b+\sqrt{bS_b}+|\rho|\bigr),\\
S_b\le L_\lambda S_\lambda,\qquad L_\lambda=1+\lambda^2m.
\end{gathered}
\tag{37.25}
$$

将 $M$ 增至 $\max(M,0)$，置 $x_b=S_b/b$。从 $\lambda^2S_\lambda\le M+4|k||\zeta|$ 得到准确的不等式

$$
x_b\le(m+\lambda^{-2})
\left[M+4K|k|\left(1+\sqrt{x_b}+|\rho|/b\right)\right].
\tag{37.26}
$$

因 $b\ge1$ 且尾部 $|\rho|\le1$，这是 $\sqrt{x_b}$ 的二次上界，故 $x_b$ 一致有界。重新代回即得

$$
S_b\le Cb,\qquad S_\lambda\le Cb/\lambda^2.
\tag{37.27}
$$

这里没有把有符号代价的上界误作正平方和的上界，而是先控制了允许的抵消。

方差项与 $\|C^2u\|\ge1$ 给

$$
\frac{n^2}{2A}\le S_\lambda,\qquad
\frac{n}{r+n}\le C/\lambda,\qquad
\frac nr\le C'/\lambda,\qquad \liminf r\ge1.
\tag{37.28}
$$

最后一步使用 $r+n\ge1$。半和、半差的加权 Cauchy–Schwarz，以及 $s_\alpha\ge2/A$，又给

$$
\|\mathsf P\|+\|\mathsf Q\|\le Cr/\lambda,\qquad
\|t_{\rm req}\|\le Cr,\qquad \|a_{\rm act}\|\le Cr.
\tag{37.29}
$$

例如 $\|t_{\rm req}\|^2\le L_\lambda S_\lambda/s_\alpha\le Cr^2$；这里已由 (37.28) 使 $b/r$ 有界。

现在排除 $r\to\infty$。若存在这种子列，置 $\chi=\nu/\ell$、$e_\ell=\ell/r$，$|e_\ell|=1$。原演员列的准确消元是

$$
\mathsf Q-\chi\mathsf P=(\iota C-\chi I_2)a_{\rm act}-Zp+\rho T_Au,
\qquad
Z=\bigl[\ell(1-\chi^2)-\iota\chi\bigr]I_2-C.
\tag{37.30}
$$

由 $\chi=O(\lambda^{-1})$，尾部 $\|Z^{-1}\|\le C/r$；结合 (37.29) 得 $p=O(1)$。再由 $\mathsf P=v-\nu p+\ell U/2$ 得 $U=O(1)$。用 $U$ 的定义和 $\mathsf Q$ 的等式，分别得到

$$
\frac qr-e_\ell p=O(\lambda^{-1}+r^{-1}),\qquad
\frac{a_{\rm act}}r+\iota e_\ell C^{-1}p
                  =O(\lambda^{-1}+r^{-1}).
\tag{37.31}
$$

实际 Hermitian 图的 $u^*q=p^*Cu$ 与 $p=O(1)$ 使
$u^*p=O(\lambda^{-1}+r^{-1})$；它本来是实数。另一个 Hermitian 条件 $(Cu)^*q\in\mathbb R$ 使

$$
\operatorname{Im}_\iota\bigl(e_\ell(Cu)^*p\bigr)
                  =O(\lambda^{-1}+r^{-1}).
\tag{37.32}
$$

准确使用 $C^{-1}T_A=3I_2-2C$，(37.31) 给

$$
\frac\zeta r=
\operatorname{Re}\!\left(\iota\overline{e_\ell}
       [3p^*u-2p^*Cu]\right)+O(\lambda^{-1}+r^{-1})
       =O(\lambda^{-1}+r^{-1}).
\tag{37.33}
$$

最后一个等号同时用了上述两个 Hermitian 配对；仅控制 $u^*p$ 不足以得此消失。另一方面，(37.25) 给

$$
\frac{\lambda^2S_\lambda}{r}
\ge\frac{\gamma b}{r(m+\lambda^{-2})}
\ge\frac\gamma{m+\lambda^{-2}}.
\tag{37.34}
$$

(37.33)–(37.34) 与
$\lambda^2\mathcal D_\lambda^{\rm red}/r\le M/r\to0$ 矛盾，因其左侧下极限至少为 $\gamma/m>0$。所以 $r$ 有界；此排除没有除以可能为零的 $\zeta$。

现在 $n=O(\lambda^{-1})$，$a_{\rm act}$ 有界，$\mathsf P,\mathsf Q\to0$。合法性给 $\liminf A\ge1$，故 (37.30) 中 $Z$ 尾部具有一致有界逆：其极限是虚系数绝对值至少 $1$ 的 $\ell I_2-C$。因而 $p$ 有界；由 $\mathsf P$ 得 $U$ 有界，再由其定义得 $q$ 有界。所有可见数据于是可取收敛子列，图极限属于 $\overline{\mathcal G}$，原 $\beta_\tau=\operatorname{Re}(\nu+\tau\ell)$ 也有界。

还须排除 $A\to1$，不能预设两权重的正下界。由 (37.27) 及 $r$ 有界，

$$
s_\alpha\|t_{\rm req}\|^2
\le(m+\lambda^{-2})\lambda^2S_\lambda\le C.
\tag{37.35}
$$

若 $A\to1$，则 $\nu\to0$ 使一个 $\alpha_\tau\to0$，故 $s_\alpha\to\infty$，进而 $t_{\rm req}\to0$。在 $\mathsf P=\mathsf Q=0,\nu=\rho=0$ 的极限中，先由 $\mathsf Q=0$ 得 $v=-\iota\ell C^{-1}p$，再由 $\mathsf P=0$ 得 $U=2\iota C^{-1}p$。这些正是 (37.19) 的两条演员接触等式，给出了被引理 37.4 排除的 $A=1$ 零需求。故尾部 $A\ge1+\delta$，$\delta>0$；两 $\alpha_\tau$ 均离零且有上界。

最后令 $\Pi_a=aa^*/m$、$\Pi_a^\perp=I_2-\Pi_a$。有

$$
R_\lambda=\Pi_a^\perp+(1+\lambda^2m)^{-1}\Pi_a.
\tag{37.36}
$$

$\lambda^2S_\lambda\le C$ 使 $\Pi_a^\perp t_{\rm req}=O(\lambda^{-1})$。因此每个可见收敛子列都满足 $t_{\rm req}\to\eta a$，并由引理 37.4 得 $\eta\ne0$。此子列的极限就是 (37.19) 的一个增广接触。设 $\eta_\lambda=a^*t_{\rm req}/m\to\eta$，则

$$
\liminf \lambda^2s_\alpha t_{\rm req}^*R_\lambda t_{\rm req}
\ge\lim s_\alpha\frac{\lambda^2m}{1+\lambda^2m}|\eta_\lambda|^2
=s(A)|\eta|^2.
\tag{37.37}
$$

其余缺陷平方与方差非负，$\zeta$ 连续收敛；原环境剩余项也非负。这证明每个收敛子列上的 (37.23)。当需要整列的下极限时，先取实现该下极限的子列，再用已经证明的紧性取子列；并不声称任意极限接触都实现整列下极限。∎

### 37.5 同一实际来源上的逐接触恢复

**定理 37.6（包括非实际轴接触的恢复）。** 对每个 $c\in\mathcal C_\iota(a)$、每个固定实数 $k$，存在对所有充分大有限 $\lambda$ 定义的归一原测试，使可见数据趋于 $c$，且

$$
\lambda^2\mathcal D_\lambda^{\rm orig}\longrightarrow J_k(c).
\tag{37.38}
$$

恢复使用 (37.2) 的同一实际 $D_\lambda^{\rm env},F,G_\lambda$；不改变源的三个矩。

证明。若接触有实际 $X$，保持 $u,X$。否则它是引理 37.2 的轴点，用 (37.18) 并取 $\tau_\lambda=\lambda^{-3}$，得到实际 $u_\lambda,X_\lambda$，且

$$
\|u_\lambda-u\|+\|X_\lambda u_\lambda-p\|
 +\|X_\lambda Cu_\lambda-q\|=O(\lambda^{-3}).
\tag{37.39}
$$

保持接触的 $a_{\rm act},\ell,\epsilon$，令

$$
\nu_\lambda=0,\qquad
\alpha_{\tau,\lambda}=A-\tau\epsilon>0,\qquad
\beta_{\tau,\lambda}=\tau\operatorname{Re}\ell,\qquad
\rho_\lambda=k/\lambda^2.
\tag{37.40}
$$

此时 $\mathsf P_\lambda=O(\lambda^{-3})$，$\mathsf Q_\lambda=O(\lambda^{-3})+O(\lambda^{-2})$，方差恰为零。令

$$
\begin{gathered}
t_\lambda=a_{\rm act}-Hu_\lambda+\ell C^2u_\lambda/2
             =\eta a+O(\lambda^{-3}),\\
e_\lambda=G_\lambda R_\lambda t_\lambda,\qquad
y_\lambda=(D_\lambda^{\rm env})^{-1}
       (e_\lambda-\ell FCu_\lambda/2-Fu_\lambda).
\end{gathered}
\tag{37.41}
$$

原矩阵 $D_\lambda^{\rm env}$ 在每个有限阶段可逆，故这个 $y_\lambda$ 有限，且直接由 (37.3) 得 $Bu_\lambda+Vy_\lambda=a_{\rm act}$。所用环境列正是原最小范数列，$e_0=0$。因此

$$
\lambda^2\mathcal A_\lambda=O(\lambda^{-2})\to0,\qquad
\lambda^2s_\alpha t_\lambda^*R_\lambda t_\lambda
             \to s(A)|\eta|^2,\qquad \zeta_\lambda\to\zeta(c).
\tag{37.42}
$$

例如垂直误差贡献为 $O(\lambda^2\lambda^{-6})$，平行项由 (37.36) 计算；这证明 (37.38)。恢复列可以由发散的 Hermitian 对角元产生，但每个有限阶段都是原来允许的探针。∎

**推论 37.7（严格负接触的原失败、两笔正预算与任意质量）。** 若 $J_k(c)<0$，定理 37.6 的原测试对所有充分大有限 $\lambda$ 严格违反 (37.5)，且两笔原预算严格正。对任意指定 $\mu\in(0,\infty)$ 都有质量 $\phi(I)=\mu$ 的这样的反例。

证明。(37.38) 给 (37.7) 严格负，(27.12) 即给原 PB 严格失败。还须检查预算本身，而不能仅由代价为负推断预算正性。由同一来源的精确末行，

$$
(e_\lambda)_3=\frac{\lambda a^*t_\lambda}{1+\lambda^2m}
               =\frac\eta\lambda+O(\lambda^{-3})\ne0.
\tag{37.43}
$$

同时 $FCu_\lambda=(C^2u_\lambda,0)^{\mathsf T}$，末坐标恰为零，首块非零。原 $R_\tau\xi_\lambda$ 的环境块是 $-\tau FCu_\lambda/2$，而 $E_\tau=(S_\tau-z_\tau R_\tau)\xi_\lambda$ 的环境块恰是 $e_\lambda$。两列复线性独立，对每个 $\tau$ 都有

$$
B_{\phi_{\xi_\lambda}}(R_\tau,S_\tau)
\ge\frac{\|C^2u_\lambda\|^2|(e_\lambda)_3|^2}{4}>0.
\tag{37.44}
$$

该下界先来自环境复 Gram 行列式，加入演员块只增加半正定 Gram 矩阵；原实 Gram 行列式又不小于复 Gram 行列式。$\eta\ne0$ 已由引理 37.4 证明。最后用 $\mu/\|\xi_\lambda\|^2$ 正倍缩放同一向量泛函，严格失败和两笔正预算一起保留。∎

### 37.6 从单位演员域回到全部正泛函

若任意原向量 $\xi=(w,y)$ 的演员分量 $w\ne0$，令 $b_w=\|w\|$，则

$$
\xi=b_w(u,y/b_w),\qquad u=w/b_w,\quad \|u\|=1.
\tag{37.45}
$$

同一 $X$ 与所有变分参数保持不动，(37.7) 和 PB 的两侧都按 $b_w^2$ 缩放。故归一对符号判定充分，即使 $b_w$ 任意小。若 $w=0$，直接由原列有 $x\xi=h_x\xi=r_x\xi=s_\rho\xi=0$，并且

$$
\phi_\xi(L_{\rm PB})=-2\operatorname{Re}((Vy)^*\iota CVy/2)=0;
\tag{37.46}
$$

因此 PB 自动成立，包括零向量。

完整正泛函具有有限谱和 $\phi=\sum_j\phi_{\xi_j}$。对每个固定 $X$，分别把 (17.15) 的二阶实 Gram 行列式根超可加性用于两笔预算，得到

$$
\sqrt{B_\phi(R_\tau,S_\tau)}\ge
\sum_j\sqrt{B_{\phi_{\xi_j}}(R_\tau,S_\tau)},\qquad \tau=\pm1.
\tag{37.47}
$$

这是 (17.14)–(17.16) 的谱和提升；结合左侧的三角不等式即可从全部向量 PB 得到 (37.5)。反向只需取向量泛函。环境密度及演员、环境混合块始终留在完整原代数中。固定任意正有限质量的全称条件等价，因为正倍缩放使 PB 两侧同阶齐次；零质量只有零泛函。两个取向的结论分别应用，要求双取向时两份全称条件同时保留。

这个符号等价不赋予未归一域相同的数值下确界。本节的 (37.14) 不得改成全部 $\xi$ 上的数值下确界：例如 $k=0$ 时，未归一域含零向量而代价非负，其下确界恰为零；归一域却由 (37.25) 得 $\lambda^2\mathcal D_\lambda\ge\gamma/(m+\lambda^{-2})$。以下下确界定理只指单位演员域。

### 37.7 下有界性与全局归一下确界极限

**定理 37.8（先下有界，再取全局极限）。** 对每个固定 $a,h,\iota,k$，存在有限 $C_0,\lambda_0$，使对所有 $\lambda\ge\lambda_0$ 和全部归一原或约化测试，

$$
\lambda^2\mathcal D_\lambda\ge-C_0.
\tag{37.48}
$$

非空接触域上的 $j(k)>-\infty$；若接触域非空则 $j(k)\in\mathbb R$，若为空则 $j(k)=+\infty$。且在扩展实数意义下

$$
\boxed{\ \lim_{\lambda\to\infty}f_\lambda(k)
       =\inf_{c\in\mathcal C_\iota(a)}J_k(c).\ }
\tag{37.49}
$$

证明。若 (37.48) 不成立，可选 $\lambda_n\ge n$ 和归一测试，使 $\lambda_n^2\mathcal D_{\lambda_n}\le-n$。定理 37.5 对上界 $M=0$ 适用，给一个收敛可见子列及有限接触值 $J_k(c)$，并给其下极限至少为 $J_k(c)>-\infty$，与趋于 $-\infty$ 矛盾。这既排除尾部任何 $f_\lambda=-\infty$，也建立统一有限下界。每个有限 $\lambda$ 有有限参数的归一测试，故 $f_\lambda<+\infty$。

若接触值无下界，可取 $c_n$ 满足 $J_k(c_n)\le-2n$，再对每个 $c_n$ 用定理 37.6 选充分大的 $\lambda_n\ge n$，使恢复值不大于 $-n$。这又违反 (37.48)。因此在引用近极小列以前，归一下确界及接触下确界的下有界性都已建立。

接触域非空时，每个固定接触的恢复给 $\limsup f_\lambda(k)\le J_k(c)$；对 $c$ 取下确界得上极限不超过有限的 $j(k)$。取实现 $\liminf_{\lambda\to\infty}f_\lambda(k)$ 的 $\lambda_n\to\infty$，再取有限近极小测试，使其值在 $[f_{\lambda_n},f_{\lambda_n}+1/n]$ 内。已有上下界使这些值具有共同有限上界。定理 37.5 给子列与接触 $c$，从而

$$
\liminf_{\lambda\to\infty}f_\lambda(k)
\ge J_k(c)\ge j(k).
$$

上下极限相合。若接触域为空，而 $f_\lambda$ 不趋于 $+\infty$，则存在 $\lambda_n\to\infty$ 和有限 $M$，使 $f_{\lambda_n}\le M$。取误差至多 $1$ 的近极小测试，定理 37.5 就会产生一个接触，矛盾。因此空域时极限确为 $+\infty$。整个证明使用序列紧性和实际恢复，没有交换未经证明的下确界与极限。∎

### 37.8 全称 PB 的严格阈值及临界边界

**推论 37.9（逐接触的必要性与严格充分性）。** 固定实 $k$。若 (37.2) 在 $\rho=k/\lambda^2$ 对所有充分大 $\lambda$ 满足全部原 PB，则每个 $c\in\mathcal C_\iota(a)$ 有 $J_k(c)\ge0$。若每个接触都有 $J_k(c)>0$，则对所有充分大 $\lambda$ 满足全部原 PB。

证明。负接触由推论 37.7 给尾部失败，证明必要性。反之，若存在 $\lambda_n\to\infty$ 上的失败，由 §37.6 的全正泛函提升及 (27.12) 选出归一原有限测试使 $\mathcal D_{\lambda_n}^{\rm orig}<0$。定理 37.5 对 $M=0$ 给一个接触，且

$$
J_k(c)\le\liminf_n\lambda_n^2\mathcal D_{\lambda_n}^{\rm orig}\le0,
$$

矛盾。此处逐接触严格正已经足够，不额外假设一个统一正间隙。空接触域也由同一矛盾论证给充分性。∎

对当前固定取向，定义两个带方向的阈值；其 $h,\iota$ 依赖在记号中省略：

$$
\begin{aligned}
K_{\rm positive}(a)
 &=\inf_{c\in\mathcal C_\iota(a):\ \epsilon\zeta(c)<0}
       \frac{s(A)|\eta|^2}{-4\epsilon\zeta(c)},\\
K_{\rm negative}(a)
 &=\inf_{c\in\mathcal C_\iota(a):\ \epsilon\zeta(c)>0}
       \frac{s(A)|\eta|^2}{4\epsilon\zeta(c)}.
\end{aligned}
\tag{37.50}
$$

空下确界仍为 $+\infty$。对每个固定 $k\ge0$，$k<K_{\rm positive}(a)$ 时 $\rho=k/\lambda^2$ 最终通过全部原 PB；$k>K_{\rm positive}(a)$ 时最终严格失败。理由是前一范围使每个 $J_k>0$，后一范围由下确界定义找到一个 $J_k<0$。对 $\rho=-k/\lambda^2$，用 $K_{\rm negative}(a)$ 得相同的严格两侧结论。要求两个取向时，分别检查各自的阈值。

在有限阈值等号处，定义只保证所有接触的领先值非负；若有零接触，(37.38) 不决定有限 $\lambda$ 的次阶符号。即使阈值下确界不取到，也必须按实际 $J_k$ 检查：若它们仍逐点严格正，推论 37.9 可用。本文不把非负替换为严格正，不宣称一般的临界等号分类。

### 37.9 一个可恢复而非实际的轴接触

取 $\iota=i$、$0<h$ 充分小，仍处于 §32 邻域。固定实际方向及接触数据

$$
\begin{gathered}
a=(1,\sqrt2)^{\mathsf T}/\sqrt2,\quad m=3/2,\quad
\epsilon=1,\quad u=e_1,\quad \ell=-1-2\iota,\quad A=2,\\
\eta=\sqrt2(-11/2+2\iota),\qquad p_1=q_1=3/2,\\
p_2=\frac{h+\eta}{-1+3\iota/2},\qquad
q_2=-2\iota p_2+\iota h,\qquad
a_{\rm act}=(-3+3\iota,h+\eta)^{\mathsf T}.
\end{gathered}
\tag{37.51}
$$

三个 Hermitian 闭包条件在第一轴只要求 $p_1$ 实且 $q_1=p_1$，故满足。第一接触等式的坐标为
$\iota(1-\ell)(3/2)=-3+3\iota$ 和
$\iota(1-\ell/2)p_2=(-1+3\iota/2)p_2=h+\eta$。
第二接触等式的第一坐标是 $(\ell+2)(3/2)+3\iota=3/2$，第二坐标恰是所给 $q_2$。最后需求的两个坐标分别为 $-11/2+2\iota=\eta/\sqrt2$ 和 $\eta$。所以 (37.19) 全部成立，且

$$
\zeta=-3,\qquad |\eta|^2=137/2,\qquad s(A)=4/3,\qquad
J_k=274/3-12k.
\tag{37.52}
$$

在 $h=0$，$q_2-p_2=(-1-2\iota)\eta/(-1+3\iota/2)\ne0$，故固定充分小正 $h$ 后仍非零。实际第一轴探针却必有 $q=p$，所以这是一个没有有限轴上实现的接触。引理 37.2 的发散对角元恢复给实际趋轴探针；它表明闭包不可直接删去。

每个固定 $k>137/18$ 由此给同源有限阶段的严格 PB 排除与两笔正预算。它们也最终通过两个取向的原 P2：令 $\beta=h/\sqrt2$、$U_0=2^{-1/2}\left(\begin{smallmatrix}1&1\\1&-1\end{smallmatrix}\right)$。这里 $U_0^*C^{-1/2}a=e_1$，实际 P2 的逆坐标矩阵为

$$
\mathsf K=\begin{pmatrix}3/2+\lambda^2&1/2\\1/2&3/2\end{pmatrix}.
$$

由 (30.29)，其精确双取向半径为

$$
\frac{h/\sqrt2}{\sqrt{(3/2+\lambda^2)(3/2)}}.
\tag{37.53}
$$

它为正的 $\lambda^{-1}$ 阶，故支配每个固定 $k/\lambda^2$。例子不声称 $137/18$ 锐，也不声称此轴值低于全部精确有限 $\nu=0$ 接触的下确界。

### 37.10 同谱比较所需的共同尺度与未决边界

若要比较两个实际方向在共同 $M_2$ 谱 $(1,L)$ 下的 PB 阈值，必须分别令

$$
\lambda^2=(L-1)/m,\qquad \rho=q_{\rm shared}/(L-1),\qquad k=q_{\rm shared}/m.
\tag{37.54}
$$

这里 $q_{\rm shared}\in\mathbb R$ 是共同残量尺度。正方向应比较 $mK_{\rm positive}(a)$，负方向应比较 $mK_{\rm negative}(a)$。只比较未乘 $m$ 的阈值不能推出共同 $\rho$ 的差异。

每份来源还必须独立通过实际 P2。若 $a=C^{1/2}U_0w$，$w\in\mathbb C^2\setminus\{0\}$，$h>0$，令

$$
\mathsf K=\begin{pmatrix}3/2&1/2\\1/2&3/2\end{pmatrix}
          +\frac{L-1}{m}ww^*,\qquad z=\mathsf K_{12},\qquad
\beta=h/\sqrt2.
\tag{37.55}
$$

这是该来源的实际逆矩阵坐标。前卷 (30.29) 对取向 $\sigma$ 给精确闭区间

$$
I_\sigma=
\left[
-\frac{\beta}{\sqrt{\mathsf K_{11}\mathsf K_{22}}+\sigma\operatorname{Im}z},\quad
 \frac{\beta}{\sqrt{\mathsf K_{11}\mathsf K_{22}}-\sigma\operatorname{Im}z}
\right].
\tag{37.56}
$$

正定性使两分母严格正。任何拟议的共同 $\rho=q_{\rm shared}/(L-1)$ 都须代入两份实际区间；要求双取向则还须分别取两取向的交。

本节尚未给出两个方向具有严格不同的 $mK_{\rm positive}(a)$ 或 $mK_{\rm negative}(a)$ 的证明，也没有给出共同 P2 允许的 $q_{\rm shared}$ 上一份全部 PB 成立、另一份 PB 失败的成对见证。§36 的共轭相位对不被提升为这种 PB 分离。

本节的 `repo-derived` 纸面增量是同一固定 $M_0$ 来源、单位演员域上的全部上子水平紧性、可见图轴闭包恢复及由此得到的归一下确界极限与严格阈值。原列、变分和完整正泛函提升复用 §§17、27、31 及 (32.4)–(32.7)、(35.13)；全部参数上的基准强制估计复用 §32、(35.16)。正交最小范数、加权方差、Schur 补、Cauchy–Schwarz、有限维序列紧性和谱和 Gram 根不等式均按成熟数学直接使用。本文没有外部文献穷尽或历史优先权主张，没有 Lean／kernel 核验，也不主张物理实现。

增广接触下确界与精确有限 $\nu=0$ 接触下确界是否相同，需要另外的密度或等价论证；本节只恢复近接触的实际原测试，不假设该等式。临界零值的次阶符号、阈值的显式最优值及共同 P2 内的成对 PB 分离仍未解决。

## 追加锚（本行以下为增补区）

## 38. 共同完整 P2 区间内的更强实际有限轴恢复排除

本节固定 (35.5)、(37.2) 的两个实来源方向 $a_\tau=(1/\sqrt2,\tau)^{\mathsf T}$，$\tau=\pm1$。两份来源的完整原 P2 区间完全相同，但在该区间的严格内部，每个固定 $k>809/480$、$\rho=k/\lambda^2$ 都在充分大的有限阶段违反原 PB。这里的界严格加强 §37.9 的 $k>137/18$：

$$
\frac{809}{480}<\frac{137}{18}.
$$

证明直接构造有限 Hermitian 探针及同一来源上的环境向量，并保留两笔严格正的原预算。原残量矩阵始终是 $T_A=\operatorname{diag}(1,-2)$；本节不将它替换成归一化后的 $\operatorname{diag}(1,-1)$。前卷式号仍取 §37 所引钉版的含义。

### 38.1 两个实际来源、原条件与排除定理

在 $\mathbb C^2\oplus(\mathbb C^2\oplus\mathbb C)$ 上置

$$
\begin{gathered}
C=\operatorname{diag}(1,2),\qquad T_A=\operatorname{diag}(1,-2),\qquad
J_A=\begin{pmatrix}0&1\\1&0\end{pmatrix},\\
a_\tau=(1/\sqrt2,\tau)^{\mathsf T},\qquad b=\|a_\tau\|^2=3/2,\qquad
H=2C+hJ_A,\qquad B=H+C,\\
\delta_\lambda=\lambda^{-3},\qquad
F=\begin{bmatrix}C\\0\end{bmatrix},\qquad
G_{\tau,\lambda}=\begin{bmatrix}I_2\\\lambda a_\tau^*\end{bmatrix},\\
D_{\tau,\lambda}=\begin{pmatrix}
C+\delta_\lambda\lambda^2a_\tau a_\tau^*&-\delta_\lambda\lambda a_\tau\\
-\delta_\lambda\lambda a_\tau^*&\delta_\lambda
\end{pmatrix},\qquad
t_{\tau,\lambda}=\begin{pmatrix}B&F^*\\F&D_{\tau,\lambda}\end{pmatrix}.
\end{gathered}
\tag{38.1}
$$

这就是 (35.5) 的原实际实现。固定一份来源后，简写 $D=D_{\tau,\lambda}$、$G=G_{\tau,\lambda}$、$t=t_{\tau,\lambda}$。环境正二次型及精确矩恒等式为

$$
\begin{gathered}
(v,z)^*D(v,z)=v^*Cv+\delta_\lambda|z-\lambda a_\tau^*v|^2,\\
DG=F,\qquad F^*F=C^2,\qquad F^*G=G^*F=C,\qquad
M_2=G^*G=I_2+\lambda^2a_\tau a_\tau^*,\\
B-F^*D^{-1}F=H.
\end{gathered}
\tag{38.2}
$$

因此每个有限 $\lambda>0$ 上 $D\succ0$；当 $0<h<2\sqrt2$ 时，$H$ 的首主子式为 $2$、行列式为 $8-h^2>0$，从而 $t\succ0$。两份来源共享 $H,M_0=C^2,M_1=C,W=0$ 及 $M_2$ 的整个谱 $\{1,1+(3/2)\lambda^2\}$，并各自保留自己的实际环境。

为区分来源符号 $\tau$ 与两笔预算，用 $d=\pm1$ 标记原列。给定取向 $\iota=\sigma i$、$\sigma=\pm1$，在完整 $M_5(\mathbb C)$ 上定义

$$
\begin{gathered}
A\circ B=(AB+BA)/2,\qquad K_\sigma(A,B)=\sigma i[A,B]/2,\\
c=C\oplus0_3,\quad s_\rho=\rho T_A\oplus0_3,\quad
x=X\oplus0_3,\quad X=X^*,\quad g=K_\sigma(c,t)+s_\rho,\\
h_x=K_\sigma(c,x),\qquad k_c=c\circ t,\qquad r_x=c\circ x,\\
R_d=x+d(h_x-k_c),\qquad S_d=t+d(r_x+g),\\
L_{\rm PB}=-2x\circ(h_x-k_c)-2t\circ(r_x+g),\\
B_\phi(R,S)=\phi(R^2)\phi(S^2)-\phi(R\circ S)^2.
\end{gathered}
\tag{38.3}
$$

完整原 P2 要求每个正复线性泛函 $\phi$ 满足

$$
\phi(g)^2\le\phi(c^2)\phi(t^2)-\phi(c\circ t)^2.
\tag{38.4}
$$

全部原 PB 要求每个实际 $X=X^*$ 及每个这样的 $\phi$ 满足

$$
|\phi(L_{\rm PB})|\le\sqrt{B_\phi(R_+,S_+)}+\sqrt{B_\phi(R_-,S_-)}.
\tag{38.5}
$$

所有平方、乘积与泛函均在 (38.1) 的完整原代数中计算。

**定理 38.1（$809/480$ 的实际有限恢复排除）。** 固定 $0<h<2\sqrt2$、有限实数 $k>809/480$ 及任意指定质量 $\mu\in(0,\infty)$。存在有限 $\Lambda(h,k)>1$，使每个有限 $\lambda>\Lambda(h,k)$、每份 $\tau=\pm1$ 来源、每个取向 $\sigma=\pm1$ 都满足：

1. 其完整原 P2 的精确允许集均为同一个闭区间

   $$
   I_{\tau,\sigma}=\left[-\frac{h/\sqrt2}{T_\lambda},\frac{h/\sqrt2}{T_\lambda}\right],
   \qquad T_\lambda=\sqrt{\frac32\left(\frac32+\lambda^2\right)},
   \tag{38.6}
   $$

   且 $\rho=k/\lambda^2$ 严格位于其内部。
2. 存在有限实际 Hermitian 探针 $x=X\oplus0_3$ 和同一来源上的一个向量正泛函 $\phi$，$\phi(I)=\mu$，使 (38.5) 严格失败，并且

   $$
   B_\phi(R_+,S_+)>0,\qquad B_\phi(R_-,S_-)>0.
   \tag{38.7}
   $$

见证可随来源与取向变化；每份输入内的两笔预算使用同一 $x$、同一 $\phi$ 和该输入自己的 $D,F,G$。固定 $h$ 后，对任意紧区间 $k\in[m,M]$、$m>809/480$，可选共同的有限截止 $\Lambda(h,[m,M])$。特别地，结论适用于 §37 所需的充分小固定正 $h$；以下证明本身只用 $0<h<2\sqrt2$。

### 38.2 精确轴接触与常数

先取 $\sigma=+1$。固定合法有限变分参数

$$
\begin{gathered}
\epsilon=1,\qquad \ell=-1-9i,\qquad \nu=0,\\
\alpha_+=8,\quad\alpha_-=10,\quad\beta_+=-1,\quad\beta_-=1,\\
z_d=\beta_d-di\alpha_d=i+d\ell,\qquad
s_\alpha=\alpha_+^{-1}+\alpha_-^{-1}=9/40.
\end{gathered}
\tag{38.8}
$$

令 $u=e_1$，并定义目标可见列

$$
\begin{gathered}
p_1=q_1=1/3,\qquad (a_{\rm act})_1=-3+2i/3,\\
d_{01}=-11/2-23i/6,\qquad\eta=\sqrt2\,d_{01},\qquad
(a_{\rm act})_2=h+\eta\tau,\\
p_2=\frac{h+\eta\tau}{i(1-\ell/2)},\qquad
q_2=(\ell+1)p_2+ih,\qquad
i(1-\ell/2)=-9/2+3i/2\ne0,\\
v=a_{\rm act}-ip,\qquad U=iq+BCu+Cv.
\end{gathered}
\tag{38.9}
$$

逐坐标代入给出

$$
v_1=-3+i/3=-i\ell/3,\quad U_1=2i/3,\qquad
v_2=-i\ell p_2/2,\quad U_2=ip_2.
$$

所以两条零残量演员接触恰为

$$
P_0=v+\ell U/2=0,\qquad Q_0=iCv-\ell p=0.
\tag{38.10}
$$

需求列及残量配对也完全确定：

$$
\begin{gathered}
d_0=a_{\rm act}-Hu+\ell C^2u/2=(d_{01},\eta\tau)^{\mathsf T}
      =\eta a_\tau,\\
|d_{01}|^2=\frac{121}{4}+\frac{529}{36}=\frac{809}{18},\qquad
|\eta|^2=\frac{809}{9},\qquad
\operatorname{Re}(v^*T_Au)=-3.
\end{gathered}
\tag{38.11}
$$

在 $u=e_1$ 上实际探针必须有 $q=p$；(38.9) 不以 $q_2=p_2$ 为前提。因此必须先恢复实际有限列，才能把这些接触数据用于原 PB。

### 38.3 包括零差分支的有限 Hermitian 恢复

记

$$
s_{\rm vis}=2p_2-q_2,\qquad t_{\rm vis}=q_2-p_2.
$$

若 $t_{\rm vis}\ne0$，对每个有限 $\lambda>1$ 置

$$
\begin{gathered}
\varepsilon_\lambda=\lambda^{-3},\qquad
(u_\lambda)_2=\varepsilon_\lambda\frac{t_{\rm vis}}{|t_{\rm vis}|},\qquad
(u_\lambda)_1=\sqrt{1-\varepsilon_\lambda^2},\\
X_\lambda=\begin{pmatrix}
1/3&\overline{s_{\rm vis}}/(u_\lambda)_1\\
s_{\rm vis}/(u_\lambda)_1&|t_{\rm vis}|/\varepsilon_\lambda
\end{pmatrix},\qquad
p_\lambda=X_\lambda u_\lambda,\qquad q_\lambda=X_\lambda Cu_\lambda.
\end{gathered}
\tag{38.12}
$$

矩阵逐项有限且 Hermitian，$\|u_\lambda\|=1$，所有分母非零。直接相乘，第二坐标精确为

$$
(p_\lambda)_2=s_{\rm vis}+t_{\rm vis}=p_2,\qquad
(q_\lambda)_2=s_{\rm vis}+2t_{\rm vis}=q_2.
$$

第一坐标分别为

$$
(p_\lambda)_1=\frac{(u_\lambda)_1}{3}
 +\frac{\overline{s_{\rm vis}}(u_\lambda)_2}{(u_\lambda)_1},\qquad
(q_\lambda)_1=\frac{(u_\lambda)_1}{3}
 +\frac{2\overline{s_{\rm vis}}(u_\lambda)_2}{(u_\lambda)_1}.
$$

若 $t_{\rm vis}=0$，则 $q=p$，改取

$$
u_\lambda=e_1,\qquad
X_\lambda=\begin{pmatrix}1/3&\overline{p_2}\\p_2&0\end{pmatrix},
\qquad p_\lambda=p,\quad q_\lambda=q.
\tag{38.13}
$$

此分支不除以 $t_{\rm vis}$，也不除以零演员坐标。两种情形共同给出实际 $x_\lambda=X_\lambda\oplus0_3$，以及

$$
u_\lambda-u=O(\lambda^{-3}),\qquad
p_\lambda-p=O(\lambda^{-3}),\qquad q_\lambda-q=O(\lambda^{-3}).
\tag{38.14}
$$

这些是可见列估计，不要求 $X_\lambda$ 一致有界。

### 38.4 同一来源上的精确环境提升

保持 $a_{\rm act},\ell$ 及 (38.8) 固定。对刚构造的实际 $u_\lambda,X_\lambda$ 定义

$$
\begin{gathered}
d_\lambda=a_{\rm act}-Hu_\lambda+\ell C^2u_\lambda/2,\qquad
w_\lambda=FCu_\lambda=(C^2u_\lambda,0)^{\mathsf T},\\
e_\lambda=GM_2^{-1}d_\lambda,\qquad
y_\lambda=D^{-1}(e_\lambda-\ell w_\lambda/2-Fu_\lambda),\qquad
\xi_\lambda=(u_\lambda,y_\lambda).
\end{gathered}
\tag{38.15}
$$

全部量在每个有限 $\lambda>1$ 上有限。由 (38.2) 有 $G^*e_\lambda=d_\lambda$，故

$$
\begin{gathered}
Fu_\lambda+Dy_\lambda=e_\lambda-\ell w_\lambda/2,\\
Bu_\lambda+F^*y_\lambda
 =Hu_\lambda+d_\lambda-\ell C^2u_\lambda/2=a_{\rm act}.
\end{gathered}
\tag{38.16}
$$

因此演员列及两条环境缺陷确由同一原向量 $\xi_\lambda$ 同时实现。

由 (38.11)、(38.14)，$d_\lambda=\eta a_\tau+\Delta_\lambda$，其中 $\Delta_\lambda=O(\lambda^{-3})$。令 $L_\lambda=1+b\lambda^2$，则

$$
\begin{gathered}
M_2^{-1}=I_2-\frac{\lambda^2a_\tau a_\tau^*}{L_\lambda},\qquad
M_2^{-1}a_\tau=\frac{a_\tau}{L_\lambda},\qquad
\|GM_2^{-1}\|\le1,\\
\|e_\lambda\|^2=d_\lambda^*M_2^{-1}d_\lambda
 =\frac{|\eta|^2b}{L_\lambda}+O(\lambda^{-4}),\qquad
\lambda^2\|e_\lambda\|^2\longrightarrow\frac{809}{9}.
\end{gathered}
\tag{38.17}
$$

这里算子范数界来自 $(GM_2^{-1})^*(GM_2^{-1})=M_2^{-1}\le I_2$；主环境列范数为 $O(\lambda^{-1})$，扰动列为 $O(\lambda^{-3})$，给出所列误差。尤其，原环境的最后坐标满足精确公式

$$
(e_\lambda)_3=\frac{\lambda a_\tau^*d_\lambda}{L_\lambda}
 =\frac{\eta}{\lambda}+O(\lambda^{-3})\ne0
\quad\text{对所有充分大有限 }\lambda.
\tag{38.18}
$$

### 38.5 原作用列与严格负缺陷

以下所有 $R_d,S_d,L_{\rm PB}$ 均取当前实际 $x_\lambda,t_{\tau,\lambda},\rho$。置

$$
\begin{gathered}
v_\lambda=a_{\rm act}-ip_\lambda,\qquad
U_\lambda=iq_\lambda+BCu_\lambda+Cv_\lambda,\\
P_\lambda=v_\lambda+\ell U_\lambda/2,\qquad
Q_\lambda=iCv_\lambda-\ell p_\lambda+\rho T_Au_\lambda.
\end{gathered}
\tag{38.19}
$$

前卷 (31.6)–(31.7) 的原列，在此记号下直接成为

$$
\begin{aligned}
R_d\xi_\lambda&=(p_\lambda-dU_\lambda/2,-dw_\lambda/2),\\
S_d\xi_\lambda&=\left(a_{\rm act}
 +d\left(\frac{Cp_\lambda+q_\lambda+iCa_{\rm act}-iBCu_\lambda}{2}
                +\rho T_Au_\lambda\right),\,
 Fu_\lambda+Dy_\lambda-di w_\lambda/2\right).
\end{aligned}
\tag{38.20}
$$

由 $z_d=i+d\ell$ 及 (38.16)，其完成列精确为

$$
E_d=(S_d-z_dR_d)\xi_\lambda=(P_\lambda+dQ_\lambda,e_\lambda).
\tag{38.21}
$$

对同一个原正向量泛函 $\phi_\lambda(A)=\xi_\lambda^*A\xi_\lambda$ 定义所选有限变分缺陷

$$
\mathcal D_\lambda=
\sum_{d=\pm1}\left(\alpha_d\|R_d\xi_\lambda\|^2
 +\alpha_d^{-1}\|(S_d-\beta_dR_d)\xi_\lambda\|^2\right)
 -2\phi_\lambda(L_{\rm PB}).
\tag{38.22}
$$

原恒等式 (31.9)，等价于 (32.4)，对 (38.20)–(38.21) 给出精确等式

$$
\mathcal D_\lambda=
\sum_{d=\pm1}\alpha_d^{-1}\|P_\lambda+dQ_\lambda\|^2
 +\frac9{40}\|e_\lambda\|^2
 +4\rho\operatorname{Re}(v_\lambda^*T_Au_\lambda).
\tag{38.23}
$$

它保留实际演员误差与实际环境误差。由 (38.10)、(38.14) 有

$$
P_\lambda=O(\lambda^{-3}),\qquad
Q_\lambda=\rho T_Au_\lambda+O(\lambda^{-3}),\qquad
\operatorname{Re}(v_\lambda^*T_Au_\lambda)=-3+O(\lambda^{-3}).
$$

取 $\rho=k/\lambda^2$，演员平方和为 $O(\lambda^{-4})$。结合 (38.17) 得

$$
\lambda^2\mathcal D_\lambda\longrightarrow
\frac9{40}\frac{809}{9}-12k=\frac{809}{40}-12k<0
\qquad(k>809/480).
\tag{38.24}
$$

因而每个充分大的有限阶段都有 $\mathcal D_\lambda<0$。前卷 (27.12) 的实 Gram 变分不等式，对这里同一对实际原列分别给

$$
2\sqrt{B_{\phi_\lambda}(R_d,S_d)}\le
\alpha_d\|R_d\xi_\lambda\|^2
 +\alpha_d^{-1}\|(S_d-\beta_dR_d)\xi_\lambda\|^2.
$$

相加并用 (38.22)，得到

$$
\phi_\lambda(L_{\rm PB})>
\sqrt{B_{\phi_\lambda}(R_+,S_+)}+
\sqrt{B_{\phi_\lambda}(R_-,S_-)}\ge0.
\tag{38.25}
$$

这严格违反原绝对值 PB，不要求所选变分参数达到任一 Gram 根的下确界。两份来源只有有限个 $\tau$ 值；各误差对有界 $k$ 一致，故 (38.24) 在每个 $[m,M]$、$m>809/480$ 上一致严格为负。

### 38.6 两笔实际预算同时严格正

由 (38.20)，$R_d\xi_\lambda$ 的最后环境坐标恰为零，而 $E_d$ 的该坐标由 (38.18) 非零。又 $R_d\xi_\lambda$ 的环境首块为 $-dC^2u_\lambda/2\ne0$。因此 $R_d\xi_\lambda$ 与 $E_d$ 复线性独立；$S_d\xi_\lambda=z_dR_d\xi_\lambda+E_d$，故 $R_d\xi_\lambda,S_d\xi_\lambda$ 也复线性独立。

更明确地，复 Gram 行列式的二坐标子式展开，只取最后环境坐标与其余两个环境坐标，就给

$$
\begin{aligned}
B_{\phi_\lambda}(R_d,S_d)
&=\|R_d\xi_\lambda\|^2\|S_d\xi_\lambda\|^2
 -\bigl[\operatorname{Re}((R_d\xi_\lambda)^*S_d\xi_\lambda)\bigr]^2\\
&\ge\|R_d\xi_\lambda\|^2\|S_d\xi_\lambda\|^2
 -|(R_d\xi_\lambda)^*S_d\xi_\lambda|^2\\
&\ge\frac{\|C^2u_\lambda\|^2|(e_\lambda)_3|^2}{4}>0,
\qquad d=\pm1.
\end{aligned}
\tag{38.26}
$$

第二个不等式也可直接对 $R_d\xi_\lambda,E_d$ 作同一子式展开，因为增加 $z_dR_d\xi_\lambda$ 不改变这些子式。这个原预算下界适用于实际随 $\lambda$ 变化的全部列，无须另加探针扰动。

### 38.7 完整 P2 的精确共同区间与严格内点

归一化 Schur 矩阵及其有序谱基为

$$
C^{-1/2}HC^{-1/2}=2I_2+\beta J_A,\qquad
\beta=h/\sqrt2>0,\qquad
U_0=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}.
$$

有 $U_0^*C^{-1/2}a_+=e_1$、$U_0^*C^{-1/2}a_-=e_2$。故原 P2 的精确逆矩阵坐标为

$$
\begin{aligned}
\mathsf K_+&=U_0^*C^{-1/2}(I_2+M_{2,+})C^{-1/2}U_0
 =\begin{pmatrix}3/2+\lambda^2&1/2\\1/2&3/2\end{pmatrix},\\
\mathsf K_-&=\begin{pmatrix}3/2&1/2\\1/2&3/2+\lambda^2\end{pmatrix},\qquad
\mathfrak d_\lambda=\det\mathsf K_\tau=2+(3/2)\lambda^2.
\end{aligned}
\tag{38.27}
$$

前卷 (30.29) 中 $\omega=1$，$Q_M=\mathsf K_\tau^{-1}$ 的非对角元是实数 $-1/(2\mathfrak d_\lambda)$。因此两份来源、两个取向都准确满足

$$
J=0,\qquad \Delta=\frac1{\mathfrak d_\lambda},\qquad
R=\frac{T_\lambda}{\mathfrak d_\lambda}.
$$

代入该完整原 P2 判据，所得恰是 (38.6)，包括两个端点。这是对完整正泛函的允许集，并非只检验所构造的向量泛函。

对于 $k>0$，$\rho=k/\lambda^2$ 严格在 (38.6) 内的充要条件为

$$
h^2\lambda^4>3k^2(\lambda^2+3/2).
\tag{38.28}
$$

固定 $h,k$ 后此式最终成立。具体地，$\lambda^2\ge3/2$ 时 $T_\lambda\le\sqrt3\lambda$，所以再取 $\lambda>\sqrt6\,k/h$ 就足够；对 $k\in[m,M]$ 将此界中的 $k$ 换成 $M$。P2 端点的非零尺度为 $\lambda^{-1}$，严格内点的残量尺度为 $\lambda^{-2}$。

### 38.8 两个取向、指定质量及结论边界

(38.1) 的两份来源和原 $T_A$ 全为实矩阵。逐项复共轭将 $\sigma=+1$ 的 $X_\lambda,\xi_\lambda$ 送到 $\sigma=-1$ 的实际 Hermitian 探针与实际向量，同时将 $i,\ell,a_{\rm act}$ 共轭，保持 $\alpha_d,\beta_d,\epsilon$ 不变。原 $R_d,S_d,L_{\rm PB}$ 的作用列也逐项共轭，所以 (38.25) 的实数值与 (38.26) 的两笔预算均保持不变。因此每份来源在两个取向都具有所需严格失败。

又 $\|u_\lambda\|=1$，故 $\xi_\lambda\ne0$。对任意指定 $\mu\in(0,\infty)$，取

$$
\widehat\xi_\lambda=\frac{\sqrt\mu}{\|\xi_\lambda\|}\xi_\lambda,\qquad
\widehat\phi_\lambda(A)=\widehat\xi_\lambda^*A\widehat\xi_\lambda.
\tag{38.29}
$$

则 $\widehat\phi_\lambda(I)=\mu$。正倍缩放使 PB 两端同倍变化、两笔预算同一个正数平方倍变化，故严格失败与两笔正预算同时保留。P2 的完整泛函判据不受此见证质量的选择影响。将有限个来源、取向及严格内点所需截止取最大值，完成定理 38.1 的全部量词；紧 $k$ 区间的统一版本由 (38.24)、(38.28) 给出。

实 Gram 变分、正交最小范数及 Schur 补沿前卷 §§27、30、31 的成熟背景使用；本节的显式接触 (38.8)–(38.11) 与原来源代入 (38.12)–(38.29) 给出具体的纸面加强。结论只把 $809/480$ 作为这组恢复轴见证的充分最终排除界，不判等号，不给必要性、最优常数或全部 PB 分类。它没有给出较小 $k$ 的 PB 成功证书，也没有给出共同 P2 内一份来源全部 PB 成功、另一份失败的成对分离。这里每个违反均属于有限矩阵、有限实际探针与同一实际正泛函；不涉及物理实现结论。

## 追加锚（本行以下为增补区）
